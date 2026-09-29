using StrataLint.Engine;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;

namespace StrataLint.EngineeringScope;

internal static partial class LeanCacheEnsureCommand
{
    private const string ColdBuildConsentVariable = "STRATALINT_ACCEPT_COLD_BUILD";
    private const string LinkedArchiveDisabled = "linked worktree: release archive disabled";

    private sealed record CacheState(
        OleanWarmthInspection Mathlib,
        OleanWarmthInspection Project)
    {
        internal bool AllCold => !Mathlib.IsWarm && !Project.IsWarm;

        internal bool HasProbeFailure => Mathlib.State == OleanWarmth.ProbeFailed
            || Project.State == OleanWarmth.ProbeFailed;

        internal string ProbeFailureDescription => string.Join(
            "; ",
            new[]
            {
                Mathlib.State == OleanWarmth.ProbeFailed
                    ? $"mathlib: {Mathlib.Error ?? "unknown probe failure"}"
                    : null,
                Project.State == OleanWarmth.ProbeFailed
                    ? $"project: {Project.Error ?? "unknown probe failure"}"
                    : null,
            }.Where(static detail => detail is not null));
    }

    internal const string Usage = "USAGE: StrataLint worktree ensure-cache [--path DIR] [--donor-repository DIR]";
    internal const string WriterUsage =
        "USAGE: StrataLint worktree with-cache-writer [--path DIR] [--donor-repository DIR] -- COMMAND [ARG ...]";

    internal static CommandResult Run(
        string repositoryRoot,
        IReadOnlyList<string> arguments,
        IWorktreeProcessRunner runner,
        IDirectoryCloner cloner,
        bool continueOnCacheGetFailure = false) =>
        Run(
            repositoryRoot,
            arguments,
            runner,
            cloner,
            removePartial: null,
            FileSystemLeanCacheStateProbe.Instance,
            continueOnCacheGetFailure);

    internal static CommandResult Run(
        string repositoryRoot,
        IReadOnlyList<string> arguments,
        IWorktreeProcessRunner runner,
        IDirectoryCloner cloner,
        Action<string>? removePartial) =>
        Run(
            repositoryRoot,
            arguments,
            runner,
            cloner,
            removePartial,
            FileSystemLeanCacheStateProbe.Instance);

    internal static CommandResult Run(
        string repositoryRoot,
        IReadOnlyList<string> arguments,
        IWorktreeProcessRunner runner,
        IDirectoryCloner cloner,
        Action<string>? removePartial,
        ILeanCacheStateProbe stateProbe,
        bool continueOnCacheGetFailure = false)
    {
        ArgumentNullException.ThrowIfNull(arguments);
        ArgumentNullException.ThrowIfNull(runner);
        ArgumentNullException.ThrowIfNull(cloner);
        ArgumentNullException.ThrowIfNull(stateProbe);
        if (!TryParseWorktreeRoot(repositoryRoot, arguments, out var root, out var donorRepository))
        {
            return new CommandResult(false, string.Empty, Usage + "\n");
        }

        var pins = LeanPinSet.TryReadWorktree(root, out var pinReason);
        if (pins is null)
        {
            return FailureReceipt(
                "failed",
                root,
                donor: null,
                method: "none",
                pinSha256: null,
                reason: pinReason ?? "Lean pin files are unavailable");
        }

        if (!LeanLakeExecutable.TryResolve(out var lakeExecutable, out var lakeReason))
        {
            return FailureReceipt(
                "failed",
                root,
                donor: null,
                method: "none",
                pins.Sha256,
                lakeReason);
        }

        var lake = Path.Combine(root, ".lake");
        using var guard = LeanCacheWriterGuard.TryAcquire(lake);
        if (guard is null)
        {
            return FailureReceipt(
                "busy",
                root,
                donor: null,
                method: "none",
                pins.Sha256,
                "canonical cache writer guard is busy");
        }

        return EnsureLocked(
            root,
            pins,
            lakeExecutable,
            runner,
            cloner,
            guard,
            removePartial,
            continueOnCacheGetFailure,
            stateProbe,
            out _, donorRepository);
    }

    internal static CommandResult RunWithWriter(
        string repositoryRoot,
        IReadOnlyList<string> arguments,
        IWorktreeProcessRunner runner,
        IDirectoryCloner cloner, Stream? standardOutput = null, Stream? standardError = null) =>
        RunWithWriter(
            repositoryRoot,
            arguments,
            runner,
            cloner,
            FileSystemLeanCacheStateProbe.Instance,
            Environment.GetEnvironmentVariable, standardOutput, standardError);

    internal static CommandResult RunWithWriter(
        string repositoryRoot,
        IReadOnlyList<string> arguments,
        IWorktreeProcessRunner runner,
        IDirectoryCloner cloner,
        ILeanCacheStateProbe stateProbe,
        Func<string, string?> readEnvironment,
        Stream? standardOutput = null, Stream? standardError = null)
    {
        ArgumentNullException.ThrowIfNull(cloner);
        ArgumentNullException.ThrowIfNull(stateProbe);
        ArgumentNullException.ThrowIfNull(readEnvironment);
        if (!TryParseWriter(repositoryRoot, arguments, out var root, out var command, out var donorRepository))
        {
            return new CommandResult(false, string.Empty, WriterUsage + "\n");
        }

        var pins = LeanPinSet.TryReadWorktree(root, out var pinReason);
        if (pins is null)
        {
            return FailureReceipt(
                "failed",
                root,
                donor: null,
                method: "none",
                pinSha256: null,
                reason: pinReason ?? "Lean pin files are unavailable");
        }

        using var guard = LeanCacheWriterGuard.TryAcquire(Path.Combine(root, ".lake"));
        if (guard is null)
        {
            return FailureReceipt(
                "busy",
                root,
                donor: null,
                method: "none",
                pins.Sha256,
                "canonical cache writer guard is busy");
        }

        var ensured = EnsureLocked(
            root,
            pins,
            command[0],
            runner,
            cloner,
            guard,
            removePartial: null,
            continueOnCacheGetFailure: true,
            stateProbe,
            out var cacheState, donorRepository);
        if (!ensured.Success) return ensured;

        var receipt = ensured.Output;
        if (cacheState is null)
        {
            return new CommandResult(
                false,
                receipt,
                "cold-build guard did not receive a cache state from ensure\n");
        }
        if (cacheState.AllCold)
        {
            var consent = string.Equals(
                readEnvironment(ColdBuildConsentVariable),
                "1",
                StringComparison.Ordinal);
            if (!consent)
            {
                var refusal = cacheState.HasProbeFailure
                    ? "COLD_BUILD_REFUSED cache warmth probe failed and was treated as cold (fail-closed): "
                        + cacheState.ProbeFailureDescription
                    : "COLD_BUILD_REFUSED mathlib and project olean caches are both cold.";
                var target = ShellQuote(root);
                return new CommandResult(
                    false,
                    receipt,
                    refusal + "\n"
                    + $"Fetch caches with: make -C {target} lean-cache-ensure\n"
                    + "To accept this cold build once, run: "
                    + $"{ColdBuildConsentVariable}=1 make -C {target} lean\n");
            }
            receipt = RecordColdBuildConsent(receipt);
        }

        try
        {
            if (standardOutput is not null)
            {
                standardOutput.Write(Encoding.UTF8.GetBytes(receipt));
                standardOutput.Flush();
            }
            var invoked = runner.Run(
                command[0],
                command.Skip(1).ToArray(),
                root,
                LeanCacheProvisioner.LeanCommandBudget, standardOutput, standardError);
            return new CommandResult(
                invoked.ExitCode == 0,
                standardOutput is null ? receipt + Encoding.UTF8.GetString(invoked.StandardOutput) : string.Empty,
                standardError is null ? Encoding.UTF8.GetString(invoked.StandardError) : string.Empty, invoked.ExitCode);
        }
        catch (OperationCanceledException) { throw; }
        catch (Exception exception)
        {
            return new CommandResult(false, standardOutput is null ? receipt : string.Empty, exception.Message + "\n");
        }
    }

    private static CommandResult EnsureLocked(
        string root,
        LeanPinSet pins,
        string lakeExecutable,
        IWorktreeProcessRunner runner,
        IDirectoryCloner cloner,
        LeanCacheWriterGuard writerGuard,
        Action<string>? removePartial,
        bool continueOnCacheGetFailure,
        ILeanCacheStateProbe stateProbe,
        out CacheState? cacheState,
        string? donorRepository)
    {
        cacheState = null;
        var archive = LeanArchiveAttempt.Skipped("not reached");
        var lake = Path.Combine(root, ".lake");
        writerGuard.RequireOwnershipOf(lake);
        string? stampMiss = null;
        var missingDonorClonefile = ClonefileReceipt.NotRun;
        try
        {
            if (IsSymlink(lake)) return RefusedSymlink(root, pins.Sha256);
            var projectWarmth = stateProbe.ProbeOleans(ProjectOleanRoot(lake));

            string? missReason = null;
            if (Directory.Exists(lake))
            {
                var stamp = LeanCacheStamp.Inspect(lake, pins);
                missReason = stamp.Reason;
                stampMiss = ReceiptStampMiss(stamp.State);
                if (stamp.State == LeanCacheStampState.Match)
                {
                    if (projectWarmth.State == OleanWarmth.Cold)
                    {
                        var location = GitWorktreeInventory.Locate(root, runner);
                        if (location.IsLinked)
                        {
                            using var mainDonor = GitWorktreeInventory.SelectMainDonor(
                                location,
                                pins,
                                runner,
                                stateProbe);
                            return mainDonor.Donor is null
                                ? LinkedFailure(
                                    root,
                                    pins,
                                    location,
                                    mainDonor.Notice,
                                    stampMiss)
                                : LinkedLaneReseedFailure(
                                    root,
                                    pins,
                                    location,
                                    stampMiss);
                        }

                        // A main checkout may fill an empty project layer from the Release archive.
                        var contentRoot = stateProbe.InspectContentRoot(
                            Path.Combine(lake, "build"));
                        archive = contentRoot.Clear
                            ? LeanArchiveFetch.Run(root, runner, ArchiveBudget, writerGuard)
                            : LeanArchiveAttempt.Skipped(
                                contentRoot.Error ?? "content root already exists");
                        if (archive.Outcome == LeanArchiveOutcome.Unpacked)
                        {
                            projectWarmth = stateProbe.ProbeOleans(ProjectOleanRoot(lake));
                        }
                    }
                    else
                    {
                        archive = LeanArchiveAttempt.Skipped(
                            $"project olean state is {ReceiptWarmth(projectWarmth.State)}");
                    }

                    return SuccessWithState(
                        SuccessReceipt(
                        "present",
                        root,
                        donor: null,
                        method: "none",
                        pins.Sha256,
                        reason: null,
                        LeanCacheProvisioner.InspectMathlibOleans(lake),
                        archive: archive),
                        root,
                        projectWarmth,
                        stateProbe,
                        out cacheState, writerGuard, runner);
                }

                if (stamp.State == LeanCacheStampState.Mismatch)
                {
                    var location = GitWorktreeInventory.Locate(root, runner);
                    if (location.IsLinked)
                    {
                        return ProvisionLinkedFromMain(
                            root,
                            pins,
                            runner,
                            cloner,
                            writerGuard,
                            removePartial,
                            stateProbe,
                            location,
                            replaceExisting: true,
                            stampMiss,
                            out cacheState);
                    }
                    RemoveProjection(lake);
                    projectWarmth = new OleanWarmthInspection(OleanWarmth.Cold, null);
                }
                else
                {
                    var location = GitWorktreeInventory.Locate(root, runner);
                    if (location.IsLinked)
                    {
                        if (stamp.State == LeanCacheStampState.Missing
                            && projectWarmth.State == OleanWarmth.Cold
                            && stateProbe.InspectContentRoot(Path.Combine(lake, "build")).Clear)
                        {
                            return ProvisionLinkedBuildFromMain(
                                root,
                                pins,
                                runner,
                                cloner,
                                writerGuard,
                                stateProbe,
                                location,
                                stampMiss,
                                out cacheState);
                        }

                        return ProvisionLinkedFromMain(
                            root,
                            pins,
                            runner,
                            cloner,
                            writerGuard,
                            removePartial,
                            stateProbe,
                            location,
                            replaceExisting: true,
                            stampMiss,
                            out cacheState);
                    }

                    if (stamp.State == LeanCacheStampState.Missing
                        && projectWarmth.State == OleanWarmth.Cold)
                    {
                        var contentRoot = stateProbe.InspectContentRoot(Path.Combine(lake, "build"));
                        if (contentRoot.Clear)
                        {
                            LeanCacheDonorSelection? buildDonor = null;
                            try
                            {
                                buildDonor = GitWorktreeInventory.SelectDonor(
                                    root,
                                    pins,
                                    runner,
                                    stateProbe,
                                    requireProjectWarm: true);
                            }
                            catch (Exception exception)
                            {
                                missReason = JoinReasons(
                                    missReason,
                                    $"donor enumeration failed closed: {exception.Message}");
                            }

                            if (buildDonor is not null)
                            {
                                using (buildDonor)
                                {
                                    missReason = JoinReasons(missReason, buildDonor.Notice);
                                    if (buildDonor.Donor is not null)
                                    {
                                        var attempt = LeanMissingBuildProvisioner.TryProvision(
                                            buildDonor,
                                            root,
                                            pins,
                                            runner,
                                            writerGuard,
                                            cloner,
                                            stateProbe);
                                        missingDonorClonefile = attempt.Clonefile;
                                        missReason = JoinReasons(missReason, attempt.Warning);
                                        if (attempt.Result is { } seeded)
                                        {
                                            return SuccessWithState(
                                                SuccessReceipt(
                                                    "seeded",
                                                    root,
                                                    buildDonor.Donor,
                                                    seeded.Method,
                                                    pins.Sha256,
                                                    missReason,
                                                    seeded.MathlibOleans,
                                                    stampMiss,
                                                    seeded.Clonefile),
                                                root,
                                                new OleanWarmthInspection(OleanWarmth.Warm, null),
                                                stateProbe,
                                                out cacheState, writerGuard, runner);
                                        }
                                    }
                                }
                            }
                        }
                        else
                        {
                            missReason = JoinReasons(missReason, contentRoot.Error);
                        }
                    }

                    // Main checkouts retain in-place reproduction for missing or corrupt stamps.
                    // Linked worktrees return above and provision only from their main checkout.
                    try
                    {
                        var reproduced = LeanCacheProvisioner.ReproduceExisting(
                            root,
                            pins,
                            lakeExecutable,
                            runner,
                            writerGuard);
                        return SuccessWithState(
                            SuccessReceipt(
                            "fetched",
                            root,
                            donor: null,
                            reproduced.Method,
                            pins.Sha256,
                            JoinReasons(missReason, reproduced.Warning),
                            reproduced.MathlibOleans,
                            stampMiss,
                            missingDonorClonefile),
                            root,
                            projectWarmth,
                            stateProbe,
                            out cacheState, writerGuard, runner);
                    }
                    catch (LeanCacheProvisionException exception)
                    {
                        if (IsSymlink(lake)) return RefusedSymlink(root, pins.Sha256);
                        if (continueOnCacheGetFailure
                            && exception.SafeToContinueToBuild
                            && !File.Exists(lake))
                        {
                            return SuccessWithState(
                                SuccessReceipt(
                                "degraded",
                                root,
                                donor: null,
                                method: "cache-get",
                                pins.Sha256,
                                JoinReasons(missReason, exception.Message),
                                LeanCacheProvisioner.InspectMathlibOleans(lake),
                                stampMiss,
                                missingDonorClonefile),
                                root,
                                projectWarmth,
                                stateProbe,
                                out cacheState, writerGuard, runner);
                        }
                        return FailureReceipt(
                            "failed",
                            root,
                            donor: null,
                            method: "cache-get",
                            pins.Sha256,
                            JoinReasons(missReason, exception.Message)
                                ?? "unknown in-place producer failure",
                            stampMiss: stampMiss,
                            clonefile: missingDonorClonefile);
                    }
                    catch (Exception exception)
                    {
                        if (IsSymlink(lake)) return RefusedSymlink(root, pins.Sha256);
                        return FailureReceipt(
                            "failed",
                            root,
                            donor: null,
                            method: "cache-get",
                            pins.Sha256,
                            JoinReasons(missReason, exception.Message)
                                ?? "unknown in-place producer failure",
                            stampMiss: stampMiss,
                            clonefile: missingDonorClonefile);
                    }
                }
            }
            else if (File.Exists(lake))
            {
                stampMiss = "corrupt";
                return FailureReceipt(
                    "failed",
                    root,
                    donor: null,
                    method: "none",
                    pins.Sha256,
                    ".lake exists but is not a directory",
                    stampMiss: stampMiss);
            }

            var worktreeLocation = GitWorktreeInventory.Locate(root, runner);
            if (worktreeLocation.IsLinked)
            {
                return ProvisionLinkedFromMain(
                    root,
                    pins,
                    runner,
                    cloner,
                    writerGuard,
                    removePartial,
                    stateProbe,
                    worktreeLocation,
                    replaceExisting: false,
                    stampMiss,
                    out cacheState);
            }

            using var selection = GitWorktreeInventory.SelectDonor(root, pins, runner, donorRepository);
            try
            {
                var provisioned = removePartial is null
                    ? LeanCacheProvisioner.Provision(
                        selection,
                        root,
                        pins,
                        lakeExecutable,
                        runner,
                        writerGuard,
                        cloner)
                    : LeanCacheProvisioner.Provision(
                        selection,
                        root,
                        pins,
                        lakeExecutable,
                        runner,
                        writerGuard,
                        cloner,
                        removePartial);
                var finalProjectWarmth = provisioned.Strategy == "cloned"
                    ? selection.ProjectWarmth ?? projectWarmth
                    : projectWarmth;

                // Main checkouts may use cache-get and the Release archive. Linked worktrees
                // return before this point and only clone a warm main-checkout cache.
                var warmthAfterProvision = provisioned.Strategy == "cloned"
                    ? stateProbe.ProbeOleans(ProjectOleanRoot(lake))
                    : finalProjectWarmth;
                if (warmthAfterProvision.State == OleanWarmth.Cold)
                {
                    archive = LeanArchiveFetch.Run(root, runner, ArchiveBudget, writerGuard);
                    if (archive.Outcome == LeanArchiveOutcome.Unpacked)
                    {
                        warmthAfterProvision = stateProbe.ProbeOleans(ProjectOleanRoot(lake));
                    }
                }
                else
                {
                    // ProbeFailed 不是 Cold。探不到就不取 —— 拿不准的时候不动别人的树。
                    archive = LeanArchiveAttempt.Skipped(
                        $"project olean state is {ReceiptWarmth(warmthAfterProvision.State)}");
                }

                finalProjectWarmth = warmthAfterProvision;
                return SuccessWithState(
                    SuccessReceipt(
                    provisioned.Strategy == "cloned" ? "seeded" : "fetched",
                    root,
                    selection.Donor,
                    provisioned.Method,
                    pins.Sha256,
                    JoinReasons(missReason, JoinReasons(selection.Notice, provisioned.Warning)),
                    provisioned.MathlibOleans,
                    stampMiss,
                    provisioned.Clonefile,
                    archive),
                    root,
                    finalProjectWarmth,
                    stateProbe,
                    out cacheState, writerGuard, runner);
            }
            catch (LeanCacheProvisionException exception)
            {
                if (IsSymlink(lake)) return RefusedSymlink(root, pins.Sha256);
                if (continueOnCacheGetFailure
                    && exception.SafeToContinueToBuild
                    && !File.Exists(lake))
                {
                    return SuccessWithState(
                        SuccessReceipt(
                        "degraded",
                        root,
                        selection.Donor,
                        method: "cache-get",
                        pins.Sha256,
                        JoinReasons(missReason, JoinReasons(selection.Notice, exception.Message)),
                        LeanCacheProvisioner.InspectMathlibOleans(lake),
                        stampMiss,
                        exception.Clonefile),
                        root,
                        projectWarmth,
                        stateProbe,
                        out cacheState, writerGuard, runner);
                }
                return FailureReceipt(
                    "failed",
                    root,
                    selection.Donor,
                    "none",
                    pins.Sha256,
                    JoinReasons(missReason, JoinReasons(selection.Notice, exception.Message))
                        ?? "unknown provisioning failure",
                    stampMiss: stampMiss,
                    clonefile: exception.Clonefile);
            }
            catch (Exception exception)
            {
                if (IsSymlink(lake)) return RefusedSymlink(root, pins.Sha256);
                return FailureReceipt(
                    "failed",
                    root,
                    selection.Donor,
                    "none",
                    pins.Sha256,
                    JoinReasons(missReason, JoinReasons(selection.Notice, exception.Message))
                        ?? "unknown provisioning failure",
                    stampMiss: stampMiss);
            }
        }
        catch (Exception exception)
        {
            return FailureReceipt(
                "failed",
                root,
                donor: null,
                method: "none",
                pins.Sha256,
                exception.Message,
                stampMiss: stampMiss,
                clonefile: exception is LeanCacheProvisionException provisionException
                    ? provisionException.Clonefile
                    : missingDonorClonefile);
        }
    }

    private static CommandResult ProvisionLinkedFromMain(
        string root,
        LeanPinSet pins,
        IWorktreeProcessRunner runner,
        IDirectoryCloner cloner,
        LeanCacheWriterGuard writerGuard,
        Action<string>? removePartial,
        ILeanCacheStateProbe stateProbe,
        LeanWorktreeLocation location,
        bool replaceExisting,
        string? stampMiss,
        out CacheState? cacheState)
    {
        cacheState = null;
        using var selection = GitWorktreeInventory.SelectMainDonor(
            location,
            pins,
            runner,
            stateProbe);
        if (selection.Donor is null)
            return LinkedFailure(root, pins, location, selection.Notice, stampMiss);

        var lake = Path.Combine(root, ".lake");
        try
        {
            if (replaceExisting) RemoveProjection(lake);
            var provisioned = LeanCacheProvisioner.ProvisionFromRequiredDonor(
                selection,
                root,
                pins,
                runner,
                writerGuard,
                cloner,
                removePartial ?? LeanCacheProvisioner.RemovePartial);
            var projectWarmth = stateProbe.ProbeOleans(ProjectOleanRoot(lake));
            return SuccessWithState(
                SuccessReceipt(
                    "seeded",
                    root,
                    location.MainCheckout,
                    provisioned.Method,
                    pins.Sha256,
                    provisioned.Warning,
                    provisioned.MathlibOleans,
                    stampMiss,
                    provisioned.Clonefile,
                    LeanArchiveAttempt.Skipped(LinkedArchiveDisabled)),
                root,
                projectWarmth,
                stateProbe,
                out cacheState,
                writerGuard,
                runner);
        }
        catch (Exception exception)
        {
            return LinkedFailure(
                root,
                pins,
                location,
                exception.Message,
                stampMiss,
                exception is LeanCacheProvisionException provisionException
                    ? provisionException.Clonefile
                    : null);
        }
    }

    private static CommandResult ProvisionLinkedBuildFromMain(
        string root,
        LeanPinSet pins,
        IWorktreeProcessRunner runner,
        IDirectoryCloner cloner,
        LeanCacheWriterGuard writerGuard,
        ILeanCacheStateProbe stateProbe,
        LeanWorktreeLocation location,
        string? stampMiss,
        out CacheState? cacheState)
    {
        cacheState = null;
        using var selection = GitWorktreeInventory.SelectMainDonor(
            location,
            pins,
            runner,
            stateProbe);
        if (selection.Donor is null)
            return LinkedFailure(root, pins, location, selection.Notice, stampMiss);

        try
        {
            var attempt = LeanMissingBuildProvisioner.TryProvision(
                selection,
                root,
                pins,
                runner,
                writerGuard,
                cloner,
                stateProbe);
            if (attempt.Result is null)
            {
                return LinkedLaneReseedFailure(
                    root,
                    pins,
                    location,
                    stampMiss,
                    attempt.Clonefile,
                    attempt.Warning ?? "main-checkout build overlay failed");
            }

            return SuccessWithState(
                SuccessReceipt(
                    "seeded",
                    root,
                    location.MainCheckout,
                    attempt.Result.Method,
                    pins.Sha256,
                    attempt.Warning,
                    attempt.Result.MathlibOleans,
                    stampMiss,
                    attempt.Clonefile,
                    LeanArchiveAttempt.Skipped(LinkedArchiveDisabled)),
                root,
                new OleanWarmthInspection(OleanWarmth.Warm, null),
                stateProbe,
                out cacheState,
                writerGuard,
                runner);
        }
        catch (Exception exception)
        {
            return LinkedLaneReseedFailure(
                root,
                pins,
                location,
                stampMiss,
                exception is LeanCacheProvisionException provisionException
                    ? provisionException.Clonefile
                    : null,
                exception.Message);
        }
    }

    private static CommandResult LinkedLaneReseedFailure(
        string root,
        LeanPinSet pins,
        LeanWorktreeLocation location,
        string? stampMiss,
        ClonefileReceipt? clonefile = null,
        string? reason = null)
    {
        var lake = ShellQuote(LeanCacheGuard.PhysicalPath(Path.Combine(root, ".lake")));
        var remediation = "the lane's content layer is cold while the main checkout is warm: "
            + $"remove {lake} and re-run so ensure seeds it from the main checkout";
        return FailureReceipt(
            "failed",
            root,
            location.MainCheckout,
            "none",
            pins.Sha256,
            JoinReasons(reason, remediation) ?? remediation,
            stampMiss,
            clonefile,
            LeanArchiveAttempt.Skipped(LinkedArchiveDisabled));
    }

    private static CommandResult LinkedFailure(
        string root,
        LeanPinSet pins,
        LeanWorktreeLocation location,
        string? reason,
        string? stampMiss,
        ClonefileReceipt? clonefile = null)
    {
        var remediation = "sync dev and warm the dev cache: "
            + $"make -C {ShellQuote(location.MainCheckout)} warm-donor";
        var completeReason = reason?.Contains(remediation, StringComparison.Ordinal) == true
            ? reason
            : JoinReasons(reason, remediation) ?? remediation;
        return FailureReceipt(
            "failed",
            root,
            location.MainCheckout,
            "none",
            pins.Sha256,
            completeReason,
            stampMiss,
            clonefile,
            LeanArchiveAttempt.Skipped(LinkedArchiveDisabled));
    }

    private static CommandResult SuccessWithState(
        CommandResult result,
        string root,
        OleanWarmthInspection projectWarmth,
        ILeanCacheStateProbe stateProbe,
        out CacheState? cacheState,
        LeanCacheWriterGuard writerGuard,
        IWorktreeProcessRunner runner)
    {
        // Every successful donor/provision path meets here while holding the
        // writer lock, including a warm donor that bypassed cold-cache fallback.
        const string prefix = "LEAN_CACHE ";
        var payload = JsonNode.Parse(result.Output[prefix.Length..])!.AsObject();
        var location = GitWorktreeInventory.Locate(root, runner);
        if (location.IsLinked)
        {
            payload["archive_status"] = "not_attempted";
            payload["archive_mode"] = null;
            payload["archive_skip_reason"] = LinkedArchiveDisabled;
            payload["archive_reason"] = null;
            payload["archive_producer_commit_sha"] = null;
            payload["archive_workflow_run_id"] = null;
            result = result with { Output = prefix + payload.ToJsonString() + "\n" };
        }
        else if (projectWarmth.IsWarm && payload["archive_status"]?.GetValue<string>() == "not_attempted")
        {
            try
            {
                if (LeanArchiveFetch.IsExpired(root, TimeProvider.System.GetUtcNow()))
                {
                    var refresh = LeanArchiveFetch.Run(root, runner, ArchiveBudget, writerGuard,
                        refreshStale: true);
                    payload["archive_status"] = ArchiveStatus(refresh);
                    payload["archive_mode"] = refresh.Mode;
                    payload["archive_skip_reason"] = refresh.SkipReason;
                    payload["archive_reason"] = refresh.Reason;
                    payload["archive_producer_commit_sha"] = refresh.ProducerCommitSha;
                    payload["archive_workflow_run_id"] = refresh.WorkflowRunId;
                    if (refresh.Outcome == LeanArchiveOutcome.Unpacked)
                        projectWarmth = stateProbe.ProbeOleans(ProjectOleanRoot(Path.Combine(root, ".lake")));
                }
            }
            catch (Exception error) when (error is IOException or UnauthorizedAccessException)
            {
                payload["archive_skip_reason"] = $"cache age unavailable: {error.Message}";
            }
            result = result with { Output = prefix + payload.ToJsonString() + "\n" };
        }
        if (RetireRootJudgeOutputs(root, writerGuard))
            projectWarmth = stateProbe.ProbeOleans(ProjectOleanRoot(Path.Combine(root, ".lake")));
        cacheState = new CacheState(
            stateProbe.ProbeOleans(MathlibOleanRoot(Path.Combine(root, ".lake"))),
            projectWarmth);
        return result with { Output = RecordCacheState(result.Output, cacheState) };
    }

    /// <summary>
    /// Bounds Release archive retrieval so the main-checkout producer retains time to finish.
    /// Linked-worktree ensure paths never consume this budget because archive retrieval is disabled.
    /// </summary>
    private static TimeSpan ArchiveBudget =>
        TimeSpan.FromMinutes(
            LeanCacheBudgetPolicy.LeanInspectJobBudgetMinutes
                - LeanCacheBudgetPolicy.PostArchiveReserveMinutes);

    private static string RecordColdBuildConsent(string receipt)
    {
        const string prefix = "LEAN_CACHE ";
        if (!receipt.StartsWith(prefix, StringComparison.Ordinal))
        {
            throw new InvalidOperationException("Lean cache receipt has an unexpected prefix");
        }
        var payload = JsonNode.Parse(receipt[prefix.Length..]) as JsonObject
            ?? throw new InvalidOperationException("Lean cache receipt is not a JSON object");
        payload["cold_build_consent"] = true;
        return prefix + payload.ToJsonString() + "\n";
    }

    private static string RecordCacheState(string receipt, CacheState cacheState)
    {
        const string prefix = "LEAN_CACHE ";
        if (!receipt.StartsWith(prefix, StringComparison.Ordinal))
        {
            throw new InvalidOperationException("Lean cache receipt has an unexpected prefix");
        }
        var payload = JsonNode.Parse(receipt[prefix.Length..]) as JsonObject
            ?? throw new InvalidOperationException("Lean cache receipt is not a JSON object");
        payload["mathlib_olean_state"] = ReceiptWarmth(cacheState.Mathlib.State);
        payload["mathlib_olean_probe_error"] = cacheState.Mathlib.Error;
        payload["project_olean_state"] = ReceiptWarmth(cacheState.Project.State);
        payload["project_olean_probe_error"] = cacheState.Project.Error;
        return prefix + payload.ToJsonString() + "\n";
    }

    private static string ReceiptWarmth(OleanWarmth warmth) => warmth switch
    {
        OleanWarmth.Cold => "cold",
        OleanWarmth.Warm => "warm",
        OleanWarmth.ProbeFailed => "probe_failed",
        _ => throw new ArgumentOutOfRangeException(nameof(warmth), warmth, null),
    };

    private static string ShellQuote(string value) => "'" + value.Replace("'", "'\"'\"'") + "'";

    private static string ProjectOleanRoot(string lake) =>
        Path.Combine(lake, "build", "lib", "lean");

    private static string MathlibOleanRoot(string lake) =>
        Path.Combine(lake, "packages", "mathlib", ".lake", "build", "lib", "lean");

    private static bool TryParseWriter(
        string repositoryRoot,
        IReadOnlyList<string> arguments,
        out string root,
        out string[] command,
        out string? donorRepository)
    {
        var index = 0;
        while (index < arguments.Count && arguments[index] != "--") index++;
        if (!TryParseWorktreeRoot(repositoryRoot, arguments.Take(index).ToArray(), out root, out donorRepository)
            || index + 1 >= arguments.Count)
        {
            command = [];
            return false;
        }
        command = arguments.Skip(index + 1).ToArray();
        return true;
    }

    private static string? JoinReasons(string? first, string? second)
    {
        if (string.IsNullOrWhiteSpace(first)) return second;
        if (string.IsNullOrWhiteSpace(second)) return first;
        return first + "; " + second;
    }

    private static string? ReceiptStampMiss(LeanCacheStampState state) => state switch
    {
        LeanCacheStampState.Missing => "missing",
        LeanCacheStampState.Corrupt => "corrupt",
        LeanCacheStampState.Mismatch => "mismatch",
        _ => null,
    };

    private static bool IsSymlink(string path) =>
        (Directory.Exists(path) || File.Exists(path))
        && File.GetAttributes(path).HasFlag(FileAttributes.ReparsePoint);

    private static void RemoveProjection(string lake) => Directory.Delete(lake, recursive: true);

}
