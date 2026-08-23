using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;

namespace StrataLint.Cli;

internal static partial class LeanCacheEnsureCommand
{
    private const string ColdBuildConsentVariable = "STRATALINT_ACCEPT_COLD_BUILD";

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

    internal const string Usage = "USAGE: StrataLint worktree ensure-cache [--path DIR]";
    internal const string WriterUsage =
        "USAGE: StrataLint worktree with-cache-writer [--path DIR] -- COMMAND [ARG ...]";

    internal static CommandResult Run(
        string repositoryRoot,
        IReadOnlyList<string> arguments,
        IWorktreeProcessRunner runner,
        IDirectoryCloner cloner) =>
        Run(
            repositoryRoot,
            arguments,
            runner,
            cloner,
            removePartial: null);

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
        ILeanCacheStateProbe stateProbe)
    {
        ArgumentNullException.ThrowIfNull(arguments);
        ArgumentNullException.ThrowIfNull(runner);
        ArgumentNullException.ThrowIfNull(cloner);
        ArgumentNullException.ThrowIfNull(stateProbe);
        if (!TryParseWorktreeRoot(repositoryRoot, arguments, out var root))
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
            continueOnCacheGetFailure: false,
            stateProbe,
            out _);
    }

    internal static CommandResult RunWithWriter(
        string repositoryRoot,
        IReadOnlyList<string> arguments,
        IWorktreeProcessRunner runner,
        IDirectoryCloner cloner) =>
        RunWithWriter(
            repositoryRoot,
            arguments,
            runner,
            cloner,
            FileSystemLeanCacheStateProbe.Instance,
            Environment.GetEnvironmentVariable);

    internal static CommandResult RunWithWriter(
        string repositoryRoot,
        IReadOnlyList<string> arguments,
        IWorktreeProcessRunner runner,
        IDirectoryCloner cloner,
        ILeanCacheStateProbe stateProbe,
        Func<string, string?> readEnvironment)
    {
        ArgumentNullException.ThrowIfNull(cloner);
        ArgumentNullException.ThrowIfNull(stateProbe);
        ArgumentNullException.ThrowIfNull(readEnvironment);
        if (!TryParseWriter(repositoryRoot, arguments, out var root, out var command))
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
            out var cacheState);
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
            var invoked = runner.Run(
                command[0],
                command.Skip(1).ToArray(),
                root,
                LeanCacheProvisioner.CommandBudget);
            return new CommandResult(
                invoked.ExitCode == 0,
                receipt + Encoding.UTF8.GetString(invoked.StandardOutput),
                Encoding.UTF8.GetString(invoked.StandardError));
        }
        catch (Exception exception)
        {
            return new CommandResult(false, receipt, exception.Message + "\n");
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
        out CacheState? cacheState)
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
                    // stamp 只表示**依赖层**身份。它 Match 而内容层是冷的，正是 CI 上
                    // 「dependency cache 命中、project build cache 未命中」的形态：不在这里
                    // 取内容层，后面的 producer 就会从源码重编（#2814 记的那条缺口）。
                    //
                    // 归档只在**内容层确实为冷且 build 根未被占用**时尝试；本机 donor 命中
                    // 时根本走不到这里。取回失败一律降级为原样返回 present —— 慢，不是错。
                    if (projectWarmth.State == OleanWarmth.Cold)
                    {
                        var contentRoot = stateProbe.InspectContentRoot(
                            Path.Combine(lake, "build"));
                        archive = contentRoot.Clear
                            ? LeanArchiveFetch.Run(root, runner, ArchiveBudget)
                            : LeanArchiveAttempt.Skipped(
                                contentRoot.Error ?? "content root already exists");
                        if (archive.Outcome == LeanArchiveOutcome.Unpacked)
                        {
                            projectWarmth = stateProbe.ProbeOleans(ProjectOleanRoot(lake));
                        }
                    }
                    else
                    {
                        archive = LeanArchiveAttempt.Skipped("project olean state is not cold");
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
                        out cacheState);
                }

                if (stamp.State == LeanCacheStampState.Mismatch)
                {
                    RemoveProjection(lake);
                    projectWarmth = new OleanWarmthInspection(OleanWarmth.Cold, null);
                }
                else
                {
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
                                                out cacheState);
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

                    // Missing or corrupt pin identity does not prove staleness. Re-run the current-pin
                    // producer in place; Lake owns any missing dependency rebuilds.
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
                            out cacheState);
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
                                out cacheState);
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

            using var selection = GitWorktreeInventory.SelectDonor(root, pins, runner);
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

                // 入口一:没有本机 donor 时,上面那步只补了**依赖层**(`lake exe cache get`),
                // 内容层仍是空的 —— 新机器、第一棵树、CI 冷启动都落在这里。归档是内容层
                // 唯一的私有供给,故在此补它。
                //
                // 顺序不能反:`.lake` 此前整个不存在,归档只供内容层,得先有 `.lake` 才有
                // 地方展开。clone 成功那一路已经整树搬过来了,不在此列。
                if (provisioned.Strategy != "cloned"
                    && finalProjectWarmth.State == OleanWarmth.Cold)
                {
                    var contentRoot = stateProbe.InspectContentRoot(
                        Path.Combine(lake, "build"));
                    archive = contentRoot.Clear
                        ? LeanArchiveFetch.Run(root, runner, ArchiveBudget)
                        : LeanArchiveAttempt.Skipped(
                            contentRoot.Error ?? "content root already exists");
                    if (archive.Outcome == LeanArchiveOutcome.Unpacked)
                    {
                        finalProjectWarmth = stateProbe.ProbeOleans(ProjectOleanRoot(lake));
                    }
                }
                else
                {
                    archive = LeanArchiveAttempt.Skipped(
                        provisioned.Strategy == "cloned"
                            ? "a local donor supplied both layers"
                            : "project olean state is not cold");
                }
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
                    out cacheState);
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
                        out cacheState);
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

    private static CommandResult SuccessWithState(
        CommandResult result,
        string root,
        OleanWarmthInspection projectWarmth,
        ILeanCacheStateProbe stateProbe,
        out CacheState? cacheState)
    {
        cacheState = new CacheState(
            stateProbe.ProbeOleans(MathlibOleanRoot(Path.Combine(root, ".lake"))),
            projectWarmth);
        return result with { Output = RecordCacheState(result.Output, cacheState) };
    }

    /// <summary>
    /// 归档取回的预算。
    ///
    /// 【这里曾直接沿用 provision 预算（3600s），那是错的】评审席指出并经亲验：本路径在
    /// CI 上位于 `lean-inspect` job 内，而该 job 的 `timeout-minutes: 45`（2700s）。
    /// 一个 3600s 的预算**大于它所在的整个 job**，即归档一旦挂住就能吃光全部预算，
    /// 把「取不到就降级」变成「job 超时取消」。复用一个值不等于它在这个域里成立 ——
    /// 我按复用选值，没把**外层容量**放进推导（「量腹而食」）。
    ///
    /// 现按 `C_i = min_j U_{i,j} - R_i` 取：唯一适用上限是 job 预算，具名保留是
    /// 归档之后仍必须跑完的产出工作（Lean 报告生产），故
    ///   archive ≤ job_budget − post_archive_reserve。
    /// 两项都取自本仓既有真源，不新立裸数；比值向下取整到分钟。
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
        out string[] command)
    {
        var index = 0;
        root = Path.GetFullPath(repositoryRoot);
        if (arguments.Count >= 2 && arguments[0] == "--path")
        {
            root = Path.GetFullPath(arguments[1]);
            index = 2;
        }
        if (index >= arguments.Count || arguments[index] != "--" || index + 1 >= arguments.Count)
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
