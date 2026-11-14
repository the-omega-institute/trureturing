using StrataLint.Engine;
using System.Text;
using System.Text.Json;
using Tomlyn;
using Tomlyn.Model;

namespace StrataLint.EngineeringScope;

internal static partial class LeanCacheEnsureCommand
{
    private const string ScopedCacheScopeVariable = "STRATALINT_LEAN_CACHE_SCOPE";
    private const string LakeArtifactCacheVariable = "LAKE_ARTIFACT_CACHE";
    private const string LakeRestoreArtifactsVariable = "LAKE_RESTORE_ARTIFACTS";
    private const string LakeNoCacheVariable = "LAKE_NO_CACHE";
    private const string MathlibNoCacheOnUpdateVariable = "MATHLIB_NO_CACHE_ON_UPDATE";

    private sealed record LocalHeatInspection(bool Usable, string? Failure);

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

        var lake = Path.Combine(root, ".lake");
        if (IsSymlink(lake))
            return RefusedSymlink(root, pins.Sha256);
        if (File.Exists(lake))
            return FailureReceipt("failed", root, donor: null, method: "none", pins.Sha256,
                ".lake exists but is not a directory", stampMiss: "corrupt");

        var location = GitWorktreeInventory.Locate(root, runner);
        var routedRunner = RouteArtifactCache(runner, location.IsLinked, coldSelected: false);
        if (IsScopedCacheRequest(command, readEnvironment))
        {
            var heat = InspectUsableLocalHeat(root, pins, runner, stateProbe, donorRepository);
            if (heat.Failure is not null)
                return FailureReceipt("failed", root, donor: null, method: "none", pins.Sha256,
                    "cache warmth inspection failed: " + heat.Failure);
            if (!heat.Usable)
            {
                // A dependency-only identity receipt must not turn the partial
                // project outputs produced below into preparation evidence.
                // Full ensure can re-establish this existing identity later.
                if (LeanCacheStamp.Inspect(lake, pins).State == LeanCacheStampState.Match)
                    File.Delete(LeanCacheStamp.PathFor(lake));
                return RunScopedCommand(
                    root,
                    command,
                    RouteArtifactCache(runner, location.IsLinked, coldSelected: true),
                    guard,
                    location.IsLinked,
                    standardOutput,
                    standardError);
            }
        }

        var ensured = EnsureLocked(
            root,
            pins,
            command[0],
            routedRunner,
            cloner,
            guard,
            removePartial: null,
            continueOnCacheGetFailure: true,
            stateProbe,
            out var cacheState, donorRepository, refreshWarmArchive: false);
        if (!ensured.Success) return ensured;

        var receipt = ensured.Output;
        if (cacheState is null)
        {
            return new CommandResult(
                false,
                receipt,
                "cold-build guard did not receive a cache state from ensure\n");
        }
        try
        {
            // Standalone additive recovery preserves outputs. Native writer admission
            // must retire former owners before deciding whether the project is warm.
            if (RetireRootJudgeOutputs(root, guard))
            {
                cacheState = cacheState with
                {
                    Project = stateProbe.ProbeOleans(ProjectOleanRoot(Path.Combine(root, ".lake"))),
                };
                receipt = RecordCacheState(receipt, cacheState);
            }
        }
        catch (OperationCanceledException) { throw; }
        catch (Exception exception)
        {
            return new CommandResult(false, receipt, exception.Message + "\n");
        }
        if (cacheState.HasProbeFailure)
        {
            return new CommandResult(
                false,
                receipt,
                "COLD_BUILD_REFUSED cache warmth probe failed (fail-closed): "
                + cacheState.ProbeFailureDescription + "\n"
                + $"Fetch caches with: make -C {ShellQuote(root)} lean-cache-ensure\n");
        }
        if (cacheState.Project.State == OleanWarmth.Cold)
        {
            var consent = string.Equals(
                readEnvironment(ColdBuildConsentVariable),
                "1",
                StringComparison.Ordinal);
            if (!consent)
            {
                var target = ShellQuote(root);
                return new CommandResult(
                    false,
                    receipt,
                    "COLD_BUILD_REFUSED project olean cache is cold.\n"
                    + $"Fetch caches with: make -C {target} lean-cache-ensure\n"
                    + "To accept this cold build once, run: "
                    + $"{ColdBuildConsentVariable}=1 make -C {target} lean\n");
            }
            receipt = RecordColdBuildConsent(receipt);
        }

        return InvokeNative(root, command, routedRunner, receipt, standardOutput, standardError);
    }

    internal static bool IsScopedCacheRequest(
        IReadOnlyList<string> command, Func<string, string?> readEnvironment)
    {
        var scope = readEnvironment(ScopedCacheScopeVariable);
        if (scope is not ("targeted" or "scoped")) return false;
        // These are the canonical whole-operation demands, not a Lake argv
        // parser. An inherited scope hint cannot narrow their preparation.
        if (command.Any(static argument => argument is "update" or "clean"
                or "cache" or "warm-donor" or "lean-cache-ensure")) return false;
        var build = command.ToList().IndexOf("build");
        if (build < 0) return true; // selected compiled readout / scope discovery
        var targets = command.Skip(build + 1).Where(static value => !value.StartsWith('-')).ToArray();
        return targets.Length > 0 && !targets.Any(static target =>
            target.StartsWith(':') || target.EndsWith(":report", StringComparison.Ordinal)
            || target is "all" or "default" or "aggregate" or "report"
            || target is "trureturing" or "Reg" or "LeanInformationAudit"
                or "LeanInformationAuditAnalysis" or "LeanInformationAuditReg"
                or "LeanInformationAuditRegAnalysis" or "LeanInformationAuditRegTests"
                or "LeanInformationAuditFibTests"
            || target.StartsWith('@'));
    }

    private static LocalHeatInspection InspectUsableLocalHeat(
        string root,
        LeanPinSet pins,
        IWorktreeProcessRunner runner,
        ILeanCacheStateProbe stateProbe,
        string? donorRepository)
    {
        var lake = Path.Combine(root, ".lake");
        if (Directory.Exists(lake))
        {
            var stamp = LeanCacheStamp.Inspect(lake, pins);
            {
                var project = stateProbe.ProbeOleans(ProjectOleanRoot(lake));
                var mathlib = stateProbe.ProbeOleans(MathlibOleanRoot(lake));
                var failure = ProbeFailure("current project", project)
                    ?? ProbeFailure("current mathlib", mathlib);
                if (failure is not null) return new(false, failure);
                if (stamp.State == LeanCacheStampState.Match && project.IsWarm && mathlib.IsWarm)
                    return new(true, null);
            }
        }

        LeanCacheDonorSelection selection;
        try
        {
            selection = GitWorktreeInventory.SelectDonor(
                root,
                pins,
                runner,
                stateProbe,
                requireProjectWarm: true,
                donorRepository: donorRepository, requireMathlibWarm: true);
        }
        catch (Exception exception)
        {
            return new(false, exception.Message);
        }

        using (selection)
        {
            if (selection.ProbeFailed)
                return new(false, selection.Notice ?? "local donor project warmth probe failed");
            if (selection.Donor is null) return new(false, null);

            return new(true, null);
        }
    }

    private static string? ProbeFailure(string layer, OleanWarmthInspection inspection) =>
        inspection.State == OleanWarmth.ProbeFailed
            ? $"{layer}: {inspection.Error ?? "enumeration failed"}"
            : null;

    private static IWorktreeProcessRunner RouteArtifactCache(
        IWorktreeProcessRunner runner, bool linked, bool coldSelected)
    {
        if (runner is not ProductionWorktreeProcessRunner production)
            return runner;

        // An empty value is intentional: Lake treats it as an unset boolean,
        // retaining its package default (readable, non-writable).  `false`
        // would disable artifact reads as well.
        var variables = new Dictionary<string, string>
        {
            [LakeArtifactCacheVariable] = linked ? string.Empty : "1",
            // Keep module outputs in the private build tree for consumers such
            // as judgeInputs/mod.oleanFile while still sharing the cache bytes.
            [LakeRestoreArtifactsVariable] = "1",
        };
        if (coldSelected)
        {
            // A cold selected delivery may fetch pinned source/configuration and
            // build native misses, but it must not restore bulk package archives
            // or trigger Mathlib's full post-update cache population.
            variables[LakeNoCacheVariable] = "1";
            variables[MathlibNoCacheOnUpdateVariable] = "1";
        }
        return production.WithEnvironment(variables);
    }

    private static CommandResult RunScopedCommand(
        string root,
        IReadOnlyList<string> command,
        IWorktreeProcessRunner runner,
        LeanCacheWriterGuard guard,
        bool linked,
        Stream? standardOutput,
        Stream? standardError)
    {
        if (RetireRootJudgeOutputs(root, guard))
        {
            // Retiring obsolete root owners is part of the existing writer
            // admission contract and remains safe when `.lake` is initially
            // absent.  Lake itself will create only the requested closure.
        }

        var receipt = "LEAN_CACHE " + JsonSerializer.Serialize(new
        {
            status = "scoped",
            worktree = root,
            donor = (string?)null,
            method = "lake-artifact-cache",
            reason = linked
                ? "linked worktree: target closure only; artifact cache reads enabled and writes disabled"
                : "main checkout: target closure only; official artifact cache reads and writes enabled",
            scope = "targeted",
            archive_status = "not_attempted",
        }) + "\n";
        return InvokeNative(root, command, runner, receipt, standardOutput, standardError);
    }

    private static CommandResult InvokeNative(
        string root, IReadOnlyList<string> command, IWorktreeProcessRunner runner,
        string receipt, Stream? standardOutput, Stream? standardError)
    {
        try
        {
            if (standardOutput is not null)
            {
                standardOutput.Write(Encoding.UTF8.GetBytes(receipt));
                standardOutput.Flush();
            }
            IReadOnlyList<string> invocation = command;
            if (!string.IsNullOrEmpty(Environment.GetEnvironmentVariable("STRATALINT_CI_COMPUTE_BUDGET"))
                && Environment.GetEnvironmentVariable("STRATALINT_CI_COMPUTE_ACTIVE") != "1")
                invocation = ["python3", Path.Combine(root, "tools/scripts/workflow/ci_compute.py"),
                    "run", "--", .. command];
            var invoked = runner.Run(
                invocation[0], invocation.Skip(1).ToArray(), root,
                LeanCacheProvisioner.LeanCommandBudget, standardOutput, standardError);
            return new CommandResult(
                invoked.ExitCode == 0,
                standardOutput is null ? receipt + Encoding.UTF8.GetString(invoked.StandardOutput) : string.Empty,
                standardError is null ? Encoding.UTF8.GetString(invoked.StandardError) : string.Empty,
                invoked.ExitCode);
        }
        catch (OperationCanceledException) { throw; }
        catch (Exception exception)
        {
            return new CommandResult(false, standardOutput is null ? receipt : string.Empty,
                exception.Message + "\n");
        }
    }

    // These two libraries moved from trureturing to leanInspector. Their former
    // namespace directories are producer-owned outputs, not dependency staleness.
    // In particular, a matching Mathlib stamp does not make them current owners.
    internal static bool RetireRootJudgeOutputs(
        string root, LeanCacheWriterGuard writerGuard, Action<string>? remove = null)
    {
        var lake = Path.Combine(root, ".lake");
        writerGuard.RequireOwnershipOf(lake);
        var config = Path.Combine(root, "lakefile.toml");
        if (!File.Exists(config)) return false;
        var package = TomlSerializer.Deserialize<TomlTable>(File.ReadAllText(config))
            ?? throw new InvalidOperationException("missing root Lake package");
        if (!package.TryGetValue("name", out var name) || !Equals(name, "trureturing")) return false;

        // Preserve a workspace that still declares the former root libraries.
        // Native adapter fixtures also retain their own root-owned driver.
        var libraries = package.TryGetValue("lean_lib", out var value)
            ? FileMapTomlTables.Parse(value, config, allowEmpty: true) : [];
        var obsolete = new List<string>();
        foreach (var library in new[] { "LeanInformationAudit", "LeanInformationAuditAnalysis" })
        {
            if (libraries.Any(table => table.TryGetValue("name", out var owner) && Equals(owner, library)))
                continue;
            foreach (var facet in new[] { "lib/lean", "ir" })
            {
                var path = Path.Combine(lake, "build", facet, library);
                if (PrivateOutputDirectory(lake, path)) obsolete.Add(path);
            }
        }
        if (obsolete.Count == 0) return false;

        // Reg may have persisted evidence while findOLean still selected the
        // former root owner. Retire its build products first, before removing
        // ANY old owner. If interrupted, an old directory remains to trigger
        // retry; after they are all gone, every Reg product has been removed.
        // No marker, report invalidation or dependency-stamp change is needed.
        var reg = Path.Combine(lake, "build", "reg");
        var hasReg = PrivateOutputDirectory(lake, reg);
        foreach (var path in obsolete) ValidateOutputTree(path);
        if (hasReg) ValidateOutputTree(reg);
        remove ??= static path => Directory.Delete(path, recursive: true);
        if (hasReg) remove(reg);
        foreach (var path in obsolete) remove(path);
        return true;
    }

    private static bool PrivateOutputDirectory(string lake, string path)
    {
        var relative = Path.GetRelativePath(lake, path);
        if (Path.IsPathRooted(relative) || relative == ".."
            || relative.StartsWith(".." + Path.DirectorySeparatorChar, StringComparison.Ordinal))
            throw new InvalidOperationException("cache output is outside the owned .lake directory");
        var current = lake;
        foreach (var component in new[] { string.Empty }.Concat(relative.Split(Path.DirectorySeparatorChar)))
        {
            if (component.Length != 0) current = Path.Combine(current, component);
            var attributes = OutputAttributes(current);
            if (attributes is null) return false;
            if (attributes.Value.HasFlag(FileAttributes.ReparsePoint)
                || !attributes.Value.HasFlag(FileAttributes.Directory))
                throw new InvalidOperationException($"cache output is not a private directory: {current}");
        }
        return true;
    }

    private static void ValidateOutputTree(string path)
    {
        foreach (var entry in Directory.EnumerateFileSystemEntries(path))
        {
            var attributes = File.GetAttributes(entry);
            if (attributes.HasFlag(FileAttributes.ReparsePoint))
                throw new InvalidOperationException($"cache output contains a forbidden symlink: {entry}");
            if (attributes.HasFlag(FileAttributes.Directory)) ValidateOutputTree(entry);
        }
    }

    private static FileAttributes? OutputAttributes(string path)
    {
        try { return File.GetAttributes(path); }
        catch (Exception error) when (error is FileNotFoundException or DirectoryNotFoundException)
        { return null; }
    }
}
