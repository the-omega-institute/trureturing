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

        // Explicit target builds and scoped reports use Lake's content-addressed
        // artifact cache directly.  They still validate pins, acquire the local
        // writer reservation, and run the requested command under the canonical
        // process runner, but must not promote a target miss into whole-cache
        // ensure/donor/archive preparation.
        var location = GitWorktreeInventory.Locate(root, runner);
        var routedRunner = RouteArtifactCache(runner, location.IsLinked);
        if (IsScopedCacheRequest())
            return RunScopedCommand(root, command, routedRunner, guard, location.IsLinked,
                standardOutput, standardError);

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

        try
        {
            if (standardOutput is not null)
            {
                standardOutput.Write(Encoding.UTF8.GetBytes(receipt));
                standardOutput.Flush();
            }
            // Provisioning above is outside ordinary CI's cumulative compute
            // allowance. The actual native command retains the writer guard.
            IReadOnlyList<string> invocation = command;
            if (!string.IsNullOrEmpty(Environment.GetEnvironmentVariable("STRATALINT_CI_COMPUTE_BUDGET"))
                && Environment.GetEnvironmentVariable("STRATALINT_CI_COMPUTE_ACTIVE") != "1")
                invocation = ["python3", Path.Combine(root, "tools/scripts/workflow/ci_compute.py"),
                    "run", "--", .. command];
            var invoked = runner.Run(
                invocation[0],
                invocation.Skip(1).ToArray(),
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

    private static bool IsScopedCacheRequest() =>
        string.Equals(Environment.GetEnvironmentVariable(ScopedCacheScopeVariable), "targeted", StringComparison.Ordinal)
        || string.Equals(Environment.GetEnvironmentVariable(ScopedCacheScopeVariable), "scoped", StringComparison.Ordinal);

    private static IWorktreeProcessRunner RouteArtifactCache(
        IWorktreeProcessRunner runner, bool linked)
    {
        if (runner is not ProductionWorktreeProcessRunner production)
            return runner;

        // An empty value is intentional: Lake treats it as an unset boolean,
        // retaining its package default (readable, non-writable).  `false`
        // would disable artifact reads as well.
        return production.WithEnvironment(new Dictionary<string, string>
        {
            [LakeArtifactCacheVariable] = linked ? string.Empty : "1",
            // Keep module outputs in the private build tree for consumers such
            // as judgeInputs/mod.oleanFile while still sharing the cache bytes.
            [LakeRestoreArtifactsVariable] = "1",
        });
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
        try
        {
            if (standardOutput is not null)
            {
                standardOutput.Write(Encoding.UTF8.GetBytes(receipt));
                standardOutput.Flush();
            }
            var invoked = runner.Run(
                command[0], command.Skip(1).ToArray(), root,
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
