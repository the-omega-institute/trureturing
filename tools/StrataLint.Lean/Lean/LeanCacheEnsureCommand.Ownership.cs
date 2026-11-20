using StrataLint.Engine;
using System.Text;
using System.Text.Json;
using Tomlyn;
using Tomlyn.Model;

namespace StrataLint.EngineeringScope;

internal static partial class LeanCacheEnsureCommand
{
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
        var prebuilt = arguments.FirstOrDefault() == "--prebuilt";
        if (prebuilt) arguments = arguments.Skip(1).ToArray();
        if (!TryParseWriter(repositoryRoot, arguments, out var root, out var command, out var donorRepository))
        {
            return new CommandResult(false, string.Empty, WriterUsage + "\n");
        }

        var fullBuild = FullBuild;
        if (!fullBuild && RequestsDefaultLakeBuild(command))
            return new CommandResult(false, string.Empty,
                "full build requires explicit FULL_BUILD=1; pass nonempty module targets for a scoped build\n", 2);

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

        if (prebuilt)
        {
            var lake = Path.Combine(root, ".lake");
            if (IsSymlink(lake)) return RefusedSymlink(root, pins.Sha256);
            var stamp = LeanCacheStamp.Inspect(lake, pins);
            if (stamp.State is LeanCacheStampState.Mismatch or LeanCacheStampState.Corrupt)
                return new CommandResult(false, string.Empty, $"Incompatible prebuilt Lake artifacts: {stamp.Reason}\n");
            var packageError = CheckPrebuiltPackages(lake, pins, runner);
            if (packageError is not null)
                return new CommandResult(false, string.Empty,
                    $"{packageError}. Run make lean-report-prepare for the selected scope.\n");
            return RunGuardedCommand(root, command, runner, localArtifacts: true, string.Empty, standardOutput, standardError);
        }

        CacheState? cacheState;
        var ensured = fullBuild
            ? EnsureLocked(root, pins, command[0], runner, cloner, guard, removePartial: null,
                continueOnCacheGetFailure: true, stateProbe, out cacheState, donorRepository, refreshWarmArchive: false)
            : InspectScopedCache(root, pins, stateProbe, out cacheState);
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
                + $"Fetch caches with: make -C {ShellQuote(root)} lean-cache-ensure FULL_BUILD=1\n");
        }
        if (fullBuild && cacheState.Project.State == OleanWarmth.Cold)
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
                    + $"Fetch caches with: make -C {target} lean-cache-ensure FULL_BUILD=1\n"
                    + ScopedColdBuildRemediation(root) + "\n");
            }
            receipt = RecordColdBuildConsent(receipt);
        }

        return RunGuardedCommand(root, command, runner, localArtifacts: !fullBuild, receipt, standardOutput, standardError);
    }

    private static string? CheckPrebuiltPackages(string lake, LeanPinSet pins, IWorktreeProcessRunner runner)
    {
        // The Reg and report host manifests already agree with these root Git pins.
        // Lake restores compiler artifacts from its store, but loading a workspace
        // would materialize a missing checkout or switch it to the requested commit.
        using var manifest = JsonDocument.Parse(pins.LakeManifest);
        foreach (var package in manifest.RootElement.GetProperty("packages").EnumerateArray())
        {
            if (package.GetProperty("type").GetString() != "git") continue;
            var name = package.GetProperty("name").GetString();
            var revision = package.GetProperty("rev").GetString();
            if (string.IsNullOrWhiteSpace(name) || name is "." or ".." || name.IndexOfAny(['/', '\\']) >= 0
                || !LeanPinSet.ValidRevision(revision))
                return "Invalid pinned Git package in lake-manifest.json";
            var directory = Path.Combine(lake, "packages", name);
            if (!Path.Exists(Path.Combine(directory, ".git")))
                return $"Missing prebuilt Git dependency {name} at {revision}";
            var head = runner.Run("git", ["rev-parse", "--verify", "HEAD"], directory,
                LeanCacheProvisioner.LeanCommandBudget);
            if (head.ExitCode != 0 || Encoding.UTF8.GetString(head.StandardOutput).Trim() != revision)
                return $"Prebuilt Git dependency {name} is not checked out at {revision}";
        }
        return null;
    }

    private static CommandResult RunGuardedCommand(string root, string[] command,
        IWorktreeProcessRunner runner, bool localArtifacts, string receipt, Stream? standardOutput, Stream? standardError)
    {
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
            if (localArtifacts && runner is ProductionWorktreeProcessRunner production)
                runner = production.ForLocalArtifactReader();
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

    private static bool RequestsDefaultLakeBuild(string[] command)
    {
        if (Path.GetFileNameWithoutExtension(command[0]) != "lake") return false;
        // Lake options may occur on either side of the verb. Ignore their values
        // when deciding whether an actual positional build target was supplied.
        var build = false;
        for (var index = 1; index < command.Length; index++)
        {
            var argument = command[index];
            if (argument is "-d" or "--dir" or "-f" or "--file" or "-K" or "--packages"
                or "--log-level" or "--fail-level") { index++; continue; }
            if (argument.StartsWith('-') || string.IsNullOrWhiteSpace(argument)) continue;
            if (build || argument != "build") return false;
            build = true;
        }
        return build;
    }

    // Lake validates each target's native trace. Scoped work may start with an empty
    // build directory and never provisions a donor, downloads an archive or writes a donor stamp.
    private static CommandResult InspectScopedCache(
        string root, LeanPinSet pins, ILeanCacheStateProbe stateProbe, out CacheState? cacheState)
    {
        cacheState = null;
        var lake = Path.Combine(root, ".lake");
        if (IsSymlink(lake)) return RefusedSymlink(root, pins.Sha256);
        var observed = new CacheState(stateProbe.ProbeOleans(MathlibOleanRoot(lake)),
            stateProbe.ProbeOleans(ProjectOleanRoot(lake)));
        return SuccessWithState(SuccessReceipt("ready", root, null, "lake-local", pins.Sha256,
            null, MathlibOleanInventory.Unknown, archive: LeanArchiveAttempt.Skipped("scoped build")),
            observed, out cacheState);
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
