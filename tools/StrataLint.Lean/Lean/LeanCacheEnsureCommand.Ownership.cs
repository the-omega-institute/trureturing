using StrataLint.Engine;
using System.Text;
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
