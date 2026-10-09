using StrataLint.Runtime;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed class WorktreeBranchTracking
{
    private sealed record Setting(string Key, string[] Before, string[] After, bool AllowsPartialWrite = false);

    private enum WriteStage { NotStarted, Applying, Applied }

    private readonly string? upstream;
    private readonly Setting[] settings;
    private readonly bool rebasing;
    private WriteStage stage;

    private WorktreeBranchTracking(string? upstream, Setting[] settings, bool rebasing)
    {
        this.upstream = upstream;
        this.settings = settings;
        this.rebasing = rebasing;
    }

    internal static WorktreeBranchTracking? Prepare(WorktreeOptions options, IWorktreeProcessRunner runner)
    {
        var mode = Read(options, runner, "branch.autoSetupMerge").LastOrDefault() ?? "true";
        if (mode is not ("always" or "simple" or "inherit"))
        {
            var boolean = Run(options, runner,
                ["config", "--type=bool", "--get", "branch.autoSetupMerge"], missing: 1);
            mode = boolean.ExitCode == 1 ? "true" : Encoding.UTF8.GetString(boolean.StandardOutput).Trim();
        }
        if (mode == "false") return null;

        var resolved = Run(options, runner,
            ["rev-parse", "--symbolic-full-name", "--verify", "--end-of-options", options.Base]);
        if (resolved.StandardError.Length != 0)
            throw new InvalidOperationException(Encoding.UTF8.GetString(resolved.StandardError).Trim());
        var reference = Encoding.UTF8.GetString(resolved.StandardOutput).TrimEnd('\r', '\n');
        if (reference.Length == 0) return null;

        string remote;
        string[] merges;
        bool remoteRebase;
        if (mode == "inherit")
        {
            if (!reference.StartsWith("refs/heads/", StringComparison.Ordinal)) return null;
            var parent = reference["refs/heads/".Length..];
            var inheritedRemote = Read(options, runner, $"branch.{parent}.remote").LastOrDefault();
            merges = Read(options, runner, $"branch.{parent}.merge");
            if (inheritedRemote is null || merges.Length == 0) return null;
            remote = inheritedRemote;
            // Git passes an origin even for inherited '.', unlike direct local tracking.
            remoteRebase = true;
        }
        else
        {
            var matches = FindRemotes(options, runner, reference);
            if (matches.Count > 1)
                throw new InvalidOperationException($"ambiguous tracking information for {reference}");
            if (matches.Count == 0)
            {
                if (mode != "always" || !reference.StartsWith("refs/heads/", StringComparison.Ordinal)) return null;
                remote = ".";
                merges = [reference];
                remoteRebase = false;
            }
            else
            {
                var match = matches.Single();
                if (mode == "simple" && match.Value != $"refs/heads/{options.Branch}") return null;
                remote = match.Key;
                merges = [match.Value];
                remoteRebase = true;
            }
        }

        var rebase = Read(options, runner, "branch.autoSetupRebase").LastOrDefault() ?? "never";
        var rebasing = rebase switch
        {
            "never" => false,
            "always" => true,
            "remote" => remoteRebase,
            "local" => !remoteRebase,
            _ => throw new InvalidOperationException($"invalid branch.autoSetupRebase: {rebase}"),
        };
        if (rebasing && merges.Length > 1)
            throw new InvalidOperationException("cannot inherit multiple upstream branches with rebase enabled");

        var prefix = $"branch.{options.Branch}.";
        var settings = new List<Setting>
        {
            new(prefix + "remote", Read(options, runner, prefix + "remote", local: true), [remote]),
            new(prefix + "merge", Read(options, runner, prefix + "merge", local: true), merges, AllowsPartialWrite: true),
        };
        if (rebasing)
            settings.Add(new(prefix + "rebase", Read(options, runner, prefix + "rebase", local: true), ["true"]));
        return new WorktreeBranchTracking(mode == "inherit" ? null : reference, settings.ToArray(), rebasing);
    }

    internal void Apply(WorktreeOptions options, IWorktreeProcessRunner runner)
    {
        stage = WriteStage.Applying;
        if (upstream is not null)
        {
            // Branch-creation hooks can change repository policy after Prepare.
            _ = Run(options, runner, ["-c", $"branch.autoSetupRebase={(rebasing ? "always" : "never")}",
                "branch", $"--set-upstream-to={upstream}", "--", options.Branch]);
        }
        else
        {
            // --set-upstream-to always means direct tracking, even with --track=inherit.
            foreach (var setting in settings) Write(options, runner, setting.Key, setting.After);
        }
        stage = WriteStage.Applied;
    }

    internal void Rollback(WorktreeOptions options, IWorktreeProcessRunner runner)
    {
        if (stage == WriteStage.NotStarted) return;
        var branch = Run(options, runner,
            ["show-ref", "--verify", "--quiet", $"refs/heads/{options.Branch}"], missing: 1);
        if (branch.ExitCode == 0) return;

        var current = settings.Select(setting => Read(options, runner, setting.Key, local: true)).ToArray();
        for (var index = 0; index < settings.Length; index++)
        {
            var setting = settings[index];
            var interruptedWrite = stage == WriteStage.Applying && setting.AllowsPartialWrite
                && current[index].Length < setting.After.Length
                && current[index].SequenceEqual(setting.After.Take(current[index].Length), StringComparer.Ordinal);
            if (!current[index].SequenceEqual(setting.Before, StringComparer.Ordinal)
                && !current[index].SequenceEqual(setting.After, StringComparer.Ordinal)
                && !interruptedWrite)
                throw new InvalidOperationException("initialization branch tracking changed; refusing configuration cleanup");
        }
        for (var index = 0; index < settings.Length; index++)
        {
            if (!current[index].SequenceEqual(settings[index].Before, StringComparer.Ordinal))
                Write(options, runner, settings[index].Key, settings[index].Before);
        }
    }

    private static Dictionary<string, string> FindRemotes(
        WorktreeOptions options, IWorktreeProcessRunner runner, string reference)
    {
        _ = Run(options, runner, ["remote"]);
        var fetched = Run(options, runner, ["config", "--null", "--get-regexp", @"^remote\..*\.fetch$"], missing: 1);
        var entries = Encoding.UTF8.GetString(fetched.StandardOutput)
            .Split('\0', StringSplitOptions.RemoveEmptyEntries)
            .Select(record => record.Split('\n', 2))
            .GroupBy(fields => fields[0]["remote.".Length..^".fetch".Length], StringComparer.Ordinal);
        var matches = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var entry in entries)
        {
            var specs = entry.Select(fields => fields[1]).ToArray();
            string? source = null;
            foreach (var spec in specs)
            {
                if (spec.StartsWith('^')) continue;
                var fields = spec.TrimStart('+').Split(':', 2);
                if (fields.Length != 2 || Match(fields[1], reference) is not { } capture) continue;
                source = fields[0].Replace("*", capture, StringComparison.Ordinal);
                break;
            }
            if (source is not null && !specs.Any(spec => spec.StartsWith('^') && Match(spec[1..], source) is not null))
                matches.Add(entry.Key, source);
        }
        return matches;
    }

    private static string? Match(string pattern, string reference)
    {
        var star = pattern.IndexOf('*');
        if (star < 0) return string.Equals(pattern, reference, StringComparison.Ordinal) ? string.Empty : null;
        var suffix = pattern[(star + 1)..];
        return reference.Length >= pattern.Length - 1
            && reference.StartsWith(pattern[..star], StringComparison.Ordinal)
            && reference.EndsWith(suffix, StringComparison.Ordinal)
                ? reference.Substring(star, reference.Length - star - suffix.Length) : null;
    }

    private static string[] Read(WorktreeOptions options, IWorktreeProcessRunner runner, string key, bool local = false)
    {
        var result = Run(options, runner, local
            ? ["config", "--local", "--null", "--get-all", key]
            : ["config", "--null", "--get-all", key], missing: 1);
        return result.ExitCode == 1 ? [] : Encoding.UTF8.GetString(result.StandardOutput).Split('\0')[..^1];
    }

    private static void Write(WorktreeOptions options, IWorktreeProcessRunner runner, string key, string[] values)
    {
        if (values.Length == 0)
        {
            _ = Run(options, runner, ["config", "--local", "--unset-all", key], missing: 5);
            return;
        }
        _ = Run(options, runner, ["config", "--local", "--replace-all", key, values[0]]);
        foreach (var value in values.Skip(1))
            _ = Run(options, runner, ["config", "--local", "--add", key, value]);
    }

    private static ProcessOutput Run(
        WorktreeOptions options, IWorktreeProcessRunner runner, IReadOnlyList<string> arguments, int missing = -1)
    {
        var result = runner.Run("git", arguments, options.Source, BoundedProcessRunner.HangDetectionBudget);
        if (result.ExitCode == 0 || result.ExitCode == missing) return result;
        var error = Encoding.UTF8.GetString(result.StandardError).Trim();
        throw new InvalidOperationException(error.Length == 0 ? "git branch tracking failed" : error);
    }
}
