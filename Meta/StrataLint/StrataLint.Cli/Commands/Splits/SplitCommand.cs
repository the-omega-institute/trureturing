using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record SplitDerivationResult(
    bool Success,
    ImmutableArray<string> Commands,
    string Error);

internal interface ISplitDerivationRunner
{
    SplitDerivationResult Run(string repositoryRoot, string baseRevision);
}

internal sealed class ProductionSplitDerivationRunner : ISplitDerivationRunner
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    public SplitDerivationResult Run(string repositoryRoot, string baseRevision)
    {
        var commands = ImmutableArray.Create(
            new DerivationCommand("make lean-report", ["lean-report"], TimeSpan.FromMinutes(30)),
            new DerivationCommand("make emit", ["emit"], TimeSpan.FromMinutes(10)),
            new DerivationCommand(
                $"make ingest BASE={baseRevision}",
                ["ingest", $"BASE={baseRevision}"],
                TimeSpan.FromMinutes(30)),
            new DerivationCommand("make emit", ["emit"], TimeSpan.FromMinutes(10)));
        var completed = ImmutableArray.CreateBuilder<string>();
        foreach (var command in commands)
        {
            var result = BoundedProcessRunner.Run(
                "make",
                command.Arguments,
                repositoryRoot,
                command.Timeout,
                16 * 1024 * 1024);
            if (result.ExitCode != 0)
            {
                var error = StrictUtf8.GetString(result.StandardError).Trim();
                if (error.Length == 0)
                {
                    error = StrictUtf8.GetString(result.StandardOutput).Trim();
                }

                return new SplitDerivationResult(
                    false,
                    completed.ToImmutable(),
                    $"{command.Display} exited {result.ExitCode}: {error}");
            }

            completed.Add(command.Display);
        }

        return new SplitDerivationResult(true, completed.ToImmutable(), string.Empty);
    }

    private sealed record DerivationCommand(
        string Display,
        ImmutableArray<string> Arguments,
        TimeSpan Timeout);
}

internal static class SplitCommand
{
    private const string Usage =
        "USAGE: StrataLint split DIRECTORY --domain DOMAIN --date YYYY-MM-DD [--base REV] [--apply]\n";

    internal static CommandResult Run(
        string repositoryRoot,
        IRepositoryGateway repository,
        ISplitDerivationRunner derivationRunner,
        IReadOnlyList<string> arguments)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(repository);
        ArgumentNullException.ThrowIfNull(derivationRunner);
        ArgumentNullException.ThrowIfNull(arguments);
        RawRepositorySnapshot? initial = null;
        try
        {
            var options = Parse(arguments);
            var prepared = repository.Prepare(options.BaseRevision);
            initial = repository.ReadCurrent();
            var current = Decode(initial);
            var baseline = Decode(repository.ReadRevision(prepared.Revision));
            var policy = LoadPolicy(current);
            var plan = SplitPlanner.Plan(
                current,
                baseline,
                policy,
                new SplitRequest(
                    options.SourceDirectory,
                    options.DestinationDomain,
                    options.Date,
                    prepared.Revision));
            if (!options.Apply || plan.Status is SplitPlanStatus.AlreadyApplied)
            {
                return new CommandResult(true, SplitReceiptWriter.Write(plan), string.Empty);
            }

            Apply(repositoryRoot, plan);
            var derivation = derivationRunner.Run(repositoryRoot, prepared.Revision);
            if (!derivation.Success)
            {
                Restore(repositoryRoot, initial);
                return new CommandResult(
                    false,
                    string.Empty,
                    $"SPLIT_FAILED {derivation.Error}; worktree rolled back\n");
            }

            VerifyApplied(repositoryRoot, plan);
            return new CommandResult(
                true,
                SplitReceiptWriter.Write(plan with
                {
                    Status = SplitPlanStatus.Applied,
                    Derivations = derivation.Commands,
                }),
                string.Empty);
        }
        catch (SplitUsageException exception)
        {
            return new CommandResult(false, string.Empty, $"{exception.Message}\n{Usage}");
        }
        catch (Exception exception)
        {
            if (initial is null)
            {
                return new CommandResult(false, string.Empty, $"SPLIT_FAILED {exception.Message}\n");
            }

            try
            {
                Restore(repositoryRoot, initial);
                return new CommandResult(
                    false,
                    string.Empty,
                    $"SPLIT_FAILED {exception.Message}; worktree rolled back\n");
            }
            catch (Exception rollback)
            {
                return new CommandResult(
                    false,
                    string.Empty,
                    $"SPLIT_FAILED {exception.Message}; rollback failed: {rollback.Message}\n");
            }
        }
    }

    private static void Apply(string repositoryRoot, SplitPlan plan)
    {
        foreach (var write in plan.Writes)
        {
            var target = FullPath(repositoryRoot, write.Path);
            Directory.CreateDirectory(Path.GetDirectoryName(target)!);
            var temporary = target + ".stratalint-split-" + Guid.NewGuid().ToString("N");
            try
            {
                File.WriteAllText(temporary, write.Text, new UTF8Encoding(false, true));
                File.Move(temporary, target, overwrite: true);
            }
            finally
            {
                if (File.Exists(temporary)) File.Delete(temporary);
            }
        }

        foreach (var move in plan.Moves)
        {
            var source = FullPath(repositoryRoot, move.Source);
            if (File.Exists(source)) File.Delete(source);
        }
    }

    private static void VerifyApplied(string repositoryRoot, SplitPlan plan)
    {
        var current = Decode(GitRepositorySnapshotReader.ReadCurrent(repositoryRoot));
        foreach (var move in plan.Moves)
        {
            if (current.TryGetFile(move.Source, out _) || !current.TryGetFile(move.Target, out _))
            {
                throw new InvalidOperationException(
                    $"applied split does not realize move {move.Source} -> {move.Target}");
            }
        }

        foreach (var path in plan.PreservedBaseMappings)
        {
            if (!current.TryGetFile(path, out _))
            {
                throw new InvalidOperationException($"applied split moved pre-existing path {path}");
            }
        }
    }

    private static void Restore(string repositoryRoot, RawRepositorySnapshot initial)
    {
        var original = initial.Entries.ToDictionary(static entry => entry.Path, StringComparer.Ordinal);
        var current = GitRepositorySnapshotReader.ReadCurrent(repositoryRoot);
        foreach (var entry in current.Entries)
        {
            if (!original.ContainsKey(entry.Path))
            {
                File.Delete(FullPath(repositoryRoot, entry.Path));
            }
        }

        foreach (var entry in initial.Entries)
        {
            var path = FullPath(repositoryRoot, entry.Path);
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllBytes(path, entry.Bytes.AsSpan().ToArray());
        }
    }

    private static ValidatedPolicy LoadPolicy(RepositorySnapshot snapshot)
    {
        if (!snapshot.TryGetFile("Meta/registry.yaml", out var registry)
            || !snapshot.TryGetFile("Meta/domains.yaml", out var domains))
        {
            throw new SplitPlanException("split requires Meta/registry.yaml and Meta/domains.yaml");
        }

        return RegistryLoader.Load(registry.RawBytes.AsSpan(), domains.RawBytes.AsSpan()) switch
        {
            RegistryLoadOutcome.Accepted accepted => accepted.Policy,
            RegistryLoadOutcome.InfrastructureFailure failure =>
                throw new SplitPlanException($"split policy failed to load: {failure.Message}"),
        };
    }

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new SplitPlanException($"split snapshot failed to decode: {failure.Message}"),
        };

    private static SplitOptions Parse(IReadOnlyList<string> arguments)
    {
        if (arguments.Count == 0 || arguments[0].StartsWith("--", StringComparison.Ordinal))
        {
            throw new SplitUsageException("SPLIT_INVALID missing source directory");
        }

        string? domain = null;
        string? date = null;
        string? baseRevision = null;
        var apply = false;
        for (var index = 1; index < arguments.Count; index++)
        {
            var option = arguments[index];
            if (option == "--apply")
            {
                if (apply) throw new SplitUsageException("SPLIT_INVALID duplicate --apply");
                apply = true;
                continue;
            }

            if (option is not ("--domain" or "--date" or "--base") || index + 1 >= arguments.Count)
            {
                throw new SplitUsageException($"SPLIT_INVALID unknown or incomplete option {option}");
            }

            var value = arguments[++index];
            switch (option)
            {
                case "--domain" when domain is null:
                    domain = value;
                    break;
                case "--date" when date is null:
                    date = value;
                    break;
                case "--base" when baseRevision is null:
                    baseRevision = value;
                    break;
                default:
                    throw new SplitUsageException($"SPLIT_INVALID duplicate option {option}");
            }
        }

        if (domain is null || date is null)
        {
            throw new SplitUsageException("SPLIT_INVALID --domain and --date are required");
        }

        return new SplitOptions(arguments[0], domain, date, baseRevision, apply);
    }

    private static string FullPath(string repositoryRoot, string relativePath)
    {
        var root = Path.GetFullPath(repositoryRoot);
        var path = Path.GetFullPath(Path.Combine(root, relativePath));
        var prefix = root.EndsWith(Path.DirectorySeparatorChar)
            ? root
            : root + Path.DirectorySeparatorChar;
        if (!path.StartsWith(prefix, StringComparison.Ordinal))
        {
            throw new InvalidOperationException($"split path escapes repository root: {relativePath}");
        }

        return path;
    }

    private sealed record SplitOptions(
        string SourceDirectory,
        string DestinationDomain,
        string Date,
        string? BaseRevision,
        bool Apply);

    private sealed class SplitUsageException(string message) : Exception(message);
}
