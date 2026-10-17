using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

// Dispatch policy belongs to the source; it has no mathematical or status authority.
internal static class SourceDispatchCommand
{
    internal static CommandResult Run(string root, IRepositoryGateway repository,
        IReadOnlyList<string> arguments, Action? beforeCommit = null, Action<string, string>? commit = null)
    {
        try
        {
            var (selectors, choice) = Parse(arguments);
            var (raw, document) = DigestionQuerySelection.ReadSourceMetadata(repository, selectors);
            var sources = document.RequireDigestionSources();
            foreach (var source in sources) _ = AtomizerRegistry.Require(source.Atomizer);
            var updates = ImmutableArray.CreateBuilder<IngestCommand.LedgerUpdate>();
            if (choice is { } selected)
            {
                foreach (var source in sources.Where(source => source.DefaultDispatch != selected))
                {
                    var path = BackfillInventoryLoader.RootPath + source.SourceId + "/source.toml";
                    var bytes = BackfillInventoryWriter.WriteSourceMetadata(source with { DefaultDispatch = selected });
                    var replay = DigestionQuerySelection.Load(RawRepositorySnapshot.Create([new(path, bytes)]));
                    if (replay.Document.RequireDigestionSources().Single().DefaultDispatch != selected)
                        throw new FormatException("source dispatch round trip failed");
                    updates.Add(new(path, bytes));
                }
                beforeCommit?.Invoke();
                IngestCommand.ApplyLedgerUpdatesAtomically(root, raw, updates.ToImmutable(), commit,
                    () => RequireUnchanged(root, raw));
            }
            return new(true, string.Concat(sources.Select(source =>
                $"SOURCE_DISPATCH source_id={source.SourceId} default={Name(choice ?? source.DefaultDispatch)}\n"))
                + (choice is null ? string.Empty : $"SOURCE_DISPATCH_UPDATED changed={updates.Count}\n"), string.Empty);
        }
        catch (Exception error) when (error is not OutOfMemoryException)
        {
            return new(false, string.Empty, $"SOURCE_DISPATCH_INVALID {error.Message}\n");
        }
    }

    private static void RequireUnchanged(string root, RawRepositorySnapshot raw)
    {
        foreach (var entry in raw.Entries)
        {
            var path = Path.Combine(root, entry.Path.Replace('/', Path.DirectorySeparatorChar));
            if (!File.Exists(path) || !File.ReadAllBytes(path).AsSpan().SequenceEqual(entry.Bytes.AsSpan()))
                throw new IOException($"source metadata changed before dispatch update: {entry.Path}");
        }
    }

    private static string Name(DigestionDefaultDispatch choice) =>
        choice == DigestionDefaultDispatch.Excluded ? "excluded" : "eligible";

    private static (string[] Sources, DigestionDefaultDispatch? Choice) Parse(IReadOnlyList<string> arguments)
    {
        var sources = new List<string>();
        DigestionDefaultDispatch? choice = null;
        for (var index = 0; index < arguments.Count; index += 2)
        {
            if (index + 1 >= arguments.Count || string.IsNullOrWhiteSpace(arguments[index + 1])) throw Usage();
            var value = arguments[index + 1];
            switch (arguments[index])
            {
                case "--source": sources.Add(value); break;
                case "--default" when choice is null:
                    choice = value switch
                    {
                        "eligible" => DigestionDefaultDispatch.Eligible,
                        "excluded" => DigestionDefaultDispatch.Excluded,
                        _ => throw Usage(),
                    };
                    break;
                default: throw Usage();
            }
        }
        if (sources.Count == 0) throw Usage();
        return (sources.Distinct(StringComparer.Ordinal).ToArray(), choice);
    }

    private static FormatException Usage() => new(
        "USAGE: StrataLint source-dispatch --source SOURCE_ID_OR_PATH [--source ...] [--default eligible|excluded]");
}
