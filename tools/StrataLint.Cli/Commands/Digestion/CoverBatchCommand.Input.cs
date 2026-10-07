using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class CoverBatchCommand
{
    private sealed record BatchItem(string AtomId, ImmutableArray<string> Gids, ImmutableArray<int> Lines);
    private sealed record BatchArguments(ImmutableArray<BatchItem> Items);
    private sealed record BatchPlan(IReadOnlyDictionary<string, BatchItem> Items,
        IReadOnlyDictionary<string, string[]> Children, ImmutableArray<string> Order);
    private sealed class BatchInputException(string message) : Exception(message);

    private static BatchArguments Parse(string root, IReadOnlyList<string> arguments)
    {
        const string usage = "USAGE: StrataLint cover-batch --atoms FILE";
        string? file = null;
        for (var index = 0; index < arguments.Count; index += 2)
        {
            if (index + 1 >= arguments.Count) throw new BatchInputException(usage);
            switch (arguments[index])
            {
                case "--atoms" when file is null: file = arguments[index + 1]; break;
                default: throw new BatchInputException(usage);
            }
        }
        if (string.IsNullOrWhiteSpace(file))
            throw new BatchInputException(usage);

        var text = new UTF8Encoding(false, true).GetString(File.ReadAllBytes(Path.GetFullPath(file, root)));
        var lines = text.Split('\n');
        var items = new Dictionary<string, (List<string> Gids, List<int> Lines)>(StringComparer.Ordinal);
        for (var index = 0; index < lines.Length; index++)
        {
            if (index == lines.Length - 1 && lines[index].Length == 0) break;
            var fields = lines[index].Split('\t');
            if (fields.Length != 2 || fields[0].Length == 0
                || fields[0].Any(character => character is not (>= 'a' and <= 'z' or >= '0' and <= '9' or '-'))
                || fields[1].Any(char.IsWhiteSpace)
                || !Gid.TryParse(fields[1], out var gid)
                || gid.ToTarget() is not Target.Formal { Declaration: not null })
            {
                throw new BatchInputException($"line {index + 1} must be ATOM_ID<TAB>DECL_GID");
            }
            if (!items.TryGetValue(fields[0], out var item))
            {
                item = ([], []);
                items.Add(fields[0], item);
            }
            if (!item.Gids.Contains(fields[1], StringComparer.Ordinal)) item.Gids.Add(fields[1]);
            item.Lines.Add(index + 1);
        }
        if (items.Count == 0) throw new BatchInputException("cover-batch input is empty");
        return new(items.Select(pair => new BatchItem(pair.Key,
            [.. pair.Value.Gids], [.. pair.Value.Lines])).ToImmutableArray());
    }

    private static BatchPlan Plan(ImmutableArray<BatchItem> items, BackfillInventoryDocument document)
    {
        var requested = items.ToDictionary(item => item.AtomId, StringComparer.Ordinal);
        var entries = document.RequireDigestionEntries().GroupBy(entry => entry.AtomId, StringComparer.Ordinal)
            .Where(group => group.Count() == 1).ToDictionary(group => group.Key, group => group.Single(), StringComparer.Ordinal);
        var children = new Dictionary<string, string[]>(StringComparer.Ordinal);
        var pending = new Queue<string>(items.Select(item => item.AtomId));
        while (pending.TryDequeue(out var atomId))
        {
            if (children.ContainsKey(atomId)) continue;
            var dependencies = entries.TryGetValue(atomId, out var entry)
                ? entry.Receipts.ChainAtoms.Distinct(StringComparer.Ordinal).ToArray() : [];
            children.Add(atomId, dependencies);
            foreach (var child in dependencies) pending.Enqueue(child);
        }

        // Include unrequested intermediates so cycles and failure propagation are transitive.
        var ranks = children.Keys.Select((atomId, index) => (atomId, index))
            .ToDictionary(item => item.atomId, item => item.index, StringComparer.Ordinal);
        var remaining = children.ToDictionary(item => item.Key, item => item.Value.Length, StringComparer.Ordinal);
        var parents = children.Keys.ToDictionary(atomId => atomId, _ => new List<string>(), StringComparer.Ordinal);
        foreach (var (parent, dependencies) in children)
            foreach (var child in dependencies) parents[child].Add(parent);
        var ready = new PriorityQueue<string, int>();
        foreach (var (atomId, count) in remaining)
            if (count == 0) ready.Enqueue(atomId, ranks[atomId]);
        var order = ImmutableArray.CreateBuilder<string>();
        while (ready.TryDequeue(out var atomId, out _))
        {
            order.Add(atomId);
            foreach (var parent in parents[atomId])
                if (--remaining[parent] == 0) ready.Enqueue(parent, ranks[parent]);
        }
        if (order.Count != children.Count)
            throw new BatchInputException("relevant chain dependency cycle: " + string.Join(",",
                remaining.Where(item => item.Value > 0).Select(item => item.Key).Order(StringComparer.Ordinal)));
        return new(requested, children, order.ToImmutable());
    }
}
