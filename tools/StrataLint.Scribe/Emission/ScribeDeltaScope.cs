using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Scribe;

internal sealed record ScribeDeltaDocument(
    string Gid,
    string DefinitionPath,
    string EmissionPath);

internal sealed class ScribeDeltaInputs
{
    private ScribeDeltaInputs(
        string? baseRevision,
        RawChangeSet changes,
        ImmutableHashSet<string> producerPaths,
        Func<string, string?> readBaseDocument)
    {
        BaseRevision = baseRevision;
        Changes = changes;
        ProducerPaths = producerPaths;
        ReadBaseDocument = readBaseDocument;
    }

    internal string? BaseRevision { get; }

    internal RawChangeSet Changes { get; }

    internal ImmutableHashSet<string> ProducerPaths { get; }

    internal Func<string, string?> ReadBaseDocument { get; }

    internal static ScribeDeltaInputs Create(
        string baseRevision,
        RawChangeSet changes,
        ImmutableHashSet<string> producerPaths,
        Func<string, string?> readBaseDocument)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(baseRevision);
        ArgumentNullException.ThrowIfNull(changes);
        ArgumentNullException.ThrowIfNull(producerPaths);
        ArgumentNullException.ThrowIfNull(readBaseDocument);
        return new ScribeDeltaInputs(baseRevision, changes, producerPaths, readBaseDocument);
    }

    internal static ScribeDeltaInputs CreateForTests(
        RawChangeSet changes,
        ImmutableHashSet<string> producerPaths) =>
        new(null, changes, producerPaths, static _ => null);
}

internal sealed class ScribeDeltaScope
{
    private ScribeDeltaScope(bool isFull, ImmutableHashSet<string> emissionPaths)
    {
        IsFull = isFull;
        EmissionPaths = emissionPaths;
    }

    internal bool IsFull { get; }

    internal ImmutableHashSet<string> EmissionPaths { get; }

    internal bool Contains(string emissionPath) => EmissionPaths.Contains(emissionPath);

    internal static ScribeDeltaScope Full(IEnumerable<ScribeDeltaDocument> documents) =>
        new(
            true,
            documents.Select(static document => document.EmissionPath)
                .ToImmutableHashSet(StringComparer.Ordinal));

    internal static ScribeDeltaScope Create(
        RawChangeSet changes,
        IReadOnlySet<string> producerPaths,
        IEnumerable<ScribeDeltaDocument> documents,
        IReadOnlyDictionary<string, ImmutableHashSet<string>> candidateDescribeTargets,
        IReadOnlyDictionary<string, ImmutableHashSet<string>> baseDescribeTargets)
    {
        ArgumentNullException.ThrowIfNull(changes);
        ArgumentNullException.ThrowIfNull(producerPaths);
        ArgumentNullException.ThrowIfNull(documents);
        ArgumentNullException.ThrowIfNull(candidateDescribeTargets);
        ArgumentNullException.ThrowIfNull(baseDescribeTargets);
        var material = documents.ToImmutableArray();
        var byDefinition = material.ToDictionary(
            static document => document.DefinitionPath,
            StringComparer.Ordinal);
        var byEmission = material.ToDictionary(
            static document => document.EmissionPath,
            StringComparer.Ordinal);
        var byGid = material.ToDictionary(static document => document.Gid, StringComparer.Ordinal);

        if (changes.Entries.Any(change =>
                FrozenLedgerDeltaPredicate.IsEnvironmentInput(change.Path.Value)
                || FrozenLedgerDeltaPredicate.IsManagedLeanSource(change.Path.Value)
                || FrozenLedgerDeltaPredicate.IsDeltaDefinitionInput(change.Path.Value)
                || IsSharedScribeProducerFamily(change.Path.Value)
                || IsSharedRuntimeInput(change.Path.Value)
                || producerPaths.Contains(change.Path.Value)
                    && !byDefinition.ContainsKey(change.Path.Value)
                || IsBlueprintDefinition(change.Path.Value)
                    && !byDefinition.ContainsKey(change.Path.Value)
                || IsBlueprintEmission(change.Path.Value)
                    && !byEmission.ContainsKey(change.Path.Value)))
        {
            return Full(material);
        }

        var selected = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
        foreach (var change in changes.Entries)
        {
            if (byEmission.TryGetValue(change.Path.Value, out var emissionDocument))
            {
                selected.Add(emissionDocument.EmissionPath);
            }

            if (!byDefinition.TryGetValue(change.Path.Value, out var definitionDocument))
            {
                continue;
            }

            selected.Add(definitionDocument.EmissionPath);
            AddDescribeTargets(change.Path.Value, candidateDescribeTargets);
            AddDescribeTargets(change.Path.Value, baseDescribeTargets);
        }

        return new ScribeDeltaScope(false, selected.ToImmutable());

        void AddDescribeTargets(
            string definitionPath,
            IReadOnlyDictionary<string, ImmutableHashSet<string>> targetsByDefinition)
        {
            if (!targetsByDefinition.TryGetValue(definitionPath, out var targets)) return;
            foreach (var target in targets)
            {
                if (!byGid.TryGetValue(target, out var targetDocument))
                {
                    throw new InvalidOperationException(
                        $"Scribe delta target does not name a candidate document: {target}");
                }

                selected.Add(targetDocument.EmissionPath);
            }
        }
    }

    internal static bool RequiresValuesProjection(
        RawChangeSet changes,
        IReadOnlySet<string> producerPaths)
    {
        ArgumentNullException.ThrowIfNull(changes);
        ArgumentNullException.ThrowIfNull(producerPaths);
        var inputs = CanonicalValuesWriter.InputPaths.ToImmutableHashSet(StringComparer.Ordinal);
        return changes.Entries.Any(change =>
            change.Path.Value == CanonicalValuesWriter.RelativePath
            || inputs.Contains(change.Path.Value)
            || producerPaths.Contains(change.Path.Value)
                && !IsBlueprintDefinition(change.Path.Value));
    }

    internal static bool RequiresBlueprintEmission(
        RawChangeSet changes,
        IReadOnlySet<string> producerPaths)
    {
        ArgumentNullException.ThrowIfNull(changes);
        ArgumentNullException.ThrowIfNull(producerPaths);
        return changes.Entries.Any(change =>
            FrozenLedgerDeltaPredicate.IsEnvironmentInput(change.Path.Value)
            || FrozenLedgerDeltaPredicate.IsManagedLeanSource(change.Path.Value)
            || FrozenLedgerDeltaPredicate.IsDeltaDefinitionInput(change.Path.Value)
            || IsSharedScribeProducerFamily(change.Path.Value)
            || IsSharedRuntimeInput(change.Path.Value)
            || producerPaths.Contains(change.Path.Value)
            || IsBlueprintDefinition(change.Path.Value)
            || IsBlueprintEmission(change.Path.Value));
    }

    private static bool IsBlueprintDefinition(string path) =>
        path.StartsWith("Blueprint/", StringComparison.Ordinal)
        && path.EndsWith(".scribe.cs", StringComparison.Ordinal);

    private static bool IsBlueprintEmission(string path) =>
        path.StartsWith("Blueprint/", StringComparison.Ordinal)
        && path.EndsWith(".md", StringComparison.Ordinal);

    private static bool IsSharedScribeProducerFamily(string path) =>
        path is "tools/StrataLint.Scribe/StrataLint.Scribe.csproj"
            or "tools/StrataLint.Scribe/packages.lock.json"
        || path.StartsWith("tools/StrataLint.Scribe/", StringComparison.Ordinal)
            && path.EndsWith(".cs", StringComparison.Ordinal);

    private static bool IsSharedRuntimeInput(string path) =>
        path.StartsWith("Library/", StringComparison.Ordinal)
        || path.StartsWith("Golden/Projection/", StringComparison.Ordinal)
        || path == "Meta/BACKFILL.yaml"
        || path == "Meta/Digestion/ticket-index.toml"
        || path.StartsWith("Meta/Digestion/backfill/", StringComparison.Ordinal);
}

internal static class ScribeBaseDocumentReferences
{
    private const string NarrativePrefix = "- Narrative reference: [";
    private const string DescribeMarker = "#describe/";

    internal static ImmutableHashSet<string> ParseDescribeTargetGids(string markdown)
    {
        ArgumentNullException.ThrowIfNull(markdown);
        var targets = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
        foreach (var line in markdown.Split('\n'))
        {
            if (!line.StartsWith(NarrativePrefix, StringComparison.Ordinal)
                || !line.Contains(DescribeMarker, StringComparison.Ordinal))
            {
                continue;
            }

            var labelEnd = line.IndexOf("](", NarrativePrefix.Length, StringComparison.Ordinal);
            var marker = line.IndexOf(DescribeMarker, NarrativePrefix.Length, StringComparison.Ordinal);
            if (labelEnd < 0 || marker < 0 || marker >= labelEnd)
            {
                throw InvalidReference(line);
            }

            var gidText = line[NarrativePrefix.Length..marker];
            var describeId = line[(marker + DescribeMarker.Length)..labelEnd];
            var expectedAnchor = "#describe-" + describeId + ")";
            if (describeId.Length == 0
                || !line.EndsWith(expectedAnchor, StringComparison.Ordinal))
            {
                throw InvalidReference(line);
            }

            GidRef gid;
            try
            {
                gid = GidRef.Create(gidText);
            }
            catch (ArgumentException exception)
            {
                throw InvalidReference(line, exception);
            }
            if (!gid.IsFormalModule)
            {
                throw InvalidReference(line);
            }

            targets.Add(gid.Value);
        }

        return targets.ToImmutable();
    }

    private static FormatException InvalidReference(string line, Exception? inner = null) =>
        new($"trusted base Markdown has a malformed describe reference: {line}", inner);
}
