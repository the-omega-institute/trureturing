using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Engine;

public static partial class FrozenLedger
{
    public static FrozenLedgerValidationOutcome ValidateCandidate(
        ImmutableArray<DagLedgerFileEvent> events,
        FrozenLedgerConsistent baseline,
        FrozenMaterialCatalog catalog) =>
        ValidateCandidate(
            events,
            baseline,
            catalog,
            requireCompleteCatalog: true);

    private static FrozenLedgerValidationOutcome ValidateCandidate(
        ImmutableArray<DagLedgerFileEvent> events,
        FrozenLedgerConsistent baseline,
        FrozenMaterialCatalog catalog,
        bool requireCompleteCatalog)
    {
        if (events.IsDefault)
        {
            throw new ArgumentException("Candidate frozen event set is uninitialized.", nameof(events));
        }
        ArgumentNullException.ThrowIfNull(baseline);
        ArgumentNullException.ThrowIfNull(catalog);
        try
        {
            var active = baseline.ActiveEntries.ToDictionary(static item => item.Key, static item => item.Value, StringComparer.Ordinal);
            var allCaseIds = baseline.AllCaseIds.ToHashSet(StringComparer.Ordinal);
            var activePathCases = active.Values.ToDictionary(
                static item => item.Material.RepoPath,
                static item => item.Payload.CaseId);
            var eventHashes = baseline.EventHashes.ToHashSet(StringComparer.Ordinal);
            foreach (var item in events)
            {
                if (item.SchemaVersion != FrozenLedgerCanonicalWriter.CurrentDagSchemaVersion)
                {
                    throw new FormatException(
                        $"New accepted event must use schema_version {FrozenLedgerCanonicalWriter.CurrentDagSchemaVersion}.");
                }

                if (!eventHashes.Add(item.EventHash))
                {
                    throw new FormatException("Candidate frozen event set duplicates an existing event hash.");
                }

                if (item.EventType == "Freeze")
                {
                    var freeze = ParseFreeze(item.Payload, catalog);
                    var freezePath = RepoPath.CreateKnown(freeze.DescriptorSelector);
                    if (!allCaseIds.Add(freeze.CaseId)
                        || activePathCases.ContainsKey(freezePath))
                    {
                        throw new FormatException(
                            "Freeze reused an active case ID or module path; revoke the active snapshot first.");
                    }

                    var material = catalog.ByPath[freezePath];
                    active.Add(
                        freeze.CaseId,
                        new FrozenActiveEntry(material, freeze, item.EventHash));
                    activePathCases.Add(freezePath, freeze.CaseId);
                    continue;
                }

                if (item.EventType == "Reanchor")
                {
                    var reanchor = ParseReanchor(item.Payload, catalog, out var previousEventHash);
                    if (!active.TryGetValue(reanchor.CaseId, out var current))
                    {
                        throw new FormatException("Reanchor targets a case that is not active.");
                    }

                    ValidateReanchorTransition(current, reanchor, previousEventHash);
                    var reanchorPath = RepoPath.CreateKnown(reanchor.DescriptorSelector);
                    active[reanchor.CaseId] = new FrozenActiveEntry(
                        catalog.ByPath[reanchorPath],
                        reanchor,
                        item.EventHash,
                        "Reanchor");
                    continue;
                }

                throw new FormatException(
                    $"Event type {item.EventType} is not legal in a candidate event set.");
            }

            var currentClosedPaths = catalog.States
                .Where(static item => item.Value is TruthState.Closed)
                .Select(static item => item.Key)
                .ToHashSet();
            var actual = active.Values.ToDictionary(static entry => entry.Material.RepoPath);
            var missing = currentClosedPaths.Except(actual.Keys)
                .OrderBy(static path => path.Value, StringComparer.Ordinal)
                .Select(static path => path.Value)
                .ToArray();
            if (requireCompleteCatalog && missing.Length > 0)
            {
                throw new FormatException("Closed modules are missing Freeze events: " + string.Join(", ", missing));
            }

            if (actual.Keys.Any(path => !currentClosedPaths.Contains(path)))
            {
                throw new FormatException(
                    "Active frozen view does not exactly match the current Closed module identities.");
            }

            var recordedPathsByIdentity = FrozenPathsByIdentity(
                active.Values.Select(static entry => entry.Material));
            var currentPathsByIdentity = FrozenPathsByIdentity(
                active.Values.Select(static entry => entry.Material),
                catalog.ClosedNodes);
            foreach (var (caseId, entry) in active.ToArray())
            {
                if (!catalog.ByPath.TryGetValue(entry.Material.RepoPath, out var candidateMaterial))
                {
                    continue;
                }

                if (!FrozenLedgerHistoricalFreezeMatcher.HistoricalActiveFreezeMatches(
                    entry.Payload,
                    candidateMaterial,
                    out _))
                {
                    throw new FormatException(
                        "Active frozen view does not exactly match the current Closed module identities.");
                }

                active[caseId] = entry with { Material = candidateMaterial };
            }

            var activeNodes = active.Values
                .Select(static entry => entry.Material)
                .OrderBy(static node => node.RepoPath.Value, StringComparer.Ordinal)
                .ToImmutableArray();
            var activeEntries = active.ToImmutableDictionary(StringComparer.Ordinal);
            var headHash = FrozenEventSetRoot.Compute(eventHashes);
            var corpusRoot = ComputeCorpusRoot(
                headHash,
                activeEntries.Values.Select(static entry => entry.Payload).ToImmutableArray());
            return new FrozenLedgerValidationOutcome.Accepted(FrozenLedgerConsistent.Create(
                activeNodes,
                headHash,
                corpusRoot,
                ComputeFrozenGraphRoot(activeNodes),
                activeEntries,
                allCaseIds.ToImmutableHashSet(StringComparer.Ordinal),
                eventHashes.ToImmutableHashSet(StringComparer.Ordinal),
                baseline.EventCount + events.Length));
        }
        catch (Exception exception) when (exception is FormatException or JsonException or InvalidOperationException)
        {
            return new FrozenLedgerValidationOutcome.Rejected(exception.Message);
        }
    }

}
