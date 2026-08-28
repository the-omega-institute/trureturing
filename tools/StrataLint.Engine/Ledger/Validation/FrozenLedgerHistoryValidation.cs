using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Engine;

public static partial class FrozenLedger
{
    private sealed class HistoryFinalStateException(
        ImmutableArray<RepoPath> paths,
        string message) : FormatException(message)
    {
        internal ImmutableArray<RepoPath> Paths { get; } = paths;
    }

    internal static FrozenLedgerValidationOutcome ValidateTrustedHistory(
        FrozenLedgerBaseView baseView,
        FrozenMaterialCatalog catalog)
    {
        ArgumentNullException.ThrowIfNull(baseView);
        ArgumentNullException.ThrowIfNull(catalog);
        try
        {
            var active = baseView.ActiveByCase.ToDictionary(
                static item => item.Key,
                static item => item.Value,
                StringComparer.Ordinal);
            ReconcileHistoricalActive(active, catalog, requireCompleteCatalog: true);
            var baseline = baseView.ToWriterBaseline();
            var activeEntries = active.ToImmutableDictionary(StringComparer.Ordinal);
            var activeNodes = activeEntries.Values
                .Select(static entry => entry.Material)
                .OrderBy(static node => node.RepoPath.Value, StringComparer.Ordinal)
                .ToImmutableArray();
            return new FrozenLedgerValidationOutcome.Accepted(FrozenLedgerConsistent.Create(
                activeNodes,
                baseline.HeadHash,
                ComputeCorpusRoot(
                    baseline.HeadHash,
                    activeEntries.Values.Select(static entry => entry.Payload).ToImmutableArray()),
                ComputeFrozenGraphRoot(activeNodes),
                activeEntries,
                baseView.AllCaseIds,
                baseline.EventHashes,
                baseView.EventCount));
        }
        catch (Exception exception) when (
            exception is FormatException or JsonException or InvalidOperationException or KeyNotFoundException)
        {
            var rejected = new FrozenLedgerValidationOutcome.Rejected(exception.Message);
            return exception is HistoryFinalStateException finalState
                ? rejected with
                {
                    HistoryFailurePaths = finalState.Paths,
                }
                : rejected;
        }
    }

    private static void ReconcileHistoricalActive(
        Dictionary<string, FrozenActiveEntry> active,
        FrozenMaterialCatalog catalog,
        bool requireCompleteCatalog)
    {
        var expectedByPath = catalog.ClosedNodes.ToDictionary(static node => node.RepoPath);
        var actualByPath = active.Values.ToDictionary(static entry => entry.Material.RepoPath);
        var recordedPathsByIdentity = FrozenPathsByIdentity(
            active.Values.Select(static entry => entry.Material));
        var currentPathsByIdentity = FrozenPathsByIdentity(catalog.ClosedNodes);
        var missing = expectedByPath.Keys.Except(actualByPath.Keys)
            .OrderBy(static path => path.Value, StringComparer.Ordinal)
            .ToImmutableArray();
        if (requireCompleteCatalog && missing.Length > 0)
        {
            throw new HistoryFinalStateException(
                missing,
                "Closed modules are missing Freeze events: "
                + string.Join(", ", missing.Select(static path => path.Value))
                + "; run ledger-append to append the missing Freeze events.");
        }

        var outside = actualByPath.Keys.Except(expectedByPath.Keys)
            .OrderBy(static path => path.Value, StringComparer.Ordinal)
            .ToImmutableArray();
        if (outside.Length > 0)
        {
            throw new HistoryFinalStateException(
                outside,
                "Active frozen history contains modules outside the current Closed catalog: "
                + string.Join(", ", outside.Select(static path => path.Value))
                + "; append Revoke before replacing or removing their Freeze events.");
        }

        foreach (var (caseId, entry) in active.OrderBy(
            static item => item.Value.Material.RepoPath.Value,
            StringComparer.Ordinal).ToArray())
        {
            var material = expectedByPath[entry.Material.RepoPath];
            if (!material.AxiomClosure.All(LeanAxiomFacts.IsStandard))
            {
                throw new HistoryFinalStateException(
                    ImmutableArray.Create(material.RepoPath),
                    $"Active module {material.RepoPath.Value} current axiom closure exceeds the standard axiom allowlist.");
            }

            var materialMatches = FrozenLedgerHistoricalFreezeMatcher.HistoricalActiveFreezeMatches(
                entry.Payload,
                material,
                out _);
            if (materialMatches)
            {
                active[caseId] = entry with { Material = material };
                continue;
            }

            if (entry.Payload.StatementId != material.StatementId
                || !entry.Payload.DeclarationStatementIds.SequenceEqual(
                    material.DeclarationStatementIds))
            {
                throw new HistoryFinalStateException(
                    ImmutableArray.Create(material.RepoPath),
                    $"Active module {material.RepoPath.Value} statement identity changed; append Revoke before rerunning ledger-append.");
            }

            throw new HistoryFinalStateException(
                ImmutableArray.Create(material.RepoPath),
                $"Active module {material.RepoPath.Value} changed identity; append Revoke before rerunning ledger-append.");
        }
    }

    private static ImmutableDictionary<FrozenNodeId, RepoPath> FrozenPathsByIdentity(
        params IEnumerable<FrozenNodeMaterial>[] materialGroups)
    {
        var result = ImmutableDictionary.CreateBuilder<FrozenNodeId, RepoPath>();
        foreach (var material in materialGroups.SelectMany(static group => group))
        {
            if (result.TryGetValue(material.FrozenNodeId, out var existing)
                && existing != material.RepoPath)
            {
                throw new FormatException(
                    $"Frozen node identity {material.FrozenNodeId.Value} resolves to multiple module paths.");
            }

            result[material.FrozenNodeId] = material.RepoPath;
        }

        return result.ToImmutable();
    }
}
