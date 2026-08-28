using System.Collections.Immutable;
using System.Text.Json;
using Dunet;
using Trureturing.Truth;

namespace StrataLint.Engine;

internal static class RevocationHashDomains
{
    internal const string Closure = "trureturing:revocation-closure:v1\0";
}

[Union(EnableImplicitConversions = false)]
public partial record RevocationEvidence
{
    public partial record KernelWitnessFailure(
        FrozenNodeId RootFrozenNodeId,
        WitnessId FailedWitnessId,
        string ReceiptBlobOid,
        string ReceiptSha256);

    public partial record AllowedAxiomRetired(
        FrozenNodeId RootFrozenNodeId,
        string AxiomName,
        string ReceiptBlobOid,
        string ReceiptSha256);

    public partial record FormalContradictionCertificate(
        FrozenNodeId RootFrozenNodeId,
        StatementId ContradictedStatementId,
        string ReceiptBlobOid,
        string ReceiptSha256);

    public partial record ContentAddressMismatch(
        FrozenNodeId RootFrozenNodeId,
        string ExpectedSha256,
        string ActualSha256,
        string ReceiptBlobOid,
        string ReceiptSha256);
}

public sealed class ValidatedRevocationEvidence
{
    private ValidatedRevocationEvidence(
        RevocationEvidence evidence,
        FrozenNodeId rootFrozenNodeId,
        string baselineHeadHash,
        string baselineGraphRoot)
    {
        Evidence = evidence;
        RootFrozenNodeId = rootFrozenNodeId;
        BaselineHeadHash = baselineHeadHash;
        BaselineGraphRoot = baselineGraphRoot;
    }

    public RevocationEvidence Evidence { get; }

    public FrozenNodeId RootFrozenNodeId { get; }

    internal string BaselineHeadHash { get; }

    internal string BaselineGraphRoot { get; }

    internal static ValidatedRevocationEvidence Create(
        RevocationEvidence evidence,
        FrozenNodeId rootFrozenNodeId,
        string baselineHeadHash,
        string baselineGraphRoot) =>
        new(evidence, rootFrozenNodeId, baselineHeadHash, baselineGraphRoot);
}

[Union(EnableImplicitConversions = false)]
public partial record RevocationEvidenceValidationOutcome
{
    public partial record Accepted
    {
        internal Accepted(ValidatedRevocationEvidence capability) =>
            Capability = capability ?? throw new ArgumentNullException(nameof(capability));

        public ValidatedRevocationEvidence Capability { get; }
    }

    public partial record Rejected(string Message);
}

public static class RevocationEvidenceValidator
{
    public static RevocationEvidenceValidationOutcome Validate(
        RevocationEvidence evidence,
        FrozenLedgerConsistent ledger,
        TrustedRevocationReceiptStore trustedReceipts)
    {
        ArgumentNullException.ThrowIfNull(evidence);
        ArgumentNullException.ThrowIfNull(ledger);
        ArgumentNullException.ThrowIfNull(trustedReceipts);
        try
        {
            var message = string.Empty;
            if (trustedReceipts.BaselineHeadHash != ledger.HeadHash
                || trustedReceipts.BaselineGraphRoot != ledger.GraphRoot
                || !trustedReceipts.Authorizes(evidence, out message))
            {
                throw new FormatException(string.IsNullOrEmpty(message)
                    ? "Typed revocation receipt store is bound to another baseline."
                    : message);
            }

            return new RevocationEvidenceValidationOutcome.Accepted(
                ValidatedRevocationEvidence.Create(
                    evidence,
                    Common(evidence).Root,
                    ledger.HeadHash,
                    ledger.GraphRoot));
        }
        catch (Exception exception) when (exception is FormatException or InvalidOperationException)
        {
            return new RevocationEvidenceValidationOutcome.Rejected(exception.Message);
        }
    }

    private static (FrozenNodeId Root, string ReceiptOid, string ReceiptSha) Common(
        RevocationEvidence evidence) => evidence switch
        {
            RevocationEvidence.KernelWitnessFailure value =>
                (value.RootFrozenNodeId, value.ReceiptBlobOid, value.ReceiptSha256),
            RevocationEvidence.AllowedAxiomRetired value =>
                (value.RootFrozenNodeId, value.ReceiptBlobOid, value.ReceiptSha256),
            RevocationEvidence.FormalContradictionCertificate value =>
                (value.RootFrozenNodeId, value.ReceiptBlobOid, value.ReceiptSha256),
            RevocationEvidence.ContentAddressMismatch value =>
                (value.RootFrozenNodeId, value.ReceiptBlobOid, value.ReceiptSha256),
            _ => throw new FormatException("Unknown revocation evidence variant."),
        };
}

public sealed class RevocationPlan
{
    private RevocationPlan(
        ImmutableArray<FrozenNodeId> rootFrozenNodeIds,
        ImmutableArray<FrozenNodeId> affectedFrozenNodeIds,
        ImmutableArray<string> affectedCaseIds,
        string closureHash,
        string graphRoot,
        string baselineHeadHash,
        ImmutableArray<ValidatedRevocationEvidence> evidence)
    {
        RootFrozenNodeIds = rootFrozenNodeIds;
        AffectedFrozenNodeIds = affectedFrozenNodeIds;
        AffectedCaseIds = affectedCaseIds;
        ClosureHash = closureHash;
        GraphRoot = graphRoot;
        BaselineHeadHash = baselineHeadHash;
        Evidence = evidence;
    }

    public ImmutableArray<FrozenNodeId> RootFrozenNodeIds { get; }

    public ImmutableArray<FrozenNodeId> AffectedFrozenNodeIds { get; }

    public ImmutableArray<string> AffectedCaseIds { get; }

    public string ClosureHash { get; }

    public string GraphRoot { get; }

    internal string BaselineHeadHash { get; }

    internal ImmutableArray<ValidatedRevocationEvidence> Evidence { get; }

    internal static RevocationPlan Create(
        ImmutableArray<FrozenNodeId> rootFrozenNodeIds,
        ImmutableArray<FrozenNodeId> affectedFrozenNodeIds,
        ImmutableArray<string> affectedCaseIds,
        string closureHash,
        string graphRoot,
        string baselineHeadHash,
        ImmutableArray<ValidatedRevocationEvidence> evidence) =>
        new(
            rootFrozenNodeIds,
            affectedFrozenNodeIds,
            affectedCaseIds,
            closureHash,
            graphRoot,
            baselineHeadHash,
            evidence);
}

[Union(EnableImplicitConversions = false)]
public partial record RevocationPlanOutcome
{
    public partial record Accepted
    {
        internal Accepted(RevocationPlan capability) =>
            Capability = capability ?? throw new ArgumentNullException(nameof(capability));

        public RevocationPlan Capability { get; }
    }

    public partial record Rejected(string Message);
}

internal sealed record RevocationClosure(
    ImmutableArray<FrozenNodeId> RootFrozenNodeIds,
    ImmutableArray<FrozenNodeId> AffectedFrozenNodeIds,
    ImmutableArray<string> AffectedCaseIds,
    string ClosureHash);

public static class RevocationPlanner
{
    public static RevocationPlanOutcome Plan(
        FrozenLedgerConsistent ledger,
        IEnumerable<ValidatedRevocationEvidence> evidence)
    {
        ArgumentNullException.ThrowIfNull(ledger);
        ArgumentNullException.ThrowIfNull(evidence);
        return Plan(
            ledger.ActiveEntries,
            ledger.HeadHash,
            ledger.GraphRoot,
            evidence);
    }

    internal static RevocationPlanOutcome Plan(
        IReadOnlyDictionary<string, FrozenActiveEntry> activeEntries,
        string baselineHeadHash,
        string graphRoot,
        IEnumerable<ValidatedRevocationEvidence> evidence)
    {
        try
        {
            var validated = evidence
                .GroupBy(static item => item.RootFrozenNodeId)
                .Select(static group => group.First())
                .OrderBy(static item => item.RootFrozenNodeId.Value, StringComparer.Ordinal)
                .ToImmutableArray();
            if (validated.Length == 0
                || validated.Any(item =>
                    item.BaselineHeadHash != baselineHeadHash
                    || item.BaselineGraphRoot != graphRoot))
            {
                throw new FormatException("Revocation evidence is empty or bound to a different ledger head/graph.");
            }

            var roots = validated.Select(static item => item.RootFrozenNodeId).ToImmutableArray();
            var closure = ComputeClosure(activeEntries, roots);
            return new RevocationPlanOutcome.Accepted(RevocationPlan.Create(
                closure.RootFrozenNodeIds,
                closure.AffectedFrozenNodeIds,
                closure.AffectedCaseIds,
                closure.ClosureHash,
                graphRoot,
                baselineHeadHash,
                validated));
        }
        catch (Exception exception) when (exception is FormatException or InvalidOperationException)
        {
            return new RevocationPlanOutcome.Rejected(exception.Message);
        }
    }

    internal static RevocationClosure ComputeClosure(
        IReadOnlyDictionary<string, FrozenActiveEntry> activeEntries,
        IEnumerable<FrozenNodeId> roots)
    {
        var orderedRoots = roots
            .Distinct()
            .OrderBy(static id => id.Value, StringComparer.Ordinal)
            .ToImmutableArray();
        var activeById = activeEntries.Values.ToDictionary(
            static entry => entry.Material.FrozenNodeId,
            static entry => entry);
        if (orderedRoots.Length == 0 || orderedRoots.Any(root => !activeById.ContainsKey(root)))
        {
            throw new FormatException("Revocation root set is empty or contains a non-active node.");
        }

        var reverse = new Dictionary<FrozenNodeId, HashSet<FrozenNodeId>>();
        var currentEdges = activeEntries.Values.Select(static entry => (
            Node: entry.Material.FrozenNodeId,
            Prerequisites: entry.Material.PrerequisiteFrozenNodeIds));
        foreach (var (node, prerequisites) in currentEdges)
        {
            foreach (var prerequisite in prerequisites)
            {
                if (!reverse.TryGetValue(prerequisite, out var dependents))
                {
                    dependents = new HashSet<FrozenNodeId>();
                    reverse.Add(prerequisite, dependents);
                }

                dependents.Add(node);
            }
        }

        var affected = new HashSet<FrozenNodeId>();
        var pending = new Stack<FrozenNodeId>(orderedRoots.Reverse());
        while (pending.TryPop(out var current))
        {
            if (!activeById.ContainsKey(current) || !affected.Add(current))
            {
                continue;
            }

            if (!reverse.TryGetValue(current, out var dependents))
            {
                continue;
            }

            foreach (var dependent in dependents.OrderByDescending(
                static item => item.Value,
                StringComparer.Ordinal))
            {
                pending.Push(dependent);
            }
        }

        var affectedIds = affected.OrderBy(static item => item.Value, StringComparer.Ordinal).ToImmutableArray();
        var caseIds = affectedIds.Select(id => activeById[id].Payload.CaseId)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();
        var material = JsonSerializer.SerializeToElement(new
        {
            affected_frozen_node_ids = affectedIds.Select(static id => id.Value),
            root_frozen_node_ids = orderedRoots.Select(static id => id.Value),
        });
        return new RevocationClosure(
            orderedRoots,
            affectedIds,
            caseIds,
            FrozenContentHash.Compute(
                RevocationHashDomains.Closure,
                StructuredCanonicalWriter.WriteJson(material).AsSpan()));
    }
}
