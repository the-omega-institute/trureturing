using System.Collections.Immutable;
using Dunet;

namespace StrataLint.Engine;

public sealed record FrozenLedgerInput(
    string BaseCommitOid,
    string BaseTreeOid,
    string DescriptorBlobOid,
    string DescriptorSelector,
    ImmutableArray<string> SupportingBlobOids);

public sealed record FrozenFreezePayload(
    string CaseId,
    ImmutableArray<FrozenDeclarationStatement> DeclarationStatementIds,
    FrozenNodeId FrozenNodeId,
    FrozenLedgerInput Input,
    ImmutableArray<FrozenNodeId> PrerequisiteFrozenNodeIds,
    StatementId StatementId,
    WitnessId WitnessId)
{
    public ImmutableArray<string> AxiomClosure { get; init; }

    internal bool HasAxiomClosure => !AxiomClosure.IsDefault;
}

public sealed record FrozenRevokePayload(
    ImmutableArray<string> AffectedCaseIds,
    ImmutableArray<FrozenNodeId> AffectedFrozenNodeIds,
    string ClosureHash,
    ImmutableArray<RevocationEvidence> Evidence,
    string GraphRoot,
    ImmutableArray<string> RootCaseIds);

public sealed class FrozenLedgerConsistent
{
    private FrozenLedgerConsistent(
        ImmutableArray<FrozenNodeMaterial> activeFrozenNodes,
        string headHash,
        string corpusRoot,
        string graphRoot,
        ImmutableDictionary<string, FrozenActiveEntry> activeEntries,
        ImmutableHashSet<string> allCaseIds,
        ImmutableHashSet<FrozenNodeId> revokedFrozenNodeIds,
        ImmutableHashSet<string> eventHashes,
        int eventCount)
    {
        ActiveFrozenNodes = activeFrozenNodes;
        HeadHash = headHash;
        CorpusRoot = corpusRoot;
        GraphRoot = graphRoot;
        ActiveEntries = activeEntries;
        AllCaseIds = allCaseIds;
        RevokedFrozenNodeIds = revokedFrozenNodeIds;
        EventHashes = eventHashes;
        EventCount = eventCount;
    }

    public ImmutableArray<FrozenNodeMaterial> ActiveFrozenNodes { get; }

    public string HeadHash { get; }

    public string CorpusRoot { get; }

    public string GraphRoot { get; }

    public ImmutableHashSet<FrozenNodeId> RevokedFrozenNodeIds { get; }

    internal ImmutableDictionary<string, FrozenActiveEntry> ActiveEntries { get; }

    internal ImmutableHashSet<string> AllCaseIds { get; }

    internal ImmutableHashSet<string> EventHashes { get; }

    internal int EventCount { get; }

    internal static FrozenLedgerConsistent Create(
        ImmutableArray<FrozenNodeMaterial> activeFrozenNodes,
        string headHash,
        string corpusRoot,
        string graphRoot,
        ImmutableDictionary<string, FrozenActiveEntry> activeEntries,
        ImmutableHashSet<string> allCaseIds,
        ImmutableHashSet<FrozenNodeId> revokedFrozenNodeIds,
        ImmutableHashSet<string> eventHashes,
        int eventCount) =>
        new(
            activeFrozenNodes,
            headHash,
            corpusRoot,
            graphRoot,
            activeEntries,
            allCaseIds,
            revokedFrozenNodeIds,
            eventHashes,
            eventCount);
}

internal sealed record FrozenActiveEntry(
    FrozenNodeMaterial Material,
    FrozenFreezePayload Payload,
    string LastAttestationEventHash,
    bool AxiomClosureKnown = true);

[Union(EnableImplicitConversions = false)]
public partial record FrozenLedgerValidationOutcome
{
    public partial record Accepted
    {
        internal Accepted(FrozenLedgerConsistent capability) =>
            Capability = capability ?? throw new ArgumentNullException(nameof(capability));

        public FrozenLedgerConsistent Capability { get; }
    }

    public partial record Rejected(string Message)
    {
        internal ImmutableArray<RepoPath> HistoryFailurePaths { get; init; } =
            ImmutableArray<RepoPath>.Empty;
    }
}
