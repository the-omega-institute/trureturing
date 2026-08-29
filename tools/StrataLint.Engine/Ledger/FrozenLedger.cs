using System.Collections.Immutable;
using Dunet;

namespace StrataLint.Engine;

public sealed record FrozenFreezePayload(
    string DescriptorSelector,
    ImmutableArray<FrozenDeclarationStatement> DeclarationStatementIds,
    ImmutableArray<FrozenNodeId> PrerequisiteFrozenNodeIds,
    StatementId StatementId)
{
    public string CaseId => FrozenLedgerCanonicalWriter.CaseId(
        RepoPath.CreateKnown(DescriptorSelector),
        StatementId);
}

public sealed class FrozenLedgerConsistent
{
    private FrozenLedgerConsistent(
        ImmutableArray<FrozenNodeMaterial> activeFrozenNodes,
        string headHash,
        string corpusRoot,
        string graphRoot,
        ImmutableDictionary<string, FrozenActiveEntry> activeEntries,
        ImmutableHashSet<string> allCaseIds,
        ImmutableHashSet<string> eventHashes,
        int eventCount)
    {
        ActiveFrozenNodes = activeFrozenNodes;
        HeadHash = headHash;
        CorpusRoot = corpusRoot;
        GraphRoot = graphRoot;
        ActiveEntries = activeEntries;
        AllCaseIds = allCaseIds;
        EventHashes = eventHashes;
        EventCount = eventCount;
    }

    public ImmutableArray<FrozenNodeMaterial> ActiveFrozenNodes { get; }

    public string HeadHash { get; }

    public string CorpusRoot { get; }

    public string GraphRoot { get; }

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
        ImmutableHashSet<string> eventHashes,
        int eventCount) =>
        new(
            activeFrozenNodes,
            headHash,
            corpusRoot,
            graphRoot,
            activeEntries,
            allCaseIds,
            eventHashes,
            eventCount);
}

internal sealed record FrozenActiveEntry(
    FrozenNodeMaterial Material,
    FrozenFreezePayload Payload,
    string EventHash);

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
