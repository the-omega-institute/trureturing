using System.Buffers.Binary;
using System.Collections.Immutable;
using System.Text.Json;
using Dunet;

namespace StrataLint.Engine;

public sealed record FrozenLedgerLineSyntax(ImmutableArray<byte> RawBytes, JsonElement Value);

public sealed record FrozenLedgerSyntax(
    ImmutableArray<byte> RawBytes,
    ImmutableArray<FrozenLedgerLineSyntax> Lines);

public sealed record FrozenLedgerInput(
    string BaseCommitOid,
    string BaseTreeOid,
    string DescriptorBlobOid,
    string DescriptorSelector,
    string Materializer,
    ImmutableArray<string> SupportingBlobOids);

public sealed record FrozenExpectedVerdict(
    ImmutableArray<string> AllowedDispositions,
    string DiagnosticMatch,
    ImmutableArray<FrozenExpectedDiagnostic> RequiredDiagnostics);

public sealed record FrozenExpectedDiagnostic(string MessageSha256, string Path, string RuleId);

public sealed record FrozenGenesisPayload(
    string GeneratorBlobOid,
    string OriginCommitOid,
    string OriginTreeOid,
    int ProtocolVersion,
    string RuleCatalogRoot);

public sealed record FrozenFreezePayload(
    string CaseClass,
    string CaseId,
    ImmutableArray<FrozenDeclarationStatement> DeclarationStatementIds,
    string Evaluation,
    FrozenExpectedVerdict Expected,
    FrozenNodeId FrozenNodeId,
    FrozenLedgerInput Input,
    string InputFingerprint,
    RepoPath NodePath,
    ImmutableArray<FrozenNodeId> PrerequisiteFrozenNodeIds,
    string SemanticReceipt,
    StatementId StatementId,
    string TruthState,
    WitnessId WitnessId);

public sealed record FrozenReattestPayload(
    string CaseId,
    FrozenLedgerInput Input,
    string InputFingerprint,
    string PreviousAttestationEventHash,
    string SemanticReceipt);

public sealed record FrozenRevokePayload(
    ImmutableArray<string> AffectedCaseIds,
    ImmutableArray<FrozenNodeId> AffectedFrozenNodeIds,
    string ClosureHash,
    ImmutableArray<RevocationEvidence> Evidence,
    string GraphRoot,
    ImmutableArray<string> RootCaseIds,
    ImmutableArray<FrozenNodeId> RootFrozenNodeIds);

[Union(EnableImplicitConversions = false)]
public partial record FrozenLedgerEvent
{
    public partial record Genesis(
        int Sequence,
        string EventHash,
        string PreviousHash,
        FrozenGenesisPayload Payload);

    public partial record Freeze(
        int Sequence,
        string EventHash,
        string PreviousHash,
        FrozenFreezePayload Payload);

    public partial record Reattest(
        int Sequence,
        string EventHash,
        string PreviousHash,
        FrozenReattestPayload Payload);

    public partial record Revoke(
        int Sequence,
        string EventHash,
        string PreviousHash,
        FrozenRevokePayload Payload);
}

public sealed class FrozenLedgerConsistent
{
    private FrozenLedgerConsistent(
        ImmutableArray<byte> rawBytes,
        ImmutableArray<FrozenLedgerEvent> events,
        ImmutableArray<FrozenNodeMaterial> activeFrozenNodes,
        string headHash,
        string corpusRoot,
        string graphRoot,
        ImmutableDictionary<string, FrozenActiveEntry> activeEntries,
        ImmutableHashSet<string> allCaseIds,
        ImmutableHashSet<FrozenNodeId> revokedFrozenNodeIds)
    {
        RawBytes = rawBytes;
        Events = events;
        ActiveFrozenNodes = activeFrozenNodes;
        HeadHash = headHash;
        CorpusRoot = corpusRoot;
        GraphRoot = graphRoot;
        ActiveEntries = activeEntries;
        AllCaseIds = allCaseIds;
        RevokedFrozenNodeIds = revokedFrozenNodeIds;
    }

    public ImmutableArray<FrozenLedgerEvent> Events { get; }

    public ImmutableArray<FrozenNodeMaterial> ActiveFrozenNodes { get; }

    public string HeadHash { get; }

    public string CorpusRoot { get; }

    public string GraphRoot { get; }

    public ImmutableHashSet<FrozenNodeId> RevokedFrozenNodeIds { get; }

    internal ImmutableArray<byte> RawBytes { get; }

    internal ImmutableDictionary<string, FrozenActiveEntry> ActiveEntries { get; }

    internal ImmutableHashSet<string> AllCaseIds { get; }

    internal static FrozenLedgerConsistent Create(
        ImmutableArray<byte> rawBytes,
        ImmutableArray<FrozenLedgerEvent> events,
        ImmutableArray<FrozenNodeMaterial> activeFrozenNodes,
        string headHash,
        string corpusRoot,
        string graphRoot,
        ImmutableDictionary<string, FrozenActiveEntry> activeEntries,
        ImmutableHashSet<string> allCaseIds,
        ImmutableHashSet<FrozenNodeId> revokedFrozenNodeIds) =>
        new(
            rawBytes,
            events,
            activeFrozenNodes,
            headHash,
            corpusRoot,
            graphRoot,
            activeEntries,
            allCaseIds,
            revokedFrozenNodeIds);
}

internal sealed record FrozenActiveEntry(
    FrozenNodeMaterial Material,
    FrozenFreezePayload Payload,
    string LastAttestationEventHash);

[Union(EnableImplicitConversions = false)]
public partial record FrozenLedgerValidationOutcome
{
    public partial record Accepted(FrozenLedgerConsistent Capability);

    public partial record Rejected(string Message);
}
