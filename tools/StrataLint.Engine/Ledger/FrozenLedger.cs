using System.Buffers.Binary;
using System.Collections.Immutable;
using System.Text.Json;
using Dunet;

namespace StrataLint.Engine;

public sealed record FrozenLedgerLineSyntax(
    ImmutableArray<byte> RawBytes,
    JsonElement Value,
    string? SourceDagEventHash = null);

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

public sealed record FrozenEnvironmentPins(
    string LakeManifestBlobOid,
    string LakefileBlobOid,
    RepoPath LakefilePath,
    string LeanToolchainBlobOid);

public sealed record FrozenSupersedePayload(
    ImmutableArray<string> AxiomClosure,
    string CaseId,
    ImmutableArray<FrozenDeclarationStatement> DeclarationStatementIds,
    FrozenEnvironmentPins Environment,
    FrozenNodeId FrozenNodeId,
    FrozenLedgerInput Input,
    ImmutableArray<FrozenNodeId> PrerequisiteFrozenNodeIds,
    string PreviousAttestationEventHash,
    StatementId StatementId,
    WitnessId WitnessId);

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

    public partial record Supersede(
        int Sequence,
        string EventHash,
        string PreviousHash,
        FrozenSupersedePayload Payload);

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
        ImmutableHashSet<FrozenNodeId> supersededFrozenNodeIds,
        ImmutableHashSet<FrozenNodeId> revokedFrozenNodeIds,
        int syntaxStartSequence)
    {
        RawBytes = rawBytes;
        Events = events;
        ActiveFrozenNodes = activeFrozenNodes;
        HeadHash = headHash;
        CorpusRoot = corpusRoot;
        GraphRoot = graphRoot;
        ActiveEntries = activeEntries;
        AllCaseIds = allCaseIds;
        SupersededFrozenNodeIds = supersededFrozenNodeIds;
        RevokedFrozenNodeIds = revokedFrozenNodeIds;
        SyntaxStartSequence = syntaxStartSequence;
    }

    public ImmutableArray<FrozenLedgerEvent> Events { get; }

    public ImmutableArray<FrozenNodeMaterial> ActiveFrozenNodes { get; }

    public string HeadHash { get; }

    public string CorpusRoot { get; }

    public string GraphRoot { get; }

    public ImmutableHashSet<FrozenNodeId> RevokedFrozenNodeIds { get; }

    public ImmutableHashSet<FrozenNodeId> SupersededFrozenNodeIds { get; }

    internal ImmutableArray<byte> RawBytes { get; }

    internal ImmutableDictionary<string, FrozenActiveEntry> ActiveEntries { get; }

    internal ImmutableHashSet<string> AllCaseIds { get; }

    internal int SyntaxStartSequence { get; }

    internal static FrozenLedgerConsistent Create(
        ImmutableArray<byte> rawBytes,
        ImmutableArray<FrozenLedgerEvent> events,
        ImmutableArray<FrozenNodeMaterial> activeFrozenNodes,
        string headHash,
        string corpusRoot,
        string graphRoot,
        ImmutableDictionary<string, FrozenActiveEntry> activeEntries,
        ImmutableHashSet<string> allCaseIds,
        ImmutableHashSet<FrozenNodeId> supersededFrozenNodeIds,
        ImmutableHashSet<FrozenNodeId> revokedFrozenNodeIds,
        int syntaxStartSequence = 0) =>
        new(
            rawBytes,
            events,
            activeFrozenNodes,
            headHash,
            corpusRoot,
            graphRoot,
            activeEntries,
            allCaseIds,
            supersededFrozenNodeIds,
            revokedFrozenNodeIds,
            syntaxStartSequence);
}

internal sealed record FrozenActiveEntry(
    FrozenNodeMaterial Material,
    FrozenFreezePayload Payload,
    string LastAttestationEventHash,
    bool AxiomClosureKnown = true,
    FrozenEnvironmentPins? Environment = null);

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
