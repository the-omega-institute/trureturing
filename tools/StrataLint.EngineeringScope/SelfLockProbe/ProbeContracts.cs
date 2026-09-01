using System.Text.Json;
using System.Text.Json.Serialization;

namespace StrataLint.EngineeringScope;

internal enum GateKind { Engineering, Lean, Admission }
internal enum SubjectKind { Merge, SyntheticNoop }
internal enum TerminationKind { Exited, Signal, Cancellation, Timeout, Aborted }
internal enum BlockerKind { MissingIdentity }

internal sealed record SubjectContract(
    SubjectKind Kind,
    string HeadSha,
    string BaseSha,
    string HeadTreeSha,
    string BaseTreeSha);

internal sealed record TerminationContract(
    TerminationKind Kind,
    int? ExitCode,
    string? Signal);

internal sealed record IdentityContract(string Assembly, string TestId);

internal sealed record BlockerContract(
    BlockerKind Kind,
    string FailureKey,
    string Assembly,
    string TestId);

internal sealed record TrxArtifactContract(
    string FileName,
    string Assembly,
    string Sha256);

internal sealed record SupervisorFinalContract(
    int SchemaVersion,
    string Publication,
    GateKind Gate,
    SubjectContract Subject,
    string EvaluatorDigest,
    TerminationContract Termination,
    bool DiagnosticsComplete,
    IReadOnlyList<string> FailureKeys,
    IReadOnlyList<IdentityContract> RequiredIdentities,
    IReadOnlyList<BlockerContract> Blockers,
    IReadOnlyList<TrxArtifactContract> TrxArtifacts,
    IReadOnlyList<string> Diagnostics,
    IReadOnlyList<string> StepFailures);

internal sealed record SentinelTrxContract(string FileName, string Sha256);

internal sealed record FinalizationSentinelContract(
    int SchemaVersion,
    string SupervisorResultSha256,
    IReadOnlyList<SentinelTrxContract> TrxArtifacts);

internal sealed record PublicationPointerContract(
    int SchemaVersion,
    string PublicationId,
    string PayloadDirectory,
    string SentinelSha256);

internal sealed record AuthorityReceiptContract(
    int SchemaVersion,
    string ControllerCommit,
    string ProducerPath,
    string ProducerSha256,
    string BundlePath,
    string PublicationId,
    string PayloadDirectory,
    string SentinelSha256,
    string SupervisorResultSha256,
    IReadOnlyList<SentinelTrxContract> TrxArtifacts);

internal sealed record PublishedEvidenceContract(
    string AuthorityReceiptPath,
    string PayloadPath);

internal static class JudgmentOutcome
{
    internal const string Admit = "admit";
    internal const string SemanticReject = "semantic_reject";
    internal const string InfrastructureFailure = "infrastructure_failure";
    internal const string Unsupported = "unsupported";
}

internal sealed record CoverageContract(
    bool Complete,
    IReadOnlyList<IdentityContract> RequiredIdentities,
    IReadOnlyList<IdentityContract> ObservedIdentities);

internal sealed record NormalizedJudgment(
    GateKind Gate,
    string Subject,
    string Outcome,
    string EvaluatorDigest,
    SubjectContract? SubjectContract,
    IReadOnlyList<string> FailureKeys,
    IReadOnlyList<BlockerContract> Blockers,
    CoverageContract? Coverage,
    IReadOnlyList<string> ReasonCodes)
{
    internal static NormalizedJudgment Infrastructure(
        GateKind gate,
        string subject,
        string reason) => new(
            gate,
            subject,
            JudgmentOutcome.InfrastructureFailure,
            string.Empty,
            null,
            [],
            [],
            null,
            [reason]);
}

internal sealed record AuthorizationContract(
    bool AllowExactRevert,
    bool ChangesGateStatus,
    bool RerunRequiredAfterDevPush,
    IReadOnlyList<string> ConfirmedRedGates,
    string CandidateHeadSha,
    string TargetMergeSha);

internal sealed record ProbeResultContract(
    int SchemaVersion,
    string Decision,
    AuthorizationContract Authorization,
    IReadOnlyList<string> ReasonCodes,
    IReadOnlyList<NormalizedJudgment> Judgments);

internal static class ContractJson
{
    internal static readonly JsonSerializerOptions Options = new()
    {
        PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower,
        UnmappedMemberHandling = JsonUnmappedMemberHandling.Disallow,
        WriteIndented = false,
        Converters =
        {
            new JsonStringEnumConverter(
                JsonNamingPolicy.SnakeCaseLower,
                allowIntegerValues: false),
        },
    };
}
