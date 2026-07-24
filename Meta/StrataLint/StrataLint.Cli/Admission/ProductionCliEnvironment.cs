using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record PreparedRepository(string Revision, RawChangeSet Changes);

internal sealed record FrozenRevisionIdentity(string Revision, string CommitOid, string TreeOid);

internal interface IRepositoryGateway
{
    AdmissionTopologyOutcome InspectAdmissionTopology();

    PreparedRepository Prepare(string? protectedBase);

    FrozenRevisionIdentity ResolveFrozenRevision(string revision);

    FrozenRevisionIdentity ResolveCurrentRevision();

    RawRepositorySnapshot ReadCurrent();

    RawRepositorySnapshot ReadRevision(string revision);

    RawRepositorySnapshot ReadFrozenRevision(string revision);

    TrustedFrozenGitReferences ValidateFrozenReferences(FrozenLedgerReferenceSet references);
}

internal interface ILeanReportSource
{
    LeanAxiomReport Load(RepositorySnapshot snapshot);
}

internal sealed class ProductionCliEnvironment : ICliEnvironment
{
    private readonly string repositoryRoot;
    private readonly IRepositoryGateway repository;
    private readonly ILeanReportSource leanReportSource;
    private readonly IScribeEmissionVerifier? scribeEmissionVerifier;

    internal ProductionCliEnvironment(string repositoryRoot)
        : this(
            repositoryRoot,
            new GitRepositoryGateway(repositoryRoot),
            new PrecomputedLeanReportSource(repositoryRoot),
            new ProductionScribeEmissionVerifier(repositoryRoot))
    {
    }

    internal ProductionCliEnvironment(
        string repositoryRoot,
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource)
        : this(repositoryRoot, repository, leanReportSource, scribeEmissionVerifier: null)
    {
    }

    internal ProductionCliEnvironment(
        string repositoryRoot,
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        IScribeEmissionVerifier? scribeEmissionVerifier)
    {
        this.repositoryRoot = Path.GetFullPath(repositoryRoot);
        this.repository = repository;
        this.leanReportSource = leanReportSource;
        this.scribeEmissionVerifier = scribeEmissionVerifier;
    }

    public AdmissionOutcome Check(IReadOnlyList<string> arguments) =>
        CheckCommand.Run(repository, scribeEmissionVerifier, arguments);

    public AdmissionTopologyOutcome Topology(IReadOnlyList<string> arguments)
    {
        try
        {
            return arguments.Count == 0
                ? repository.InspectAdmissionTopology()
                : new AdmissionTopologyOutcome.InfrastructureFailure("USAGE: StrataLint topology");
        }
        catch (Exception exception)
        {
            return new AdmissionTopologyOutcome.InfrastructureFailure(exception.Message);
        }
    }

    public CommandResult Coverage(IReadOnlyList<string> arguments) =>
        CoverageCommand.Run(repository, leanReportSource, arguments);

    public CommandResult DigestStatus(IReadOnlyList<string> arguments) =>
        scribeEmissionVerifier is null
            ? new CommandResult(
                false,
                string.Empty,
                "DIGEST_STATUS_INVALID Scribe emission verifier is unavailable\n")
            : DigestStatusCommand.Run(
                repository,
                leanReportSource,
                scribeEmissionVerifier,
                arguments);

    public ExplicitCommandResult EchoVerify(IReadOnlyList<string> arguments) =>
        scribeEmissionVerifier is null
            ? new ExplicitCommandResult(
                2,
                string.Empty,
                "ECHO_VERIFY_INFRASTRUCTURE Scribe emission verifier is unavailable\n")
            : EchoVerifyCommand.Run(
                repositoryRoot,
                repository,
                leanReportSource,
                scribeEmissionVerifier,
                arguments);

    public CommandResult Ingest(IReadOnlyList<string> arguments) =>
        scribeEmissionVerifier is null
            ? new CommandResult(
                false,
                string.Empty,
                "INGEST_INVALID Scribe emission verifier is unavailable\n")
            : IngestCommand.Run(
                repositoryRoot,
                repository,
                leanReportSource,
                scribeEmissionVerifier,
                arguments);

    public CommandResult Route(IReadOnlyList<string> arguments) =>
        RouteCommand.Run(repositoryRoot, arguments);

    public CommandResult RecordGolden(IReadOnlyList<string> arguments) =>
        GoldenRecordCommand.Run(repositoryRoot, arguments);

    public CommandResult SelfTest(IReadOnlyList<string> arguments) =>
        SelfTestCommand.Run(repositoryRoot, arguments);

    public CommandResult GenerateLedger(IReadOnlyList<string> arguments) =>
        DagLedgerGenesisWriter.Generate(
            repositoryRoot,
            repository,
            leanReportSource,
            arguments);

    public CommandResult AppendLedger(IReadOnlyList<string> arguments) =>
        DagLedgerAppendWriter.Append(repositoryRoot, repository, arguments);

    public CommandResult ReattestLedger(IReadOnlyList<string> arguments) =>
        DagLedgerReattestWriter.Reattest(repositoryRoot, repository, arguments);

    public CommandResult CleanLanes(IReadOnlyList<string> arguments) =>
        CleanLanesCommand.Run(repositoryRoot, arguments);

    public CommandResult AppendPerf(IReadOnlyList<string> arguments) =>
        PerfAppendCommand.Run(repositoryRoot, arguments);

    public CommandResult PerfReport(IReadOnlyList<string> arguments) =>
        PerfReportCommand.Run(arguments);

    public CommandResult Worktree(IReadOnlyList<string> arguments) =>
        WorktreeCommand.Run(repositoryRoot, arguments);

    public CommandResult RenewC0(IReadOnlyList<string> arguments) =>
        C0RenewCommand.Run(repositoryRoot, arguments);

    public ExplicitCommandResult VerifyConservative(IReadOnlyList<string> arguments) =>
        ConservativeExtensionCommand.Run(arguments);

    public ExplicitCommandResult EvaluateConservativeCorpus(IReadOnlyList<string> arguments) =>
        ConservativeCorpusWorker.Run(arguments);
}
