using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.Cli;

internal sealed record PreparedRepository(string Revision, RawChangeSet Changes);

internal sealed record FrozenRevisionIdentity(string Revision, string CommitOid, string TreeOid);

internal sealed record CheckArguments(
    string? ProtectedBase,
    string? CandidateLeanReport,
    string? ScribePaths = null);

internal interface IRepositoryGateway
{
    AdmissionTopologyOutcome InspectAdmissionTopology();

    PreparedRepository Prepare(string? protectedBase);

    FrozenRevisionIdentity ResolveCurrentRevision();

    FrozenRevisionIdentity ResolveFrozenRevision(string revision) =>
        throw new InvalidOperationException("fixed revision identity is not supported by this gateway");

    RawRepositorySnapshot ReadCurrent();

    /// Preserves the whole path inventory and link policy while selecting regular bodies.
    /// An optional observer receives each original file's raw SHA256, including omitted bodies.
    RawRepositorySnapshot ReadCurrentProjection(Func<string, bool> readContents,
        Action<string, ReadOnlyMemory<byte>>? observeContentDigest = null)
    {
        var snapshot = ReadCurrent();
        if (observeContentDigest is not null && snapshot.Entries.Any(static entry => !entry.ContentWasRead))
            throw new InvalidOperationException("Full provenance requires original bodies, not unread placeholders.");
        foreach (var entry in snapshot.Entries)
            observeContentDigest?.Invoke(entry.Path, System.Security.Cryptography.SHA256.HashData(entry.Bytes.AsSpan()));
        return ProjectBodies(snapshot, readContents);
    }

    /// Reads the files at the given paths from the current repository snapshot. A
    /// directory selects everything under it, and the same FILEMAP/symlink policy as
    /// the whole-tree reader is applied.
    RawRepositorySnapshot ReadCurrent(IReadOnlyList<string> paths);

    /// Searches current paths without reading their file bodies.
    IReadOnlyList<string> SearchCurrentPaths(IReadOnlyList<string> paths);

    RawRepositorySnapshot ReadRevision(string revision);

    RawRepositorySnapshot ReadRevisionProjection(string revision, Func<string, bool> readContents,
        Action<string, ReadOnlyMemory<byte>>? observeContentDigest = null)
    {
        var snapshot = ReadRevision(revision);
        if (observeContentDigest is not null && snapshot.Entries.Any(static entry => !entry.ContentWasRead))
            throw new InvalidOperationException("Full provenance requires original bodies, not unread placeholders.");
        foreach (var entry in snapshot.Entries)
            observeContentDigest?.Invoke(entry.Path, System.Security.Cryptography.SHA256.HashData(entry.Bytes.AsSpan()));
        return ProjectBodies(snapshot, readContents);
    }

    private static RawRepositorySnapshot ProjectBodies(RawRepositorySnapshot snapshot, Func<string, bool> readContents)
    {
        ArgumentNullException.ThrowIfNull(readContents);
        var links = snapshot.PathInventory.IsDefault ? new HashSet<string>(StringComparer.Ordinal)
            : snapshot.PathInventory.Where(static entry => entry.State == "symlink")
                .Select(static entry => entry.Path).ToHashSet(StringComparer.Ordinal);
        return RawRepositorySnapshot.Create(snapshot.Entries.Select(entry =>
            readContents(entry.Path) || links.Contains(entry.Path) || FileMapDocuments.IsPolicyPath(entry.Path)
                ? entry : entry with { Bytes = [], ContentWasRead = false }), snapshot.PathInventory);
    }

    /// Reads selected paths and the FILEMAP inputs and link referents needed to validate them.
    RawRepositorySnapshot ReadRevision(string revision, IReadOnlyList<string> paths) =>
        throw new InvalidOperationException("scoped revision reads are not supported by this gateway");

    RawChangeSet ReadCurrentChanges();

    /// Reads the working-tree delta against an explicit revision, in the caller-supplied
    /// revision's own words -- no remote-ref resolution happens here (CLAUDE.md 第Ⅵ节 git
    /// reference discipline: only the caller may name a revision; this gateway just diffs it).
    RawChangeSet ReadChanges(string revision);

}

internal interface ILeanReportSource
{
    LeanAxiomReport Load(RepositorySnapshot snapshot);
}

/// Implemented by report sources that can consume a producer's scoped artifact.
/// Full-only test sources deliberately keep the default path, which preserves
/// existing full-mode tests while production rejects a scoped schema in Raw's
/// strict reader.
internal interface IScopedLeanReportSource
{
    LeanAxiomReport Load(LeanReportScope scope);
}

internal static class LeanReportSourceScope
{
    internal static LeanAxiomReport Load(
        ILeanReportSource source,
        RepositorySnapshot snapshot,
        IEnumerable<RepoPath> requestedTargets)
    {
        ArgumentNullException.ThrowIfNull(source);
        var scope = LeanReportScope.Create(snapshot, requestedTargets);
        return source is IScopedLeanReportSource scoped
            ? scoped.Load(scope)
            : source.Load(snapshot);
    }
}

internal sealed partial class ProductionCliEnvironment : ICliEnvironment
{
    private static readonly JsonSerializerOptions RouteJsonOptions = new()
    {
        WriteIndented = true,
        PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower,
    };

    private readonly string repositoryRoot;
    private readonly IRepositoryGateway repository;
    private readonly ILeanReportSource leanReportSource;
    private readonly IScribeEmissionVerifier? scribeEmissionVerifier;
    private readonly TimeProvider timeProvider;
    private readonly ReportFreeIngestDependencies reportFreeIngestDependencies;

    internal ProductionCliEnvironment(string repositoryRoot)
        : this(
            repositoryRoot,
            new GitRepositoryGateway(repositoryRoot),
            new PrecomputedLeanReportSource(repositoryRoot),
            new ProductionScribeEmissionVerifier())
    {
    }

    internal ProductionCliEnvironment(
        string repositoryRoot,
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource)
        : this(
            repositoryRoot,
            repository,
            leanReportSource,
            scribeEmissionVerifier: null)
    {
    }

    internal ProductionCliEnvironment(
        string repositoryRoot,
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        IScribeEmissionVerifier? scribeEmissionVerifier,
        ReportFreeIngestDependencies? reportFreeIngestDependencies = null)
        : this(
            repositoryRoot,
            repository,
            leanReportSource,
            scribeEmissionVerifier,
            TimeProvider.System,
            reportFreeIngestDependencies)
    {
    }

    internal ProductionCliEnvironment(
        string repositoryRoot,
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        IScribeEmissionVerifier? scribeEmissionVerifier,
        TimeProvider timeProvider,
        ReportFreeIngestDependencies? reportFreeIngestDependencies = null)
    {
        this.repositoryRoot = Path.GetFullPath(repositoryRoot);
        this.repository = repository;
        this.leanReportSource = leanReportSource;
        this.scribeEmissionVerifier = scribeEmissionVerifier;
        this.timeProvider = timeProvider;
        this.reportFreeIngestDependencies =
            reportFreeIngestDependencies ?? new ReportFreeIngestDependencies();
    }

    public ExplicitCommandResult CapacityAudit(IReadOnlyList<string> arguments) =>
        CapacityAuditCommand.Run(arguments, repositoryRoot);

    public AdmissionOutcome Check(IReadOnlyList<string> arguments)
    {
        var timing = new AdmissionCheckTiming(timeProvider);
        ImmutableArray<Diagnostic> planeObservations = [];
        try
        {
            var repositoryPhase = timing.Measure(
                "repository-prepare",
                () =>
                {
                    var options = ParseCheckArguments(arguments);
                    var prepared = repository.Prepare(options.ProtectedBase);
                    var bootstrap = BootstrapGate.Evaluate(prepared.Changes);
                    return (
                        Options: options,
                        Prepared: prepared,
                        Bootstrap: bootstrap);
                },
                static result => result.Bootstrap is BootstrapOutcome.InfrastructureFailure
                    || result.Options.CandidateLeanReport is null);
            var options = repositoryPhase.Options;
            var prepared = repositoryPhase.Prepared;
            var bootstrap = repositoryPhase.Bootstrap;
            if (bootstrap is BootstrapOutcome.InfrastructureFailure bootstrapFailure)
            {
                return new AdmissionOutcome.InfrastructureFailure(bootstrapFailure.Message);
            }
            if (options.CandidateLeanReport is null)
            {
                return new AdmissionOutcome.InfrastructureFailure(
                    "check requires --candidate-lean-report FILE");
            }
            var rawSnapshots = timing.Measure(
                "repository-read",
                () => (
                    Current: AdmissionRepositoryInputs.ReadCurrent(repository),
                    Baseline: AdmissionRepositoryInputs.ReadBaseline(repository, prepared.Revision)));
            var currentRaw = AdmissionRepositoryInputs.ReadDeltaInputs(
                repository, rawSnapshots.Current, rawSnapshots.Baseline, prepared.Changes);
            var baselineRaw = rawSnapshots.Baseline;
            var admissionPlane = timing.Measure(
                "admission-plane",
                () => EvaluateAdmissionPlane(currentRaw, baselineRaw, prepared.Changes, out planeObservations),
                static result => result is not null);
            if (admissionPlane is not null)
            {
                return admissionPlane;
            }

            var snapshots = timing.Measure(
                "snapshot-load",
                () =>
                {
                    var current = Decode(currentRaw);
                    var baseline = Decode(baselineRaw);
                    return (Current: current, Baseline: baseline);
                });
            var current = snapshots.Current;
            var baseline = snapshots.Baseline;
            var candidateLeanReport = timing.Measure(
                "lean-report-load",
                () => RawLeanReportArtifact.ReadFile(
                    options.CandidateLeanReport,
                    current));
            var verifiedScribeEmissions = timing.Measure(
                "scribe-verify",
                () => VerifyScribeForAdmission(
                    scribeEmissionVerifier,
                    current,
                    candidateLeanReport,
                    prepared.Changes));
            return WithAdmissionPlaneObservations(SnapshotAdmissionCore.Evaluate(
                current,
                baseline,
                candidateLeanReport,
                prepared.Changes,
                bootstrap,
                verifiedScribeEmissions,
                timing).Outcome, planeObservations);
        }
        catch (Exception exception)
        {
            return WithAdmissionPlaneObservations(new AdmissionOutcome.InfrastructureFailure(exception.Message), planeObservations);
        }
    }

    public CommandResult SelfTest(IReadOnlyList<string> arguments)
    {
        try
        {
            if (arguments.Count != 0)
            {
                return new CommandResult(false, string.Empty, "USAGE: StrataLint selftest\n");
            }

            var fileMap = LoadPolicy();
            var probe = new ManifestSyntax("D5", "F", "Carrier", "Probe", "G", string.Empty, "lean", string.Empty, null);
            var route = RouteEngine.Route(fileMap.Policy, probe);
            if (route is not RouteOutcome.Routed routed
                || routed.Result.Gid.Value != "D5/S0/Carrier/Probe"
                || routed.Result.Path.Value != "D5/S0/Carrier/Probe.lean")
            {
                return new CommandResult(false, string.Empty, "SELFTEST FAIL invariant mismatch\n");
            }

            var governanceFindings = SelfTestGovernancePolicy.InspectRepository(repositoryRoot);
            if (governanceFindings.Length > 0)
            {
                return new CommandResult(
                    false,
                    string.Empty,
                    string.Concat(governanceFindings.Select(static finding =>
                        $"SELFTEST FAIL governance={finding}\n")));
            }

            var rules = string.Join(",", RuleCatalog.Default.Descriptors
                .Select(static item => item.Id.Value)
                .Order(StringComparer.Ordinal));
            var deferred = string.Join(
                ",",
                RuleCatalog.Default.Descriptors
                    .Where(static item => item.Lifecycle is RuleLifecycle.Deferred)
                    .Select(static item => $"{item.Id.Value}:{item.DeferredCase?.Value}")
                    .Order(StringComparer.Ordinal));
            var output = "SELFTEST PASS\n"
                + $"CANONICAL_FILEMAP {fileMap.Policy.FileMapSha256}\n"
                + $"CANONICAL_DOMAINS {fileMap.Policy.DomainsSha256}\n"
                + "GOVERNANCE tower=pass banned-api=pass banned-symbols=pass tools-namespace=pass\n"
                + $"RULES {rules}\n"
                + $"DEFERRED {deferred}\n";
            return new CommandResult(true, output, string.Empty);
        }
        catch (Exception exception)
        {
            return new CommandResult(false, string.Empty, $"SELFTEST FAIL {exception.Message}\n");
        }
    }

    internal static VerifiedScribeEmissions? VerifyScribeForAdmission(
        IScribeEmissionVerifier? verifier,
        RepositorySnapshot snapshot,
        LeanAxiomReport report,
        RawChangeSet? changes)
    {
        if (verifier is null)
        {
            return null;
        }

        return verifier.Verify(snapshot, report, changes);
    }

    public CommandResult RenderDag(IReadOnlyList<string> arguments) =>
        DagRenderCommand.Run(repositoryRoot, repository, leanReportSource, arguments);

    public CommandResult AlignLedger(IReadOnlyList<string> arguments) =>
        DagLedgerAlignWriter.Align(repositoryRoot, repository, arguments);

    public CommandResult AppendLedger(IReadOnlyList<string> arguments) =>
        DagLedgerAppendWriter.Append(repositoryRoot, repository, arguments);

    public CommandResult RevokeLedger(IReadOnlyList<string> arguments) =>
        DagLedgerRevokeWriter.Revoke(repositoryRoot, repository, arguments);

    public CommandResult ReanchorMathlibLedger(IReadOnlyList<string> arguments) =>
        DagLedgerMathlibReanchorWriter.Reanchor(
            repositoryRoot,
            repository,
            leanReportSource,
            arguments);

    public ExplicitCommandResult TruthRelease(IReadOnlyList<string> arguments) =>
        TruthReleaseCommand.Run(repository, scribeEmissionVerifier, arguments);

    public ExplicitCommandResult TruthExport(IReadOnlyList<string> arguments) =>
        TruthExportCommand.Run(repository, arguments);

    public CommandResult CleanLanes(IReadOnlyList<string> arguments) =>
        CleanLanesCommand.Run(repositoryRoot, arguments, TimeProvider.System.GetUtcNow());

    public CommandResult Worktree(IReadOnlyList<string> arguments) =>
        WorktreeCommand.Run(repositoryRoot, arguments);

    private PolicyLoadOutcome.Accepted LoadPolicy()
    {
        var outcome = RepositoryPolicyLoader.LoadRepository(repositoryRoot);
        return outcome is PolicyLoadOutcome.Accepted accepted
            ? accepted
            : throw new InvalidOperationException(((PolicyLoadOutcome.InfrastructureFailure)outcome).Message);
    }

    private byte[] ReadRepositoryFile(string relativePath)
    {
        if (!RepoPath.TryCreate(relativePath, out var path))
        {
            throw new InvalidOperationException("manifest path must be repository-relative");
        }

        return File.ReadAllBytes(Path.Combine(repositoryRoot, path.Value));
    }

    private static byte[] ReadStandardInput()
    {
        using var memory = new MemoryStream();
        Console.OpenStandardInput().CopyTo(memory);
        return memory.ToArray();
    }

    private static CheckArguments ParseCheckArguments(IReadOnlyList<string> arguments)
    {
        string? protectedBase = null;
        string? candidateLeanReport = null;
        string? scribePaths = null;
        for (var index = 0; index < arguments.Count; index += 2)
        {
            if (index + 1 >= arguments.Count)
            {
                throw CheckUsage();
            }

            var target = arguments[index] switch
            {
                "--protected-base" when protectedBase is null => 0,
                "--candidate-lean-report" when candidateLeanReport is null => 1,
                "--scribe-paths-from" when scribePaths is null => 2,
                _ => throw CheckUsage(),
            };
            switch (target)
            {
                case 0:
                    protectedBase = arguments[index + 1];
                    break;
                case 1:
                    candidateLeanReport = arguments[index + 1];
                    break;
                case 2:
                    scribePaths = arguments[index + 1];
                    break;
            }
        }

        return new CheckArguments(protectedBase, candidateLeanReport, scribePaths);
    }

    private static InvalidOperationException CheckUsage() => new(
        "USAGE: StrataLint check [--protected-base REV] "
        + "--candidate-lean-report FILE [--scribe-paths-from FILE]");

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };

}
