using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record PreparedRepository(string Revision, string ChangeBase, RawChangeSet Changes);

internal sealed record FrozenRevisionIdentity(string Revision, string CommitOid, string TreeOid);

internal sealed record CheckArguments(
    string? ProtectedBase,
    string? CandidateLeanReport);

internal sealed class AdmissionCheckTiming(TimeProvider timeProvider, bool enabled = true)
{
    internal static AdmissionCheckTiming Disabled { get; } = new(TimeProvider.System, enabled: false);

    internal T Measure<T>(
        string stage,
        Func<T> action,
        Func<T, bool>? failed = null)
    {
        ArgumentException.ThrowIfNullOrEmpty(stage);
        ArgumentNullException.ThrowIfNull(action);
        var started = enabled ? TryGetTimestamp() : null;
        try
        {
            var result = action();
            Write(stage, failed?.Invoke(result) is true ? "failed" : "passed", started);
            return result;
        }
        catch
        {
            Write(stage, "failed", started);
            throw;
        }
    }

    private long? TryGetTimestamp()
    {
        try
        {
            return timeProvider.GetTimestamp();
        }
        catch
        {
            // Telemetry cannot change the admission decision when the clock is unavailable.
            return null;
        }
    }

    private void Write(string stage, string status, long? started)
    {
        if (!enabled)
        {
            return;
        }

        try
        {
            var elapsedSeconds = started is null
                ? 0
                : Math.Max(0, timeProvider.GetElapsedTime(started.Value).TotalSeconds);
            Console.Error.WriteLine(JsonSerializer.Serialize(new
            {
                @event = "gate_stage_timing",
                scope = "admission-check",
                stage,
                status,
                elapsed_seconds = elapsedSeconds,
            }));
        }
        catch
        {
            // The check result remains the fail-closed signal if timing output is unavailable.
        }
    }
}

internal interface IRepositoryGateway
{
    AdmissionTopologyOutcome InspectAdmissionTopology();

    PreparedRepository Prepare(string? protectedBase);

    FrozenRevisionIdentity ResolveCurrentRevision();

    RawRepositorySnapshot ReadCurrent();

    RawRepositorySnapshot ReadRevision(string revision);

    RawChangeSet ReadCurrentChanges();

    /// Reads the working-tree delta against an explicit revision, in the caller-supplied
    /// changeBase's own words -- no remote-ref resolution happens here (CLAUDE.md 第Ⅵ节 git
    /// reference discipline: only the caller may name a revision; this gateway just diffs it).
    RawChangeSet ReadChanges(string changeBase);

}

internal interface ILeanReportSource
{
    LeanAxiomReport Load(RepositorySnapshot snapshot);
}

internal interface IFrozenLedgerAdmissionServices
{
    IReadOnlySet<string> LeanReportProducerPaths { get; }

    FrozenLedgerAdmissionPreparation Prepare(
        RepositorySnapshot current,
        RepositorySnapshot protectedBase,
        RawChangeSet changes);

    AdmissionOutcome? Validate(
        FrozenLedgerAdmissionPreparation preparation,
        RepositorySnapshot current,
        AcceptedLeanClosure lean,
        LeanAxiomReport report,
        RawChangeSet changes,
        FrozenRevisionIdentity currentIdentity,
        AdmissionCheckTiming timing);
}

internal sealed class ProductionCliEnvironment : ICliEnvironment
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
    private readonly IFrozenLedgerAdmissionServices frozenLedgerAdmission;
    private readonly TimeProvider timeProvider;

    internal ProductionCliEnvironment(string repositoryRoot)
        : this(
            repositoryRoot,
            new GitRepositoryGateway(repositoryRoot),
            new PrecomputedLeanReportSource(repositoryRoot),
            new ProductionScribeEmissionVerifier(),
            new ProductionFrozenLedgerAdmissionServices(repositoryRoot))
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
            scribeEmissionVerifier: null,
            new ProductionFrozenLedgerAdmissionServices(
                repositoryRoot,
                ImmutableHashSet<string>.Empty))
    {
    }

    internal ProductionCliEnvironment(
        string repositoryRoot,
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        IScribeEmissionVerifier? scribeEmissionVerifier)
        : this(
            repositoryRoot,
            repository,
            leanReportSource,
            scribeEmissionVerifier,
            new ProductionFrozenLedgerAdmissionServices(
                repositoryRoot,
                ImmutableHashSet<string>.Empty))
    {
    }

    internal ProductionCliEnvironment(
        string repositoryRoot,
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        IScribeEmissionVerifier? scribeEmissionVerifier,
        TimeProvider timeProvider)
        : this(
            repositoryRoot,
            repository,
            leanReportSource,
            scribeEmissionVerifier,
            new ProductionFrozenLedgerAdmissionServices(
                repositoryRoot,
                ImmutableHashSet<string>.Empty),
            timeProvider)
    {
    }

    internal ProductionCliEnvironment(
        string repositoryRoot,
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        IScribeEmissionVerifier? scribeEmissionVerifier,
        IFrozenLedgerAdmissionServices frozenLedgerAdmission,
        TimeProvider? timeProvider = null)
    {
        this.repositoryRoot = Path.GetFullPath(repositoryRoot);
        this.repository = repository;
        this.leanReportSource = leanReportSource;
        this.scribeEmissionVerifier = scribeEmissionVerifier;
        this.frozenLedgerAdmission = frozenLedgerAdmission;
        this.timeProvider = timeProvider ?? TimeProvider.System;
    }

    public ExplicitCommandResult CapacityAudit(IReadOnlyList<string> arguments) =>
        CapacityAuditCommand.Run(arguments, repositoryRoot);

    public AdmissionOutcome Check(IReadOnlyList<string> arguments)
    {
        var timing = new AdmissionCheckTiming(timeProvider);
        try
        {
            var repositoryPhase = timing.Measure(
                "repository-prepare",
                () =>
                {
                    var options = ParseCheckArguments(arguments);
                    var prepared = repository.Prepare(options.ProtectedBase);
                    var hasFrozenLedgerDelta = FrozenLedgerDeltaPredicate.HasLedgerDelta(
                        prepared.Changes,
                        frozenLedgerAdmission.LeanReportProducerPaths);
                    var bootstrap = BootstrapGate.Evaluate(prepared.Changes);
                    return (
                        Options: options,
                        Prepared: prepared,
                        HasFrozenLedgerDelta: hasFrozenLedgerDelta,
                        Bootstrap: bootstrap);
                },
                static result => result.Bootstrap is BootstrapOutcome.InfrastructureFailure
                    || result.Options.CandidateLeanReport is null);
            var options = repositoryPhase.Options;
            var prepared = repositoryPhase.Prepared;
            var hasFrozenLedgerDelta = repositoryPhase.HasFrozenLedgerDelta;
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

            var snapshots = timing.Measure(
                "snapshot-load",
                () =>
                {
                    var current = Decode(repository.ReadCurrent());
                    var baseline = Decode(repository.ReadRevision(prepared.Revision));
                    // fork point 只需树,不需要 Lean report:append-only 保留性检查比的是文件字节。
                    var forkPoint = string.Equals(
                        prepared.ChangeBase,
                        prepared.Revision,
                        StringComparison.Ordinal)
                        ? baseline
                        : Decode(repository.ReadRevision(prepared.ChangeBase));
                    return (Current: current, Baseline: baseline, ForkPoint: forkPoint);
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
            var evaluation = SnapshotAdmissionCore.Evaluate(
                current,
                baseline,
                candidateLeanReport,
                prepared.Changes,
                bootstrap,
                verifiedScribeEmissions,
                snapshots.ForkPoint,
                timing);
            if (!hasFrozenLedgerDelta)
            {
                return evaluation.Outcome;
            }

            if (evaluation.Outcome is not AdmissionOutcome.Admitted
                && evaluation.Outcome is not AdmissionOutcome.ProtectedSurfaceChange)
            {
                return evaluation.Outcome;
            }

            if (evaluation.CurrentLean is null)
            {
                return new AdmissionOutcome.InfrastructureFailure(
                    "frozen-ledger delta evaluation lacks its Lean closure");
            }

            FrozenLedgerAdmissionPreparation frozenLedgerPreparation;
            FrozenRevisionIdentity currentIdentity;
            try
            {
                var frozenPreparation = timing.Measure(
                    "frozen-ledger-prepare",
                    () =>
                    {
                        var preparation = frozenLedgerAdmission.Prepare(
                            current,
                            baseline,
                            prepared.Changes);
                        var identity = DagLedgerCommandPreparation.Ask(
                            repository.ResolveCurrentRevision);
                        return (Preparation: preparation, Identity: identity);
                    });
                frozenLedgerPreparation = frozenPreparation.Preparation;
                currentIdentity = frozenPreparation.Identity;
            }
            catch (FrozenLedgerAdmissionPreparationException exception)
            {
                return MergeFrozenLedgerRejection(
                    evaluation.Outcome,
                    FrozenLedgerRuleRejection(exception.Paths, exception.Message));
            }
            catch (DagLedgerCommandPreparation.RepositoryUnavailableException exception)
            {
                return new AdmissionOutcome.InfrastructureFailure(
                    (exception.InnerException ?? exception).Message);
            }

            var serviceRejection = frozenLedgerAdmission.Validate(
                frozenLedgerPreparation,
                current,
                evaluation.CurrentLean,
                candidateLeanReport,
                prepared.Changes,
                currentIdentity,
                timing);
            if (serviceRejection is AdmissionOutcome.RuleRejected serviceRuleRejection)
            {
                return MergeFrozenLedgerRejection(evaluation.Outcome, serviceRuleRejection);
            }
            if (serviceRejection is AdmissionOutcome.InfrastructureFailure serviceInfrastructureFailure)
            {
                return serviceInfrastructureFailure;
            }

            return evaluation.Outcome;
        }
        catch (Exception exception)
        {
            return new AdmissionOutcome.InfrastructureFailure(exception.Message);
        }
    }

    private static AdmissionOutcome.RuleRejected FrozenLedgerRuleRejection(
        ImmutableArray<RepoPath> paths,
        string message) =>
        new(paths.Select(path => new Diagnostic(
            RuleId.CreateKnown(8),
            "Frozen Hearts semantics",
            DisplaySeverity.Error,
            AdmissionEffect.Block,
            path.Value,
            message)).ToImmutableArray());

    internal static AdmissionOutcome MergeFrozenLedgerRejection(
        AdmissionOutcome admission,
        AdmissionOutcome.RuleRejected frozenRejection) => admission switch
        {
            AdmissionOutcome.Admitted => frozenRejection,
            AdmissionOutcome.ProtectedSurfaceChange protectedChange =>
                new AdmissionOutcome.RuleRejected(
                    protectedChange.Sl022Diagnostics
                        .AddRange(frozenRejection.Diagnostics)
                        .ToImmutableArray()),
            AdmissionOutcome.RuleRejected rejected => new AdmissionOutcome.RuleRejected(
                rejected.Diagnostics
                    .AddRange(frozenRejection.Diagnostics)
                    .ToImmutableArray()),
            _ => throw new InvalidOperationException(
                "unknown admission outcome while merging frozen-ledger rejection"),
        };

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

    public CommandResult ShowAtom(IReadOnlyList<string> arguments) =>
        ShowAtomCommand.Run(repository, arguments);

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

    public ExplicitCommandResult GateAuthority(IReadOnlyList<string> arguments) =>
        GateAuthorityCommand.Run(repositoryRoot, arguments);

    public ExplicitCommandResult FileMapConform(IReadOnlyList<string> arguments) =>
        FileMapConformCommand.Run(arguments, repositoryRoot);

    public ExplicitCommandResult DepositHeaderCheck(IReadOnlyList<string> arguments) =>
        DepositHeaderCheckCommand.Run(repository, arguments);

    public CommandResult Ingest(IReadOnlyList<string> arguments) =>
        IngestCommand.RunReportFree(
            repositoryRoot,
            repository,
            arguments);

    public CommandResult AlignDigestionStatus(IReadOnlyList<string> arguments) =>
        scribeEmissionVerifier is null
            ? new CommandResult(
                false,
                string.Empty,
                "ALIGN_DIGESTION_STATUS_INVALID Scribe emission verifier is unavailable\n")
            : IngestCommand.Run(
                repositoryRoot,
                repository,
                leanReportSource,
                scribeEmissionVerifier,
                arguments);

    public CommandResult CoverAtom(IReadOnlyList<string> arguments) =>
        scribeEmissionVerifier is null
            ? new CommandResult(
                false,
                string.Empty,
                "COVER_INVALID Scribe emission verifier is unavailable\n")
            : CoverAtomCommand.Run(
                repositoryRoot,
                repository,
                leanReportSource,
                scribeEmissionVerifier,
                timeProvider.GetUtcNow(),
                arguments);

    public CommandResult AlignScribeReceipt(IReadOnlyList<string> arguments)
    {
        if (scribeEmissionVerifier is null)
        {
            return new CommandResult(
                false,
                string.Empty,
                "ALIGN_SCRIBE_RECEIPT_INVALID Scribe emission verifier is unavailable\n");
        }

        try
        {
            return CoverAtomCommand.AlignScribeReceipt(
                repositoryRoot,
                repository,
                leanReportSource,
                scribeEmissionVerifier,
                arguments);
        }
        catch (Exception exception)
        {
            return new CommandResult(
                false,
                string.Empty,
                $"ALIGN_SCRIBE_RECEIPT_INVALID {exception.Message}\n");
        }
    }

    public CommandResult EmitFormalizationReceipt(IReadOnlyList<string> arguments) =>
        EmitFormalizationReceiptCommand.Run(
            repositoryRoot,
            repository,
            leanReportSource,
            arguments);

    public CommandResult Route(IReadOnlyList<string> arguments)
    {
        try
        {
            if (arguments.Count != 1)
            {
                return new CommandResult(false, string.Empty, "USAGE: StrataLint route MANIFEST|-\n");
            }

            var registry = LoadRegistry();
            var manifestBytes = arguments[0] == "-"
                ? ReadStandardInput()
                : ReadRepositoryFile(arguments[0]);
            var manifestOutcome = ManifestLoader.Load(manifestBytes);
            if (manifestOutcome is ManifestLoadOutcome.InfrastructureFailure manifestFailure)
            {
                return new CommandResult(false, string.Empty, $"INFRASTRUCTURE_FAILURE {manifestFailure.Message}\n");
            }

            var manifest = ((ManifestLoadOutcome.Loaded)manifestOutcome).Syntax;
            return RouteEngine.Route(registry.Policy, manifest) switch
            {
                RouteOutcome.Routed routed => RenderRoute(registry.Policy, routed),
                RouteOutcome.Rejected rejected => new CommandResult(
                    false,
                    string.Empty,
                    $"{rejected.RuleId.Value} route: {rejected.Message}\n"),
            };
        }
        catch (Exception exception)
        {
            return new CommandResult(false, string.Empty, $"INFRASTRUCTURE_FAILURE {exception.Message}\n");
        }
    }

    private CommandResult RenderRoute(ValidatedPolicy policy, RouteOutcome.Routed routed)
    {
        var capacityFailure = routed.Result.Gid.ToTarget() switch
        {
            Target.Formal formal => RouteCapacityPreflight.Evaluate(
                repository.ReadCurrent(),
                policy,
                routed.Result.Stratum,
                formal),
            Target.Blueprint blueprint => RouteCapacityPreflight.Evaluate(
                repository.ReadCurrent(),
                policy,
                routed.Result.Stratum,
                blueprint),
            _ => null,
        };
        if (capacityFailure is not null)
        {
            return new CommandResult(false, string.Empty, $"SL-003 route: {capacityFailure}\n");
        }

        return new CommandResult(
            true,
            JsonSerializer.Serialize(
                new
                {
                    gid = routed.Result.Gid.Value,
                    path = routed.Result.Path.Value,
                    stratum = routed.Result.Stratum?.ToString(),
                    skeleton = routed.Result.Skeleton,
                },
                RouteJsonOptions) + "\n",
            string.Empty);
    }

    public CommandResult SelfTest(IReadOnlyList<string> arguments)
    {
        try
        {
            if (arguments.Count != 0)
            {
                return new CommandResult(false, string.Empty, "USAGE: StrataLint selftest\n");
            }

            var registry = LoadRegistry();
            var probe = new ManifestSyntax("D5", "F", "Carrier", "Probe", "G", string.Empty, "lean", string.Empty, null);
            var route = RouteEngine.Route(registry.Policy, probe);
            if (route is not RouteOutcome.Routed routed
                || routed.Result.Gid.Value != "D5/S0/Carrier/Probe"
                || routed.Result.Path.Value != "D5/S0/Carrier/Probe.lean"
                || RuleCatalog.Default.Descriptors.Length != 28)
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
                + $"CANONICAL_REGISTRY {registry.Policy.RegistrySha256}\n"
                + $"CANONICAL_DOMAINS {registry.Policy.DomainsSha256}\n"
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
        RawChangeSet? changes = null)
    {
        if (verifier is null)
        {
            return null;
        }

        return verifier.Verify(snapshot, report, changes);
    }

    public CommandResult RenderDag(IReadOnlyList<string> arguments) =>
        DagRenderCommand.Run(repositoryRoot, repository, leanReportSource, arguments);

    public CommandResult AppendLedger(IReadOnlyList<string> arguments) =>
        DagLedgerAppendWriter.Append(repositoryRoot, repository, arguments);

    public CommandResult RevokeLedger(IReadOnlyList<string> arguments) =>
        DagLedgerRevokeWriter.Revoke(repositoryRoot, repository, arguments);

    public ExplicitCommandResult TruthRelease(IReadOnlyList<string> arguments) =>
        TruthReleaseCommand.Run(repository, scribeEmissionVerifier, arguments);

    public ExplicitCommandResult TruthExport(IReadOnlyList<string> arguments) =>
        TruthExportCommand.Run(repository, arguments);

    public CommandResult CleanLanes(IReadOnlyList<string> arguments) =>
        CleanLanesCommand.Run(repositoryRoot, arguments, TimeProvider.System.GetUtcNow());

    public CommandResult Worktree(IReadOnlyList<string> arguments) =>
        WorktreeCommand.Run(repositoryRoot, arguments);

    private RegistryLoadOutcome.Accepted LoadRegistry()
    {
        var registryPath = Path.Combine(repositoryRoot, "Meta", "registry.yaml");
        var domainsPath = Path.Combine(repositoryRoot, "Meta", "domains.yaml");
        var outcome = RegistryLoader.Load(
            File.ReadAllBytes(registryPath),
            File.ReadAllBytes(domainsPath));
        return outcome is RegistryLoadOutcome.Accepted accepted
            ? accepted
            : throw new InvalidOperationException(((RegistryLoadOutcome.InfrastructureFailure)outcome).Message);
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
            }
        }

        return new CheckArguments(protectedBase, candidateLeanReport);
    }

    private static InvalidOperationException CheckUsage() => new(
        "USAGE: StrataLint check [--protected-base REV] "
        + "--candidate-lean-report FILE");

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };

}
