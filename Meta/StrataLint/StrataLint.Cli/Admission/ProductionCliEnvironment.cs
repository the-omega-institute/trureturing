using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record PreparedRepository(string Revision, string ChangeBase, RawChangeSet Changes);

internal sealed record FrozenRevisionIdentity(string Revision, string CommitOid, string TreeOid);

internal sealed record CheckArguments(
    string? ProtectedBase,
    string? CandidateLeanReport,
    string? BaselineLeanReport,
    string? FrozenEvidenceRoot);

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
    private static readonly JsonSerializerOptions RouteJsonOptions = new()
    {
        WriteIndented = true,
        PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower,
    };

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

    public AdmissionOutcome Check(IReadOnlyList<string> arguments)
    {
        try
        {
            var options = ParseCheckArguments(arguments);
            var prepared = repository.Prepare(options.ProtectedBase);
            var bootstrap = BootstrapGate.Evaluate(prepared.Changes);
            if (bootstrap is BootstrapOutcome.InfrastructureFailure bootstrapFailure)
            {
                return new AdmissionOutcome.InfrastructureFailure(bootstrapFailure.Message);
            }

            if (options.CandidateLeanReport is null || options.BaselineLeanReport is null)
            {
                return new AdmissionOutcome.InfrastructureFailure(
                    "check requires --candidate-lean-report FILE and --baseline-lean-report FILE");
            }

            var current = Decode(repository.ReadCurrent());
            var baseline = Decode(repository.ReadRevision(prepared.Revision));
            // fork point 只需树,不需要 Lean report:append-only 保留性检查比的是文件字节。
            var forkPoint = string.Equals(prepared.ChangeBase, prepared.Revision, StringComparison.Ordinal)
                ? baseline
                : Decode(repository.ReadRevision(prepared.ChangeBase));
            var candidateLeanReport = RawLeanReportArtifact.ReadFile(
                options.CandidateLeanReport,
                current);
            var verifiedScribeEmissions = VerifyScribeForAdmission(
                scribeEmissionVerifier,
                candidateLeanReport,
                bootstrap);
            var evaluation = SnapshotAdmissionCore.Evaluate(
                current,
                baseline,
                candidateLeanReport,
                RawLeanReportArtifact.ReadFile(options.BaselineLeanReport, baseline),
                prepared.Changes,
                bootstrap,
                verifiedScribeEmissions,
                forkPoint);
            var admission = evaluation.Outcome;
            if (admission is not AdmissionOutcome.Admitted
                && admission is not AdmissionOutcome.ProtectedSurfaceChange)
            {
                return admission;
            }

            return admission;
        }
        catch (Exception exception)
        {
            return new AdmissionOutcome.InfrastructureFailure(exception.Message);
        }
    }

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

    public ExplicitCommandResult Papergen(IReadOnlyList<string> arguments) =>
        PapergenCommand.Run(repositoryRoot, repository, leanReportSource, arguments);

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

    public ExplicitCommandResult ValidateBlueprintPins(IReadOnlyList<string> arguments)
    {
        try
        {
            if (arguments.Count != 1)
            {
                return new ExplicitCommandResult(
                    2,
                    string.Empty,
                    "USAGE: StrataLint validate-blueprint-pins PIN_MANIFEST|-\n");
            }

            var manifestBytes = arguments[0] == "-"
                ? ReadStandardInput()
                : ReadRepositoryFile(arguments[0]);
            var loaded = BlueprintPinManifestLoader.Load(manifestBytes);
            if (loaded is BlueprintPinManifestLoadOutcome.Rejected malformed)
            {
                return new ExplicitCommandResult(
                    1,
                    $"BLUEPRINT_PINS_REJECTED manifest: {malformed.Message}\n",
                    string.Empty);
            }

            var manifest = ((BlueprintPinManifestLoadOutcome.Loaded)loaded).Manifest;
            var outcome = BlueprintPinValidator.Validate(
                LoadRegistry().Policy,
                Decode(repository.ReadCurrent()),
                manifest);
            if (outcome is BlueprintPinValidationOutcome.Rejected rejected)
            {
                return new ExplicitCommandResult(
                    1,
                    string.Concat(rejected.Diagnostics.Select(
                        static diagnostic => $"BLUEPRINT_PINS_REJECTED {diagnostic}\n")),
                    string.Empty);
            }

            var accepted = (BlueprintPinValidationOutcome.Accepted)outcome;
            var output = $"BLUEPRINT_PINS_ACCEPTED gid={accepted.TargetGid} "
                + $"generality={accepted.Generality} anchors={accepted.AnchorCount} "
                + $"imports={accepted.ImportCount}\n";
            foreach (var unverified in accepted.Unverified)
            {
                output += $"ASSUMED-UNVERIFIED {unverified}\n";
            }

            return new ExplicitCommandResult(0, output, string.Empty);
        }
        catch (Exception exception)
        {
            return new ExplicitCommandResult(
                2,
                string.Empty,
                $"BLUEPRINT_PINS_INFRASTRUCTURE {exception.Message}\n");
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

            var registry = LoadRegistry();
            var probe = new ManifestSyntax("D5", "F", "Carrier", "Probe", "G", string.Empty, "lean", string.Empty, null);
            var route = RouteEngine.Route(registry.Policy, probe);
            if (route is not RouteOutcome.Routed routed
                || routed.Result.Gid.Value != "D5/S0/Carrier/Probe"
                || routed.Result.Path.Value != "D5/S0/Carrier/Probe.lean"
                || RuleCatalog.Default.Descriptors.Length != 25)
            {
                return new CommandResult(false, string.Empty, "SELFTEST FAIL invariant mismatch\n");
            }

            var rules = string.Join(",", RuleCatalog.Default.Descriptors.Select(static item => item.Id.Value));
            var deferred = string.Join(
                ",",
                RuleCatalog.Default.Descriptors
                    .Where(static item => item.Lifecycle is RuleLifecycle.Deferred)
                    .Select(static item => $"{item.Id.Value}:{item.DeferredCase?.Value}"));
            var output = "SELFTEST PASS\n"
                + $"CANONICAL_REGISTRY {registry.Policy.RegistrySha256}\n"
                + $"CANONICAL_DOMAINS {registry.Policy.DomainsSha256}\n"
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
        LeanAxiomReport report,
        BootstrapOutcome bootstrap)
    {
        if (verifier is null)
        {
            return null;
        }

        try
        {
            return verifier.Verify(report);
        }
        catch (InvalidOperationException) when (
            bootstrap is BootstrapOutcome.ProtectedSurfaceVerificationRequired)
        {
            return null;
        }
    }

    public CommandResult RenderDag(IReadOnlyList<string> arguments) =>
        DagRenderCommand.Run(repositoryRoot, repository, leanReportSource, arguments);

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
        string? baselineLeanReport = null;
        string? frozenEvidenceRoot = null;
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
                "--baseline-lean-report" when baselineLeanReport is null => 2,
                "--frozen-evidence-root" when frozenEvidenceRoot is null => 3,
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
                    baselineLeanReport = arguments[index + 1];
                    break;
                case 3:
                    frozenEvidenceRoot = RequireDirectory(
                        arguments[index + 1],
                        "frozen evidence root");
                    break;
            }
        }

        return new CheckArguments(
            protectedBase,
            candidateLeanReport,
            baselineLeanReport,
            frozenEvidenceRoot);
    }

    private static string RequireDirectory(string path, string label)
    {
        var full = Path.GetFullPath(path);
        return Directory.Exists(full)
            ? full
            : throw new DirectoryNotFoundException($"{label} is absent: {full}");
    }

    private static InvalidOperationException CheckUsage() => new(
        "USAGE: StrataLint check [--protected-base REV] "
        + "--candidate-lean-report FILE --baseline-lean-report FILE "
        + "[--frozen-evidence-root DIR]");

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };

}
