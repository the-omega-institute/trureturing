using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record PreparedRepository(string Revision, RawChangeSet Changes);

internal sealed record FrozenRevisionIdentity(string Revision, string CommitOid, string TreeOid);

internal interface IRepositoryGateway
{
    AdmissionTopologyOutcome InspectAdmissionTopology();

    PreparedRepository Prepare(string? protectedBase);

    FrozenRevisionIdentity ResolveFrozenRevision(string revision);

    RawRepositorySnapshot ReadCurrent();

    RawRepositorySnapshot ReadRevision(string revision);

    RawRepositorySnapshot ReadFrozenRevision(string revision);

    TrustedFrozenGitReferences ValidateFrozenReferences(FrozenLedgerReferenceSet references);
}

internal interface ILeanInspector
{
    LeanAxiomReport Inspect(RepositorySnapshot snapshot);
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
    private readonly ILeanInspector leanInspector;

    internal ProductionCliEnvironment(string repositoryRoot)
        : this(
            repositoryRoot,
            new GitRepositoryGateway(repositoryRoot),
            new LeanProcessInspector(repositoryRoot))
    {
    }

    internal ProductionCliEnvironment(
        string repositoryRoot,
        IRepositoryGateway repository,
        ILeanInspector leanInspector)
    {
        this.repositoryRoot = Path.GetFullPath(repositoryRoot);
        this.repository = repository;
        this.leanInspector = leanInspector;
    }

    public AdmissionOutcome Check(IReadOnlyList<string> arguments)
    {
        try
        {
            var protectedBase = ParseCheckArguments(arguments);
            var prepared = repository.Prepare(protectedBase);
            var bootstrap = BootstrapGate.Evaluate(prepared.Changes);
            if (bootstrap is BootstrapOutcome.HumanReviewRequired review)
            {
                var descriptor = RuleCatalog.Default.Descriptors[21];
                return new AdmissionOutcome.HumanReviewRequired(
                    review.ChangeSet.Paths
                        .OrderBy(static item => item.Value, StringComparer.Ordinal)
                        .Select(path => new Diagnostic(
                            descriptor.Id,
                            descriptor.Title,
                            descriptor.DisplaySeverity,
                            descriptor.AdmissionEffect,
                            path.Value,
                            "meta change requires external human review"))
                        .ToImmutableArray());
            }

            if (bootstrap is BootstrapOutcome.InfrastructureFailure bootstrapFailure)
            {
                return new AdmissionOutcome.InfrastructureFailure(bootstrapFailure.Message);
            }

            var metaClear = ((BootstrapOutcome.Clear)bootstrap).Capability;
            var current = Decode(repository.ReadCurrent());
            var baseline = Decode(repository.ReadRevision(prepared.Revision));
            if (!current.TryGetFile("Meta/registry.yaml", out var registryFile))
            {
                return new AdmissionOutcome.InfrastructureFailure("Meta/registry.yaml is missing");
            }

            if (!current.TryGetFile("Meta/domains.yaml", out var domainsFile))
            {
                return new AdmissionOutcome.InfrastructureFailure("Meta/domains.yaml is missing");
            }

            var registryOutcome = RegistryLoader.Load(
                registryFile.RawBytes.AsSpan(),
                domainsFile.RawBytes.AsSpan());
            if (registryOutcome is RegistryLoadOutcome.InfrastructureFailure registryFailure)
            {
                return new AdmissionOutcome.InfrastructureFailure(registryFailure.Message);
            }

            var registry = (RegistryLoadOutcome.Accepted)registryOutcome;
            var lean = ValidateLean(current, leanInspector.Inspect(current));
            var dag = AcyclicTruthDag.Build(current, lean);
            if (dag is DagBuildOutcome.Rejected rejectedDag)
            {
                return RejectCycle(rejectedDag.Witness);
            }

            var baselineLean = ValidateLean(baseline, leanInspector.Inspect(baseline));
            var baselineDag = AcyclicTruthDag.Build(baseline, baselineLean);
            if (baselineDag is DagBuildOutcome.Rejected baselineRejected)
            {
                return new AdmissionOutcome.InfrastructureFailure(
                    "protected baseline truth DAG is cyclic: "
                    + string.Join(" -> ", baselineRejected.Witness.Select(static path => path.Value)));
            }

            var admission = AdmissionPipeline.Evaluate(
                current,
                baseline,
                registry.Policy,
                lean,
                baselineLean,
                prepared.Changes,
                metaClear);
            if (admission is not AdmissionOutcome.Admitted)
            {
                return admission;
            }

            return ProductionFrozenLedgerValidator.Validate(
                current,
                baseline,
                lean,
                baselineLean,
                ((DagBuildOutcome.Accepted)dag).Capability,
                ((DagBuildOutcome.Accepted)baselineDag).Capability,
                repository)
                ?? admission;
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
                RouteOutcome.Routed routed => new CommandResult(
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
                    string.Empty),
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

    public CommandResult SelfTest(IReadOnlyList<string> arguments)
    {
        try
        {
            if (arguments.Count != 0)
            {
                return new CommandResult(false, string.Empty, "USAGE: StrataLint selftest\n");
            }

            var registry = LoadRegistry();
            var probe = new ManifestSyntax("D5", "F", "Carrier", "Probe", "G", string.Empty, "lean", string.Empty);
            var route = RouteEngine.Route(registry.Policy, probe);
            if (route is not RouteOutcome.Routed routed
                || routed.Result.Gid.Value != "D5/S0/Carrier/Probe"
                || routed.Result.Path.Value != "D5/S0/Carrier/Probe.lean"
                || RuleCatalog.Default.Descriptors.Length != 22)
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

    public CommandResult GenerateLedger(IReadOnlyList<string> arguments) =>
        DagLedgerGenesisWriter.Generate(
            repositoryRoot,
            repository,
            leanInspector,
            arguments);

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

    private static string? ParseCheckArguments(IReadOnlyList<string> arguments)
    {
        if (arguments.Count == 0) return null;
        if (arguments.Count == 2 && arguments[0] is "--protected-base" or "--merge-base")
        {
            return arguments[1];
        }

        throw new InvalidOperationException("USAGE: StrataLint check [--protected-base REV]");
    }

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };

    private static AcceptedLeanClosure ValidateLean(
        RepositorySnapshot snapshot,
        LeanAxiomReport report) =>
        LeanClosureValidator.Validate(snapshot, report) switch
        {
            LeanValidationOutcome.Accepted accepted => accepted.Capability,
            LeanValidationOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };

    private static AdmissionOutcome RejectCycle(ImmutableArray<RepoPath> witness)
    {
        if (witness.Length < 2 || witness[0] != witness[^1])
        {
            throw new InvalidOperationException("Truth DAG cycle rejection did not carry a closed witness.");
        }

        var descriptor = RuleCatalog.Default.Descriptors[0];
        return new AdmissionOutcome.RuleRejected(ImmutableArray.Create(new Diagnostic(
            descriptor.Id,
            descriptor.Title,
            descriptor.DisplaySeverity,
            descriptor.AdmissionEffect,
            witness[0].Value,
            "managed import cycle: " + string.Join(" -> ", witness.Select(static path => path.Value)))));
    }

}
