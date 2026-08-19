using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

// This assembly must reference only StrataLint (Cli) and StrataLint.Engine -- never StrataLint.Scribe
// (DependencyDirectionTests.FunctionalTestsReferenceOnlyCliAndEngine enforces the direction). The
// exported file is therefore parsed with System.Text.Json rather than TruthExportJsonReader; the
// command already round-trips its own output through the Scribe reader before renaming (PIN 3), and
// TruthExportJsonTests covers the reader/writer directly.

namespace StrataLint.Tests;

// truth-export routes the export through the REAL strict FrozenLedger.ValidateHistory, so an Engine
// regression in Revoke/Reattest/hash handling flips these assertions. The fixtures build a divergent
// ledger with the real generator (Genesis + Reattest + Revoke) and hand the same snapshot to the
// production command and to an independent strict re-validation; the two must agree on the live set.
public sealed class TruthExportCommandTests
{
    private const string Toolchain = "leanprover/lean4:v4.24.0\n";
    private const string Lakefile = "[package]\nname = \"fixture\"\n";
    private const string Manifest = "{}\n";

    [Fact]
    public void ExportEqualsStrictActiveSetDroppingRevokedAndKeepingReattested()
    {
        using var fixture = DivergentLedgerFixture();
        using var output = new TemporaryDirectory();

        var (exitCode, console) = Run(fixture, output.Path);

        Assert.Equal(0, exitCode);
        Assert.Equal(string.Empty, console.Error);
        var exportPath = Path.Combine(output.Path, "truth-export.v1.json");
        Assert.True(File.Exists(exportPath));
        var model = ParseExport(exportPath);
        Assert.Equal(nameof(TruthExportCommand), model.Producer);

        // Independent strict re-validation over the SAME ledger + the current Closed catalog.
        var expected = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateHistory(Load(fixture.LedgerBytes), fixture.FinalCatalog)).Capability.ActiveFrozenNodes;

        // Live-set equality, never a fixed count.
        Assert.Equal(
            expected.Select(static node => node.RepoPath.Value).OrderBy(static value => value, StringComparer.Ordinal),
            model.Nodes.Select(static node => node.RepoPath));
        // Revoked B is gone; reattested A and unchanged C survive.
        Assert.DoesNotContain(model.Nodes, node => node.RepoPath == PathFor("B"));
        Assert.Contains(model.Nodes, node => node.RepoPath == PathFor("A"));
        Assert.Contains(model.Nodes, node => node.RepoPath == PathFor("C"));

        // The A node carries the REATTESTED (changed) frozen node id, not the original one.
        var exportedA = model.Nodes.Single(node => node.RepoPath == PathFor("A"));
        Assert.Equal(fixture.ChangedAFrozenNodeId, exportedA.FrozenNodeId);
        Assert.NotEqual(fixture.OriginalAFrozenNodeId, exportedA.FrozenNodeId);

        // Every exported node is the strict material's faithful projection.
        foreach (var node in expected)
        {
            var exportedNode = model.Nodes.Single(item => item.FrozenNodeId == node.FrozenNodeId.Value);
            Assert.Equal(node.RepoPath.Value, exportedNode.RepoPath);
            Assert.Equal(
                node.AxiomClosure.OrderBy(static value => value, StringComparer.Ordinal),
                exportedNode.AxiomClosure);
            Assert.Equal(
                node.DeclarationStatementIds.Select(static declaration => declaration.StatementId.Value)
                    .OrderBy(static value => value, StringComparer.Ordinal),
                exportedNode.DeclarationStatementIds
                    .OrderBy(static value => value, StringComparer.Ordinal));
        }
    }

    [Fact]
    public void PendingReattestationDriftFailsClosedWithNoOutput()
    {
        // The ledger froze A at its original blob; the working tree changed A without a Reattest, so
        // the strict validator (allowPendingReattestation=false) rejects and nothing is written.
        var original = Module("A", source: "theorem a : True := by trivial\n");
        var changed = Module("A", source: "-- drifted\ntheorem a : True := by trivial\n");
        var genesisCatalog = BuildCatalog(original);
        var ledgerBytes = FrozenLedgerGenerator.GenerateGenesis(
            genesisCatalog,
            new FrozenGenesisDescriptor(GitOid('e'), Sha256("historical-rule-catalog")));
        using var fixture = FixtureFromLedger(ledgerBytes, new[] { changed });
        using var output = new TemporaryDirectory();

        var (exitCode, console) = Run(fixture, output.Path);

        Assert.Equal(2, exitCode);
        Assert.Contains("TRUTH_EXPORT_REJECTED", console.Error, StringComparison.Ordinal);
        Assert.False(File.Exists(Path.Combine(output.Path, "truth-export.v1.json")));
        Assert.Empty(Directory.EnumerateFiles(output.Path));
    }

    [Fact]
    public void ClosedModuleWithoutAFreezeFailsClosedWithNoOutput()
    {
        // A and B are Closed in the working tree but only A is frozen: requireCompleteCatalog rejects.
        var genesisCatalog = BuildCatalog(Module("A"));
        var ledgerBytes = FrozenLedgerGenerator.GenerateGenesis(
            genesisCatalog,
            new FrozenGenesisDescriptor(GitOid('e'), Sha256("historical-rule-catalog")));
        using var fixture = FixtureFromLedger(ledgerBytes, new[] { Module("A"), Module("B") });
        using var output = new TemporaryDirectory();

        var (exitCode, console) = Run(fixture, output.Path);

        Assert.Equal(2, exitCode);
        Assert.Contains("TRUTH_EXPORT_REJECTED", console.Error, StringComparison.Ordinal);
        Assert.False(File.Exists(Path.Combine(output.Path, "truth-export.v1.json")));
    }

    [Fact]
    public void MissingLeanReportFailsClosedWithNoOutput()
    {
        var genesisCatalog = BuildCatalog(Module("A"));
        var ledgerBytes = FrozenLedgerGenerator.GenerateGenesis(
            genesisCatalog,
            new FrozenGenesisDescriptor(GitOid('e'), Sha256("historical-rule-catalog")));
        using var fixture = FixtureFromLedger(ledgerBytes, new[] { Module("A") }, supplyLeanReport: false);
        using var output = new TemporaryDirectory();

        var (exitCode, console) = Run(fixture, output.Path);

        Assert.Equal(2, exitCode);
        Assert.Contains("TRUTH_EXPORT_INVALID", console.Error, StringComparison.Ordinal);
        Assert.False(File.Exists(Path.Combine(output.Path, "truth-export.v1.json")));
    }

    [Fact]
    public void SourceCommitAndTreeBindTheResolvedRevision()
    {
        var identity = new FrozenRevisionIdentity(
            new string('c', 40),
            "git-sha1:" + new string('c', 40),
            "git-sha1:" + new string('d', 40));
        using var fixture = DivergentLedgerFixture(identity);
        using var output = new TemporaryDirectory();

        var (exitCode, _) = Run(fixture, output.Path);

        Assert.Equal(0, exitCode);
        var model = ParseExport(Path.Combine(output.Path, "truth-export.v1.json"));
        Assert.Equal(new string('c', 40), model.SourceCommit);
        Assert.Equal(new string('d', 40), model.SourceTree);
    }

    [Fact]
    public void TwoRunsOnTheSameCheckoutAreByteIdentical()
    {
        using var fixture = DivergentLedgerFixture();
        using var first = new TemporaryDirectory();
        using var second = new TemporaryDirectory();

        Assert.Equal(0, Run(fixture, first.Path).ExitCode);
        Assert.Equal(0, Run(fixture, second.Path).ExitCode);

        Assert.Equal(
            File.ReadAllBytes(Path.Combine(first.Path, "truth-export.v1.json")),
            File.ReadAllBytes(Path.Combine(second.Path, "truth-export.v1.json")));
    }

    [Theory]
    [InlineData("truth-export")]
    [InlineData("truth-export", "--out")]
    [InlineData("truth-export", "--wrong", "dir")]
    public void UsageErrorsExitOneAndWriteNothing(params string[] arguments)
    {
        using var fixture = DivergentLedgerFixture();
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(arguments, fixture.Environment, console);

        Assert.Equal(1, exitCode);
        Assert.Contains("USAGE", console.Error, StringComparison.Ordinal);
    }

    private static (int ExitCode, BufferedConsole Console) Run(TruthExportFixture fixture, string outDirectory)
    {
        var console = new BufferedConsole();
        var exitCode = CliApplication.Run(
            new[] { "truth-export", "--out", outDirectory },
            fixture.Environment,
            console);
        return (exitCode, console);
    }

    // Builds Genesis(A,B,C) -> Reattest(A) -> Revoke(B). The live set is {A' (reattested), C}.
    private static TruthExportFixture DivergentLedgerFixture(FrozenRevisionIdentity? identity = null)
    {
        var originalA = Module("A", source: "theorem a : True := by trivial\n");
        var changedA = Module("A", source: "-- reattested\ntheorem a : True := by trivial\n");
        var moduleB = Module("B");
        var moduleC = Module("C");

        var genesisCatalog = BuildCatalog(originalA, moduleB, moduleC);
        var genesis = Baseline(FrozenLedgerGenerator.GenerateGenesis(
            genesisCatalog,
            new FrozenGenesisDescriptor(GitOid('e'), Sha256("historical-rule-catalog"))), genesisCatalog);

        var reattestCatalog = BuildCatalog(changedA, moduleB, moduleC);
        var reattestBytes = FrozenLedgerGenerator.AppendReattestation(genesis, reattestCatalog);
        var reattested = Baseline(reattestBytes, reattestCatalog);

        var bNode = reattested.ActiveFrozenNodes.Single(node => node.RepoPath.Value == PathFor("B"));
        var (evidence, store) = ReceiptStore(reattested, KernelFailure(bNode));
        var validated = Assert.IsType<RevocationEvidenceValidationOutcome.Accepted>(
            RevocationEvidenceValidator.Validate(evidence[0], reattested, store)).Capability;
        var plan = Assert.IsType<RevocationPlanOutcome.Accepted>(
            RevocationPlanner.Plan(reattested, new[] { validated })).Capability;
        var ledgerBytes = FrozenLedgerGenerator.AppendRevocation(reattested, plan);

        var finalCatalog = BuildCatalog(changedA, moduleC);
        var fixture = FixtureFromLedger(ledgerBytes, new[] { changedA, moduleC }, identity);
        fixture.LedgerBytes = ledgerBytes;
        fixture.FinalCatalog = finalCatalog;
        fixture.OriginalAFrozenNodeId = genesisCatalog.ClosedNodes
            .Single(node => node.RepoPath.Value == PathFor("A")).FrozenNodeId.Value;
        fixture.ChangedAFrozenNodeId = finalCatalog.ClosedNodes
            .Single(node => node.RepoPath.Value == PathFor("A")).FrozenNodeId.Value;
        return fixture;
    }

    private static TruthExportFixture FixtureFromLedger(
        ImmutableArray<byte> ledgerBytes,
        ModuleSpec[] modules,
        FrozenRevisionIdentity? identity = null,
        bool supplyLeanReport = true)
    {
        var temporary = new TemporaryDirectory();
        var files = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["lean-toolchain"] = Toolchain,
            ["lakefile.toml"] = Lakefile,
            ["lake-manifest.json"] = Manifest,
        };
        var reports = new Dictionary<string, LeanFileReport>(StringComparer.Ordinal);
        foreach (var module in modules)
        {
            files[PathFor(module.Name)] = module.Source;
            reports[PathFor(module.Name)] = ReportFor(module);
        }

        var raw = RawRepositorySnapshot.Create(
            files.Select(static pair => RawRepositoryEntry.FromText(pair.Key, pair.Value)));
        var ledgerPath = Path.Combine(
            temporary.Path,
            FrozenLedgerChangeClassifier.AcceptedRoot.Replace('/', Path.DirectorySeparatorChar));
        WriteLedgerDirectory(ledgerPath, ledgerBytes);

        var gateway = new FakeRepositoryGateway(
            RawChangeSet.Create([]),
            raw,
            null,
            frozenReferenceValidator: null,
            currentRevisionResolver: identity is null ? null : () => identity);
        var source = supplyLeanReport
            ? new FakeLeanReportSource(LeanAxiomReport.Create(reports))
            : new FakeLeanReportSource(null);
        var environment = new ProductionCliEnvironment(temporary.Path, gateway, source);
        return new TruthExportFixture(temporary, environment);
    }

    private static FrozenLedgerConsistent Baseline(ImmutableArray<byte> bytes, FrozenMaterialCatalog catalog) =>
        Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateHistory(Load(bytes), catalog)).Capability;

    private static FrozenLedgerSyntax Load(ImmutableArray<byte> bytes) =>
        Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(bytes.AsSpan())).Syntax;

    private static ParsedExport ParseExport(string path)
    {
        using var document = JsonDocument.Parse(File.ReadAllBytes(path));
        var root = document.RootElement;
        var nodes = root.GetProperty("nodes").EnumerateArray()
            .Select(static node => new ParsedExportNode(
                node.GetProperty("repo_path").GetString()!,
                node.GetProperty("frozen_node_id").GetString()!,
                node.GetProperty("node_axiom_closure").EnumerateArray()
                    .Select(static axiom => axiom.GetString()!).ToArray(),
                node.GetProperty("declarations").EnumerateArray()
                    .Select(static declaration => declaration.GetProperty("statement_id").GetString()!)
                    .ToArray()))
            .ToArray();
        return new ParsedExport(
            root.GetProperty("source_commit").GetString()!,
            root.GetProperty("source_tree").GetString()!,
            root.GetProperty("producer").GetString()!,
            nodes);
    }

    private sealed record ParsedExport(
        string SourceCommit,
        string SourceTree,
        string Producer,
        ParsedExportNode[] Nodes);

    private sealed record ParsedExportNode(
        string RepoPath,
        string FrozenNodeId,
        string[] AxiomClosure,
        string[] DeclarationStatementIds);

    private static LeanFileReport ReportFor(ModuleSpec module)
    {
        var declaration = module.Name.ToLowerInvariant();
        return new LeanFileReport(
            module.Imports.Select(static import => $"D5.S0.Carrier.{import}").ToImmutableArray(),
            ImmutableArray.Create(new LeanDeclaration(
                declaration,
                module.Kind,
                module.StatementMaterial,
                module.Axioms)
            {
                NameKey = $"ns(n0,{declaration.Length}:{declaration})",
                IncludeInStatement = true,
            }));
    }

    private static (ImmutableArray<RevocationEvidence> Evidence, TrustedRevocationReceiptStore Store) ReceiptStore(
        FrozenLedgerConsistent ledger,
        params RevocationEvidence[] provisional)
    {
        var evidence = ImmutableArray.CreateBuilder<RevocationEvidence>();
        var entries = ImmutableArray.CreateBuilder<RawRepositoryEntry>();
        var oids = ImmutableArray.CreateBuilder<string>();
        foreach (var (item, index) in provisional.Select(static (item, index) => (item, index)))
        {
            var bytes = RevocationReceiptWriter.Write(ledger, item);
            var text = Encoding.UTF8.GetString(bytes.AsSpan());
            var oid = GitBlobOid(text);
            entries.Add(new RawRepositoryEntry($"Evidence/D5/revocation-{index}.json", bytes, oid));
            oids.Add(oid);
            evidence.Add(item switch
            {
                RevocationEvidence.KernelWitnessFailure failure => failure with
                {
                    ReceiptBlobOid = oid,
                    ReceiptSha256 = Sha256(text),
                },
                _ => throw new InvalidOperationException("unexpected evidence variant"),
            });
        }

        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(RawRepositorySnapshot.Create(entries))).Snapshot;
        var store = Assert.IsType<RevocationReceiptStoreOutcome.Accepted>(
            TrustedRevocationReceiptStore.Materialize(ledger, snapshot, oids)).Capability;
        return (evidence.ToImmutable(), store);
    }

    private static RevocationEvidence KernelFailure(FrozenNodeMaterial node) =>
        new RevocationEvidence.KernelWitnessFailure(node.FrozenNodeId, node.WitnessId, string.Empty, string.Empty);

    private sealed class TruthExportFixture(TemporaryDirectory temporary, ProductionCliEnvironment environment)
        : IDisposable
    {
        internal ProductionCliEnvironment Environment { get; } = environment;

        internal ImmutableArray<byte> LedgerBytes { get; set; }

        internal FrozenMaterialCatalog FinalCatalog { get; set; } = null!;

        internal string OriginalAFrozenNodeId { get; set; } = string.Empty;

        internal string ChangedAFrozenNodeId { get; set; } = string.Empty;

        public void Dispose() => temporary.Dispose();
    }
}
