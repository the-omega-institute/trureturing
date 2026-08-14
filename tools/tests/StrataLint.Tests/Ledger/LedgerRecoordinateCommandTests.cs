using System.Collections.Immutable;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class LedgerRecoordinateCommandTests
{
    [Fact]
    public void ProductionCommandRequiresOldLeanReportBeforeReadingRepository()
    {
        using var temporary = new TemporaryDirectory();
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(RawChangeSet.Create([]), null, null),
            new FakeLeanReportSource(null));
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            [
                "ledger-recoordinate",
                "--old-environment",
                RecoordinateFixture.OldRevision,
                "--candidate-lean-report",
                "candidate.json",
            ],
            environment,
            console);

        Assert.Equal(2, exitCode);
        Assert.Contains("--old-lean-report", console.Error, StringComparison.Ordinal);
        Assert.DoesNotContain("should not be read", console.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void ProductionCommandUsesOldReportForOldAxiomClosure()
    {
        using var fixture = new RecoordinateFixture();
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(fixture.Arguments, fixture.Environment, console);

        Assert.Equal(0, exitCode);
        Assert.Contains("appended_recoordinates=1", console.Output, StringComparison.Ordinal);
        var candidateBytes = ImmutableArray.CreateRange(
            FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath));
        var syntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(candidateBytes.AsSpan())).Syntax;
        var accepted = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            FrozenLedgerTestData.ValidateCandidate(
                syntax,
                fixture.Baseline,
                fixture.CandidateCatalog)).Capability;
        var migration = Assert.IsType<FrozenLedgerEvent.EnvironmentRecoordinate>(
            accepted.Events[^1]);
        Assert.Equal("propext", Assert.Single(migration.Payload.OldAxiomClosure));
        Assert.Empty(migration.Payload.NewAxiomClosure);
        Assert.Equal("D5.S0.Carrier.OldDependency", Assert.Single(migration.Payload.OldImports));
        Assert.Equal("D5.S0.Carrier.NewDependency", Assert.Single(migration.Payload.NewImports));
    }

    [Fact]
    public void ProductionCommandWritesRecoordinateWithoutStatementDrift()
    {
        using var fixture = new RecoordinateFixture(
            candidateStatementMaterial: "old-elaborated-expression");
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(fixture.Arguments, fixture.Environment, console);

        Assert.Equal(0, exitCode);
        Assert.Contains("appended_recoordinates=1", console.Output, StringComparison.Ordinal);
        var syntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(
            FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath))).Syntax;
        var migration = Assert.IsType<FrozenLedgerEvent.EnvironmentRecoordinate>(
            Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
                FrozenLedgerTestData.ValidateCandidate(
                    syntax,
                    fixture.Baseline,
                    fixture.CandidateCatalog)).Capability.Events[^1]);
        Assert.Equal(migration.Payload.OldStatementId, migration.Payload.NewStatementId);
    }

    private sealed class RecoordinateFixture : IDisposable
    {
        internal const string OldRevision = "cccccccccccccccccccccccccccccccccccccccc";

        private const string Source = "theorem a : True := by trivial\n";
        private const string OldToolchain = "leanprover/lean4:v4.31.0\n";
        private const string NewToolchain = "leanprover/lean4:v4.33.0\n";
        private const string OldLakefile = "[package]\nname = \"old\"\n";
        private const string NewLakefile = "[package]\nname = \"new\"\n";
        private const string OldManifest = "{\"version\":\"old\"}\n";
        private const string NewManifest = "{\"version\":\"new\"}\n";

        private readonly TemporaryDirectory temporary = new();

        internal RecoordinateFixture(string candidateStatementMaterial = "new-elaborated-expression")
        {
            var oldModule = FrozenLedgerTestData.ModuleWithReport(
                "A",
                Source,
                "old-elaborated-expression",
                ["propext"]) with
            {
                Imports = ["OldDependency"],
            };
            var oldCatalog = FrozenLedgerTestData.BuildCatalogWithEnvironment(
                OldToolchain,
                OldLakefile,
                OldManifest,
                FrozenLedgerTestData.GitOid('c'),
                FrozenLedgerTestData.GitOid('b'),
                oldModule);
            BaselineBytes = FrozenLedgerGenerator.GenerateGenesis(
                oldCatalog,
                new FrozenGenesisDescriptor(
                    FrozenLedgerTestData.GitOid('e'),
                    RuleCatalog.Default.RootSha256));
            var baselineSyntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
                DagLedgerLoader.Load(BaselineBytes.AsSpan())).Syntax;
            Baseline = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
                FrozenLedgerTestData.ValidateGenesis(baselineSyntax, oldCatalog)).Capability;

            var candidateModule = FrozenLedgerTestData.ModuleWithReport(
                "A",
                Source,
                candidateStatementMaterial) with
            {
                BaseCommitOid = FrozenLedgerTestData.GitOid('a'),
                BaseTreeOid = FrozenLedgerTestData.GitOid('b'),
                Imports = ["NewDependency"],
            };
            CandidateCatalog = FrozenLedgerTestData.BuildCatalogWithEnvironment(
                NewToolchain,
                NewLakefile,
                NewManifest,
                FrozenLedgerTestData.GitOid('c'),
                FrozenLedgerTestData.GitOid('b'),
                candidateModule);

            var candidateFiles = EnvironmentFiles(
                NewToolchain,
                NewLakefile,
                NewManifest);
            FrozenLedgerTestData.AddLedgerFiles(candidateFiles, BaselineBytes);
            var candidateRaw = RawRepositorySnapshot.Create(
                candidateFiles.Select(static item => RawRepositoryEntry.FromText(item.Key, item.Value)));
            var candidateSnapshot = Decode(candidateRaw);
            var candidateReport = Report(
                candidateStatementMaterial,
                [],
                "D5.S0.Carrier.NewDependency");

            var oldFiles = EnvironmentFiles(OldToolchain, OldLakefile, OldManifest);
            var oldRaw = RawRepositorySnapshot.Create(
                oldFiles.Select(static item => RawRepositoryEntry.FromText(item.Key, item.Value)));
            var oldSnapshot = Decode(oldRaw);
            var oldReport = Report(
                "old-elaborated-expression",
                ["propext"],
                "D5.S0.Carrier.OldDependency");

            LedgerPath = Path.Combine(
                temporary.Path,
                FrozenLedgerChangeClassifier.AcceptedRoot.Replace('/', Path.DirectorySeparatorChar));
            FrozenLedgerTestData.WriteLedgerDirectory(LedgerPath, BaselineBytes);
            CandidateReportPath = Path.Combine(temporary.Path, "candidate-lean-report.json");
            OldReportPath = Path.Combine(temporary.Path, "old-lean-report.json");
            File.WriteAllBytes(
                CandidateReportPath,
                RawLeanReportArtifact.Write(candidateSnapshot, candidateReport).AsSpan());
            File.WriteAllBytes(
                OldReportPath,
                RawLeanReportArtifact.Write(oldSnapshot, oldReport).AsSpan());
            Environment = new ProductionCliEnvironment(
                temporary.Path,
                new FakeRepositoryGateway(
                    RawChangeSet.Create([]),
                    candidateRaw,
                    oldRaw,
                    references => TrustedFrozenGitReferences.CreateForTrustedAdapter(
                        references.Inputs,
                        references.EnvironmentReferences)),
                new FakeLeanReportSource(null));
        }

        internal IReadOnlyList<string> Arguments =>
        [
            "ledger-recoordinate",
            "--old-environment",
            OldRevision,
            "--old-lean-report",
            OldReportPath,
            "--candidate-lean-report",
            CandidateReportPath,
        ];

        internal FrozenLedgerConsistent Baseline { get; }

        internal ImmutableArray<byte> BaselineBytes { get; }

        internal string CandidateReportPath { get; }

        internal FrozenMaterialCatalog CandidateCatalog { get; }

        internal ProductionCliEnvironment Environment { get; }

        internal string LedgerPath { get; }

        internal string OldReportPath { get; }

        public void Dispose() => temporary.Dispose();

        private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
            Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;

        private static Dictionary<string, string> EnvironmentFiles(
            string toolchain,
            string lakefile,
            string manifest) =>
            new(StringComparer.Ordinal)
            {
                ["lean-toolchain"] = toolchain,
                ["lakefile.toml"] = lakefile,
                ["lake-manifest.json"] = manifest,
                [FrozenLedgerTestData.PathFor("A")] = Source,
            };

        private static LeanAxiomReport Report(
            string statementMaterial,
            ImmutableArray<string> axioms,
            string import) =>
            LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
            {
                [FrozenLedgerTestData.PathFor("A")] = new(
                    ImmutableArray.Create(import),
                    ImmutableArray.Create(new LeanDeclaration(
                        "a",
                        "theorem",
                        statementMaterial,
                        axioms)
                    {
                        NameKey = "ns(n0,1:a)",
                    })),
            });
    }
}
