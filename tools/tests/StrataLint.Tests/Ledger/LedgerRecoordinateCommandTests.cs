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
        Assert.Equal(["propext"], migration.Payload.OldAxiomClosure);
        Assert.Empty(migration.Payload.NewAxiomClosure);
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

        internal RecoordinateFixture()
        {
            var oldModule = FrozenLedgerTestData.ModuleWithReport(
                "A",
                Source,
                "old-elaborated-expression",
                ["propext"]);
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
                "new-elaborated-expression") with
            {
                BaseCommitOid = FrozenLedgerTestData.GitOid('a'),
                BaseTreeOid = FrozenLedgerTestData.GitOid('b'),
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
            var candidateReport = Report("new-elaborated-expression", []);

            var oldFiles = EnvironmentFiles(OldToolchain, OldLakefile, OldManifest);
            var oldRaw = RawRepositorySnapshot.Create(
                oldFiles.Select(static item => RawRepositoryEntry.FromText(item.Key, item.Value)));
            var oldSnapshot = Decode(oldRaw);
            var oldReport = Report("old-elaborated-expression", ["propext"]);

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
            ImmutableArray<string> axioms) =>
            LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
            {
                [FrozenLedgerTestData.PathFor("A")] = new(
                    ImmutableArray<string>.Empty,
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
