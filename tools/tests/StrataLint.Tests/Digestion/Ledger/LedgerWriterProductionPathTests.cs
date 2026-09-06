using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class LedgerWriterProductionPathTests
{
    private const string AlphaGid = "D5/S0/Carrier/Alpha.alpha";
    private const string ZetaGid = "D5/S0/Carrier/Zeta.zeta";

    [Fact]
    public void CoverAtom_AppendWritesCoverageAndScribeReceiptsInOrdinalOrder()
    {
        var definition = DigestionFingerprint.Compute(
            Encoding.UTF8.GetBytes("scribe definition\n")).RawSha256;
        var emission = DigestionFingerprint.Compute(
            Encoding.UTF8.GetBytes("# emitted narrative\n")).RawSha256;
        var inputs = MaterializeSpec() with
        {
            InitialCoverage = [ZetaGid],
            InitialDefinitionSha256 = definition,
            InitialEmissionSha256 = emission,
            Migration = "absorbed",
            Truth = "closed",
            BaselineTargetIdentical = true,
        };
        var world = inputs.Materialize();
        using var repository = new TemporaryDirectory();
        var environment = Environment(repository, world, world.Document, world.Document);

        var result = environment.CoverAtom(
            ["--cover-atom", inputs.AtomId, "--gid", AlphaGid, "--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        AssertCanonicalGidBytes(ReadAtomBytes(repository, inputs.AtomId));
    }

    [Fact]
    public void DepositDelegatedMultiGidCover_WritesLedgerBytesInOrdinalOrder()
    {
        var spec = MaterializeSpec();
        var world = spec.Materialize();
        using var repository = new TemporaryDirectory();
        var environment = Environment(repository, world, world.Document, world.Document);

        // deposit delegates its coverage write to this production command. Keep
        // the command input deliberately reversed so the writer owns ordering.
        var result = environment.CoverAtom(
        [
            "--cover-atom", spec.AtomId,
            "--gid", ZetaGid,
            "--gid", AlphaGid,
            "--base", "baseline",
        ]);

        Assert.True(result.Success, result.Error);
        AssertCanonicalGidBytes(ReadAtomBytes(repository, spec.AtomId));
    }

    [Fact]
    public void AlignScribeReceipt_SeedMissingWritesScribeReceiptsInOrdinalOrder()
    {
        var spec = MaterializeSpec() with { BaselineTargetIdentical = true };
        var world = spec.Materialize();
        var target = Assert.Single(world.Document.RequireDigestionEntries());
        var seedDocument = world.Document.WithDigestionSources(
        [
            Assert.Single(world.Document.RequireDigestionSources()) with
            {
                Entries =
                [
                    target with
                    {
                        Coverage =
                        [
                            new DigestionCoverageEdge(ZetaGid, spec.TargetStatementId),
                            new DigestionCoverageEdge(
                                AlphaGid,
                                FrozenStatementReceiptTestData.Id('c')),
                        ],
                        Receipts = target.Receipts with
                        {
                            Scribe = ImmutableArray<DigestionScribeReceipt>.Empty,
                        },
                        ProjectedStatus = new DigestionStatus(
                            DigestionMigrationState.Partial,
                            DigestionTruthState.Closed),
                    },
                ],
            },
        ]);
        using var repository = new TemporaryDirectory();
        var environment = Environment(repository, world, seedDocument, seedDocument);
        var pairsPath = Path.Combine(repository.Path, "pairs.tsv");
        File.WriteAllText(
            pairsPath,
            $"{spec.AtomId}\t{ZetaGid}\n{spec.AtomId}\t{AlphaGid}\n",
            new UTF8Encoding(false));

        var result = environment.AlignScribeReceipt(
            ["--seed-missing", "--pairs", "pairs.tsv", "--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        AssertCanonicalGidBytes(ReadAtomBytes(repository, spec.AtomId));
    }

    private static CoverSpec MaterializeSpec() => new()
    {
        ModuleGid = "D5/S0/Carrier/Zeta",
        Declaration = "zeta",
        ReportDeclarations = ["zeta"],
        SecondaryTarget = ("D5/S0/Carrier/Alpha", "alpha"),
    };

    private static ProductionCliEnvironment Environment(
        TemporaryDirectory repository,
        CoverInputs world,
        BackfillInventoryDocument currentDocument,
        BackfillInventoryDocument baselineDocument)
    {
        var currentFiles = new Dictionary<string, string>(world.Files, StringComparer.Ordinal);
        var baselineFiles = new Dictionary<string, string>(world.Baseline, StringComparer.Ordinal);
        DirectoryLedgerTestSupport.ReplaceWithProjection(currentFiles, currentDocument);
        DirectoryLedgerTestSupport.ReplaceWithProjection(baselineFiles, baselineDocument);
        DirectoryLedgerTestSupport.Write(repository.Path, currentFiles);
        return new ProductionCliEnvironment(
            repository.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                CoverWorld.Raw(currentFiles),
                CoverWorld.Raw(baselineFiles)),
            new FakeLeanReportSource(world.Report),
            new FakeScribeEmissionVerifier(world.VerifiedEmissions),
            CoverWorld.TimeProvider);
    }

    private static byte[] ReadAtomBytes(TemporaryDirectory repository, string atomId)
    {
        var ledgerRoot = Path.Combine(
            repository.Path,
            BackfillInventoryLoader.RootPath.Replace('/', Path.DirectorySeparatorChar));
        var path = Assert.Single(Directory.EnumerateFiles(
            ledgerRoot,
            atomId + ".yaml",
            SearchOption.AllDirectories));
        return File.ReadAllBytes(path);
    }

    private static void AssertCanonicalGidBytes(byte[] bytes)
    {
        var text = new UTF8Encoding(false, true).GetString(bytes);
        var receipts = text.IndexOf("receipts:\n", StringComparison.Ordinal);
        var alphaCoverage = text.IndexOf($"  - gid: {AlphaGid}\n", StringComparison.Ordinal);
        var zetaCoverage = text.IndexOf($"  - gid: {ZetaGid}\n", StringComparison.Ordinal);
        var alphaScribe = text.IndexOf(
            $"    - gid: {AlphaGid}\n",
            receipts,
            StringComparison.Ordinal);
        var zetaScribe = text.IndexOf(
            $"    - gid: {ZetaGid}\n",
            receipts,
            StringComparison.Ordinal);

        Assert.True(alphaCoverage >= 0 && alphaCoverage < zetaCoverage && zetaCoverage < receipts, text);
        Assert.True(alphaScribe > receipts && alphaScribe < zetaScribe, text);
    }
}
