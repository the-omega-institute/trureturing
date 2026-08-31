using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void IngestWarnsWithoutBlockingWhenSharedResidueIsClearedOnOnlyOneSource()
    {
        var result = RunSharedResidueIngest(clearFirst: true, clearSecond: false);

        Assert.True(result.Success, result.Error);
        Assert.Contains(
            "code=cross-volume-shared-residue-half-cleared severity=warn",
            result.Output,
            StringComparison.Ordinal);
        Assert.Contains("\"cleared_source\":\"source-a\"", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"hanging_hosts\":[\"source-b/", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void IngestDoesNotWarnWhenSharedResidueIsClearedOnEverySource()
    {
        var result = RunSharedResidueIngest(clearFirst: true, clearSecond: true);

        Assert.True(result.Success, result.Error);
        Assert.DoesNotContain(
            "cross-volume-shared-residue-half-cleared",
            result.Output,
            StringComparison.Ordinal);
    }

    [Fact]
    public void IngestDoesNotWarnWhenAnotherAtomOnTheSameSourceRetainsTheSharedResidue()
    {
        var result = RunSharedResidueIngest(
            clearFirst: true,
            clearSecond: false,
            includeSecondFirstSourceAtom: true,
            clearSecondFirstSourceAtom: false);

        Assert.True(result.Success, result.Error);
        Assert.DoesNotContain(
            "cross-volume-shared-residue-half-cleared",
            result.Output,
            StringComparison.Ordinal);
    }

    [Fact]
    public void IngestWarnsOnceWhenEveryAtomOnOneSourceClearsTheSharedResidue()
    {
        var result = RunSharedResidueIngest(
            clearFirst: true,
            clearSecond: false,
            includeSecondFirstSourceAtom: true,
            clearSecondFirstSourceAtom: true);

        Assert.True(result.Success, result.Error);
        Assert.Single(
            result.Output.Split('\n'),
            static line => line.Contains(
                "code=cross-volume-shared-residue-half-cleared",
                StringComparison.Ordinal));
    }

    private static BackfillInventoryDocument SharedResidueLedger(
        string atomizerId,
        DigestionAtom firstSourceAtom,
        DigestionAtom? secondFirstSourceAtom,
        DigestionAtom secondSourceAtom,
        bool clearFirst,
        bool clearSecond,
        bool includeSecondFirstSourceAtom,
        bool clearSecondFirstSourceAtom)
    {
        DigestionLedgerEntry Entry(
            string sourceId,
            string sourcePath,
            DigestionAtom atom,
            bool clear) => new(
                sourceId,
                sourcePath,
                atomizerId,
                AtomId(atom),
                atom.Fingerprints,
                [],
                new DigestionReceipts(
                    [],
                    [],
                    clear ? [] : ["shared-residue"],
                    [],
                    null),
                new DigestionStatus(
                    DigestionMigrationState.Residual,
                    DigestionTruthState.Open),
                atom.Fingerprints.RawSha256);

        var sourceAEntries = new List<DigestionLedgerEntry>
        {
            Entry(
                "source-a",
                RuleFixture.FixtureDigestionSourcePath,
                firstSourceAtom,
                clearFirst),
        };
        if (includeSecondFirstSourceAtom && secondFirstSourceAtom is not null)
        {
            sourceAEntries.Add(Entry(
                "source-a",
                RuleFixture.FixtureDigestionSourcePath,
                secondFirstSourceAtom,
                clearSecondFirstSourceAtom));
        }

        return BackfillInventoryDocument.Create(
        [
            new DigestionLedgerSource(
                "source-a",
                RuleFixture.FixtureDigestionSourcePath,
                atomizerId,
                [],
                GenreRegistryProjection.Available(GenreRegistryCheck.Collected([])),
                [.. sourceAEntries]),
            new DigestionLedgerSource(
                "source-b",
                "docs/CONTRIBUTING.md",
                atomizerId,
                [],
                GenreRegistryProjection.Available(GenreRegistryCheck.Collected([])),
                [Entry("source-b", "docs/CONTRIBUTING.md", secondSourceAtom, clearSecond)]),
        ],
        []);
    }

    private static CommandResult RunSharedResidueIngest(
        bool clearFirst,
        bool clearSecond,
        bool includeSecondFirstSourceAtom = false,
        bool clearSecondFirstSourceAtom = false)
    {
        var fixture = new RuleFixture();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var firstSourceText = "# Synthetic\n\n**定理 1.1(A)**。source A claim。\n"
            + (includeSecondFirstSourceAtom ? "\n**定理 1.2(B)**。source A sibling。\n" : "");
        const string secondSourceText =
            "# Synthetic\n\n**定理 1.1(A)**。source B claim。\n";
        var firstSourceAtoms = AtomizerRegistry.Atomize(
            atomizerId,
            Encoding.UTF8.GetBytes(firstSourceText),
            DigestionTestSupport.Rules).Claims;
        Assert.Equal(includeSecondFirstSourceAtom ? 2 : 1, firstSourceAtoms.Length);
        var secondSourceAtom = Assert.Single(AtomizerRegistry.Atomize(
            atomizerId,
            Encoding.UTF8.GetBytes(secondSourceText),
            DigestionTestSupport.Rules).Claims);
        var secondFirstSourceAtom = includeSecondFirstSourceAtom ? firstSourceAtoms[1] : null;
        var baselineLedger = SharedResidueLedger(
            atomizerId,
            firstSourceAtoms[0],
            secondFirstSourceAtom,
            secondSourceAtom,
            clearFirst: false,
            clearSecond: false,
            includeSecondFirstSourceAtom,
            clearSecondFirstSourceAtom: false);
        var currentLedger = SharedResidueLedger(
            atomizerId,
            firstSourceAtoms[0],
            secondFirstSourceAtom,
            secondSourceAtom,
            clearFirst,
            clearSecond,
            includeSecondFirstSourceAtom,
            clearSecondFirstSourceAtom);
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = firstSourceText;
        fixture.Files["docs/CONTRIBUTING.md"] = secondSourceText;
        fixture.Baseline[RuleFixture.FixtureDigestionSourcePath] = firstSourceText;
        fixture.Baseline["docs/CONTRIBUTING.md"] = secondSourceText;
        DirectoryLedgerTestSupport.ReplaceWithProjection(fixture.Files, currentLedger);
        DirectoryLedgerTestSupport.ReplaceWithProjection(fixture.Baseline, baselineLedger);
        fixture.Files.Remove(RuleFixture.FixtureCasPath);
        fixture.Baseline.Remove(RuleFixture.FixtureCasPath);
        foreach (var atom in firstSourceAtoms.Add(secondSourceAtom))
        {
            var captured = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
            var text = Encoding.UTF8.GetString(captured.Bytes.AsSpan());
            fixture.Files[captured.RelativePath] = text;
            fixture.Baseline[captured.RelativePath] = text;
        }
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, fixture.Files);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        return environment.AlignDigestionStatus(["--base", "baseline"]);
    }
}
