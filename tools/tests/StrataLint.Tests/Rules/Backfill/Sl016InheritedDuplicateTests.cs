using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;
using Xunit.Abstractions;

namespace StrataLint.Tests;

public sealed class Sl016InheritedDuplicateTests(ITestOutputHelper output)
{
    private const string Root = "Meta/Digestion/backfill/fixture-source/";
    private const string ClosedPath = Root + "absorbed-closed/" + RuleFixture.FixtureAtomId + ".yaml";
    private const string ResidualPath = Root + "residual-open/" + RuleFixture.FixtureAtomId + ".yaml";
    private const string TargetGid = "D5/S0/Carrier/BackfillTarget";
    private const string ImplementationPath = "tools/StrataLint.Engine/Rules/Backfill/BackfillInventoryRule.cs";

    [Fact]
    public void JudgeOnlyChangeObservesUnchangedInheritedDuplicates()
    {
        var fixture = DuplicateFixture();
        fixture.Files[ImplementationPath] = "// candidate judge change\n";

        var diagnostics = Evaluate(fixture);

        Assert.DoesNotContain(diagnostics, static diagnostic => diagnostic.AdmissionEffect == AdmissionEffect.Block);
        var duplicate = Assert.Single(diagnostics, static diagnostic =>
            diagnostic.Message.StartsWith("duplicate atom_id inherited", StringComparison.Ordinal));
        Assert.Equal(AdmissionEffect.Observe, duplicate.AdmissionEffect);
    }

    [Theory]
    [InlineData("coverage")]
    [InlineData("chain")]
    [InlineData("unresolved")]
    [InlineData("fingerprint")]
    [InlineData("residual-payload")]
    [InlineData("same-count-replacement")]
    [InlineData("count-increase")]
    [InlineData("introduced")]
    [InlineData("source-metadata")]
    public void CandidateAuthoredDuplicateIsBlockedBeforeInheritedPartition(string mutation)
    {
        var fixture = DuplicateFixture();
        switch (mutation)
        {
            case "coverage":
                fixture.Files[ClosedPath] = fixture.Files[ClosedPath].Replace(
                    FrozenStatementReceiptTestData.Id('a'), FrozenStatementReceiptTestData.Id('c'), StringComparison.Ordinal);
                break;
            case "chain":
                fixture.Files[ClosedPath] = fixture.Files[ClosedPath].Replace(
                    "chain_atoms: []", "chain_atoms:\n    - " + RuleFixture.FixtureAtomId, StringComparison.Ordinal);
                break;
            case "unresolved":
                fixture.Files[ClosedPath] = fixture.Files[ClosedPath].Replace(
                    "unresolved_subitems: []", "unresolved_subitems:\n    - missing-proof", StringComparison.Ordinal);
                break;
            case "fingerprint":
                fixture.Files[ClosedPath] = fixture.Files[ClosedPath].Replace(
                    "normalized_sha256: " + RuleFixture.FixtureCasReference,
                    "normalized_sha256: " + FrozenStatementReceiptTestData.Id('c'), StringComparison.Ordinal);
                break;
            case "residual-payload":
                fixture.Files[ResidualPath] = fixture.Files[ResidualPath].Replace(
                    "unresolved_subitems: []", "unresolved_subitems:\n    - missing-proof", StringComparison.Ordinal);
                break;
            case "same-count-replacement":
                fixture.Files[RuleFixture.FixtureBackfillAtomPath] = fixture.Files[ResidualPath];
                fixture.Files.Remove(ResidualPath);
                break;
            case "count-increase":
                fixture.Files[RuleFixture.FixtureBackfillAtomPath] = fixture.Files[ResidualPath];
                break;
            case "introduced":
                fixture.Baseline.Remove(ResidualPath);
                break;
            case "source-metadata":
                fixture.Files[RuleFixture.FixtureBackfillSourcePath] = fixture.Files[RuleFixture.FixtureBackfillSourcePath]
                    .Replace("atomizer = \"none\"", "atomizer = \"generic-v1\"", StringComparison.Ordinal);
                break;
            default:
                throw new ArgumentOutOfRangeException(nameof(mutation));
        }

        var diagnostics = Evaluate(fixture);

        Assert.Contains(diagnostics, static diagnostic =>
            diagnostic.AdmissionEffect == AdmissionEffect.Block
            && diagnostic.Message == "duplicate atom_id: " + RuleFixture.FixtureAtomId);
        Assert.DoesNotContain(diagnostics, static diagnostic =>
            diagnostic.Message.Contains("inherited from baseline", StringComparison.Ordinal));
    }

    [Fact]
    public void ConflictingBaselineFingerprintIdentitiesDoNotSelectAnExemptWinner()
    {
        var fixture = DuplicateFixture();
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
            files[ResidualPath] = files[ResidualPath].Replace(
                "raw_sha256: " + RuleFixture.FixtureCasReference,
                "raw_sha256: " + FrozenStatementReceiptTestData.Id('c'), StringComparison.Ordinal);
        fixture.Files[ImplementationPath] = "// candidate judge change\n";

        var diagnostics = Evaluate(fixture);

        Assert.Contains(diagnostics, static diagnostic =>
            diagnostic.AdmissionEffect == AdmissionEffect.Block
            && diagnostic.Message == "duplicate atom_id: " + RuleFixture.FixtureAtomId);
        Assert.DoesNotContain(diagnostics, static diagnostic =>
            diagnostic.Message.Contains("inherited from baseline", StringComparison.Ordinal));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void RemovingStaleDuplicateReplaysSurvivingCoverage(bool invalidCoverage)
    {
        var fixture = DuplicateFixture();
        if (invalidCoverage)
        {
            // The bad receipt is already inherited: deletion must recheck the survivor.
            foreach (var files in new[] { fixture.Files, fixture.Baseline })
                files[ClosedPath] = files[ClosedPath].Replace(
                    FrozenStatementReceiptTestData.Id('a'), FrozenStatementReceiptTestData.Id('c'), StringComparison.Ordinal);
        }
        fixture.Files.Remove(ResidualPath);

        var diagnostics = Evaluate(fixture);

        Assert.DoesNotContain(diagnostics, static diagnostic =>
            diagnostic.Message.Contains("duplicate atom_id", StringComparison.Ordinal));
        if (invalidCoverage)
        {
            Assert.Contains(diagnostics, static diagnostic =>
                diagnostic.AdmissionEffect == AdmissionEffect.Block
                && diagnostic.Message.Contains("coverage-target-mismatch", StringComparison.Ordinal));
        }
        else
        {
            Assert.DoesNotContain(diagnostics, static diagnostic => diagnostic.AdmissionEffect == AdmissionEffect.Block);
        }
    }

    private ImmutableArray<Diagnostic> Evaluate(RuleFixture fixture)
    {
        var changes = RawChangeSet.CreateWithKinds(fixture.Files.Keys.Union(fixture.Baseline.Keys)
            .Where(path => !fixture.Files.TryGetValue(path, out var current)
                || !fixture.Baseline.TryGetValue(path, out var baseline)
                || current != baseline)
            .Select(path => (path, !fixture.Files.ContainsKey(path) ? RawChangeKind.Deleted
                : !fixture.Baseline.ContainsKey(path) ? RawChangeKind.Added : RawChangeKind.Modified)));
        var context = fixture.Build(changes);
        Assert.True(BackfillInventoryRule.IsAffectedBy(context));
        var result = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(16), context);
        Assert.Null(result.DeferredCase);
        output.WriteLine(JsonSerializer.Serialize(new
        {
            changes = changes.Entries,
            diagnostics = result.Diagnostics,
        }));
        return result.Diagnostics;
    }

    private static RuleFixture DuplicateFixture()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Baseline[TargetGid + ".lean"] = fixture.Files[TargetGid + ".lean"];
        fixture.BaselineReports[TargetGid + ".lean"] = fixture.Reports[TargetGid + ".lean"];
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            var covered = files[RuleFixture.FixtureBackfillAtomPath].Replace(
                "target_statement_id: null", "target_statement_id: " + FrozenStatementReceiptTestData.Id('a'),
                StringComparison.Ordinal);
            files.Remove(RuleFixture.FixtureBackfillAtomPath);
            files[ClosedPath] = covered;
            files[ResidualPath] = RuleFixture.FixtureBackfillAtom.Replace(
                "coverage_gids:\n  - gid: " + TargetGid + "\n    target_statement_id: null",
                "coverage_gids: []", StringComparison.Ordinal);
            FrozenStatementReceiptTestData.AddLedger(files,
                new FrozenStatementReceiptTestData.Module(TargetGid + ".lean",
                    FrozenStatementReceiptTestData.Id('a'),
                    [new FrozenStatementReceiptTestData.Declaration("protectedTargetFixture",
                        FrozenStatementReceiptTestData.Id('b'))]));
        }
        return fixture;
    }
}
