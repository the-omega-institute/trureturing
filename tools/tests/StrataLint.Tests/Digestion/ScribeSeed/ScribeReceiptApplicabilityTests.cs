using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ScribeReceiptApplicabilityTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void QueryRendersApplicabilityObservationsWithoutReceiptDebt(bool json)
    {
        var fixture = ReceiptApplicabilityFixture.Create(waived: true);
        fixture.Baseline = fixture.Document;
        var result = DigestStatusCommand.Run(fixture.Gateway(RawChangeSet.Create(["notes/unrelated.txt"])),
            new FakeLeanReportSource(fixture.Inputs.Report), new FakeScribeEmissionVerifier(fixture.Verified),
            ["--base", "baseline", .. json ? new[] { "--json" } : []],
            FakeAtomHistorySource.ForPaths(fixture.Files.Keys), new DigestAgeClock());

        Assert.True(result.Success, result.Error);
        Assert.DoesNotContain("scribe-receipt-missing", result.Output, StringComparison.Ordinal);
        if (json)
        {
            using var document = JsonDocument.Parse(result.Output);
            var observations = document.RootElement.GetProperty("entries")[0].GetProperty("receipt_observations");
            Assert.Equal("scribe-not-applicable:mirror-waiver", observations[0].GetProperty("code").GetString());
        }
        else
            Assert.Contains($"OBSERVATION atom={fixture.First.AtomId} code=scribe-not-applicable:mirror-waiver detail=\"{ScribeSeedFixture.DeclarationGid}\"", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void WaivedTargetWithValidOptionalReceiptKeepsDeletionAndMigration()
    {
        var fixture = ReceiptApplicabilityFixture.Create(waived: true);
        ReceiptApplicabilityFixture.Receipts(fixture, 1);

        var entry = Assert.Single(ReceiptApplicabilityFixture.Evaluate(fixture).Entries);

        Assert.True(entry.Deletable);
        Assert.Equal(DigestionMigrationState.Absorbed, entry.DerivedStatus.Migration);
        Assert.Empty(entry.Gaps);
    }

    [Theory]
    [InlineData(false, 0)]
    [InlineData(false, 1)]
    [InlineData(false, 2)]
    [InlineData(true, 0)]
    [InlineData(true, 1)]
    [InlineData(true, 2)]
    public void RequiredTargetsDemandExactlyOneReceipt(bool module, int count)
    {
        var fixture = ReceiptApplicabilityFixture.Create(module: module);
        ReceiptApplicabilityFixture.Receipts(fixture, count);
        var evaluation = ReceiptApplicabilityFixture.Evaluate(fixture);

        Assert.Equal(count != 1, evaluation.HasReceiptIntegrityFailure);
        Assert.Equal(count != 1, evaluation.Findings.Any(message =>
            message.Contains("coverage-scribe-receipt-required", StringComparison.Ordinal)));
        Assert.Equal(count == 0, Assert.Single(evaluation.Entries).Gaps.Any(gap =>
            gap.Code == "scribe-receipt-missing"));
    }

    [Theory]
    [InlineData(false, "definition")]
    [InlineData(false, "emission")]
    [InlineData(true, "definition")]
    [InlineData(true, "emission")]
    public void OptionalAndRequiredReceiptsRetainIntegrityChecks(bool waived, string corrupt)
    {
        var fixture = ReceiptApplicabilityFixture.Create(waived: waived);
        ReceiptApplicabilityFixture.Receipts(fixture, 1, corrupt);

        var evaluation = ReceiptApplicabilityFixture.Evaluate(fixture);

        Assert.True(evaluation.HasReceiptIntegrityFailure);
        Assert.Contains(evaluation.ReceiptIntegrityGaps, item => item.Gap.Code == $"scribe-{corrupt}-mismatch");
    }

    [Fact]
    public void WaivedTargetWithoutBlueprintHasNoReceiptObligationAndPreservesStatus()
    {
        var fixture = ReceiptApplicabilityFixture.Create(waived: true);
        fixture.Files.Remove(ScribeEmissionAttestation.DefinitionPath(ScribeSeedFixture.ModuleGid));
        fixture.Verified = VerifiedScribeEmissions.Empty;

        var evaluation = ReceiptApplicabilityFixture.Evaluate(fixture);

        Assert.False(evaluation.HasReceiptIntegrityFailure, string.Join('\n', evaluation.Findings));
        var entry = Assert.Single(evaluation.Entries);
        Assert.Equal(fixture.First.ProjectedStatus, entry.DerivedStatus);
        Assert.DoesNotContain(entry.Gaps, gap => gap.Code.StartsWith("scribe-", StringComparison.Ordinal));
        Assert.Equal(["scribe-not-applicable:mirror-waiver"], entry.ReceiptObservations.Select(gap => gap.Code));
    }

    [Fact]
    public void RequiredMirrorWithoutBlueprintStillRequiresReceipt()
    {
        var fixture = ReceiptApplicabilityFixture.Create();
        fixture.Files.Remove(ScribeEmissionAttestation.DefinitionPath(ScribeSeedFixture.ModuleGid));
        fixture.Verified = VerifiedScribeEmissions.Empty;

        var evaluation = ReceiptApplicabilityFixture.Evaluate(fixture);

        Assert.True(evaluation.HasReceiptIntegrityFailure);
        Assert.Contains(evaluation.Findings, finding => finding.Contains("coverage-scribe-receipt-required", StringComparison.Ordinal));
        Assert.Contains(Assert.Single(evaluation.Entries).Gaps, gap => gap.Code == "scribe-definition-missing");
    }

    [Theory]
    [InlineData("empty-waiver")]
    [InlineData("malformed-header")]
    [InlineData("missing-header")]
    [InlineData("invalid-mirror")]
    [InlineData("wrong-mirror-plane")]
    [InlineData("invalid-frozen-authority")]
    public void InvalidApplicabilityAuthorityFailsClosed(string scenario)
    {
        var fixture = ReceiptApplicabilityFixture.Create();
        switch (scenario)
        {
            case "empty-waiver": ReceiptApplicabilityFixture.Header(fixture, "none(waiver: )"); break;
            case "malformed-header": fixture.Files[ScribeSeedFixture.ModuleGid + ".lean"] = "malformed\n"; break;
            case "missing-header": fixture.Files.Remove(ScribeSeedFixture.ModuleGid + ".lean"); break;
            case "invalid-mirror": ReceiptApplicabilityFixture.Header(fixture, "none"); break;
            case "wrong-mirror-plane": ReceiptApplicabilityFixture.Header(fixture, "D5/E/values--json"); break;
            case "invalid-frozen-authority":
                fixture.Files[FrozenStatePath.FromModulePath(RepoPath.CreateKnown(ScribeSeedFixture.ModuleGid + ".lean")).Value] = "{}";
                break;
        }

        var evaluation = ReceiptApplicabilityFixture.Evaluate(fixture);

        Assert.Contains(evaluation.Findings, message => message.Contains("scribe-applicability-invalid", StringComparison.Ordinal));
        Assert.DoesNotContain(Assert.Single(evaluation.Entries).ReceiptObservations, gap =>
            gap.Code.StartsWith("scribe-not-applicable", StringComparison.Ordinal) || gap.Code == "scribe-pending-target");
    }

    [Fact]
    public void NonFormalTargetIsNotApplicableAndNullTargetRemainsOpen()
    {
        var fixture = ReceiptApplicabilityFixture.Create();
        fixture.Files["Evidence/D5/values.json"] = "{}";
        fixture.Document = ScribeSeedFixture.Map(fixture.Document, entry => entry with
        { Coverage = [new DigestionCoverageEdge("D5/E/values--json", null)] });

        var evaluation = ReceiptApplicabilityFixture.Evaluate(fixture);

        Assert.False(evaluation.HasReceiptIntegrityFailure, string.Join('\n', evaluation.Findings));
        var entry = Assert.Single(evaluation.Entries);
        Assert.Equal(DigestionTruthState.Open, entry.DerivedStatus.Truth);
        Assert.DoesNotContain(entry.Gaps, gap => gap.Code.StartsWith("scribe-", StringComparison.Ordinal));
        Assert.Equal(["scribe-not-applicable:non-formal"], entry.ReceiptObservations.Select(gap => gap.Code));
    }

    [Theory]
    [InlineData("unfrozen")]
    [InlineData("absent-selector")]
    [InlineData("not-closed")]
    public void PositivelyUnresolvedTargetsArePending(string scenario)
    {
        var fixture = ReceiptApplicabilityFixture.Create();
        if (scenario == "unfrozen")
        {
            fixture.Files.Remove(FrozenStatePath.FromModulePath(RepoPath.CreateKnown(ScribeSeedFixture.ModuleGid + ".lean")).Value);
            fixture.Document = ScribeSeedFixture.Map(fixture.Document, entry => entry with
            { Coverage = [entry.Coverage[0] with { TargetStatementId = null }] });
        }
        else if (scenario == "absent-selector")
            fixture.Document = ScribeSeedFixture.Map(fixture.Document, entry => entry with
            { Coverage = [new DigestionCoverageEdge(ScribeSeedFixture.ModuleGid + ".absent", null)] });
        else
            fixture.Inputs = fixture.Inputs with { Report = LeanAxiomReport.Create(fixture.Inputs.Report.Files.ToDictionary(
                pair => pair.Key.Value, pair => pair.Value with
                { Declarations = pair.Value.Declarations.Select(declaration => declaration with { Axioms = ["sorryAx"] }).ToImmutableArray() })) };

        var evaluation = ReceiptApplicabilityFixture.Evaluate(fixture);

        Assert.False(evaluation.HasReceiptIntegrityFailure, string.Join('\n', evaluation.Findings));
        var observed = Assert.Single(evaluation.Entries);
        Assert.DoesNotContain(observed.Gaps, gap => gap.Code.StartsWith("scribe-", StringComparison.Ordinal));
        Assert.Equal(["scribe-pending-target"], observed.ReceiptObservations.Select(gap => gap.Code));
    }

    [Theory]
    [InlineData("duplicate")]
    [InlineData("extra")]
    [InlineData("reference")]
    public void WaiverDoesNotHidePresentReceiptDefects(string defect)
    {
        var fixture = ReceiptApplicabilityFixture.Create(waived: true);
        ReceiptApplicabilityFixture.Receipts(fixture, defect == "duplicate" ? 2 : 1);
        if (defect == "extra")
            fixture.Document = ScribeSeedFixture.Map(fixture.Document, entry => entry with { Coverage = [] });
        if (defect == "reference")
        {
            Assert.True(fixture.Verified.TryGet(ScribeSeedFixture.ModuleGid, out var record));
            fixture.Verified = VerifiedScribeEmissions.Create([record]);
        }

        var evaluation = ReceiptApplicabilityFixture.Evaluate(fixture);

        if (defect == "reference")
        {
            Assert.Contains(Assert.Single(evaluation.Entries).Gaps, gap => gap.Code == "scribe-declaration-reference-missing");
            Assert.Equal(DigestionMigrationState.Partial, Assert.Single(evaluation.Entries).DerivedStatus.Migration);
        }
        else
            Assert.True(evaluation.HasReceiptIntegrityFailure);
    }
}

internal static class ReceiptApplicabilityFixture
{
    internal static ScribeSeedFixture Create(bool module = false, bool waived = false)
    {
        var fixture = new ScribeSeedFixture(module: module);
        fixture.Baseline = ScribeSeedFixture.Map(fixture.Baseline, entry => entry with { Coverage = [] });
        if (waived) Header(fixture, "none(waiver:synthetic reason)");
        return fixture;
    }

    internal static void Header(ScribeSeedFixture fixture, string mirror) =>
        fixture.Files[ScribeSeedFixture.ModuleGid + ".lean"] = DigestionTestSupport.Lean(ScribeSeedFixture.ModuleGid)
            .Replace("mirror-B: none(waiver:test)", "mirror-B: " + mirror, StringComparison.Ordinal);

    internal static void Receipts(ScribeSeedFixture fixture, int count, string? corrupt = null)
    {
        Assert.True(fixture.Verified.TryGet(ScribeSeedFixture.ModuleGid, out var record));
        fixture.Document = ScribeSeedFixture.Map(fixture.Document, entry => entry with
        {
            Receipts = entry.Receipts with { Scribe = Enumerable.Repeat(new DigestionScribeReceipt(entry.Coverage[0].Gid,
                corrupt == "definition" ? "sha256:" + new string('a', 64) : record.DefinitionSha256,
                corrupt == "emission" ? "sha256:" + new string('b', 64) : record.EmissionSha256), count).ToImmutableArray() },
        });
    }

    internal static DigestionLedgerEvaluation Evaluate(ScribeSeedFixture fixture, RawChangeSet? changes = null)
    {
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(fixture.Raw(fixture.Document))).Snapshot;
        var baseline = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(fixture.Raw(fixture.Baseline))).Snapshot;
        var lean = AcceptedLeanClosure.Create(fixture.Inputs.Report);
        return DigestionStatusEvaluator.Evaluate(DigestionEvaluationScope.ChangedSet, fixture.Document, snapshot, lean,
            fixture.Verified, fixture.Baseline, validateProjectedStatus: false, baselineSnapshot: baseline,
            changes: changes ?? RawChangeSet.Create([ScribeSeedFixture.EntryPath(fixture.First)]));
    }
}
