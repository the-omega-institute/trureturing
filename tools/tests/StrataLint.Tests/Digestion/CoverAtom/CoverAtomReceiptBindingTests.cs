using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal sealed partial record CoverSpec
{
    internal bool FreezeTargetModule { get; init; } = true;

    internal bool FrozenTargetInBaseline { get; init; } = true;

    internal string TargetStatementId { get; init; } = FrozenStatementReceiptTestData.Id('a');
}

public sealed partial class CoverAtomTests
{
    [Fact]
    public void CoverWithoutReceiptInSameDepositDeltaWritesEdgeAndSl016HasNoFinding()
    {
        var spec = new CoverSpec
        {
            FrozenTargetInBaseline = false,
        };
        var inputs = spec.Materialize();
        var currentFiles = DirectoryLedgerTestSupport.Project(inputs.Files);
        var baselineFiles = DirectoryLedgerTestSupport.Project(inputs.Baseline);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, currentFiles);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                CoverWorld.Raw(currentFiles),
                CoverWorld.Raw(baselineFiles)),
            new FakeLeanReportSource(inputs.Report),
            new FakeScribeEmissionVerifier(inputs.VerifiedEmissions),
            CoverWorld.TimeProvider);

        var result = environment.CoverAtom(
            ["--cover-atom", spec.AtomId, "--gid", inputs.Gid, "--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        var afterDocument = BackfillInventoryLoader.LoadRoot(temporary.Path);
        var entry = Assert.Single(
            afterDocument.RequireDigestionEntries(),
            candidate => candidate.AtomId == spec.AtomId);
        Assert.Equal([inputs.Gid], entry.CoverageGids.ToArray());
        Assert.Single(entry.Coverage);
        DirectoryLedgerTestSupport.ReplaceWithProjection(currentFiles, afterDocument);

        var fixture = new RuleFixture();
        Replace(fixture.Files, currentFiles);
        Replace(fixture.Baseline, baselineFiles);
        Replace(fixture.ForkPoint, baselineFiles);
        fixture.Reports.Clear();
        foreach (var report in inputs.Report.Files)
        {
            fixture.Reports.Add(report.Key.Value, report.Value);
        }

        var changes = currentFiles.Keys
            .Union(baselineFiles.Keys, StringComparer.Ordinal)
            .Where(path => !currentFiles.TryGetValue(path, out var current)
                || !baselineFiles.TryGetValue(path, out var baseline)
                || !string.Equals(current, baseline, StringComparison.Ordinal))
            .Select(path => (
                Path: path,
                Kind: !baselineFiles.ContainsKey(path)
                    ? RawChangeKind.Added
                    : !currentFiles.ContainsKey(path)
                        ? RawChangeKind.Deleted
                        : RawChangeKind.Modified));
        var context = fixture.Build(
            RawChangeSet.CreateWithKinds(changes),
            verifiedScribeEmissions: inputs.VerifiedEmissions);

        Assert.Empty(BackfillInventoryRule.EvaluateCandidateDelta(context));
    }

    [Fact]
    public void CoverCallsCurrentEdgeValidatorForGidAbsentFromCurrentReport()
    {
        var spec = new CoverSpec
        {
            ReportDeclarations = ImmutableArray.Create("unrelated"),
        };

        var execution = Execute(
            spec,
            ["--cover-atom", spec.AtomId, "--gid", spec.Gid, "--base", "baseline"]);

        Assert.False(execution.Result.Success);
        Assert.Contains("current edge GID", execution.Result.Error, StringComparison.Ordinal);
        Assert.Contains("resolves to 0 report declarations", execution.Result.Error, StringComparison.Ordinal);
        Assert.Equal(execution.Before, execution.After);
    }

    [Fact]
    public void CoverCallsCurrentEdgeValidatorForGidAmbiguousInCurrentReport()
    {
        var spec = new CoverSpec();
        var inputs = spec.Materialize();
        var reportFiles = inputs.Report.Files.ToDictionary(
            pair => pair.Key.Value,
            pair => pair.Value,
            StringComparer.Ordinal);
        var targetPath = spec.ModuleGid + ".lean";
        var targetReport = reportFiles[targetPath];
        var targetDeclaration = Assert.Single(targetReport.Declarations);
        reportFiles[targetPath] = targetReport with
        {
            Declarations =
            [
                targetDeclaration,
                targetDeclaration with { Name = "Namespace." + targetDeclaration.Name },
            ],
        };
        var ambiguousReport = LeanAxiomReport.Create(reportFiles);

        var execution = Execute(
            spec,
            ["--cover-atom", spec.AtomId, "--gid", spec.Gid, "--base", "baseline"],
            currentReport: ambiguousReport);

        Assert.False(execution.Result.Success);
        Assert.Contains("COVER_INVALID", execution.Result.Error, StringComparison.Ordinal);
        Assert.Contains("current edge GID", execution.Result.Error, StringComparison.Ordinal);
        Assert.Contains("resolves to 2 report declarations", execution.Result.Error, StringComparison.Ordinal);
        Assert.Equal(execution.Before, execution.After);
    }

    [Fact]
    public void CoverCallsCurrentEdgeValidatorForGidThatIsNotClosedInCurrentReport()
    {
        var spec = new CoverSpec
        {
            TargetAxioms = ImmutableArray.Create("sorryAx"),
        };

        var execution = Execute(
            spec,
            ["--cover-atom", spec.AtomId, "--gid", spec.Gid, "--base", "baseline"]);

        Assert.False(execution.Result.Success);
        Assert.Contains("current edge GID", execution.Result.Error, StringComparison.Ordinal);
        Assert.Contains("lean-state-open", execution.Result.Error, StringComparison.Ordinal);
        Assert.Equal(execution.Before, execution.After);
    }

    [Fact]
    public void CoverReceiptBindsTheFrozenDeclarationStatementId()
    {
        var spec = new CoverSpec
        {
            ReportDeclarations = ImmutableArray.Create("other", "probe"),
        };
        var execution = Execute(spec);

        Assert.True(execution.Result.Success, execution.Result.Error);
        var entry = Assert.Single(
            execution.AfterDocument.RequireDigestionEntries(),
            candidate => candidate.AtomId == spec.AtomId);
        var receipt = Assert.Single(entry.Coverage);
        Assert.Equal(spec.TargetStatementId, receipt.TargetStatementId);
    }

    [Fact]
    public void CoverRejectsTargetWhoseHostModuleIsNotFrozen()
    {
        var spec = new CoverSpec { FreezeTargetModule = false };
        var execution = Execute(spec);

        Assert.False(execution.Result.Success);
        Assert.Contains(spec.ModuleGid + ".lean", execution.Result.Error, StringComparison.Ordinal);
        Assert.Contains("is not frozen; run make deposit before cover", execution.Result.Error, StringComparison.Ordinal);
        Assert.Equal(execution.Before, execution.After);
    }

    [Fact]
    public void CoverAcceptsGidAlreadyBoundToAnotherAtomWithIndependentPairReceipts()
    {
        const string gid = "D5/S0/Carrier/Probe.probe";
        var execution = Execute(new CoverSpec
        {
            OtherAtomGid = gid,
            InitialDefinitionSha256 = DigestionFingerprint.Compute(
                Encoding.UTF8.GetBytes("scribe definition\n")).RawSha256,
            InitialEmissionSha256 = DigestionFingerprint.Compute(
                Encoding.UTF8.GetBytes("# emitted narrative\n")).RawSha256,
        });
        var (result, after, before) = execution;

        Assert.True(result.Success, result.Error);
        Assert.NotEqual(before, after);
        var entries = execution.AfterDocument.RequireDigestionEntries();
        var target = Assert.Single(entries, candidate => candidate.AtomId == CoverWorld.DefaultAtomId);
        var sibling = Assert.Single(entries, candidate => candidate.AtomId == CoverWorld.OtherAtomId);
        Assert.Equal([gid], target.CoverageGids.ToArray());
        Assert.Equal([gid], sibling.CoverageGids.ToArray());
        Assert.Equal([gid], target.Coverage.Select(static receipt => receipt.Gid).ToArray());
        Assert.Equal([gid], sibling.Coverage.Select(static receipt => receipt.Gid).ToArray());
        Assert.Equal([gid], target.Receipts.Scribe.Select(static receipt => receipt.Gid).ToArray());
        Assert.Equal([gid], sibling.Receipts.Scribe.Select(static receipt => receipt.Gid).ToArray());
    }

    [Fact]
    public void CoverReceiptUsesVerifiedProducerEmissionWhenTrackedProjectionDiffers()
    {
        var spec = new CoverSpec();
        var inputs = spec.Materialize();
        var currentFiles = DirectoryLedgerTestSupport.Project(inputs.Files);
        var baselineFiles = DirectoryLedgerTestSupport.Project(inputs.Baseline);
        var documentGid = ScribeEmissionAttestation.DocumentGid(inputs.Gid);
        Assert.True(inputs.VerifiedEmissions!.TryGet(documentGid, out var verifiedRecord));

        var emissionPath = ScribeEmissionAttestation.EmissionPath(documentGid);
        var trackedEmission = "# stale tracked projection\n";
        currentFiles[emissionPath] = trackedEmission;
        var trackedEmissionSha256 = DigestionFingerprint.Compute(
            Encoding.UTF8.GetBytes(trackedEmission)).RawSha256;

        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, currentFiles);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                CoverWorld.Raw(currentFiles),
                CoverWorld.Raw(baselineFiles)),
            new FakeLeanReportSource(inputs.Report),
            new FakeScribeEmissionVerifier(inputs.VerifiedEmissions),
            CoverWorld.TimeProvider);

        var result = environment.CoverAtom(
            ["--cover-atom", spec.AtomId, "--gid", inputs.Gid, "--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        var entry = Assert.Single(
            BackfillInventoryLoader.LoadRoot(temporary.Path).RequireDigestionEntries(),
            candidate => candidate.AtomId == spec.AtomId);
        var receipt = Assert.Single(entry.Receipts.Scribe);
        Assert.Equal(verifiedRecord.EmissionSha256, receipt.EmissionSha256);
        Assert.NotEqual(trackedEmissionSha256, receipt.EmissionSha256);
    }

    private static void Replace(
        IDictionary<string, string> target,
        IReadOnlyDictionary<string, string> source)
    {
        target.Clear();
        foreach (var item in source)
        {
            target.Add(item.Key, item.Value);
        }
    }
}
