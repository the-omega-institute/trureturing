using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class CoverAtomTests
{
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
            new FakeScribeEmissionVerifier(inputs.VerifiedEmissions));

        var result = environment.CoverAtom(
            ["--cover-atom", spec.AtomId, "--gid", inputs.Gid, "--base", "baseline",
                "--envelope", inputs.EnvelopePath]);

        Assert.True(result.Success, result.Error);
        var entry = Assert.Single(
            BackfillInventoryLoader.LoadRoot(temporary.Path).RequireDigestionEntries(),
            candidate => candidate.AtomId == spec.AtomId);
        var receipt = Assert.Single(entry.Receipts.Scribe);
        Assert.Equal(verifiedRecord.EmissionSha256, receipt.EmissionSha256);
        Assert.NotEqual(trackedEmissionSha256, receipt.EmissionSha256);
    }
}
