using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    // Preserve the baseline test identity; the display name describes its current contract.
    [Fact(DisplayName = "Cover accepts Scribe byte drift when the baseline projection is stale")]
    public void CoverAtomRejectsNewScribeEmissionGapWhenBaselineTrackedProjectionIsStale()
    {
        var materialized = CoverWorld.Materialize(new CoverSpec
        {
            OtherAtomGid = "D5/S0/Carrier/Probe.sibling",
            ReportDeclarations = ImmutableArray.Create("probe", "sibling"),
        });
        var inputs = DirectoryInputs(WithNewScribeEmissionGapHiddenByBaselineProjection(materialized));
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var before = DirectoryLedgerTestSupport.Image(temporary.Path);
        var environment = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files);

        var result = environment.CoverAtom(CoverArgs(inputs));

        Assert.True(result.Success, result.Error);
        Assert.DoesNotContain("scribe-emission-mismatch", result.Error, StringComparison.Ordinal);
        Assert.NotEqual(before, DirectoryLedgerTestSupport.Image(temporary.Path));
    }

    private static CoverInputs WithNewScribeEmissionGapHiddenByBaselineProjection(CoverInputs inputs)
    {
        var siblingAtomId = CoverWorld.OtherAtomId;
        var siblingGid = inputs.Document.RequireDigestionEntries()
            .Single(entry => entry.AtomId == siblingAtomId)
            .CoverageGids.Single();
        var documentGid = ScribeEmissionAttestation.DocumentGid(siblingGid);
        Assert.True(inputs.VerifiedEmissions!.TryGet(documentGid, out var baselineVerified));
        var targetStatementId = FrozenStatementReceiptTestData.Resolve(inputs.Files, siblingGid);
        var document = inputs.Document.WithDigestionSources(
            inputs.Document.RequireDigestionSources()
                .Select(source => source with
                {
                    Entries = source.Entries.Select(entry => entry.AtomId == siblingAtomId
                        ? entry with
                        {
                            Coverage =
                            [
                                new DigestionCoverageEdge(
                                    siblingGid,
                                    targetStatementId),
                            ],
                            Receipts = entry.Receipts with
                            {
                                Scribe =
                                [
                                    new DigestionScribeReceipt(
                                        siblingGid,
                                        baselineVerified.DefinitionSha256,
                                        baselineVerified.EmissionSha256),
                                ],
                            },
                        }
                        : entry).ToImmutableArray(),
                })
                .ToImmutableArray());
        var files = new Dictionary<string, string>(inputs.Files, StringComparer.Ordinal);
        DirectoryLedgerTestSupport.ReplaceWithProjection(files, document);
        var candidateEmission = "# candidate verified emission\n";
        files[baselineVerified.EmissionPath] = candidateEmission;
        var candidateVerified = VerifiedScribeEmissions.Create(
        [
            baselineVerified with
            {
                EmissionSha256 = DigestionFingerprint.Compute(
                    Encoding.UTF8.GetBytes(candidateEmission)).RawSha256,
            },
        ],
        [inputs.Gid, siblingGid]);
        var baseline = new Dictionary<string, string>(files, StringComparer.Ordinal);
        baseline[baselineVerified.EmissionPath] = "# stale tracked baseline projection\n";
        return inputs with
        {
            Files = files,
            Baseline = baseline,
            Document = document,
            VerifiedEmissions = candidateVerified,
        };
    }
}
