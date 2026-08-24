using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void CoverAtomRejectsNewScribeEmissionGapWhenBaselineTrackedProjectionIsStale()
    {
        var materialized = CoverWorld.Materialize(new CoverSpec
        {
            OtherAtomBinding = ("receipt-gap-sibling", "D5/S0/Carrier/Probe.sibling"),
            ReportDeclarations = ImmutableArray.Create("probe", "sibling"),
        });
        var inputs = DirectoryInputs(WithNewScribeEmissionGapHiddenByBaselineProjection(materialized));
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var before = DirectoryLedgerTestSupport.Image(temporary.Path);
        var environment = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files);

        var result = environment.CoverAtom(CoverArgs(inputs));

        Assert.False(
            result.Success,
            $"new candidate Scribe gap was admitted: {result.Output}");
        Assert.Contains("scribe-emission-mismatch", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.Image(temporary.Path));
    }

    [Fact]
    public void CoverAtomRejectsNewScribeEmissionGapWhenAnIndirectScribeInputChanges()
    {
        var materialized = CoverWorld.Materialize(new CoverSpec
        {
            OtherAtomBinding = ("receipt-gap-sibling", "D5/S0/Carrier/Probe.sibling"),
            ReportDeclarations = ImmutableArray.Create("probe", "sibling"),
        });
        var inputs = DirectoryInputs(WithNewScribeEmissionGapFromIndirectInput(materialized));
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var before = DirectoryLedgerTestSupport.Image(temporary.Path);
        var environment = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files);

        var result = environment.CoverAtom(CoverArgs(inputs));

        Assert.False(
            result.Success,
            $"indirectly new candidate Scribe gap was admitted: {result.Output}");
        Assert.Contains("scribe-emission-mismatch", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.Image(temporary.Path));
    }

    private static CoverInputs WithNewScribeEmissionGapHiddenByBaselineProjection(CoverInputs inputs)
    {
        const string siblingAtomId = "receipt-gap-sibling";
        var siblingGid = inputs.Document.RequireDigestionEntries()
            .Single(entry => entry.AtomId == siblingAtomId)
            .CoverageGids.Single();
        var documentGid = ScribeEmissionAttestation.DocumentGid(siblingGid);
        Assert.True(inputs.VerifiedEmissions!.TryGet(documentGid, out var baselineVerified));
        var targetSha256 = DigestionFingerprint.Compute(
            Encoding.UTF8.GetBytes(inputs.Files[documentGid + ".lean"])).RawSha256;
        var document = inputs.Document.WithDigestionSources(
            inputs.Document.RequireDigestionSources()
                .Select(source => source with
                {
                    Entries = source.Entries.Select(entry => entry.AtomId == siblingAtomId
                        ? entry with
                        {
                            Receipts = entry.Receipts with
                            {
                                Coverage =
                                [
                                    new DigestionCoverageReceipt(
                                        siblingGid,
                                        entry.Fingerprints.RawSha256,
                                        targetSha256),
                                ],
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
        var baseline = new Dictionary<string, string>(inputs.Baseline, StringComparer.Ordinal);
        DirectoryLedgerTestSupport.ReplaceWithProjection(baseline, document);
        baseline[baselineVerified.EmissionPath] = "# stale tracked baseline projection\n";
        return inputs with
        {
            Files = files,
            Baseline = baseline,
            Document = document,
            VerifiedEmissions = candidateVerified,
        };
    }

    private static CoverInputs WithNewScribeEmissionGapFromIndirectInput(CoverInputs inputs)
    {
        const string producerPath =
            "tools/StrataLint.Scribe/Writers/CanonicalMarkdownWriter.cs";
        var changed = WithNewScribeEmissionGapHiddenByBaselineProjection(inputs);
        var files = new Dictionary<string, string>(changed.Files, StringComparer.Ordinal);
        var baseline = new Dictionary<string, string>(files, StringComparer.Ordinal);
        files[producerPath] = "// candidate Scribe producer\n";
        baseline[producerPath] = "// baseline Scribe producer\n";
        return changed with { Files = files, Baseline = baseline };
    }
}
