using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    private const string CanonicalScribeInputPath =
        "tools/scripts/report/report-supervisor.sh";

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
    public void CoverAtomRejectsScribeBacklogWhenReceiptChanges()
    {
        AssertScribeBacklogRejected(WithCandidateScribeReceiptChanged(ScribeBacklogInputs()));
    }

    [Fact]
    public void CoverAtomRejectsScribeBacklogWhenBaselineEntryFingerprintDiffers()
    {
        AssertScribeBacklogRejected(WithBaselineEntryFingerprintChanged(ScribeBacklogInputs()));
    }

    [Fact]
    public void CoverAtomRejectsScribeBacklogWhenDefinitionChanges()
    {
        AssertScribeBacklogRejected(WithBaselineFileChanged(
            ScribeBacklogInputs(),
            static (inputs, gid) => ScribeEmissionAttestation.DefinitionPath(
                ScribeEmissionAttestation.DocumentGid(gid)),
            "// baseline definition\n"));
    }

    [Fact]
    public void CoverAtomRejectsScribeBacklogWhenLeanTargetChanges()
    {
        AssertScribeBacklogRejected(WithBaselineFileChanged(
            ScribeBacklogInputs(),
            static (_, gid) => GidPath(gid),
            "-- baseline Lean target\n"));
    }

    [Fact]
    public void CoverAtomRejectsScribeBacklogWhenCanonicalClosureInputChanges()
    {
        var inputs = ScribeBacklogInputs();
        var files = new Dictionary<string, string>(inputs.Files, StringComparer.Ordinal)
        {
            [CanonicalScribeInputPath] = "candidate canonical Scribe input\n",
        };
        var baseline = new Dictionary<string, string>(inputs.Baseline, StringComparer.Ordinal)
        {
            [CanonicalScribeInputPath] = "baseline canonical Scribe input\n",
        };
        AssertScribeBacklogRejected(inputs with { Files = files, Baseline = baseline });
    }

    private static void AssertScribeBacklogRejected(CoverInputs inputs)
    {
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var before = DirectoryLedgerTestSupport.Image(temporary.Path);
        var environment = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files);

        var result = environment.CoverAtom(CoverArgs(inputs));

        Assert.False(
            result.Success,
            $"touched Scribe backlog was admitted: {result.Output}");
        Assert.Contains("scribe-emission-mismatch", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.Image(temporary.Path));
    }

    private static CoverInputs ScribeBacklogInputs()
    {
        var materialized = CoverWorld.Materialize(new CoverSpec
        {
            OtherAtomBinding = ("receipt-gap-sibling", "D5/S0/Carrier/Probe.sibling"),
            ReportDeclarations = ImmutableArray.Create("probe", "sibling"),
        });
        return DirectoryInputs(WithReceiptMismatchAtForkPoint(
            materialized,
            "scribe-emission-mismatch",
            byteIdenticalBaseline: true));
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

    private static CoverInputs WithCandidateScribeReceiptChanged(CoverInputs inputs)
    {
        const string siblingAtomId = "receipt-gap-sibling";
        var document = inputs.Document.WithDigestionSources(
            inputs.Document.RequireDigestionSources()
                .Select(source => source with
                {
                    Entries = source.Entries.Select(entry => entry.AtomId == siblingAtomId
                        ? entry with
                        {
                            Receipts = entry.Receipts with
                            {
                                Scribe = entry.Receipts.Scribe.Select(static receipt => receipt with
                                {
                                    EmissionSha256 = "sha256:" + new string('d', 64),
                                }).ToImmutableArray(),
                            },
                        }
                        : entry).ToImmutableArray(),
                })
                .ToImmutableArray());
        var files = new Dictionary<string, string>(inputs.Files, StringComparer.Ordinal);
        DirectoryLedgerTestSupport.ReplaceWithProjection(files, document);
        return inputs with { Files = files, Document = document };
    }

    private static CoverInputs WithBaselineEntryFingerprintChanged(CoverInputs inputs)
    {
        const string siblingAtomId = "receipt-gap-sibling";
        var changed = inputs.Document.WithDigestionSources(
            inputs.Document.RequireDigestionSources()
                .Select(source => source with
                {
                    Entries = source.Entries.Select(entry => entry.AtomId == siblingAtomId
                        ? entry with
                        {
                            Fingerprints = new DigestionFingerprints(
                                "sha256:" + new string('d', 64),
                                "sha256:" + new string('e', 64)),
                        }
                        : entry).ToImmutableArray(),
                })
                .ToImmutableArray());
        var baseline = new Dictionary<string, string>(inputs.Baseline, StringComparer.Ordinal);
        DirectoryLedgerTestSupport.ReplaceWithProjection(baseline, changed);
        return inputs with { Baseline = baseline };
    }

    private static CoverInputs WithBaselineFileChanged(
        CoverInputs inputs,
        Func<CoverInputs, string, string> path,
        string content)
    {
        var siblingGid = inputs.Document.RequireDigestionEntries()
            .Single(entry => entry.AtomId == "receipt-gap-sibling")
            .CoverageGids.Single();
        var baseline = new Dictionary<string, string>(inputs.Baseline, StringComparer.Ordinal)
        {
            [path(inputs, siblingGid)] = content,
        };
        return inputs with { Baseline = baseline };
    }

    private static string GidPath(string gid)
    {
        Assert.True(Gid.TryParse(gid, out var parsed));
        return parsed.Path.Value;
    }
}
