using System.Text;
using StrataLint.Engine;
using static StrataLint.Tests.UpstreamTestSupport;

namespace StrataLint.Tests;

public sealed class Sl016UpstreamIntegrationTests
{
    [Theory]
    [InlineData("missing", true)]
    [InlineData("mismatch", true)]
    [InlineData("valid", true)]
    [InlineData("missing", false)]
    public void UpstreamProbeBindingReachesCandidateRule(string value, bool affected)
    {
        var atoms = AtomContextFixture.Create("## Claim\n\nProse.\n");
        var entry = Settled(atoms.Ledger.RequireDigestionEntries().Single());
        atoms = atoms.WithEntries([entry]);
        var fixture = new RuleFixture();
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            foreach (var path in files.Keys.Where(path => path.StartsWith(BackfillInventoryLoader.RootPath, StringComparison.Ordinal)).ToArray())
                files.Remove(path);
            foreach (var file in WithCas(atoms).Entries) files[file.Path] = Encoding.UTF8.GetString(file.Bytes.AsSpan());
        }
        if (value == "missing") fixture.Files.Remove(ProbePath(entry));
        if (value == "mismatch") fixture.Files[ProbePath(entry)] = "changed";
        var context = fixture.BuildScopeProbe(RawChangeSet.Create([affected ? ProbePath(entry) : "README.md"]));
        var findings = BackfillInventoryRule.EvaluateCandidateDelta(context);
        Assert.Equal(affected && value != "valid", findings.Any(f => f.Effect == AdmissionEffect.Block
            && f.Message.Contains("BACKFILL_UPSTREAM_PROBE", StringComparison.Ordinal)));
    }
}
