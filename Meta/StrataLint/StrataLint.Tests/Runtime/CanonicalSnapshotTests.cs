using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class CanonicalSnapshotTests
{
    [Fact]
    public void WholeRepositorySnapshotHasOneStableCanonicalFixedPoint()
    {
        var fixture = new RuleFixture();
        var context = fixture.Build();
        var policy = Assert.IsType<RegistryLoadOutcome.Accepted>(
            RegistryLoader.Load(
                Encoding.UTF8.GetBytes(TestRegistry.Canonical),
                Encoding.UTF8.GetBytes(TestRegistry.Domains))).Policy;

        var first = RepositoryCanonicalizer.Validate(context.Current, policy);
        var second = RepositoryCanonicalizer.Validate(context.Current, policy);

        var accepted = Assert.IsType<CanonicalizationOutcome.Accepted>(first);
        var acceptedAgain = Assert.IsType<CanonicalizationOutcome.Accepted>(second);
        Assert.Empty(typeof(CanonicalFixedPoint).GetConstructors());
        Assert.Equal(accepted.Capability.Bytes.ToArray(), acceptedAgain.Capability.Bytes.ToArray());
        Assert.Equal(accepted.Capability.Sha256, acceptedAgain.Capability.Sha256);
        Assert.Equal(policy.RegistrySha256, accepted.Capability.RegistrySha256);
    }

    [Fact]
    public void NoncanonicalStructuredArtifactCannotProduceCapability()
    {
        var fixture = new RuleFixture();
        fixture.Files["Evidence/D5/S0/Carrier/Result.run.json"] = "{\"omega\":2,\"alpha\":1}\n";
        var context = fixture.Build();
        var policy = Assert.IsType<RegistryLoadOutcome.Accepted>(
            RegistryLoader.Load(
                Encoding.UTF8.GetBytes(TestRegistry.Canonical),
                Encoding.UTF8.GetBytes(TestRegistry.Domains))).Policy;

        var outcome = RepositoryCanonicalizer.Validate(context.Current, policy);

        var failure = Assert.IsType<CanonicalizationOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("canonical", failure.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void YamlSubsetParserRoundTripsInlineEmptyList()
    {
        var parsed = YamlSubsetParser.Parse("sources:\n  - source_id: fresh\n    entries: []\n");
        var root = Assert.IsType<Dictionary<string, object?>>(parsed);
        var sources = Assert.IsType<List<object?>>(root["sources"]);
        var source = Assert.IsType<Dictionary<string, object?>>(sources[0]);
        var entries = Assert.IsType<List<object?>>(source["entries"]);
        Assert.Empty(entries);
    }

    [Fact]
    public void BackfillWriterRoundTripsEmptyEntriesSource()
    {
        var text = "schema_version: 3\nledger: theory-digestion-v1\nsources:\n  - source_id: fresh\n    path: docs/develop/theory/FRESH.md\n    atomizer: gict-v1\n    entries: []\nticket_index: []\n";
        var document = StrataLint.Engine.BackfillInventoryLoader.Load(text);
        var sources = document.RequireDigestionSources();
        Assert.Empty(sources[0].Entries);
    }
}
