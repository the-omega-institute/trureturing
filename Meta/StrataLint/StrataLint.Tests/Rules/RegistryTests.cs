using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class RegistryTests
{
    private const string CanonicalRegistry = TestRegistry.Canonical;

    [Fact]
    public void CanonicalRegistryProducesPrivatePolicyAndStableTwoPassBytes()
    {
        Assert.True(
            CanonicalRegistry.EndsWith('\n'),
            $"fixture must end with LF; last code point is {(int)CanonicalRegistry[^1]}");
        var raw = Encoding.UTF8.GetBytes(CanonicalRegistry);
        var domainRaw = Encoding.UTF8.GetBytes(TestRegistry.Domains);

        var first = RegistryLoader.Load(raw, domainRaw);
        var second = RegistryLoader.Load(raw, domainRaw);

        Assert.True(
            first is RegistryLoadOutcome.Accepted,
            first is RegistryLoadOutcome.InfrastructureFailure failure ? failure.Message : first.ToString());
        var firstAccepted = Assert.IsType<RegistryLoadOutcome.Accepted>(first);
        var secondAccepted = Assert.IsType<RegistryLoadOutcome.Accepted>(second);
        Assert.Empty(typeof(ValidatedPolicy).GetConstructors());
        Assert.Equal(raw, firstAccepted.Policy.CanonicalRegistryBytes.ToArray());
        Assert.Equal(domainRaw, firstAccepted.Policy.CanonicalDomainsBytes.ToArray());
        Assert.Equal(
            firstAccepted.Policy.CanonicalRegistryBytes.ToArray(),
            secondAccepted.Policy.CanonicalRegistryBytes.ToArray());
        Assert.Equal(firstAccepted.Policy.RegistrySha256, secondAccepted.Policy.RegistrySha256);
        Assert.Equal(firstAccepted.Policy.DomainsSha256, secondAccepted.Policy.DomainsSha256);
        Assert.Equal(2, firstAccepted.Policy.Domains.Count);
        Assert.Equal(2, firstAccepted.Policy.ArtifactKinds.Count);
    }

    public static TheoryData<string, string> InvalidDocuments => new()
    {
        { CanonicalRegistry.Replace("schema_version: 1", "schema_version: 2", StringComparison.Ordinal), "schema_version" },
        { CanonicalRegistry + "unknown_key: true\n", "unknown" },
        { CanonicalRegistry.Replace("schema_version: 1", "schema_version: 1\nschema_version: 1", StringComparison.Ordinal), "duplicate" },
        { CanonicalRegistry.Replace("root_files:", "root_files: &root", StringComparison.Ordinal), "anchor" },
        { CanonicalRegistry.Replace("governance_documents:\n", "governance_documents: *root\n", StringComparison.Ordinal), "alias" },
        { CanonicalRegistry.Replace("schema_version: 1", "schema_version: !custom 1", StringComparison.Ordinal), "tag" },
        { CanonicalRegistry.Replace("artifact_kinds:\n", "artifact_kinds:\n  <<: {}\n", StringComparison.Ordinal), "merge" },
        { CanonicalRegistry.Replace("profile: structured-json", "profile: structured-toml", StringComparison.Ordinal), "profile" },
    };

    [Theory]
    [MemberData(nameof(InvalidDocuments))]
    public void RegistryFailsClosedForInvalidSchemaOrYamlFeature(string document, string marker)
    {
        var outcome = RegistryLoader.Load(
            Encoding.UTF8.GetBytes(document),
            Encoding.UTF8.GetBytes(TestRegistry.Domains));

        var failure = Assert.IsType<RegistryLoadOutcome.InfrastructureFailure>(outcome);
        Assert.Contains(marker, failure.Message, StringComparison.OrdinalIgnoreCase);
    }
}
