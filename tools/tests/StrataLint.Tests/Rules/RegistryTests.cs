using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class RegistryTests
{
    private static readonly string CanonicalRegistry = TestRegistry.Canonical;

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
        var firstAccepted = RegistryLoadAssert.Accepted(first);
        var secondAccepted = RegistryLoadAssert.Accepted(second);
        Assert.Empty(typeof(ValidatedPolicy).GetConstructors());
        Assert.Equal(raw, firstAccepted.Policy.CanonicalRegistryBytes.ToArray());
        Assert.Equal(domainRaw, firstAccepted.Policy.CanonicalDomainsBytes.ToArray());
        Assert.Equal(
            firstAccepted.Policy.CanonicalRegistryBytes.ToArray(),
            secondAccepted.Policy.CanonicalRegistryBytes.ToArray());
        Assert.Equal(firstAccepted.Policy.RegistrySha256, secondAccepted.Policy.RegistrySha256);
        Assert.Equal(firstAccepted.Policy.DomainsSha256, secondAccepted.Policy.DomainsSha256);
        Assert.Equal(4, firstAccepted.Policy.Domains.Count);
        Assert.Equal(2, firstAccepted.Policy.ArtifactKinds.Count);
    }

    [Fact]
    public void RepositoryRegistryAndDomainsRemainAcceptedByTheYamlSubset()
    {
        var registry = TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create("Meta/registry.yaml"));
        var domains = TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create("Meta/domains.yaml"));

        var outcome = RegistryLoader.Load(
            Encoding.UTF8.GetBytes(registry),
            Encoding.UTF8.GetBytes(domains));

        Assert.IsType<RegistryLoadOutcome.Accepted>(outcome);
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void RegistryCompilerDefersStoredByteCanonicalityToSnapshotWriteGate(
        bool mutateRegistry)
    {
        var registry = mutateRegistry
            ? CanonicalRegistry.Replace(
                "schema_version: 1",
                "schema_version: \"1\"",
                StringComparison.Ordinal)
            : CanonicalRegistry;
        var domains = mutateRegistry
            ? TestRegistry.Domains
            : TestRegistry.Domains.Replace(
                "stratum: S0",
                "stratum: \"S0\"",
                StringComparison.Ordinal);

        var outcome = RegistryLoader.Load(
            Encoding.UTF8.GetBytes(registry),
            Encoding.UTF8.GetBytes(domains));

        var accepted = RegistryLoadAssert.Accepted(outcome);
        Assert.Equal(
            Encoding.UTF8.GetBytes(CanonicalRegistry),
            accepted.Policy.CanonicalRegistryBytes.ToArray());
        Assert.Equal(
            Encoding.UTF8.GetBytes(TestRegistry.Domains),
            accepted.Policy.CanonicalDomainsBytes.ToArray());
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
    [InlineData("[ &carrier_anchor \"carrier definition\" ]")]
    [InlineData("[ *carrier_anchor ]")]
    [InlineData("[ !custom \"carrier definition\" ]")]
    public void RegistryRejectsYamlFeaturesInsideFlowCollections(string definition)
    {
        var domains = TestRegistry.Domains.Replace(
            "definition: The golden integer carrier.",
            $"definition: {definition}",
            StringComparison.Ordinal);

        var outcome = RegistryLoader.Load(
            Encoding.UTF8.GetBytes(CanonicalRegistry),
            Encoding.UTF8.GetBytes(domains));

        Assert.IsType<RegistryLoadOutcome.InfrastructureFailure>(outcome);
    }

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

    /// The point of RegistryLoadAssert is what a reader sees when it fails, so the failure
    /// path needs its own check: a green run never reaches the throw. Asserting only the
    /// outcome type would report "expected Accepted, got InfrastructureFailure" and drop
    /// the reason, which is the defect #993 records. This fails if the helper ever goes
    /// back to reporting the type alone.
    [Theory]
    [MemberData(nameof(InvalidDocuments))]
    public void RegistryLoadAssertCarriesTheFailureReasonNotJustTheOutcomeType(
        string document,
        string marker)
    {
        var outcome = RegistryLoader.Load(
            Encoding.UTF8.GetBytes(document),
            Encoding.UTF8.GetBytes(TestRegistry.Domains));

        var thrown = Assert.ThrowsAny<Exception>(() => RegistryLoadAssert.Accepted(outcome));

        Assert.Contains(marker, thrown.Message, StringComparison.OrdinalIgnoreCase);
    }
}
