using System.Text;
using StrataLint.Configuration;
using StrataLint.TestSupport;
using Xunit;
using StrataLint.Engine;

namespace StrataLint.Configuration.Tests;

public sealed class RepositoryPolicyLoaderTests
{
    private static readonly string CanonicalFileMap = TestFileMap.Canonical;

    [Fact]
    public void CanonicalFileMapProducesPrivatePolicyAndStableTwoPassBytes()
    {
        Assert.True(
            CanonicalFileMap.EndsWith('\n'),
            $"fixture must end with LF; last code point is {(int)CanonicalFileMap[^1]}");
        var raw = Encoding.UTF8.GetBytes(CanonicalFileMap);
        var domainRaw = Encoding.UTF8.GetBytes(TestFileMap.Domains);

        var first = RepositoryPolicyLoader.Load(raw, domainRaw);
        var second = RepositoryPolicyLoader.Load(raw, domainRaw);

        Assert.True(
            first is PolicyLoadOutcome.Accepted,
            first is PolicyLoadOutcome.InfrastructureFailure failure ? failure.Message : first.ToString());
        var firstAccepted = PolicyLoadAssert.Accepted(first);
        var secondAccepted = PolicyLoadAssert.Accepted(second);
        Assert.Empty(typeof(ValidatedPolicy).GetConstructors());
        Assert.Equal(raw, firstAccepted.Policy.CanonicalFileMapBytes.ToArray());
        Assert.Equal(domainRaw, firstAccepted.Policy.CanonicalDomainsBytes.ToArray());
        Assert.Equal(
            firstAccepted.Policy.CanonicalFileMapBytes.ToArray(),
            secondAccepted.Policy.CanonicalFileMapBytes.ToArray());
        Assert.Equal(firstAccepted.Policy.FileMapSha256, secondAccepted.Policy.FileMapSha256);
        Assert.Equal(firstAccepted.Policy.DomainsSha256, secondAccepted.Policy.DomainsSha256);
        Assert.Equal(4, firstAccepted.Policy.Domains.Count);
        Assert.Equal(7, firstAccepted.Policy.ArtifactKinds.Count);
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void PolicyLoaderNormalizesAcceptedFileMapAndDomainSpellings(
        bool mutateFileMap)
    {
        var fileMap = mutateFileMap
            ? CanonicalFileMap.Replace(
                "schema_version = 5",
                "schema_version = 0x5",
                StringComparison.Ordinal)
            : CanonicalFileMap;
        var domains = mutateFileMap
            ? TestFileMap.Domains
            : TestFileMap.Domains.Replace(
                "stratum: S0",
                "stratum: \"S0\"",
                StringComparison.Ordinal);

        var outcome = RepositoryPolicyLoader.Load(
            Encoding.UTF8.GetBytes(fileMap),
            Encoding.UTF8.GetBytes(domains));

        var accepted = PolicyLoadAssert.Accepted(outcome);
        Assert.Equal(
            Encoding.UTF8.GetBytes(CanonicalFileMap),
            accepted.Policy.CanonicalFileMapBytes.ToArray());
        Assert.Equal(
            Encoding.UTF8.GetBytes(TestFileMap.Domains),
            accepted.Policy.CanonicalDomainsBytes.ToArray());
    }

    public static TheoryData<string, string, string> InvalidDocuments => new()
    {
        { CanonicalFileMap.Replace("schema_version = 5", "schema_version = 4", StringComparison.Ordinal), TestFileMap.Domains, "schema_version" },
        { "unknown_key = true\n" + CanonicalFileMap, TestFileMap.Domains, "unknown" },
        { CanonicalFileMap, TestFileMap.Domains + "domains: {}\n", "duplicate" },
        { CanonicalFileMap, TestFileMap.Domains.Replace("domains:", "domains: &root", StringComparison.Ordinal), "anchor" },
        { CanonicalFileMap, "domains: *root\n", "alias" },
        { CanonicalFileMap, TestFileMap.Domains.Replace("stratum: S0", "stratum: !custom S0", StringComparison.Ordinal), "tag" },
        { CanonicalFileMap, TestFileMap.Domains.Replace("domains:\n", "domains:\n  <<: {}\n", StringComparison.Ordinal), "merge" },
        { CanonicalFileMap.Replace("profile = \"structured-json\"", "profile = \"structured-toml\"", StringComparison.Ordinal), TestFileMap.Domains, "profile" },
    };

    [Theory]
    [MemberData(nameof(InvalidDocuments))]
    public void PolicyLoaderFailsClosedForInvalidSchemaOrDomainYamlFeature(
        string fileMap,
        string domains,
        string marker)
    {
        var outcome = RepositoryPolicyLoader.Load(
            Encoding.UTF8.GetBytes(fileMap),
            Encoding.UTF8.GetBytes(domains));

        var failure = Assert.IsType<PolicyLoadOutcome.InfrastructureFailure>(outcome);
        Assert.Contains(marker, failure.Message, StringComparison.OrdinalIgnoreCase);
    }

    /// The point of PolicyLoadAssert is what a reader sees when it fails, so the failure
    /// path needs its own check: a green run never reaches the throw. Asserting only the
    /// outcome type would report "expected Accepted, got InfrastructureFailure" and drop
    /// the reason, which is the defect #993 records. This fails if the helper ever goes
    /// back to reporting the type alone.
    [Theory]
    [MemberData(nameof(InvalidDocuments))]
    public void PolicyLoadAssertCarriesTheFailureReasonNotJustTheOutcomeType(
        string fileMap,
        string domains,
        string marker)
    {
        var outcome = RepositoryPolicyLoader.Load(
            Encoding.UTF8.GetBytes(fileMap),
            Encoding.UTF8.GetBytes(domains));

        var thrown = Assert.ThrowsAny<Exception>(() => PolicyLoadAssert.Accepted(outcome));

        Assert.Contains(marker, thrown.Message, StringComparison.OrdinalIgnoreCase);
    }
}
