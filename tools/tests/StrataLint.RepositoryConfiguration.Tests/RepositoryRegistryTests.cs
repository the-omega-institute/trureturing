using System.Collections.Immutable;
using StrataLint.Configuration;
using StrataLint.Engine;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.RepositoryConfiguration.Tests;

public sealed class RepositoryRegistryTests
{
    [Theory]
    [InlineData("Meta/judge-seed.json")]
    [InlineData("Meta/package-materials.json")]
    public void RealRepositoryMetadataRegistrationsAreAdmissible(string value)
    {
        var path = RepoPath.CreateKnown(value);
        var policy = RealRepositoryPolicy();

        Assert.Null(RepositoryPathPolicy.Validate(path, policy));
        Assert.Contains(path, policy.GovernanceDocuments);
        Assert.False(RepositoryPathPolicy.TryResolve(path, out _));
    }

    [Theory]
    [InlineData("Meta/unregistered.json")]
    [InlineData("Meta/judge-seed-extra.json")]
    [InlineData("Meta/package-materials-extra.json")]
    public void RealRepositoryMetadataRegistrationRejectsUnregisteredNeighbors(string value)
    {
        var path = RepoPath.CreateKnown(value);
        var policy = RealRepositoryPolicy();

        var issue = Assert.IsType<RepositoryPathIssue>(RepositoryPathPolicy.Validate(path, policy));

        Assert.Equal("SL-000", issue.RuleId.Value);
        Assert.Equal(value, issue.Path);
        Assert.Equal("unknown Meta artifact", issue.Message);
        Assert.DoesNotContain(path, policy.GovernanceDocuments);
    }

    private static ValidatedPolicy RealRepositoryPolicy()
    {
        var root = TestRepositoryLayout.FindRoot();
        return RegistryLoadAssert.Accepted(RegistryLoader.Load(
            File.ReadAllBytes(Path.Combine(root, "Meta/registry.yaml")),
            File.ReadAllBytes(Path.Combine(root, "Meta/domains.yaml")))).Policy;
    }

    [Fact]
    public void RealRepositoryRegistryHasCanonicalSnapshotFixedPoint()
    {
        var root = TestRepositoryLayout.FindRoot();
        var registry = File.ReadAllBytes(Path.Combine(root, "Meta/registry.yaml"));
        var domains = File.ReadAllBytes(Path.Combine(root, "Meta/domains.yaml"));
        var policy = RegistryLoadAssert.Accepted(RegistryLoader.Load(registry, domains)).Policy;
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create([
                new RawRepositoryEntry("Meta/registry.yaml", ImmutableArray.CreateRange(registry)),
                new RawRepositoryEntry("Meta/domains.yaml", ImmutableArray.CreateRange(domains)),
            ]))).Snapshot;

        // No path admission or changed-path filter participates in this byte contract.
        var outcome = RepositoryCanonicalizer.Validate(snapshot, policy);
        Assert.True(outcome is CanonicalizationOutcome.Accepted,
            outcome is CanonicalizationOutcome.InfrastructureFailure failure ? failure.Message : outcome.ToString());
        var first = Assert.IsType<CanonicalizationOutcome.Accepted>(outcome);
        var reloaded = RegistryLoadAssert.Accepted(RegistryLoader.Load(
            policy.CanonicalRegistryBytes.AsSpan(), policy.CanonicalDomainsBytes.AsSpan())).Policy;
        var second = Assert.IsType<CanonicalizationOutcome.Accepted>(
            RepositoryCanonicalizer.Validate(snapshot, reloaded));

        Assert.Equal(registry, reloaded.CanonicalRegistryBytes.ToArray());
        Assert.Equal(domains, reloaded.CanonicalDomainsBytes.ToArray());
        Assert.Equal(first.Capability.Bytes.ToArray(), second.Capability.Bytes.ToArray());
        Assert.Equal(first.Capability.Sha256, second.Capability.Sha256);
    }

}
