using System.Collections.Immutable;
using StrataLint.Configuration;
using StrataLint.Engine;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.RepositoryConfiguration.Tests;

public sealed class RepositoryPolicyTests
{
    [Theory]
    [InlineData("Meta/judge-seed.json")]
    [InlineData("Meta/package-materials.json")]
    public void RealRepositoryMetadataRegistrationsAreAdmissible(string value)
    {
        var path = RepoPath.CreateKnown(value);
        var policy = RealRepositoryPolicy();

        Assert.Null(RepositoryPathPolicy.Validate(path, policy));
        Assert.Single(policy.Manifest.Match(path.Value));
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
        Assert.Equal("path must match exactly one FILEMAP entry; matches=0", issue.Message);
        Assert.Empty(policy.Manifest.Match(path.Value));
    }

    private static ValidatedPolicy RealRepositoryPolicy()
    {
        var root = TestRepositoryLayout.FindRoot();
        return PolicyLoadAssert.Accepted(RepositoryPolicyLoader.LoadRepository(root)).Policy;
    }

    [Fact]
    public void RealRepositoryPolicyHasCanonicalSnapshotFixedPoint()
    {
        var root = TestRepositoryLayout.FindRoot();
        var fileMap = File.ReadAllBytes(Path.Combine(root, "Meta/FILEMAP.toml"));
        var domains = File.ReadAllBytes(Path.Combine(root, "Meta/domains.yaml"));
        var policy = PolicyLoadAssert.Accepted(RepositoryPolicyLoader.LoadRepository(root)).Policy;
        var documents = FileMapDocuments.Resolve(fileMap, FileMapLoader.RelativePath,
            path => File.ReadAllBytes(Path.Combine(root, path)));
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create([
                .. documents.Select(document => new RawRepositoryEntry(document.Path, document.Bytes)),
                new RawRepositoryEntry("Meta/domains.yaml", ImmutableArray.CreateRange(domains)),
            ]))).Snapshot;

        // No path admission or changed-path filter participates in this byte contract.
        var outcome = RepositoryCanonicalizer.Validate(snapshot, policy);
        Assert.True(outcome is CanonicalizationOutcome.Accepted,
            outcome is CanonicalizationOutcome.InfrastructureFailure failure ? failure.Message : outcome.ToString());
        var first = Assert.IsType<CanonicalizationOutcome.Accepted>(outcome);
        var reloaded = PolicyLoadAssert.Accepted(RepositoryPolicyLoader.Load(
            policy.CanonicalFileMapBytes.AsSpan(), policy.CanonicalDomainsBytes.AsSpan())).Policy;
        var second = Assert.IsType<CanonicalizationOutcome.Accepted>(
            RepositoryCanonicalizer.Validate(snapshot, reloaded));

        Assert.Equal(policy.CanonicalFileMapBytes.ToArray(), reloaded.CanonicalFileMapBytes.ToArray());
        Assert.Equal(domains, reloaded.CanonicalDomainsBytes.ToArray());
        Assert.Equal(first.Capability.Bytes.ToArray(), second.Capability.Bytes.ToArray());
        Assert.Equal(first.Capability.Sha256, second.Capability.Sha256);
    }

}
