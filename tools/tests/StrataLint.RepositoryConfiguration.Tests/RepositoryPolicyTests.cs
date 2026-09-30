using System.Collections.Immutable;
using StrataLint.Configuration;
using StrataLint.Engine;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.RepositoryConfiguration.Tests;

public sealed class RepositoryPolicyTests
{
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
