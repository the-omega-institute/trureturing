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
}
