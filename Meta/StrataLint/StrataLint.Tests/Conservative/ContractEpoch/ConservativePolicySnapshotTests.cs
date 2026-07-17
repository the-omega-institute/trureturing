using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ConservativePolicySnapshotTests
{
    private const string BootstrapGatePath =
        "Meta/StrataLint/StrataLint.Engine/Admission/BootstrapGate.cs";
    private const string SpecificationPath = "docs/develop/spec/golden-ledger-repo-spec.md";
    private const string BlueprintSourcePath = "Blueprint/D5/S0/Carrier/Ring.scribe.cs";
    private const string BlueprintProjectionPath = "Blueprint/D5/S0/Carrier/Ring.md";
    private const string ValuesKernelPath = "Meta/StrataLint/Golden/values-kernels.toml";
    private static readonly string[] ResidenceEpochRetiredPaths =
    [
        "Meta/StrataLint/Golden/cases/digestion-and-anchors.toml",
        "Meta/StrataLint/Golden/cases/protected-semantics.toml",
        "Meta/StrataLint/Golden/cases/structure-and-identities.toml",
        "Meta/StrataLint/Golden/cases/structured-ledger.toml",
        ValuesKernelPath,
    ];

    [Theory]
    [InlineData(BootstrapGatePath, true)]
    [InlineData(ContractEpochTestData.LedgerPath, true)]
    [InlineData(SpecificationPath, true)]
    [InlineData(BlueprintSourcePath, true)]
    [InlineData(ValuesKernelPath, false)]
    [InlineData("Meta/StrataLint/StrataLint.Definitions/Retired.cs", false)]
    [InlineData(BlueprintProjectionPath, false)]
    public void DeclarativeProtectionPolicyPreservesTheExistingPredicate(
        string rawPath,
        bool expected)
    {
        var path = Assert.IsType<RepoPath>(RepoPath.TryCreate(rawPath, out var parsed) ? parsed : null);

        Assert.Equal(expected, BootstrapProtectionPolicy.IsProtected(path));
        Assert.Equal(expected, BootstrapGate.IsProtected(path));
    }

    [Fact]
    public void PolicyRootIsCanonicalAndStable()
    {
        var first = ConservativePolicySnapshot.Current();
        var second = ConservativePolicySnapshot.Current();

        Assert.StartsWith("sha256:", first.Root, StringComparison.Ordinal);
        Assert.Equal(71, first.Root.Length);
        Assert.Equal(first.Root, second.Root);
        Assert.Equal(first.CanonicalBytes.ToArray(), second.CanonicalBytes.ToArray());
        Assert.NotEmpty(first.ProtectionMatchers);
        Assert.Contains(first.RuleObligations, item => item.RuleId == "SL-022");
    }

    [Fact]
    public void ResidenceEpochRetiresExactlyTheFiveRegisteredPaths()
    {
        var current = ConservativePolicySnapshot.Current();

        Assert.Equal(ResidenceEpochRetiredPaths, current.ExactExclusions);
        Assert.Equal(
            "sha256:0daa1a195c3ff86a2da019f267933c40e4402fe54bde1203b9123adbb6e957ec",
            current.Root);
        Assert.All(ResidenceEpochRetiredPaths, path => Assert.False(current.IsProtected(path)));
    }

    [Fact]
    public void ExactExclusionCreatesADeclaredPathRetirementWithoutActualPathInference()
    {
        var baseline = ConservativePolicySnapshot.Current().WithExactExclusions([]);
        var candidate = baseline.WithExactExclusions([ValuesKernelPath]);

        var delta = ContractEpochVerifier.ComputePolicyDelta(baseline, candidate);

        Assert.Equal(
            [ValuesKernelPath],
            delta.RetiredExactPaths.ToArray());
        Assert.Empty(delta.RetiredRuleObligations);
        Assert.Empty(delta.OpaqueRetirements);
    }

    [Fact]
    public void RemovingAProtectionMatcherIsAnOpaqueRetirement()
    {
        var baseline = ConservativePolicySnapshot.Current();
        var candidate = baseline.WithoutProtectionMatcher("meta-stratalint");

        var delta = ContractEpochVerifier.ComputePolicyDelta(baseline, candidate);

        Assert.Empty(delta.RetiredExactPaths);
        Assert.Contains("protection:meta-stratalint", delta.OpaqueRetirements);
    }
}
