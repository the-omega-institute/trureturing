using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ConservativePolicySnapshotTests
{
    private const string UnprotectedTruthGraphPath = "Generated/truth-graph.v1.json";
    private const string ProtectedScribeEmissionsPath =
        "Meta/StrataLint/Generated/scribe-emissions.v1.json";
    private const string ProtectedAnchorCatalogPath =
        "Meta/StrataLint/Generated/anchor-catalog.v1.json";

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
    public void TopLevelTruthGraphChangeDoesNotProduceSl022Diagnostics()
    {
        var clear = Assert.IsType<BootstrapOutcome.Clear>(
            BootstrapGate.Evaluate(RawChangeSet.Create([UnprotectedTruthGraphPath])));
        Assert.NotNull(clear.Capability);
    }

    [Theory]
    [InlineData(ProtectedScribeEmissionsPath)]
    [InlineData(ProtectedAnchorCatalogPath)]
    public void BaseJudgeGeneratedInputsProduceSl022Diagnostics(string protectedPath)
    {
        var verification = Assert.IsType<BootstrapOutcome.ProtectedSurfaceVerificationRequired>(
            BootstrapGate.Evaluate(RawChangeSet.Create([protectedPath])));

        var diagnostic = Assert.Single(BootstrapGate.CreateSl022Diagnostics(verification.ChangeSet));
        Assert.Equal("SL-022", diagnostic.RuleId.Value);
        Assert.Equal(protectedPath, diagnostic.Path);
    }

    private static string FindRepositoryRoot()
    {
        var directory = new DirectoryInfo(AppContext.BaseDirectory);
        while (directory is not null && !File.Exists(Path.Combine(directory.FullName, "Trureturing.lean")))
        {
            directory = directory.Parent;
        }

        return directory?.FullName
            ?? throw new InvalidOperationException("Could not locate repository root.");
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
    public void FrozenLedgerStorageMigrationPreservesSl008DescriptorRoot()
    {
        var sl008 = Assert.Single(
            ConservativePolicySnapshot.Current().RuleObligations,
            item => item.RuleId == "SL-008");

        Assert.Equal(
            "sha256:1dcf5e1f74a961aa05f68a2332edd8de824de10a58875f9cde05589d947ed7f1",
            sl008.DescriptorRoot);
    }

    [Fact]
    public void FrozenLedgerStorageMigrationHasNoContractPolicyDelta()
    {
        var before = ConservativePolicySnapshot.Current();
        var after = ConservativePolicySnapshot.Current();

        var delta = ContractEpochVerifier.ComputePolicyDelta(before, after);

        Assert.Empty(delta.RetiredExactPaths);
        Assert.Empty(delta.RetiredRuleObligations);
        Assert.Empty(delta.OpaqueRetirements);
    }

    [Fact]
    public void Sl023AndSl024AreActiveObligationsDuringTheExpandEpoch()
    {
        var current = ConservativePolicySnapshot.Current();
        var sl023 = Assert.Single(current.RuleObligations, item => item.RuleId == "SL-023");
        var sl024 = Assert.Single(current.RuleObligations, item => item.RuleId == "SL-024");
        Assert.Equal(AdmissionEffect.Observe.ToString(), sl023.AdmissionEffect);
        Assert.StartsWith("sha256:", sl023.DescriptorRoot, StringComparison.Ordinal);
        Assert.Equal(71, sl023.DescriptorRoot.Length);
        Assert.Equal(AdmissionEffect.Block.ToString(), sl024.AdmissionEffect);
        Assert.StartsWith("sha256:", sl024.DescriptorRoot, StringComparison.Ordinal);
        Assert.Equal(71, sl024.DescriptorRoot.Length);
        Assert.Equal(
            "sha256:b610352dd551e20e27f89b8b878bef5e9ac5ea4e13b49a3a389667b579daca0b",
            current.Root);
    }

    [Fact]
    public void UnregisteredFutureRuleStillFailsClosed()
    {
        var current = ConservativePolicySnapshot.Current();

        var exception = Assert.Throws<ArgumentException>(() =>
            current.WithRuleObligations(["SL-025"]));
        Assert.Contains("unknown active rules: SL-025", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ResidenceEpochRetiresExactlyTheFiveRegisteredPaths()
    {
        var current = ConservativePolicySnapshot.Current();

        Assert.Equal(ResidenceEpochRetiredPaths, current.ExactExclusions);
        Assert.Equal(
            "sha256:b610352dd551e20e27f89b8b878bef5e9ac5ea4e13b49a3a389667b579daca0b",
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
