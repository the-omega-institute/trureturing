using System.Security.Cryptography;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ConservativePolicySnapshotTests
{
    private const string UnprotectedTruthGraphPath = "Generated/truth-graph.v1.json";
    private const string ProtectedScribeEmissionsPath =
        "Meta/StrataLint/Generated/scribe-emissions.v1.json";

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
    public void Sl023IsAnActiveObserveObligationDuringTheExpandEpoch()
    {
        var current = ConservativePolicySnapshot.Current();
        var sl023 = Assert.Single(current.RuleObligations, item => item.RuleId == "SL-023");
        Assert.Equal(AdmissionEffect.Observe.ToString(), sl023.AdmissionEffect);
        Assert.StartsWith("sha256:", sl023.DescriptorRoot, StringComparison.Ordinal);
        Assert.Equal(71, sl023.DescriptorRoot.Length);
        Assert.Equal(
            "sha256:859fa8e16c1ca28771a8d2165f89580d5b54ae34dfe487d38450fd350ffff9df",
            current.Root);
    }

    [Fact]
    public void Sl026IsPreRegisteredWithRepositoryRuleDefaults()
    {
        var current = ConservativePolicySnapshot.Current();
        var sl026 = Assert.Single(
            current.WithRuleObligations(["SL-026"]).RuleObligations,
            item => item.RuleId == "SL-026");
        var descriptor = new RuleDescriptor(
            RuleId.CreateKnown(26),
            "Scribe legacy constructor budget",
            DisplaySeverity.Error,
            "repository",
            AdmissionEffect.Block,
            RuleLifecycle.Active,
            null);
        var material = JsonSerializer.SerializeToElement(new
        {
            admission_effect = descriptor.AdmissionEffect.ToString(),
            category = descriptor.Category,
            deferred_case = descriptor.DeferredCase?.Value,
            display_severity = descriptor.DisplaySeverity.ToString(),
            id = descriptor.Id.Value,
            lifecycle = descriptor.Lifecycle.ToString(),
            title = descriptor.Title,
        });
        var descriptorRoot = "sha256:" + Convert.ToHexStringLower(
            SHA256.HashData(StructuredCanonicalWriter.WriteJson(material).AsSpan()));

        Assert.Equal(AdmissionEffect.Block.ToString(), sl026.AdmissionEffect);
        Assert.Equal(descriptorRoot, sl026.DescriptorRoot);
    }

    [Fact]
    public void UnregisteredFutureRuleStillFailsClosed()
    {
        var current = ConservativePolicySnapshot.Current();

        var exception = Assert.Throws<ArgumentException>(() =>
            current.WithRuleObligations(["SL-024"]));
        Assert.Contains("unknown active rules: SL-024", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ResidenceEpochRetiresExactlyTheFiveRegisteredPaths()
    {
        var current = ConservativePolicySnapshot.Current();

        Assert.Equal(ResidenceEpochRetiredPaths, current.ExactExclusions);
        Assert.Equal(
            "sha256:859fa8e16c1ca28771a8d2165f89580d5b54ae34dfe487d38450fd350ffff9df",
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
