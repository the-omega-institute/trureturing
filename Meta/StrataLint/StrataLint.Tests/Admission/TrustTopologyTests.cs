using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class TrustTopologyTests
{
    public static TheoryData<string> ProtectedPaths => new()
    {
        "Meta/StrataLint/StrataLint.Engine/Coordinates/Gid.cs",
        "Meta/StrataLint/StrataLint.Cli/Program.cs",
        "Meta/StrataLint/StrataLint.Tests/Admission/TrustTopologyTests.cs",
        "docs/develop/spec/golden-ledger-repo-spec.md",
        "Meta/registry.yaml",
        "Meta/domains.yaml",
        "D5/X_Frontier/Hearts.lean",
        "D5/X_Assumptions/REGISTRY.md",
        "Meta/StrataLint/Golden/rules.json",
        "Meta/StrataLint/StrataLint.sln",
        "Meta/StrataLint/StrataLint.Engine/StrataLint.Engine.csproj",
        "global.json",
        "Directory.Build.props",
        "Directory.Packages.props",
        "Meta/StrataLint/StrataLint.Engine/packages.lock.json",
        "lean-toolchain",
        ".github/CODEOWNERS",
        ".github/workflows/ci.yml",
        ".github/scripts/harness-gate.sh",
    };

    [Theory]
    [MemberData(nameof(ProtectedPaths))]
    public void Sl022RequiresExternalHumanReviewForEveryProtectedSurface(string path)
    {
        var changes = RawChangeSet.Create(new[] { path });

        var outcome = BootstrapGate.Evaluate(changes);

        var required = Assert.IsType<BootstrapOutcome.HumanReviewRequired>(outcome);
        Assert.Contains(required.ChangeSet.Paths, item => item.Value == path);
    }

    [Theory]
    [InlineData("Blueprint/D5/S0/Carrier/Ring.md")]
    [InlineData("Blueprint/D5/S1/Digit/Raw.scribe.cs")]
    public void ContentContributionProducesAnUnforgeableMetaClearCapability(string path)
    {
        var changes = RawChangeSet.Create(new[] { path });

        var outcome = BootstrapGate.Evaluate(changes);

        var clear = Assert.IsType<BootstrapOutcome.Clear>(outcome);
        Assert.NotNull(clear.Capability);
        Assert.Empty(typeof(MetaClear).GetConstructors());
    }

    [Fact]
    public void RuleCatalogIsExplicitCompleteAndCannotDowngradeEffectsFromConfiguration()
    {
        var descriptors = RuleCatalog.Default.Descriptors;

        Assert.Equal(22, descriptors.Length);
        Assert.Equal(22, descriptors.Select(item => item.Id).Distinct().Count());
        Assert.Equal(
            Enumerable.Range(1, 22).Select(RuleId.CreateKnown),
            descriptors.Select(item => item.Id));
        Assert.Equal(AdmissionEffect.HumanGate, descriptors[21].AdmissionEffect);
        Assert.All(
            descriptors.Where(item => item.Id.Value is not ("SL-007" or "SL-009" or "SL-014" or "SL-022")),
            item => Assert.Equal(AdmissionEffect.Block, item.AdmissionEffect));
        Assert.All(
            descriptors.Where(item => item.Id.Value is "SL-007" or "SL-009" or "SL-014"),
            item => Assert.Equal(RuleLifecycle.Deferred, item.Lifecycle));
    }
}
