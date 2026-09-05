using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class RuleEngineCapacityDerivationTests
{
    [Fact]
    public void Sl003D5OnlyDeltaSkipsUnknownDebtDerivationAndStillNamesCapacityFinding()
    {
        var fixture = new RuleFixture();
        fixture.Files[RuleFixture.RingPath] += string.Concat(
            Enumerable.Repeat("-- pad\n", RepositoryRules.ArtifactHardLineLimit + 1));
        var context = fixture.Build(RawChangeSet.Create([RuleFixture.RingPath]));

        var findings = RepositoryRules.EvaluateCapacity(
            context,
            static _ => throw new InvalidOperationException("unknown-debt derivation was called"));

        var finding = Assert.Single(findings, item => item.Path == RuleFixture.RingPath);
        Assert.Equal("artifact exceeds 800 lines", finding.Message);
    }

    [Fact]
    public void Sl003BlueprintScribeDeltaRunsUnknownDebtDerivation()
    {
        var fixture = new RuleFixture();
        var context = fixture.Build(RawChangeSet.Create([RuleFixture.BlueprintSourcePath]));
        var calls = 0;

        RepositoryRules.EvaluateCapacity(context, _ =>
        {
            calls++;
            return EmptyTestMap();
        });

        Assert.Equal(2, calls);
    }

    [Theory]
    [InlineData("D5/S0/Carrier/Generated.cs")]
    [InlineData("tools/Synthetic/Synthetic.csproj")]
    [InlineData("tools/Synthetic/packages.lock.json")]
    [InlineData("global.json")]
    [InlineData("eng/Directory.Build.rsp")]
    [InlineData("eng/Directory.Packages.targets")]
    [InlineData("eng/NUGET.CONFIG")]
    [InlineData("eng/imported.props")]
    [InlineData("eng/imported.targets")]
    public void ScribeDerivationInputIncludesTrackedAndImportedBuildInputs(string path)
    {
        Assert.True(ScribeTestMapDeriver.IsDerivationInput(path));
    }

    [Theory]
    [InlineData("D5/S0/Carrier/Ring.lean")]
    [InlineData("Blueprint/D5/S0/Carrier/Ring.md")]
    [InlineData("README.md")]
    public void ScribeDerivationInputExcludesUnrelatedContent(string path)
    {
        Assert.False(ScribeTestMapDeriver.IsDerivationInput(path));
    }

    private static ScribeTestMap EmptyTestMap() => new([], [], [], [], []);
}
