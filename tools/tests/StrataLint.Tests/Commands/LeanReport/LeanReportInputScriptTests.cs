using System.Text;

namespace StrataLint.Tests;

public sealed class LeanReportInputScriptTests
{
    [Fact]
    public void ProducerClosureFollowsRegisteredDependencies()
    {
        using var fixture = new ProducerInputFixture();
        var before = fixture.Address();
        fixture.Write(".github/workflows/ci.yml", "not a workflow");
        fixture.Write("tools/StrataLint.Cli/Unused.cs", "not registered");
        Assert.Equal(before, fixture.Address());
        const string dependency = "tools/lean-inspector/fixture_dependency.py";
        fixture.Write(dependency, "SEMANTIC_VALUE = 1\n");
        fixture.RegisterScripts(dependency);
        var registered = fixture.Address();
        fixture.Write(dependency, "SEMANTIC_VALUE = 2\n");
        Assert.NotEqual(registered[1], fixture.Address()[1]);
        fixture.Remove(dependency);
        var rejected = fixture.Run("address");
        Assert.Equal(2, rejected.ExitCode);
        Assert.Contains(dependency, Encoding.UTF8.GetString(rejected.StandardError));
    }

    [Fact]
    public void MetadataAndSemanticInputsHaveDistinctBehavior()
    {
        using var fixture = new ProducerInputFixture();
        var before = fixture.Address();
        fixture.Plan(before, before);
        Assert.Equal(0, fixture.VerifySeed().ExitCode);
        fixture.Write("lakefile.toml", "name = \"renamed\"\nkeywords = [\"metadata\"]\n");
        Assert.Equal(0, fixture.VerifySeed().ExitCode);
        Assert.Empty(fixture.Plan(before, fixture.Address())["recheck"]!.AsArray());
        fixture.Append(ProducerInputFixture.FetcherPath, "# declared producer changed\n");
        Assert.Equal(2, fixture.VerifySeed().ExitCode);
        fixture.Write(ProducerInputFixture.FetcherPath, "#!/bin/bash\n");
        fixture.Append("D5/Probe.lean", "-- changed source\n");
        Assert.Equal(2, fixture.VerifySeed().ExitCode);
        fixture.Write("D5/Probe.lean", "def probe := 1\n");
        fixture.Write("lakefile.toml", "[leanOptions]\nmaxRecDepth = 2000\n");
        Assert.Equal(2, fixture.VerifySeed().ExitCode);
    }

    [Theory]
    [InlineData("tools/StrataLint.Cli/Fixture.cs", 2)]
    [InlineData("tools/StrataLint.Engine/Fixture.cs", 2)]
    [InlineData("tools/Trureturing.Truth/Fixture.cs", 2)]
    [InlineData("producer.props", 2)]
    [InlineData("tools/StrataLint.Scribe/Fixture.cs", 0)]
    public void RegisteredProducerInputsInvalidateReportReuse(string path, int expected)
    {
        using var fixture = new ProducerInputFixture();
        var before = fixture.Address();
        fixture.Plan(before, before);
        fixture.Append(path, "\n// changed declared bytes\n");
        var after = fixture.Address();
        Assert.Equal(expected == 0, before[1] == after[1]);
        Assert.Equal(before[2..], after[2..]);
        Assert.Equal(expected, fixture.Plan(before, after)["recheck"]!.AsArray().Count);
    }

    [Fact]
    public void ActionsWritePolicyDoesNotInvalidateReportReuse()
    {
        using var fixture = new ProducerInputFixture();
        const string policyPath = "tools/scripts/worktree/lean_actions.py";
        foreach (var path in new[] { policyPath, "tools/scripts/worktree/lean_cache_release.py", "tools/scripts/worktree/cache_material.py" })
            fixture.Write(path, File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), path)));
        var before = fixture.Address();
        fixture.Plan(before, before);
        Assert.False(fixture.ActionsPolicy()["save_allowed"]!.GetValue<bool>());
        var original = File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), policyPath));
        var changed = original.Replace("== \"refs/heads/dev\"",
            "in (\"refs/heads/dev\", \"refs/heads/feature-policy-probe\")", StringComparison.Ordinal);
        Assert.NotEqual(original, changed);
        fixture.Write(policyPath, changed);
        Assert.True(fixture.ActionsPolicy()["save_allowed"]!.GetValue<bool>());
        Assert.Equal(before, fixture.Address());
        Assert.Empty(fixture.Plan(before, fixture.Address())["recheck"]!.AsArray());
    }
}
