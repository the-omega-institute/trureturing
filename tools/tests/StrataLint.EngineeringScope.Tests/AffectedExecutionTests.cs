using Xunit;

namespace StrataLint.EngineeringScope.Tests;

[Collection("Engineering scope process boundary")]
public sealed class AffectedExecutionTests
{
    [Fact]
    public void CommonRuntimeReusesKnownTestsForMetadataWithoutLosingBaseCoverage()
    {
        using var fixture = new AffectedExecutionFixture();
        var coldBuild = fixture.Build();
        var cold = fixture.Tests(coldBuild);
        Assert.Equal(2, cold.Projects.Sum(project => project.Executed));
        fixture.Write("README.md", "metadata changed\n");
        var warmBuild = fixture.Build();
        Assert.NotEqual(coldBuild.Candidate, warmBuild.Candidate);
        var warm = fixture.Tests(warmBuild);
        Assert.Equal(0, warm.Projects.Sum(project => project.Executed));
        Assert.All(warm.Projects.SelectMany(project => project.Coverage), coverage =>
        {
            Assert.Equal("reused", coverage.Status);
            Assert.Equal(cold.Candidate, coverage.Source.Candidate);
            Assert.Equal(cold.Round, coverage.Source.Round);
            Assert.NotEqual(warm.Candidate, coverage.Source.Candidate);
        });
        CommonExecutionEvidence.ValidateTests(fixture.Root, [AffectedExecutionFixture.First, AffectedExecutionFixture.Second]);
        Assert.ThrowsAny<Exception>(() => CommonExecutionEvidence.ValidateTests(fixture.Root, ["tools/tests/Deleted/Deleted.csproj"]));

        var evidencePath = Path.Combine(fixture.Root, CommonExecutionEvidence.TestsPath);
        var evidenceBytes = File.ReadAllBytes(evidencePath);
        File.Delete(evidencePath);
        Assert.ThrowsAny<Exception>(() => CommonExecutionEvidence.ValidateTests(fixture.Root));
        File.WriteAllBytes(evidencePath, evidenceBytes);
        CommonExecutionEvidence.Write(fixture.Root, CommonExecutionEvidence.TestsPath, warm with { Projects = warm.Projects.Take(1).ToArray() });
        Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.ValidateTests(fixture.Root));
        CommonExecutionEvidence.Write(fixture.Root, CommonExecutionEvidence.TestsPath, warm with
        { Projects = warm.Projects.Select(project => project with { Exit = 1 }).ToArray() });
        Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.ValidateTests(fixture.Root));
        File.WriteAllBytes(evidencePath, evidenceBytes);
        var reusedTrx = Path.Combine(fixture.Root, warm.Projects[0].Coverage[0].Results[0]);
        var trxBytes = File.ReadAllBytes(reusedTrx);
        File.WriteAllText(reusedTrx, "corrupt");
        Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.ValidateTests(fixture.Root));
        File.WriteAllBytes(reusedTrx, trxBytes);

        // Existing Actions primitives transport only the small success seed.
        fixture.Transport("snapshot");
        var key = fixture.TransportKey();
        fixture.ClearSeed();
        fixture.Transport("restore", "--tests-key", key);
        var transported = fixture.Tests(warmBuild);
        Assert.Equal(0, transported.Projects.Sum(project => project.Executed));
        Assert.Equal(Covered(cold), Covered(transported));

        var localCache = Path.Combine(fixture.Root, AffectedTestCache.CachePath);
        var sharedCache = Path.Combine(fixture.Root, "build/shared-test-cache");
        Directory.Move(localCache, sharedCache);
        var previousCache = Environment.GetEnvironmentVariable("STRATALINT_TEST_CACHE_ROOT");
        try
        {
            Environment.SetEnvironmentVariable("STRATALINT_TEST_CACHE_ROOT", sharedCache);
            Assert.Equal(0, fixture.Tests(warmBuild).Projects.Sum(project => project.Executed));
        }
        finally
        {
            Environment.SetEnvironmentVariable("STRATALINT_TEST_CACHE_ROOT", previousCache);
            Directory.Move(sharedCache, localCache);
        }

        var plan = fixture.Plan();
        var cache = new AffectedTestCache(fixture.Root, fixture.Output);
        var action = plan.Actions[0];
        Assert.Equal("producer-changed", cache.Select(action with { Producer = action.Producer + "changed" }).Reason);
        var previousRuntimeOption = Environment.GetEnvironmentVariable("DOTNET_TieredCompilation");
        try
        {
            Environment.SetEnvironmentVariable("DOTNET_TieredCompilation", previousRuntimeOption == "0" ? "1" : "0");
            var changed = action with { Environment = CommonStages.TestEnvironment(fixture.Root).ValuesIdentity };
            changed = changed with { Identity = AffectedTestPlan.Identity(changed) };
            Assert.NotEqual(action.Environment, changed.Environment);
            Assert.Equal("environment-changed", cache.Select(changed).Reason);
            Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.ValidateTests(fixture.Root));
        }
        finally { Environment.SetEnvironmentVariable("DOTNET_TieredCompilation", previousRuntimeOption); }
        File.Delete(Path.Combine(fixture.CacheDirectory, "trx", warm.Projects[0].Coverage[0].Source.Trx[0].Sha256, "source.trx"));
        var repaired = fixture.Tests(warmBuild);
        Assert.Equal(1, repaired.Projects.Sum(project => project.Executed));
        Assert.Contains("unusable-success", fixture.Output.ToString(), StringComparison.Ordinal);
        File.WriteAllText(Path.Combine(fixture.CacheDirectory, "seed.json"), "corrupt");
        var full = fixture.Tests(warmBuild);
        Assert.Equal(2, full.Projects.Sum(project => project.Executed));
        Assert.Equal(Covered(warm), Covered(full));
        fixture.Transport("snapshot");
        File.WriteAllText(Path.Combine(fixture.Root, "build/lean-cache/tests/data/seed.json"), "corrupt transfer");
        fixture.ClearSeed();
        fixture.Transport("restore", "--tests-key", key);
        Assert.Equal(2, fixture.Tests(warmBuild).Projects.Sum(project => project.Executed));
        Assert.Contains("integrity mismatch", fixture.Output.ToString(), StringComparison.Ordinal);
        var seed = CommonExecutionEvidence.Read<TestSuccessSeed>(fixture.CacheDirectory, "seed.json");
        CommonExecutionEvidence.Write(fixture.CacheDirectory, "seed.json", seed with { Successes = [] });
        File.WriteAllText(Path.Combine(fixture.CacheDirectory, "seed.json.sha256"), CommonExecutionEvidence.Hash(Path.Combine(fixture.CacheDirectory, "seed.json")));
        Assert.Equal("missing-success-coverage", new AffectedTestCache(fixture.Root, fixture.Output).Select(action).Reason);
        var cacheRoot = Path.Combine(fixture.Root, AffectedTestCache.CachePath);
        fixture.ClearSeed();
        File.WriteAllText(cacheRoot, "cache destination is unavailable");
        var saveFailed = fixture.Tests(warmBuild);
        Assert.Equal(2, saveFailed.Projects.Sum(project => project.Executed));
        Assert.Contains("status=save-failed", fixture.Output.ToString(), StringComparison.Ordinal);
        CommonExecutionEvidence.ValidateTests(fixture.Root);
    }

    [Fact]
    public void OneUnknownClassDoesNotForceUnrelatedKnownTestsToExecute()
    {
        // Scheduling now owns whole projects; preserve the original isolation/dependency checks.
        using var fixture = new AffectedExecutionFixture(unknown: true);
        Assert.Equal(4, fixture.Tests(fixture.Build()).Projects.Sum(project => project.Executed));
        fixture.Write("README.md", "metadata changed\n");
        var warmBuild = fixture.Build();
        var warm = fixture.Tests(warmBuild);
        Assert.Equal(3, warm.Projects.Sum(project => project.Executed));
        Assert.Equal(0, warm.Projects[0].Executed);
        Assert.Equal("executed", Assert.Single(warm.Projects[1].Coverage).Status);
        Assert.Contains("Environment.GetEnvironmentVariable", fixture.Output.ToString(), StringComparison.Ordinal);
        CommonExecutionEvidence.ValidateTests(fixture.Root);
        Assert.Contains(fixture.Plan().Actions.SelectMany(action => action.Inputs), input =>
            input.Path.EndsWith("local-runtime/value.txt", StringComparison.Ordinal));
        fixture.Remove("local-runtime/value.txt");
        var runtimeFailure = fixture.Tests(warmBuild, expectedExit: 1);
        Assert.Equal(0, runtimeFailure.Projects[0].Executed);
        Assert.NotNull(runtimeFailure.Projects[1].Error);
        Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.ValidateTests(fixture.Root));
    }

    [Fact]
    public void SharedSourceRemovalAndOptionsInvalidateAndFailingAffectedTestsCannotReuseSuccess()
    {
        using var fixture = new AffectedExecutionFixture();
        fixture.Write("tools/tests/StrataLint.First/Unused.cs", "internal class Unused { }\n");
        fixture.Tests(fixture.Build());
        fixture.Remove("tools/tests/StrataLint.First/Unused.cs");
        var removed = fixture.Tests(fixture.Build());
        Assert.Equal(1, removed.Projects.Sum(project => project.Executed));
        Assert.Contains("Unused.cs", fixture.Output.ToString(), StringComparison.Ordinal);
        fixture.Write("tools/tests/StrataLint.First/Directory.Build.props", "<Project><PropertyGroup><DefineConstants>CHANGED_OPTIONS</DefineConstants></PropertyGroup></Project>");
        var options = fixture.Tests(fixture.Build());
        Assert.Equal(1, options.Projects.Sum(project => project.Executed));
        fixture.Write("tools/StrataLint.Shared/Value.cs", "public static class Shared { public static int Value() { return 7; } }\n");
        Assert.Equal(2, fixture.Tests(fixture.Build()).Projects.Sum(project => project.Executed));
        var firstProject = Path.Combine(fixture.Root, AffectedExecutionFixture.First);
        File.WriteAllText(firstProject, File.ReadAllText(firstProject).Replace("<ProjectReference Include=\"../../StrataLint.Shared/StrataLint.Shared.csproj\" />", "", StringComparison.Ordinal));
        fixture.Write("tools/tests/StrataLint.First/Tests.cs", "namespace First; public class Tests { [Xunit.Fact] public void Runs() { Xunit.Assert.Equal(7, Local.AddTwo(5)); } } internal static class Local { public static int AddTwo(int value) => value + 2; }\n");
        Assert.Equal(1, fixture.Tests(fixture.Build()).Projects.Sum(project => project.Executed));
        Assert.Contains("removed-edges:", fixture.Output.ToString(), StringComparison.Ordinal);
        Assert.DoesNotContain(fixture.Plan().Projects.Where(project => project.Project == AffectedExecutionFixture.First).SelectMany(project => project.Edges), edge => edge.Contains("StrataLint.Shared", StringComparison.Ordinal));
        fixture.Write("tools/StrataLint.Shared/Value.cs", "public static class Shared { public static int Value() => 9; }\n");
        var build = fixture.Build();
        var incremental = fixture.Tests(build, expectedExit: 1);
        Assert.Equal(0, incremental.Projects[0].Executed);
        Assert.Null(incremental.Projects[0].Error);
        Assert.NotNull(incremental.Projects[1].Error);
        Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.ValidateTests(fixture.Root));
        fixture.ClearSeed();
        var full = fixture.Tests(build, expectedExit: 1);
        Assert.Equal(incremental.Projects.Select(project => project.Exit), full.Projects.Select(project => project.Exit));
        Assert.Equal(1, full.Projects[0].Executed);
        Assert.NotNull(full.Projects[1].Error);
    }

    private static int Covered(TestExecutionRecord record) => record.Projects.Sum(project =>
        project.Executed + project.Coverage.Where(coverage => coverage.Status == "reused").Sum(coverage => coverage.Covered));
}
