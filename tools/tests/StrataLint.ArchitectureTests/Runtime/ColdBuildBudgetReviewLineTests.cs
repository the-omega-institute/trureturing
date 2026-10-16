using StrataLint.Runtime;

namespace StrataLint.ArchitectureTests;

public sealed class ColdBuildBudgetReviewLineTests
{
    [Fact]
    public void CandidateEnumerationAndHangGuardReadUntrackedBytes()
    {
        using var fixture = new TemporaryDirectory();
        var git = TestProcessRunner.Run("git", ["init", "--quiet"], fixture.Path,
            BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
        Assert.Equal(0, git.ExitCode);
        Directory.CreateDirectory(Path.Combine(fixture.Path, "tools/tests"));
        var path = Path.Combine(fixture.Path, "tools/tests/Candidate.cs");
        var violation = string.Concat("BoundedProcessRunner.",
            "Run(\"tool\", [], \".\", BoundedProcessRunner.HangDetectionBudget);\n");
        File.WriteAllText(path, violation);
        Assert.Equal(new[] { "tools/tests/Candidate.cs" },
            GitIndexRepositoryFiles.EnumerateDeclared(fixture.Path, "tools/tests")
                .Select(static file => file.RelativePath));
        Assert.Equal(violation, File.ReadAllText(
            Assert.Single(GitIndexRepositoryFiles.Enumerate(fixture.Path)).FullPath));
        Assert.Single(HangGuardRouting.FindUnroutedHangGuardCalls(fixture.Path));
        git = TestProcessRunner.Run("git", ["add", "."], fixture.Path,
            BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
        Assert.Equal(0, git.ExitCode);
        File.WriteAllText(path, "// canonical process routing\n");
        Assert.Empty(HangGuardRouting.FindUnroutedHangGuardCalls(fixture.Path));
        File.Delete(path);
        Assert.Empty(GitIndexRepositoryFiles.Enumerate(fixture.Path));
    }

    [Fact]
    public void CommandCutoffAndConfiguredFloorRemainIndependentlyPinned()
    {
        Assert.Equal(21600, StrataLint.EngineeringScope.LeanCacheBudgetPolicy.DefaultProvisionBudgetSeconds);
        Assert.Equal(300, StrataLint.EngineeringScope.LeanCacheBudgetPolicy.MinimumConfigurableBudgetSeconds);
    }

    [Fact]
    public void DeclaredD5LeanFilesIncludeTheProtectedFrontier()
    {
        var d5Files = GitIndexRepositoryFiles.EnumerateDeclared(RepositoryLayout.FindRoot(), "D5");
        var leanFiles = d5Files
            .Where(static file => file.RelativePath.EndsWith(".lean", StringComparison.Ordinal))
            .ToArray();

        Assert.NotEmpty(d5Files);
        Assert.NotEmpty(leanFiles);
        Assert.Contains(leanFiles, static file => file.RelativePath == "D5/X_Frontier/Hearts.lean");
    }

    // Compare the declared prefix with the complete candidate enumeration.
    [Fact]
    public void EnumerateDeclaredReturnsEveryTrackedFileUnderThePrefix()
    {
        var root = RepositoryLayout.FindRoot();

        var independent = GitIndexRepositoryFiles.Enumerate(root)
            .Where(static file => file.RelativePath.StartsWith("D5/", StringComparison.Ordinal))
            .Select(static file => file.RelativePath)
            .ToArray();
        var declared = GitIndexRepositoryFiles.EnumerateDeclared(root, "D5")
            .Select(static file => file.RelativePath)
            .ToArray();

        Assert.NotEmpty(independent);
        Assert.Equal(independent, declared);
    }
}
