using StrataLint.Engine;

namespace StrataLint.FileMap.Tests;

public sealed partial class FileMapPolicyTests
{
    [Theory]
    [InlineData("docs/reports/new/results.json")]
    [InlineData("docs/reports/new/probe.py")]
    [InlineData("docs/reports/new/README.md")]
    [InlineData("docs/reports/new/results.txt")]
    [InlineData("docs/reports/licenses/results.json")]
    [InlineData("docs/reports/new/results-LICENSE.json")]
    [InlineData("experiments/new/probe.py")]
    [InlineData("Evidence/D5/experiments/D5-X0001.run.json")]
    public void ExperimentalMaterialIsRejectedEvenWithAnExactRegistration(string path)
    {
        var policy = SyntheticPolicy(path);
        var issue = Assert.IsType<RepositoryPathIssue>(
            RepositoryPathPolicy.Validate(RepoPath.CreateKnown(path), policy.Policy));
        Assert.Equal("SL-000", issue.RuleId.Value);
        Assert.Contains("trureturing-experiments", issue.Message, StringComparison.Ordinal);

        var manifest = Parse(Entry(path, "data", "none", "agent", "SnapshotDecoder"));
        var finding = Assert.Single(FileMapPolicy.InspectCoverage(manifest, [path]));
        Assert.Equal("FILEMAP-EXPERIMENT-EXTERNAL", finding.Code);
    }

    [Theory]
    [InlineData("docs/reports/README.md")]
    [InlineData("docs/reports/new/library-LICENSE.txt")]
    [InlineData("docs/reports/new/library-NOTICE.txt")]
    [InlineData("docs/reports/new/LICENSE-MIT.txt")]
    [InlineData("docs/reports/licenses/third-party.md")]
    public void ReportEntrypointAndLicensesRemainAdmissible(string path)
    {
        var policy = SyntheticPolicy(path);
        Assert.Null(RepositoryPathPolicy.Validate(RepoPath.CreateKnown(path), policy.Policy));
        var manifest = Parse(Entry(path, "data", "none", "agent", "SnapshotDecoder"));
        Assert.Empty(FileMapPolicy.InspectCoverage(manifest, [path]));
    }
}
