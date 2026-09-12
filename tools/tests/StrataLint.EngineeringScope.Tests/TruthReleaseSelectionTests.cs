using System.Text.Json;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed class TruthReleaseSelectionTests
{
    private const string Commit = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";

    [Fact]
    public void SelectedPushAndArtifactShareCommitRunAndAttempt()
    {
        var (exit, text) = Select(Artifact(22, 2));
        Assert.Equal(0, exit);
        using var result = JsonDocument.Parse(text);
        Assert.True(result.RootElement.GetProperty("publish_ready").GetBoolean());
        Assert.Equal(22, result.RootElement.GetProperty("run_id").GetInt64());
        Assert.Equal(2, result.RootElement.GetProperty("run_attempt").GetInt32());
        Assert.Equal("ci-current-22-2", result.RootElement.GetProperty("artifact_name").GetString());
        Assert.Equal(2, result.RootElement.GetProperty("required_checks").GetArrayLength());
    }

    [Theory]
    [InlineData("missing")]
    [InlineData("expired")]
    [InlineData("wrong-run")]
    [InlineData("wrong-attempt")]
    [InlineData("wrong-commit")]
    [InlineData("malformed-id")]
    public void UnavailableBundleSelectsAnOlderEligiblePush(string defect)
    {
        var artifact = Artifact(22, 2, defect);
        var (exit, text) = Select(artifact, fallback: true);
        Assert.Equal(0, exit);
        using var result = JsonDocument.Parse(text);
        Assert.Equal(21, result.RootElement.GetProperty("run_id").GetInt64());
    }

    [Fact]
    public void MissingAllBundlesWaitsWithoutReportProduction()
    {
        var (exit, text) = Select(null);
        Assert.Equal(0, exit);
        using var result = JsonDocument.Parse(text);
        Assert.False(result.RootElement.GetProperty("publish_ready").GetBoolean());
    }

    private static object? Artifact(long run, int attempt, string defect = "") => defect == "missing" ? null : new
    {
        id = defect == "malformed-id" ? (object)"invalid" : run * 10,
        name = $"ci-current-{run}-{(defect == "wrong-attempt" ? attempt + 1 : attempt)}",
        expired = defect == "expired",
        workflow_run = new { id = defect == "wrong-run" ? run + 1 : run, head_sha = defect == "wrong-commit" ? new string('b', 40) : Commit },
    };

    private static (int Exit, string Output) Select(object? artifact, bool fallback = false)
    {
        using var directory = new CurrentExecutionContractTests.CandidateFixture();
        object Run(long id, int attempt) => new
        {
            id, run_attempt = attempt, workflow_id = 7, path = ".github/workflows/ci-push.yml",
            @event = "push", head_branch = "dev", head_sha = Commit, status = "completed", conclusion = "success",
        };
        object[] Jobs(long id, int attempt) => new[] { "engineering", "current" }.Select(name => (object)new
        {
            name, run_id = id, run_attempt = attempt, head_sha = Commit, status = "completed", conclusion = "success",
        }).ToArray();
        var input = Path.Combine(directory.Root, "selection.json");
        TemporaryFileSystem.File.WriteAllText(input, JsonSerializer.Serialize(new
        {
            source_commit = Commit,
            workflow = new { id = 7, path = ".github/workflows/ci-push.yml" },
            runs = fallback ? new[] { Run(22, 2), Run(21, 1) } : new[] { Run(22, 2) },
            jobs = new Dictionary<string, object[]> { ["22/2"] = Jobs(22, 2), ["21/1"] = Jobs(21, 1) },
            artifacts = new Dictionary<string, object?[]> { ["22"] = artifact is null ? [] : [artifact], ["21"] = [Artifact(21, 1)] },
        }));
        using var output = new StringWriter();
        var exit = Program.Run(["truth-release-select", "--input", input], _ => throw new InvalidOperationException(), output, TextWriter.Null);
        return (exit, output.ToString());
    }
}
