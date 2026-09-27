using System.Text.Json;
using StrataLint.EngineeringScope;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.ReleaseIntegration.Tests;

public sealed class ReleaseCommandTests
{
    [Fact]
    public void CommandUsesTransportArtifactIdentityForTheSelectedRun()
    {
        using var directory = new TemporaryDirectory();
        var input = Path.Combine(directory.Path, "selection.json");
        const string commit = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
        File.WriteAllText(input, JsonSerializer.Serialize(new
        {
            source_commit = commit,
            workflow = new { id = 7, path = ".github/workflows/ci-push.yml" },
            runs = new[] { new { id = 22, run_attempt = 2, workflow_id = 7, path = ".github/workflows/ci-push.yml",
                @event = "push", head_branch = "dev", head_sha = commit, status = "completed", conclusion = "success" } },
            jobs = new Dictionary<string, object[]> { ["22/2"] = new[] { "engineering", "current" }.Select(name => (object)new
                { name, run_id = 22, run_attempt = 2, head_sha = commit, status = "completed", conclusion = "success" }).ToArray() },
            artifacts = new Dictionary<string, object[]> { ["22"] = [new { id = 220,
                name = CiTransport.ArtifactName("current", 22, 2), expired = false,
                workflow_run = new { id = 22, head_sha = commit } }] },
        }));
        using var output = new StringWriter();
        using var error = new StringWriter();
        Assert.Equal(0, Program.Run(["truth-release-select", "--input", input],
            _ => throw new InvalidOperationException("selection must not load execution evidence"), output, error));
        using var result = JsonDocument.Parse(output.ToString());
        Assert.True(result.RootElement.GetProperty("publish_ready").GetBoolean());
        Assert.Equal("ci-current-22-2", result.RootElement.GetProperty("artifact_name").GetString());
        Assert.Empty(error.ToString());
    }

    [Fact]
    public void InvalidCommandReturnsInputFailureWithoutTestExecution()
    {
        using var output = new StringWriter();
        using var error = new StringWriter();
        Assert.Equal(2, Program.Run(["truth-release-select"],
            _ => throw new InvalidOperationException("selection must not load execution evidence"), output, error));
        Assert.Empty(output.ToString());
        Assert.Contains("truth-release-select --input FILE", error.ToString(), StringComparison.Ordinal);
    }
}
