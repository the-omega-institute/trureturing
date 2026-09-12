using System.Text.Json;
using System.Text.Json.Nodes;
using Xunit;

namespace Trureturing.Truth.Tests;

public sealed class TruthReleasePushRunSelectorTests
{
    private const string Commit = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    private const string WorkflowPath = ".github/workflows/ci-push.yml";

    [Fact]
    public void SelectsTheNamedDevPushAndReadsOnlyThatRunAttempt()
    {
        var calls = new List<(long, int)>();
        var selected = TruthReleasePushRunSelector.Select(Commit, Workflow(),
            [Run(41), Change(Run(44), "event", "pull_request_target"), Run(43)],
            (id, attempt) =>
            {
                calls.Add((id, attempt));
                return Jobs(id);
            });

        Assert.NotNull(selected);
        Assert.Equal(43, selected.RunId);
        Assert.Equal(2, selected.RunAttempt);
        Assert.Equal(70, selected.WorkflowId);
        Assert.Equal(Commit, selected.SourceCommit);
        Assert.Equal(new[] { (43L, 2) }, calls);
        Assert.Equal(new[] { "engineering", "current" }, selected.RequiredChecks.Select(check => check.Name));
        Assert.All(selected.RequiredChecks, check => Assert.Equal("success", check.Conclusion));
    }

    [Theory]
    [InlineData("event", "pull_request_target")]
    [InlineData("event", "workflow_dispatch")]
    [InlineData("head_branch", "integration-ci")]
    [InlineData("head_sha", "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb")]
    [InlineData("path", ".github/workflows/other.yml")]
    [InlineData("status", "in_progress")]
    [InlineData("conclusion", "failure")]
    public void WrongEventBranchHeadWorkflowOrFailedRunCannotPublish(string field, string value)
    {
        var selected = TruthReleasePushRunSelector.Select(Commit, Workflow(), [Change(Run(43), field, value)],
            (_, _) => throw new InvalidOperationException("ineligible runs must not supply jobs"));

        Assert.Null(selected);
    }

    [Fact]
    public void AWorkflowIdFromAnotherWorkflowCannotSupplyChecks()
    {
        Assert.Null(TruthReleasePushRunSelector.Select(Commit, Workflow(),
            [Change(Run(43), "workflow_id", 71)],
            (_, _) => throw new InvalidOperationException("wrong workflow")));
    }

    [Fact]
    public void TheWorkflowEndpointMustResolveTheCanonicalPath()
    {
        Assert.Throws<FormatException>(() => TruthReleasePushRunSelector.Select(Commit,
            Change(Workflow(), "path", ".github/workflows/ci-pr.yml"), [Run(43)], (_, _) => Jobs(43)));
    }

    [Theory]
    [InlineData("head_sha", "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb")]
    [InlineData("name", "push / current")]
    [InlineData("status", "queued")]
    [InlineData("conclusion", "failure")]
    [InlineData("conclusion", "skipped")]
    [InlineData("conclusion", "neutral")]
    public void CurrentJobMustBeTheSuccessfulDirectCheckAtTheSameHead(string field, string value)
    {
        Assert.Null(TruthReleasePushRunSelector.Select(Commit, Workflow(), [Run(43)],
            _ReadJobs));

        IEnumerable<JsonElement> _ReadJobs(long id, int _) =>
            [Job("engineering", id), Change(Job("current", id), field, value)];
    }

    [Theory]
    [InlineData("run_id", 99)]
    [InlineData("run_attempt", 1)]
    public void ChecksFromDifferentRunsOrAttemptsCannotBeCombined(string field, int value)
    {
        Assert.Null(TruthReleasePushRunSelector.Select(Commit, Workflow(), [Run(43)],
            (id, _) => [Job("engineering", id), Change(Job("current", id), field, value)]));
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void MissingOrDuplicateRequiredJobsCannotSupplyEvidence(bool duplicate)
    {
        Assert.Null(TruthReleasePushRunSelector.Select(Commit, Workflow(), [Run(43)],
            (id, _) => duplicate ? [.. Jobs(id), Job("current", id)] : [Job("engineering", id)]));
    }

    [Fact]
    public void AFailedEngineeringJobCannotBeHiddenBySuccessfulCurrent()
    {
        Assert.Null(TruthReleasePushRunSelector.Select(Commit, Workflow(), [Run(43)],
            (id, _) => [Change(Job("engineering", id), "conclusion", "failure"), Job("current", id)]));
    }

    [Fact]
    public void AnEarlierSuccessfulRunMayBeSelectedWithoutMixingJobs()
    {
        var calls = new List<long>();
        var selected = TruthReleasePushRunSelector.Select(Commit, Workflow(), [Run(43), Run(41)],
            (id, _) =>
            {
                calls.Add(id);
                return id == 43 ? [Job("current", id)] : Jobs(id);
            });

        Assert.NotNull(selected);
        Assert.Equal(41, selected.RunId);
        Assert.Equal(new long[] { 43, 41 }, calls);
    }

    [Fact]
    public void NoSuccessfulRunIsAnExplicitNoSelection()
    {
        Assert.Null(TruthReleasePushRunSelector.Select(Commit, Workflow(), [], (_, _) => Jobs(43)));
    }

    [Fact]
    public void ApiFailureIsNotReportedAsNoSelectionOrSuccess()
    {
        Assert.Throws<IOException>(() => TruthReleasePushRunSelector.Select(Commit, Workflow(), [Run(43)],
            (_, _) => throw new IOException("API unavailable")));
    }

    [Fact]
    public void MalformedApiEvidenceIsAnExplicitFailure()
    {
        Assert.Throws<FormatException>(() => TruthReleasePushRunSelector.Select(Commit, Workflow(), [Run(43)],
            (_, _) => [JsonSerializer.SerializeToElement(new { name = "current" }), Job("engineering", 43)]));
    }

    private static JsonElement Workflow() => JsonSerializer.SerializeToElement(new { id = 70, path = WorkflowPath });
    private static JsonElement Run(long id) => JsonSerializer.SerializeToElement(new
    {
        id, run_attempt = 2, workflow_id = 70, path = WorkflowPath,
        head_sha = Commit, head_branch = "dev", @event = "push", status = "completed", conclusion = "success",
    });
    private static JsonElement[] Jobs(long id) => [Job("engineering", id), Job("current", id)];
    private static JsonElement Job(string name, long runId) => JsonSerializer.SerializeToElement(new
    {
        name, run_id = runId, run_attempt = 2, head_sha = Commit, status = "completed", conclusion = "success",
    });
    private static JsonElement Change<T>(JsonElement value, string field, T replacement)
    {
        var node = JsonNode.Parse(value.GetRawText())!.AsObject();
        node[field] = JsonSerializer.SerializeToNode(replacement);
        return JsonSerializer.SerializeToElement(node);
    }
}
