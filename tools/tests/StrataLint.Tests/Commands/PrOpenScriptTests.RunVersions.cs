using System.Text.Json;

namespace StrataLint.Tests;

public sealed partial class PrOpenScriptTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void PrWatchCannotSupersedeAcrossPullRequestsSharingTheSourceHead(bool reverse)
    {
        using var fixture = new PrScriptFixture();
        // These executions share every field in the old origin key. The older
        // failure belongs to PR 42/dev; the newer success to PR 43/integration-x.
        // Both open PRs match the source head. matchingPullRequests cannot say
        // which PR triggered either execution, so it cannot authorize supersession.
        var older = JsonSerializer.SerializeToNode(Check("engineering", "COMPLETED", "FAILURE"))!;
        var newer = JsonSerializer.SerializeToNode(Check("engineering", "COMPLETED", "SUCCESS",
            checkId: 102, runId: 202, runNumber: 2))!;
        var matches = JsonSerializer.SerializeToNode(new
        {
            nodes = new[]
            {
                new { number = 42, baseRefName = "dev", headRefOid = HeadSha },
                new { number = 43, baseRefName = "integration-x", headRefOid = HeadSha },
            },
            pageInfo = new { hasNextPage = false },
        });
        older["checkSuite"]!["matchingPullRequests"] = matches!.DeepClone();
        newer["checkSuite"]!["matchingPullRequests"] = matches.DeepClone();
        fixture.SnapshotResponses(Ok(Snapshot("OPEN", reverse ? [newer, older] : [older, newer])));

        var result = fixture.RunWatch42();

        Assert.True(result.ExitCode == 69, $"watcher_exit={result.ExitCode}\n" + Text(result.StandardOutput) + Text(result.StandardError));
        Assert.DoesNotContain("outcome=green", Text(result.StandardOutput), StringComparison.Ordinal);
        Assert.Contains("reason=ambiguous-pr-origin", Text(result.StandardError), StringComparison.Ordinal);
        Assert.Equal(3, fixture.Invocations.Count(IsSnapshotInvocation));
    }

    [Theory]
    [InlineData("pull_request")]
    [InlineData("pull_request_target")]
    [InlineData("pull_request_review")]
    [InlineData("pull_request_review_comment")]
    public void PrWatchRequiresOriginEvenWhenAllPrRunsSucceed(string eventName)
    {
        using var fixture = new PrScriptFixture();
        fixture.SnapshotResponses(Ok(Snapshot("OPEN",
            Check("engineering", "COMPLETED", "SUCCESS", eventName: eventName),
            Check("engineering", "COMPLETED", "SUCCESS", checkId: 102, runId: 202, runNumber: 2, eventName: eventName))));

        var result = fixture.RunWatch42();

        Assert.Equal(69, result.ExitCode);
        Assert.Contains("reason=ambiguous-pr-origin", Text(result.StandardError), StringComparison.Ordinal);
    }

    [Fact]
    public void PrWatchWaitsForTheExpectedHeadBeforeRejectingAmbiguousPrOrigins()
    {
        using var fixture = new PrScriptFixture();
        fixture.SnapshotResponses(
            Ok(Snapshot("OPEN", OldHeadSha, HeadSha,
                Check("engineering", "COMPLETED", "FAILURE"),
                Check("engineering", "COMPLETED", "SUCCESS", checkId: 102, runId: 202, runNumber: 2))),
            Ok(Snapshot("OPEN", Check("engineering", "COMPLETED", "SUCCESS"))));

        var result = fixture.RunWatch42();

        Assert.Equal(0, result.ExitCode);
        Assert.Contains("state=stale", Text(result.StandardError), StringComparison.Ordinal);
        Assert.DoesNotContain("reason=ambiguous-pr-origin", Text(result.StandardError), StringComparison.Ordinal);
        Assert.Equal(2, fixture.Invocations.Count(IsSnapshotInvocation));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void PrWatchRejectsUnknownHistoricalOriginFromObservedPr9253(bool reverse)
    {
        using var fixture = new PrScriptFixture();
        const string head = "f9139835b80bce712b50dd9a77396a83abf167c9";
        fixture.RequiredResponses(Ok(Required("push / engineering", "push / current", "delta")));
        // GitHub run 1353 was cancelled; run 1354 completed all required jobs.
        // Both are first attempts of the same workflow, app, event and branch,
        // but the API returns no PR association for these merged-PR runs. The shared
        // source head does not establish their historical execution origin.
        var names = new[] { "push / engineering", "push / current", "delta" };
        var oldIds = new long[] { 106217103031, 106217103546, 106217104145 };
        var newIds = new long[] { 106217240674, 106217240777, 106217309734 };
        var items = names.SelectMany((name, i) => new[]
        {
            Check(name, "COMPLETED", "CANCELLED", head, oldIds[i], 35562164528, 1353),
            Check(name, "COMPLETED", "SUCCESS", head, newIds[i], 35562213366, 1354),
        }).ToArray();
        fixture.SnapshotResponses(Ok(Snapshot("MERGED", head, head, reverse ? items.Reverse().ToArray() : items)));

        var result = fixture.RunWatch("--pr", "9253", "--head-sha", head, "--interval-seconds", "1");

        Assert.True(result.ExitCode == 69, $"watcher_exit={result.ExitCode}\n" + Text(result.StandardOutput) + Text(result.StandardError));
        Assert.Contains("outcome=query-unavailable", Text(result.StandardOutput), StringComparison.Ordinal);
        Assert.Contains("reason=ambiguous-pr-origin", Text(result.StandardError), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void PrWatchAcceptsSupersedingPushRun(bool reverse)
    {
        using var fixture = new PrScriptFixture();
        var older = Check("engineering", "COMPLETED", "CANCELLED", eventName: "push");
        var newer = Check("engineering", "COMPLETED", "SUCCESS", checkId: 102, runId: 202, runNumber: 2, eventName: "push");
        fixture.SnapshotResponses(Ok(Snapshot("OPEN", reverse ? [newer, older] : [older, newer])));

        var result = fixture.RunWatch42();

        Assert.True(result.ExitCode == 0, $"watcher_exit={result.ExitCode}\n" + Text(result.StandardOutput) + Text(result.StandardError));
        Assert.Contains("outcome=green", Text(result.StandardOutput), StringComparison.Ordinal);
        var line = Text(result.StandardError).Split('\n').Single(value => value.StartsWith("PR_WATCH_EVIDENCE", StringComparison.Ordinal));
        using var evidence = JsonDocument.Parse(line[(line.IndexOf("checks=", StringComparison.Ordinal) + "checks=".Length)..]);
        Assert.Single(evidence.RootElement.EnumerateArray(), item =>
            item.GetProperty("run_id").GetInt64() == 201 && item.GetProperty("superseded").GetBoolean());
        Assert.Single(evidence.RootElement.EnumerateArray(), item =>
            item.GetProperty("run_id").GetInt64() == 202 && !item.GetProperty("superseded").GetBoolean());
    }

    [Theory]
    [InlineData("SUCCESS", "COMPLETED", "FAILURE", "push", 1)]
    [InlineData("SUCCESS", "COMPLETED", "CANCELLED", "push", 1)]
    [InlineData("SUCCESS", "IN_PROGRESS", null, "push", 124)]
    [InlineData("CANCELLED", "IN_PROGRESS", null, "push", 124)]
    [InlineData("SUCCESS", "COMPLETED", "FAILURE", "pull_request", 69)]
    [InlineData("SUCCESS", "COMPLETED", "CANCELLED", "pull_request", 69)]
    [InlineData("SUCCESS", "IN_PROGRESS", null, "pull_request", 69)]
    [InlineData("CANCELLED", "IN_PROGRESS", null, "pull_request", 69)]
    public void PrWatchUsesNewRunStateRegardlessOfOldSuccess(string oldConclusion, string status, string? conclusion, string eventName, int exit)
    {
        using var fixture = new PrScriptFixture();
        fixture.SnapshotResponses(Ok(Snapshot("OPEN",
            Check("engineering", status, conclusion, checkId: 102, runId: 202, runNumber: 2, eventName: eventName),
            Check("engineering", "COMPLETED", oldConclusion, eventName: eventName))));
        var result = exit == 124 ? fixture.RunWatch42WithDeadline() : fixture.RunWatch42();
        Assert.Equal(exit, result.ExitCode);
    }

    [Theory]
    [InlineData("push", 124)]
    [InlineData("pull_request", 69)]
    public void PrWatchDoesNotBorrowMissingJobsFromAnOlderRun(string eventName, int exit)
    {
        using var fixture = new PrScriptFixture();
        fixture.SnapshotResponses(Ok(Snapshot("OPEN",
            Check("engineering", "COMPLETED", "SUCCESS", eventName: eventName),
            Check("resolve", "IN_PROGRESS", null, checkId: 102, runId: 202, runNumber: 2, eventName: eventName))));
        var result = exit == 124 ? fixture.RunWatch42WithDeadline() : fixture.RunWatch42();
        Assert.Equal(exit, result.ExitCode);
        if (exit == 124)
            Assert.Contains("pending=0 missing=1", Text(result.StandardOutput), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("push", 124)]
    [InlineData("pull_request", 69)]
    public void PrWatchCannotFillAnOriginsMissingCurrentJobFromAnotherOrigin(string eventName, int exit)
    {
        using var fixture = new PrScriptFixture();
        fixture.SnapshotResponses(Ok(Snapshot("OPEN",
            Check("engineering", "COMPLETED", "SUCCESS", eventName: eventName), Context("engineering", "SUCCESS"),
            Check("resolve", "IN_PROGRESS", null, checkId: 102, runId: 202, runNumber: 2, eventName: eventName))));
        var result = exit == 124 ? fixture.RunWatch42WithDeadline() : fixture.RunWatch42();
        Assert.Equal(exit, result.ExitCode);
    }

    [Fact]
    public void PrWatchOrdersExecutionsByRunNumberRatherThanJobOrRunId()
    {
        using var fixture = new PrScriptFixture();
        fixture.SnapshotResponses(Ok(Snapshot("OPEN",
            Check("engineering", "COMPLETED", "FAILURE", checkId: 900, runId: 900, runNumber: 1, eventName: "push"),
            Check("engineering", "COMPLETED", "SUCCESS", checkId: 100, runId: 100, runNumber: 2, eventName: "push"))));
        Assert.Equal(0, fixture.RunWatch42().ExitCode);
    }

    [Theory]
    [InlineData("app")]
    [InlineData("workflow")]
    [InlineData("event")]
    [InlineData("branch")]
    [InlineData("external")]
    [InlineData("status")]
    [InlineData("deleted-branch")]
    public void PrWatchPreservesFailuresFromOtherOrigins(string origin)
    {
        using var fixture = new PrScriptFixture();
        var old = JsonSerializer.SerializeToNode(Check("engineering", "COMPLETED", "FAILURE"))!;
        switch (origin)
        {
            case "app": old["checkSuite"]!["app"]!["id"] = "other-app"; break;
            case "workflow": old["checkSuite"]!["workflowRun"]!["workflow"]!["id"] = "other-workflow"; break;
            case "event": old["checkSuite"]!["workflowRun"]!["event"] = "push"; break;
            case "branch": old["checkSuite"]!["branch"]!["id"] = "other-repository-or-branch"; break;
            case "external": old["checkSuite"]!["workflowRun"] = null; break;
            case "status": old = JsonSerializer.SerializeToNode(Context("engineering", "FAILURE"))!; break;
            case "deleted-branch": old["checkSuite"]!["branch"] = null; break;
        }
        fixture.SnapshotResponses(Ok(Snapshot("OPEN", old,
            Check("engineering", "COMPLETED", "SUCCESS", checkId: 102, runId: 202, runNumber: 2))));
        Assert.Equal(1, fixture.RunWatch42().ExitCode);
    }

    [Fact]
    public void PrWatchDoesNotInferJobAttemptFromWorkflowAttempt()
    {
        using var fixture = new PrScriptFixture();
        fixture.SnapshotResponses(Ok(Snapshot("OPEN",
            Check("engineering", "COMPLETED", "CANCELLED", runAttempt: 2),
            Check("engineering", "COMPLETED", "SUCCESS", checkId: 102, runAttempt: 2))));
        Assert.Equal(1, fixture.RunWatch42().ExitCode);
    }

    [Theory]
    [InlineData("run-number-collision")]
    [InlineData("run-id-collision")]
    [InlineData("inconsistent-origin")]
    [InlineData("inconsistent-attempt")]
    [InlineData("older-run-reattempted")]
    public void PrWatchRejectsAmbiguousRunVersions(string defect)
    {
        using var fixture = new PrScriptFixture();
        var newer = JsonSerializer.SerializeToNode(Check("engineering", "COMPLETED", "SUCCESS",
            checkId: 102, runId: 202, runNumber: 2, eventName: "push"))!;
        var older = JsonSerializer.SerializeToNode(Check("engineering", "COMPLETED", "CANCELLED", eventName: "push"))!;
        var run = newer["checkSuite"]!["workflowRun"]!;
        switch (defect)
        {
            case "run-number-collision": run["runNumber"] = 1; break;
            case "run-id-collision": run["databaseId"] = 201; break;
            case "inconsistent-origin": run["databaseId"] = 201; run["runNumber"] = 1; run["event"] = "pull_request"; break;
            case "inconsistent-attempt": run["databaseId"] = 201; run["runNumber"] = 1; run["runAttempt"] = 2; break;
            case "older-run-reattempted": older["checkSuite"]!["workflowRun"]!["runAttempt"] = 2; break;
        }
        fixture.SnapshotResponses(Ok(Snapshot("OPEN", older, newer)));
        Assert.Equal(69, fixture.RunWatch42().ExitCode);
    }
}
