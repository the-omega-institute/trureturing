using System.Text.Json;
using System.Text.Json.Nodes;
using System.IO.Compression;
using System.Text;

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
        AddOrigin(fixture, [older], 42);
        AddOrigin(fixture, [newer], 43);

        var result = fixture.RunWatch42();

        Assert.True(result.ExitCode == 69, $"watcher_exit={result.ExitCode}\n" + Text(result.StandardOutput) + Text(result.StandardError));
        Assert.DoesNotContain("outcome=green", Text(result.StandardOutput), StringComparison.Ordinal);
        Assert.Contains("reason=ambiguous-pr-origin", Text(result.StandardError), StringComparison.Ordinal);
        Assert.Equal(3, fixture.Invocations.Count(IsSnapshotInvocation));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void PrWatchRejectsCrossPrOriginsWhenOriginEnumerationFailsBeforeAnyRow(bool reverse)
    {
        using var fixture = new PrScriptFixture();
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
        AddOrigin(fixture, [older], 42);
        AddOrigin(fixture, [newer], 43);
        fixture.FailOriginEnumeration();
        fixture.SnapshotResponses(Ok(Snapshot("OPEN", reverse ? [newer, older] : [older, newer])));

        var result = fixture.RunWatch42();

        Assert.Equal(69, result.ExitCode);
        Assert.DoesNotContain("outcome=green", Text(result.StandardOutput), StringComparison.Ordinal);
        Assert.Contains("reason=ambiguous-pr-origin", Text(result.StandardError), StringComparison.Ordinal);
        Assert.DoesNotContain(fixture.Invocations, invocation => invocation.Contains("/attempts/", StringComparison.Ordinal));
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

    [Fact]
    public void PrWatchWaitsForStaleHeadBeforeRejectingRerunOrdering()
    {
        using var fixture = new PrScriptFixture();
        fixture.SnapshotResponses(Ok(Snapshot("OPEN", OldHeadSha, HeadSha,
            Check("engineering", "COMPLETED", "CANCELLED", runAttempt: 2),
            Check("engineering", "COMPLETED", "SUCCESS", checkId: 102, runId: 202, runNumber: 2))));

        var result = fixture.RunWatch("--pr", "42", "--head-sha", HeadSha,
            "--interval-seconds", "1", "--timeout-seconds", "2");

        Assert.Equal(124, result.ExitCode);
        Assert.Contains("state=stale", Text(result.StandardError), StringComparison.Ordinal);
        Assert.DoesNotContain("reason=ambiguous-pr-origin", Text(result.StandardError), StringComparison.Ordinal);
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

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void PrWatchAcceptsSamePrSystemOrigins(bool reverse)
    {
        using var fixture = new PrScriptFixture();
        var old = Check("engineering", "COMPLETED", "CANCELLED");
        var current = Check("engineering", "COMPLETED", "SUCCESS", checkId: 102, runId: 202, runNumber: 2);
        AddOrigin(fixture, [old], 42);
        AddOrigin(fixture, [current], 42);
        fixture.SnapshotResponses(Ok(Snapshot("OPEN", reverse ? [current, old] : [old, current])));
        var result = fixture.RunWatch42();
        Assert.True(result.ExitCode == 0, $"watcher_exit={result.ExitCode}\n" + Text(result.StandardOutput) + Text(result.StandardError));
        Assert.Contains("outcome=green", Text(result.StandardOutput), StringComparison.Ordinal);
        Assert.Equal(2, fixture.Invocations.Count(x => x.Contains("/attempts/1/logs", StringComparison.Ordinal)));
    }

    [Theory]
    [InlineData(42, 43, 0)]
    [InlineData(43, 42, 69)]
    public void PrWatchUsesFirstRootRatherThanNestedLeaf(int rootPr, int leafPr, int exit)
    {
        using var fixture = new PrScriptFixture();
        var old = Check("engineering", "COMPLETED", "CANCELLED");
        var current = Check("engineering", "COMPLETED", "SUCCESS", checkId: 102, runId: 202, runNumber: 2);
        AddOrigin(fixture, [old], 42);
        var leaf = $"foreign/project/.github/workflows/leaf.yml@refs/pull/{leafPr}/merge";
        var root = $"owner/repo/.github/workflows/root.yml@refs/pull/{rootPr}/merge";
        AddOrigin(fixture, [current], rootPr, entries: [("engineering/system.txt", SystemRecord(
            $"Job defined at: {leaf}", "Reusable workflow chain:", $"{root} ({HeadSha})",
            $"-> owner/repo/.github/workflows/middle.yml@refs/heads/main ({OldHeadSha})", $"-> {leaf} ({HeadSha})"))]);
        fixture.SnapshotResponses(Ok(Snapshot("OPEN", old, current)));
        var result = fixture.RunWatch42();
        Assert.True(result.ExitCode == exit, $"watcher_exit={result.ExitCode}\n" + Text(result.StandardError));
    }

    [Theory]
    [InlineData("stdout")]
    [InlineData("unknown")]
    [InlineData("malformed-ref")]
    [InlineData("missing-root")]
    [InlineData("conflicting-root")]
    [InlineData("duplicate-member")]
    [InlineData("unsafe-path")]
    [InlineData("unknown-job")]
    [InlineData("colliding-job")]
    [InlineData("wrong-head")]
    [InlineData("wrong-attempt")]
    [InlineData("wrong-run")]
    [InlineData("wrong-workflow")]
    [InlineData("wrong-repository")]
    [InlineData("wrong-suite")]
    [InlineData("current-reattempt")]
    [InlineData("missing-job")]
    [InlineData("partial-jobs")]
    [InlineData("duplicate-job")]
    [InlineData("nonzip")]
    public void PrWatchRejectsInvalidSystemOriginEvidence(string defect)
    {
        using var fixture = new PrScriptFixture();
        var old = Check("engineering", "COMPLETED", "CANCELLED");
        var current = Check("engineering", "COMPLETED", "SUCCESS", checkId: 102, runId: 202, runNumber: 2);
        AddOrigin(fixture, [old], 42);
        var root = "owner/repo/.github/workflows/root.yml@refs/pull/42/merge";
        var good = SystemRecord("Job defined at: " + root);
        var entries = new List<(string, string)> { ("engineering/system.txt", good) };
        switch (defect)
        {
            case "stdout": entries = [("0_engineering.txt", good)]; break;
            case "unknown": entries = [("engineering/system.txt", SystemRecord("Job source: " + root))]; break;
            case "malformed-ref": entries = [("engineering/system.txt", SystemRecord("Job defined at: " + root + "/suffix"))]; break;
            case "missing-root": entries = [("engineering/system.txt", SystemRecord("Job defined at: " + root,
                "Reusable workflow chain:", $"-> {root} ({HeadSha})"))]; break;
            case "conflicting-root": entries.Add(("setup/system.txt", SystemRecord("Job defined at: " + root.Replace("/42/", "/43/")))); break;
            case "duplicate-member": entries.Add(("engineering/system.txt", good)); break;
            case "unsafe-path": entries.Add(("../engineering/system.txt", good)); break;
            case "unknown-job": entries = [("alien/system.txt", good)]; break;
        }
        AddOrigin(fixture, [current], 42, entries: entries.ToArray(), defect: defect);
        fixture.SnapshotResponses(Ok(Snapshot("OPEN", old, current)));
        var result = fixture.RunWatch42();
        Assert.True(result.ExitCode == 69, $"watcher_exit={result.ExitCode}\n" + Text(result.StandardOutput) + Text(result.StandardError));
        Assert.DoesNotContain("outcome=green", Text(result.StandardOutput), StringComparison.Ordinal);
    }

    [Fact]
    public void PrWatchRejectsNulTruncatedOriginalArchiveName()
    {
        using var fixture = new PrScriptFixture();
        var old = Check("engineering", "COMPLETED", "CANCELLED");
        var current = Check("engineering", "COMPLETED", "SUCCESS", checkId: 102, runId: 202, runNumber: 2);
        AddOrigin(fixture, [old], 42);
        AddOrigin(fixture, [current], 42, defect: "nul-name");
        fixture.SnapshotResponses(Ok(Snapshot("OPEN", old, current)));

        var result = fixture.RunWatch42();

        Assert.Equal(69, result.ExitCode);
        Assert.DoesNotContain("outcome=green", Text(result.StandardOutput), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("FAILURE", 1)]
    [InlineData(null, 124)]
    public void PrWatchPreservesNewStateAfterOriginCertification(string? conclusion, int exit)
    {
        using var fixture = new PrScriptFixture();
        var old = Check("engineering", "COMPLETED", "SUCCESS");
        var current = Check("engineering", conclusion is null ? "IN_PROGRESS" : "COMPLETED", conclusion,
            checkId: 102, runId: 202, runNumber: 2);
        AddOrigin(fixture, [old], 42);
        AddOrigin(fixture, [current], 42);
        fixture.SnapshotResponses(Ok(Snapshot("OPEN", old, current)));
        var result = exit == 124 ? fixture.RunWatch42WithDeadline() : fixture.RunWatch42();
        Assert.True(result.ExitCode == exit, Text(result.StandardError));
    }

    [Fact]
    public void PrWatchKeepsMissingCurrentJobAfterOriginCertification()
    {
        using var fixture = new PrScriptFixture();
        var old = Check("engineering", "COMPLETED", "SUCCESS");
        var current = Check("preparation", "IN_PROGRESS", null, checkId: 102, runId: 202, runNumber: 2);
        AddOrigin(fixture, [old], 42);
        AddOrigin(fixture, [current], 42);
        fixture.SnapshotResponses(Ok(Snapshot("OPEN", old, current)));
        var result = fixture.RunWatch42WithDeadline();
        Assert.Equal(124, result.ExitCode);
        Assert.Contains("pending=0 missing=1", Text(result.StandardOutput), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void PrWatchAcceptsHistoricalPairWithSystemRecords(bool reverse)
    {
        using var fixture = new PrScriptFixture();
        const string head = "f9139835b80bce712b50dd9a77396a83abf167c9";
        var names = new[] { "push / engineering", "push / current", "delta" };
        fixture.RequiredResponses(Ok(Required(names)));
        var oldIds = new long[] { 106217103031, 106217103546, 106217104145 };
        var newIds = new long[] { 106217240674, 106217240777, 106217309734 };
        var old = names.Select((name, i) => Check(name, "COMPLETED", "CANCELLED", head, oldIds[i], 35562164528, 1353)).ToArray();
        var current = names.Select((name, i) => Check(name, "COMPLETED", "SUCCESS", head, newIds[i], 35562213366, 1354)).ToArray();
        AddOrigin(fixture, old, 9253);
        AddOrigin(fixture, current, 9253);
        var items = old.Concat(current).ToArray();
        fixture.SnapshotResponses(Ok(Snapshot("MERGED", head, head, reverse ? items.Reverse().ToArray() : items)));
        var result = fixture.RunWatch("--pr", "9253", "--head-sha", head, "--interval-seconds", "1");
        Assert.True(result.ExitCode == 0, Text(result.StandardError));
    }

    private static string SystemRecord(params string[] messages) => string.Join("\n",
        messages.Select(x => "2026-09-21T04:45:47.6680000Z " + x)) + "\n";

    private static byte[] NulArchiveName(byte[] archive)
    {
        var bytes = (byte[])archive.Clone();
        var original = Encoding.UTF8.GetBytes("engineering/system.txtXa");
        var replacement = Encoding.UTF8.GetBytes("engineering/system.txt\0a");
        var matches = 0;
        for (var offset = 0; offset <= bytes.Length - original.Length; offset++)
        {
            if (!bytes.AsSpan(offset, original.Length).SequenceEqual(original)) continue;
            replacement.CopyTo(bytes.AsSpan(offset, replacement.Length));
            matches++;
        }
        Assert.Equal(2, matches);
        return bytes;
    }

    private static void AddOrigin(PrScriptFixture fixture, object[] checks, int pr,
        (string Name, string Text)[]? entries = null, string defect = "")
    {
        var nodes = checks.Select(x => JsonSerializer.SerializeToNode(x)!).ToArray();
        var run = nodes[0]["checkSuite"]!["workflowRun"]!;
        var runId = run["databaseId"]!.GetValue<long>();
        var head = nodes[0]["checkSuite"]!["commit"]!["oid"]!.GetValue<string>();
        var metadata = JsonSerializer.SerializeToNode(new
        {
            id = runId, run_attempt = 1, run_number = run["runNumber"]!.GetValue<int>(),
            head_sha = head, @event = "pull_request", workflow_id = 301,
            check_suite_id = runId + 1000, repository = new { id = 401, full_name = "owner/repo" },
            path = ".github/workflows/root.yml",
        })!;
        var jobs = nodes.Select(x => JsonSerializer.SerializeToNode(new
        {
            id = x["databaseId"]!.GetValue<long>(), name = x["name"]!.GetValue<string>(),
            run_id = runId, run_attempt = 1, head_sha = head,
        })!).ToList();
        jobs.Add(JsonSerializer.SerializeToNode(new { id = runId + 10000, name = "setup", run_id = runId, run_attempt = 1, head_sha = head })!);
        switch (defect)
        {
            case "wrong-head": metadata["head_sha"] = OldHeadSha; break;
            case "wrong-attempt": metadata["run_attempt"] = 2; break;
            case "wrong-run": metadata["id"] = 999; break;
            case "wrong-workflow": metadata["workflow_id"] = 999; break;
            case "wrong-repository": metadata["repository"]!["id"] = 999; break;
            case "wrong-suite": metadata["check_suite_id"] = 999; break;
            case "missing-job": jobs.RemoveAt(0); break;
            case "duplicate-job": jobs.Add(jobs[0].DeepClone()); break;
            case "colliding-job": jobs.Add(JsonSerializer.SerializeToNode(new { id = 999, name = "engineering", run_id = runId, run_attempt = 1, head_sha = head })!); break;
        }
        var endpoint = $"repos/owner/repo/actions/runs/{runId}";
        fixture.ApiResponse(endpoint + "/attempts/1", metadata.ToJsonString());
        if (defect == "current-reattempt") metadata["run_attempt"] = 2;
        fixture.ApiResponse(endpoint, metadata.ToJsonString());
        fixture.ApiResponse(endpoint + "/attempts/1/jobs?per_page=100&page=1",
            JsonSerializer.Serialize(new { total_count = jobs.Count + (defect == "partial-jobs" ? 1 : 0), jobs }));
        entries ??= [((defect == "nul-name" ? "engineering/system.txtXa" : nodes[0]["name"]!.GetValue<string>().Replace('/', '_') + "/system.txt"),
            SystemRecord($"Job defined at: owner/repo/.github/workflows/root.yml@refs/pull/{pr}/merge"))];
        using var stream = new MemoryStream();
        using (var zip = new ZipArchive(stream, ZipArchiveMode.Create, leaveOpen: true))
            foreach (var (name, text) in entries)
            {
                using var writer = new StreamWriter(zip.CreateEntry(name).Open(), new UTF8Encoding(false));
                writer.Write(text);
            }
        var archive = stream.ToArray();
        if (defect == "nul-name")
            archive = NulArchiveName(archive);
        fixture.ApiResponse(endpoint + "/attempts/1/logs", defect == "nonzip" ? Encoding.UTF8.GetBytes("not a zip") : archive);
    }
}
