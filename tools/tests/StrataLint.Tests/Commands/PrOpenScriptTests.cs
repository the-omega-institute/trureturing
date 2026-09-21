using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class PrOpenScriptTests
{
    private const string DeadlineBehaviorTimeoutSeconds = "30";
    private const string HeadSha = "2222222222222222222222222222222222222222";
    private const string OldHeadSha = "1111111111111111111111111111111111111111";

    [Theory]
    [InlineData("SUCCESS", "FAILURE", 1)]
    [InlineData("FAILURE", "SUCCESS", 0)]
    public void PrWatchWaitsForExpectedHeadBeforeDeciding(string oldConclusion, string conclusion, int exitCode)
    {
        using var fixture = new PrScriptFixture();
        fixture.SnapshotResponses(
            Ok(BoundSnapshot(OldHeadSha, HeadSha, Check("engineering", "COMPLETED", oldConclusion))),
            Ok(BoundSnapshot(HeadSha, HeadSha, Check("engineering", "COMPLETED", conclusion))));

        var result = fixture.RunWatch42();

        Assert.Equal(exitCode, result.ExitCode);
        Assert.Equal(2, fixture.Invocations.Count(IsSnapshotInvocation));
        Assert.Contains("head_sha=" + HeadSha, Text(result.StandardOutput), StringComparison.Ordinal);
        Assert.Contains("expected_head=" + HeadSha + " observed_head=" + OldHeadSha,
            Text(result.StandardError), StringComparison.Ordinal);
        Assert.All(fixture.Invocations.Where(IsSnapshotInvocation), invocation =>
            Assert.Contains("-f head=" + HeadSha, invocation, StringComparison.Ordinal));
    }

    [Theory]
    [InlineData("object")]
    [InlineData("check")]
    [InlineData("status")]
    public void PrWatchRejectsMixedCommitIdentities(string mismatch)
    {
        using var fixture = new PrScriptFixture();
        var item = mismatch == "status"
            ? Context("engineering", "SUCCESS", OldHeadSha)
            : Check("engineering", "COMPLETED", "SUCCESS", mismatch == "check" ? OldHeadSha : HeadSha);
        fixture.SnapshotResponses(Ok(BoundSnapshot(HeadSha, mismatch == "object" ? OldHeadSha : HeadSha, item)));

        Assert.Equal(69, fixture.RunWatch42().ExitCode);
    }

    [Fact]
    public void PrWatchRequiresAnExplicitCommitWithoutCallingGh()
    {
        using var fixture = new PrScriptFixture();
        Assert.Equal(2, fixture.RunWatch("--pr", "42").ExitCode);
        foreach (var head in new[] { "", "HEAD", "2222222", new string('z', 40) })
            Assert.Equal(2, fixture.RunWatch("--pr", "42", "--head-sha", head).ExitCode);
        Assert.Empty(fixture.Invocations);
    }

    [Theory]
    [InlineData("missing-pr-head")]
    [InlineData("missing-check-id")]
    [InlineData("missing-run-field")]
    [InlineData("invalid-run-id")]
    [InlineData("missing-status-id")]
    [InlineData("partial-errors")]
    [InlineData("truncated-contexts")]
    [InlineData("missing-app")]
    [InlineData("empty-app-id")]
    [InlineData("missing-workflow")]
    [InlineData("missing-run-number")]
    [InlineData("invalid-run-number")]
    [InlineData("invalid-run-attempt")]
    [InlineData("missing-event")]
    [InlineData("missing-branch")]
    [InlineData("missing-branch-id")]
    public void PrWatchCannotDecideFromIncompleteIdentityOrResponse(string defect)
    {
        using var fixture = new PrScriptFixture();
        var snapshot = JsonNode.Parse(Snapshot("OPEN", Check("engineering", "COMPLETED", "FAILURE"),
            Context("other", "SUCCESS")))!;
        var repo = snapshot["data"]!["repository"]!;
        var contexts = repo["object"]!["statusCheckRollup"]!["contexts"]!;
        var check = contexts["nodes"]![0]!;
        switch (defect)
        {
            case "missing-pr-head": repo["pullRequest"]!.AsObject().Remove("headRefOid"); break;
            case "missing-check-id": check.AsObject().Remove("databaseId"); break;
            case "missing-run-field": check["checkSuite"]!.AsObject().Remove("workflowRun"); break;
            case "invalid-run-id": check["checkSuite"]!["workflowRun"]!["databaseId"] = "201"; break;
            case "missing-status-id": contexts["nodes"]![1]!.AsObject().Remove("id"); break;
            case "partial-errors": snapshot["errors"] = JsonNode.Parse("""[{"message":"partial failure"}]"""); break;
            case "truncated-contexts": contexts["pageInfo"]!["hasNextPage"] = true; break;
            case "missing-app": check["checkSuite"]!.AsObject().Remove("app"); break;
            case "empty-app-id": check["checkSuite"]!["app"]!["id"] = ""; break;
            case "missing-workflow": check["checkSuite"]!["workflowRun"]!.AsObject().Remove("workflow"); break;
            case "missing-run-number": check["checkSuite"]!["workflowRun"]!.AsObject().Remove("runNumber"); break;
            case "invalid-run-number": check["checkSuite"]!["workflowRun"]!["runNumber"] = "2"; break;
            case "invalid-run-attempt": check["checkSuite"]!["workflowRun"]!["runAttempt"] = 0; break;
            case "missing-event": check["checkSuite"]!["workflowRun"]!.AsObject().Remove("event"); break;
            case "missing-branch": check["checkSuite"]!.AsObject().Remove("branch"); break;
            case "missing-branch-id": check["checkSuite"]!["branch"]!.AsObject().Remove("id"); break;
        }
        fixture.SnapshotResponses(Ok(snapshot.ToJsonString()));

        var result = fixture.RunWatch42();

        Assert.Equal(69, result.ExitCode);
        Assert.DoesNotContain("PR_WATCH_EVIDENCE", Text(result.StandardError), StringComparison.Ordinal);
    }

    [Fact]
    public void PrWatchReportsActualCheckAndRunIdentitiesAndAllowsExternalChecks()
    {
        using var fixture = new PrScriptFixture();
        fixture.RequiredResponses(Ok(Required("engineering", "external", "status")));
        var snapshot = JsonNode.Parse(Snapshot("OPEN", Check("engineering", "COMPLETED", "SUCCESS"),
            Check("external", "COMPLETED", "SUCCESS"), Context("status", "SUCCESS")))!;
        var external = snapshot["data"]!["repository"]!["object"]!["statusCheckRollup"]!["contexts"]!["nodes"]![1]!;
        external["databaseId"] = 102;
        external["checkSuite"]!["workflowRun"] = null;
        fixture.SnapshotResponses(Ok(snapshot.ToJsonString()));

        var result = fixture.RunWatch42();

        Assert.Equal(0, result.ExitCode);
        var line = Text(result.StandardError).Split('\n').Single(value => value.StartsWith("PR_WATCH_EVIDENCE", StringComparison.Ordinal));
        var evidence = JsonNode.Parse(line[(line.IndexOf("checks=", StringComparison.Ordinal) + "checks=".Length)..])!.AsArray();
        Assert.Equal(101, evidence[0]!["check_id"]!.GetValue<int>());
        Assert.Equal(201, evidence[0]!["run_id"]!.GetValue<int>());
        Assert.Equal(102, evidence[1]!["check_id"]!.GetValue<int>());
        Assert.Null(evidence[1]!["run_id"]);
        Assert.Equal("status-101", evidence[2]!["check_id"]!.GetValue<string>());
        Assert.All(evidence, item => Assert.Equal(HeadSha, item!["commit"]!.GetValue<string>()));
        Assert.All(fixture.Invocations, invocation => Assert.EndsWith("|token=none", invocation, StringComparison.Ordinal));
    }

    [Fact]
    public void PrWatchWaitsUntilDeadlineForStaleClosedHead()
    {
        using var fixture = new PrScriptFixture();
        fixture.SnapshotResponses(Ok(Snapshot("CLOSED", OldHeadSha, HeadSha, Check("engineering", "COMPLETED", "FAILURE"))));
        Assert.Equal(124, fixture.RunWatch42WithDeadline().ExitCode);
    }

    [Fact]
    public void PrWatchTreatsNullRollupAsMissingChecks()
    {
        using var fixture = new PrScriptFixture();
        var snapshot = JsonNode.Parse(Snapshot("OPEN"))!;
        snapshot["data"]!["repository"]!["object"]!["statusCheckRollup"] = null;
        fixture.SnapshotResponses(Ok(snapshot.ToJsonString()));
        var result = fixture.RunWatch42WithDeadline();
        Assert.Equal(124, result.ExitCode);
        Assert.Contains("pending=0 missing=1", Text(result.StandardOutput), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("topic", "owner")]
    [InlineData("fork:topic", "fork")]
    public void PrOpenFreezesExplicitRemoteBranchBeforeCreating(string branch, string owner)
    {
        using var fixture = new PrScriptFixture();
        fixture.HeadResponses(Ok(HeadResponse(OldHeadSha)));
        fixture.SnapshotResponses(Ok(Snapshot("OPEN", OldHeadSha, OldHeadSha,
            Check("engineering", "COMPLETED", "SUCCESS", OldHeadSha))));
        var result = fixture.RunOpen("--head", branch, "--message-file", fixture.Message("title\n"));

        Assert.Equal(0, result.ExitCode);
        Assert.Contains("-f owner=" + owner + " -f repo=repo -f ref=refs/heads/topic", fixture.Invocations[0], StringComparison.Ordinal);
        Assert.StartsWith("pr create ", fixture.Invocations[1], StringComparison.Ordinal);
        Assert.Contains("-f head=" + OldHeadSha, Assert.Single(fixture.Invocations, IsSnapshotInvocation), StringComparison.Ordinal);
        Assert.Contains("head_sha=" + OldHeadSha, Text(result.StandardOutput), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("{}")]
    [InlineData("{\"data\":null}")]
    [InlineData("{\"errors\":[{\"message\":\"unavailable\"}]}")]
    public void PrOpenCannotCreateWithoutResolvingExplicitHead(string response)
    {
        using var fixture = new PrScriptFixture();
        fixture.HeadResponses(Ok(response));
        Assert.Equal(69, fixture.RunOpen("--head", "topic", "--message-file", fixture.Message("title\n")).ExitCode);
        Assert.Single(fixture.Invocations);
        Assert.DoesNotContain(fixture.Invocations, invocation => invocation.StartsWith("pr create ", StringComparison.Ordinal));
    }

    [Fact]
    public void PrWatchConsumesNestedBranchProtectionNamesWithoutFlattening()
    {
        using var fixture = new PrScriptFixture();
        fixture.RequiredResponses(Ok(Required("push / engineering", "push / current", "delta")));
        fixture.SnapshotResponses(Ok(Snapshot("OPEN",
            Check("push / engineering", "COMPLETED", "SUCCESS"),
            Context("push / current", "SUCCESS"), Check("delta", "COMPLETED", "SUCCESS"),
            Check("current", "COMPLETED", "FAILURE"))));

        var result = fixture.RunWatch42();

        Assert.Equal(0, result.ExitCode);
        Assert.Equal($"PR_WATCH_RESULT pr=42 outcome=green head_sha={HeadSha}\n", Text(result.StandardOutput));
    }

    [Fact]
    public void PrWatchKeepsNestedFailureEvenWhenDirectChecksPass()
    {
        using var fixture = new PrScriptFixture();
        fixture.RequiredResponses(Ok(Required("push / engineering", "push / current", "delta")));
        fixture.SnapshotResponses(Ok(Snapshot("OPEN",
            Check("push / engineering", "COMPLETED", "FAILURE"),
            Check("push / current", "IN_PROGRESS", null), Check("delta", "IN_PROGRESS", null),
            Check("engineering", "COMPLETED", "SUCCESS"), Check("current", "COMPLETED", "SUCCESS"))));

        var result = fixture.RunWatch42();

        Assert.Equal(1, result.ExitCode);
        Assert.Equal($"PR_WATCH_RESULT pr=42 outcome=red check=push / engineering state=FAILURE head_sha={HeadSha}\n",
            Text(result.StandardOutput));
    }

    [Fact]
    public void PrWatchWaitsForNestedChecksWhenOnlyDirectChecksExist()
    {
        using var fixture = new PrScriptFixture();
        fixture.RequiredResponses(Ok(Required("push / engineering", "push / current", "delta")));
        fixture.SnapshotResponses(
            Ok(Snapshot("OPEN", Check("engineering", "COMPLETED", "SUCCESS"),
                Check("current", "COMPLETED", "SUCCESS"), Check("delta", "COMPLETED", "SUCCESS"))),
            Ok(Snapshot("OPEN", Check("push / engineering", "COMPLETED", "SUCCESS"),
                Check("push / current", "COMPLETED", "FAILURE"), Check("delta", "COMPLETED", "SUCCESS"))));

        Assert.Equal(1, fixture.RunWatch42().ExitCode);
        Assert.Equal(2, fixture.Invocations.Count(IsSnapshotInvocation));
    }

    [Fact]
    public void PrWatchRejectsMissingOrInvalidPullRequestNumber()
    {
        using var fixture = new PrScriptFixture();
        var results = new[]
        {
            fixture.RunWatch("--head-sha", HeadSha), fixture.RunWatch("--head-sha", HeadSha, "--pr", "0"),
            fixture.RunWatch("--head-sha", HeadSha, "--pr", "-1"), fixture.RunWatch("--head-sha", HeadSha, "--pr", "nope"),
            fixture.RunWatch("--head-sha", HeadSha, "--pr", "42", "--unknown"),
            fixture.RunWatch("--head-sha", HeadSha, "--pr", "42", "--timeout-seconds", "0"),
            fixture.RunWatch("--head-sha", HeadSha, "--pr", "42", "--interval-seconds", "1.5"),
        };
        Assert.All(results, result =>
        {
            Assert.Equal(2, result.ExitCode);
            Assert.Contains("pr.sh watch", Text(result.StandardError), StringComparison.Ordinal);
        });
        Assert.Empty(fixture.Invocations);
    }
    [Fact]
    public void PrWatchReturnsQueryUnavailableWhenRequiredSetQueryFails()
    {
        using var fixture = new PrScriptFixture();
        fixture.RequiredResponses(Fail(), Fail(), Fail());
        var result = fixture.RunWatch42();
        Assert.Equal(69, result.ExitCode);
        Assert.Equal($"PR_WATCH_RESULT pr=42 outcome=query-unavailable step=required-set attempts=3 head_sha={HeadSha}\n", Text(result.StandardOutput));
    }
    [Fact]
    public void PrWatchReturnsQueryUnavailableWhenSuccessfulGhProducesEmptyStdout()
    {
        using var fixture = new PrScriptFixture();
        fixture.RequiredResponses(Ok(""), Ok(""), Ok(""));
        Assert.Equal(69, fixture.RunWatch42().ExitCode);
    }
    [Fact]
    public void PrWatchReadsProtectedBranchWithLocalCredentials()
    {
        using var fixture = new PrScriptFixture();
        Assert.Equal(0, fixture.RunWatch42().ExitCode);
        Assert.Equal("api repos/owner/repo/branches/dev|token=none", fixture.Invocations[0]);
    }
    [Theory]
    [InlineData("{")]
    [InlineData("null")]
    [InlineData("[]")]
    [InlineData("{}")]
    [InlineData("""{"protection":{"required_status_checks":{"contexts":[],"checks":[]}}}""")]
    [InlineData("""{"protected":null,"protection":{"required_status_checks":{"contexts":[],"checks":[]}}}""")]
    [InlineData("""{"protected":false,"protection":{"required_status_checks":{"contexts":[],"checks":[]}}}""")]
    [InlineData("""{"protected":"true","protection":{"required_status_checks":{"contexts":[],"checks":[]}}}""")]
    [InlineData("""{"protected":true}""")]
    [InlineData("""{"protected":true,"protection":null}""")]
    [InlineData("""{"protected":true,"protection":[]}""")]
    [InlineData("""{"protected":true,"protection":{}}""")]
    [InlineData("""{"protected":true,"protection":{"required_status_checks":null}}""")]
    [InlineData("""{"protected":true,"protection":{"required_status_checks":[]}}""")]
    [InlineData("""{"protected":true,"protection":{"required_status_checks":{"checks":[{"context":"valid"}]}}}""")]
    [InlineData("""{"protected":true,"protection":{"required_status_checks":{"contexts":null,"checks":[{"context":"valid"}]}}}""")]
    [InlineData("""{"protected":true,"protection":{"required_status_checks":{"contexts":"valid","checks":[]}}}""")]
    [InlineData("""{"protected":true,"protection":{"required_status_checks":{"contexts":["valid",""],"checks":[]}}}""")]
    [InlineData("""{"protected":true,"protection":{"required_status_checks":{"contexts":["valid",null],"checks":[]}}}""")]
    [InlineData("""{"protected":true,"protection":{"required_status_checks":{"contexts":["valid",7],"checks":[]}}}""")]
    [InlineData("""{"protected":true,"protection":{"required_status_checks":{"contexts":["valid"]}}}""")]
    [InlineData("""{"protected":true,"protection":{"required_status_checks":{"contexts":["valid"],"checks":null}}}""")]
    [InlineData("""{"protected":true,"protection":{"required_status_checks":{"contexts":["valid"],"checks":{}}}}""")]
    [InlineData("""{"protected":true,"protection":{"required_status_checks":{"contexts":["valid"],"checks":["valid"]}}}""")]
    [InlineData("""{"protected":true,"protection":{"required_status_checks":{"contexts":["valid"],"checks":[{"context":"valid"},null]}}}""")]
    [InlineData("""{"protected":true,"protection":{"required_status_checks":{"contexts":["valid"],"checks":[{}]}}}""")]
    [InlineData("""{"protected":true,"protection":{"required_status_checks":{"contexts":["valid"],"checks":[{"context":null}]}}}""")]
    [InlineData("""{"protected":true,"protection":{"required_status_checks":{"contexts":["valid"],"checks":[{"context":""}]}}}""")]
    [InlineData("""{"protected":true,"protection":{"required_status_checks":{"contexts":["valid"],"checks":[{"context":7}]}}}""")]
    [InlineData("""{"protected":true,"protection":{"required_status_checks":{"contexts":[],"checks":[]}}} {}""")]
    public void PrWatchRejectsIncompleteOrMalformedRequiredMetadata(string metadata)
    {
        using var fixture = new PrScriptFixture();
        fixture.RequiredResponses(Ok(metadata));
        var result = fixture.RunWatch42();
        Assert.Equal(69, result.ExitCode);
        Assert.Equal($"PR_WATCH_RESULT pr=42 outcome=query-unavailable step=required-set attempts=3 head_sha={HeadSha}\n", Text(result.StandardOutput));
        Assert.Equal(3, fixture.Invocations.Count);
        Assert.DoesNotContain(fixture.Invocations, IsSnapshotInvocation);
    }
    [Fact]
    public void PrWatchRetriesInvalidRequiredMetadataThenUsesValidBranchMetadata()
    {
        using var fixture = new PrScriptFixture();
        fixture.RequiredResponses(Ok("null"), Ok(Required("engineering")));
        var result = fixture.RunWatch42();
        Assert.Equal(0, result.ExitCode);
        Assert.Contains("step=required-set unavailable_attempts=1", Text(result.StandardError), StringComparison.Ordinal);
        Assert.Equal(3, fixture.Invocations.Count);
    }
    [Fact]
    public void PrWatchAcceptsExplicitlyEmptyRequiredArrays()
    {
        using var fixture = new PrScriptFixture();
        fixture.RequiredResponses(Ok(Required()));
        fixture.SnapshotResponses(Ok(Snapshot("OPEN")));
        Assert.Equal(0, fixture.RunWatch42().ExitCode);
        Assert.Equal(2, fixture.Invocations.Count);
    }
    [Fact]
    public void PrWatchWaitsForExactNameUnionFromBothRequiredArrays()
    {
        using var fixture = new PrScriptFixture();
        fixture.RequiredResponses(Ok("""
            {"protected":true,"name":"dev","protection":{"required_status_checks":{
              "enforcement_level":"non_admins","contexts":[" Context only "],
              "checks":[{"context":"Checks only","app_id":1},{"context":"Checks only","app_id":2}]}}}
            """));
        fixture.SnapshotResponses(
            Ok(Snapshot("OPEN", Context("Context only", "SUCCESS"))),
            Ok(Snapshot("OPEN", Context(" Context only ", "SUCCESS"))),
            Ok(Snapshot("OPEN", Context(" Context only ", "SUCCESS"), Check("Checks only", "COMPLETED", "SUCCESS"))));
        var result = fixture.RunWatch42();
        Assert.Equal(0, result.ExitCode);
        Assert.Equal($"PR_WATCH_RESULT pr=42 outcome=green head_sha={HeadSha}\n", Text(result.StandardOutput));
        Assert.Contains("state=OPEN pending=0 missing=2", Text(result.StandardError), StringComparison.Ordinal);
        Assert.Contains("state=OPEN pending=0 missing=1", Text(result.StandardError), StringComparison.Ordinal);
        Assert.Equal(4, fixture.Invocations.Count);
    }
    [Fact]
    public void PrWatchReturnsQueryUnavailableForMalformedJson()
    {
        using var fixture = new PrScriptFixture();
        fixture.SnapshotResponses(Ok("{"));
        Assert.Equal(69, fixture.RunWatch42().ExitCode);
    }
    [Fact]
    public void PrWatchReturnsQueryUnavailableForUnknownCheckEnum()
    {
        using var fixture = new PrScriptFixture();
        fixture.SnapshotResponses(Ok(Snapshot("OPEN", Check("engineering", "COMPLETED", "ACTION_REQUIRED"))));
        Assert.Equal(69, fixture.RunWatch42().ExitCode);
    }
    [Fact]
    public void PrWatchDoesNotDecideRedFromPartiallyUnparseableSnapshot()
    {
        using var fixture = new PrScriptFixture();
        fixture.SnapshotResponses(Ok(Snapshot(
            "OPEN", Check("engineering", "COMPLETED", "FAILURE"), new { __typename = "Mystery" })));
        var result = fixture.RunWatch42();
        Assert.Equal(69, result.ExitCode);
        Assert.DoesNotContain("outcome=red", Text(result.StandardOutput), StringComparison.Ordinal);
    }
    [Fact]
    public void PrWatchReturnsRedImmediatelyWhileOtherRequiredChecksArePending()
    {
        using var fixture = new PrScriptFixture();
        fixture.RequiredResponses(Ok(Required("engineering", "admission")));
        fixture.SnapshotResponses(Ok(Snapshot("OPEN",
            Check("engineering", "COMPLETED", "FAILURE"), Check("admission", "IN_PROGRESS", null))));
        var result = fixture.RunWatch42();
        Assert.Equal(1, result.ExitCode);
        Assert.Equal($"PR_WATCH_RESULT pr=42 outcome=red check=engineering state=FAILURE head_sha={HeadSha}\n", Text(result.StandardOutput));
        Assert.Equal(2, fixture.Invocations.Count);
    }
    [Theory]
    [InlineData("CANCELLED")]
    [InlineData("TIMED_OUT")]
    [InlineData("ERROR")]
    public void PrWatchReturnsRedForCancelledAndTimedOut(string state)
    {
        using var fixture = new PrScriptFixture();
        var item = state == "ERROR" ? Context("engineering", state) : Check("engineering", "COMPLETED", state);
        fixture.SnapshotResponses(Ok(Snapshot("OPEN", item)));
        Assert.Equal(1, fixture.RunWatch42().ExitCode);
    }
    [Theory]
    [InlineData("MERGED")]
    [InlineData("CLOSED")]
    public void PrWatchKeepsObservedRedAheadOfMergedOrClosedInSameSnapshot(string prState)
    {
        using var fixture = new PrScriptFixture();
        fixture.SnapshotResponses(Ok(Snapshot(prState, Check("engineering", "COMPLETED", "FAILURE"))));
        Assert.Equal(1, fixture.RunWatch42().ExitCode);
    }
    [Fact]
    public void PrWatchDoesNotCompleteWhileAFrozenRequiredContextIsMissingFromRollup()
    {
        using var fixture = new PrScriptFixture();
        fixture.RequiredResponses(Ok(Required("engineering", "admission")));
        fixture.SnapshotResponses(Ok(Snapshot("OPEN", Check("engineering", "COMPLETED", "SUCCESS"))));
        var result = fixture.RunWatch42WithDeadline();
        Assert.Equal(124, result.ExitCode);
        Assert.Contains("pending=0 missing=1", Text(result.StandardOutput), StringComparison.Ordinal);
    }
    [Fact]
    public void PrWatchReturnsTimeoutOnlyAfterAValidPendingSnapshot()
    {
        using var fixture = new PrScriptFixture();
        fixture.SnapshotResponses(Ok(Snapshot("OPEN", Check("engineering", "IN_PROGRESS", null))));
        var result = fixture.RunWatch42WithDeadline();
        Assert.Equal(124, result.ExitCode);
        Assert.Contains("outcome=timeout pending=1 missing=0", Text(result.StandardOutput), StringComparison.Ordinal);
    }
    [Fact]
    public void PrWatchReturnsQueryUnavailableWhenDeadlineArrivesDuringFailureStreak()
    {
        using var fixture = new PrScriptFixture();
        fixture.SnapshotResponses(
            Fail(), Ok(Snapshot("OPEN", Check("engineering", "IN_PROGRESS", null))), Fail(delaySeconds: 60));
        var result = fixture.RunWatch42WithDeadline();
        Assert.Equal(69, result.ExitCode);
        Assert.Contains("outcome=query-unavailable step=snapshot attempts=1", Text(result.StandardOutput), StringComparison.Ordinal);
    }
    [Fact]
    public void PrWatchReturnsClosedExitCodeForClosedUnmergedPullRequest()
    {
        using var fixture = new PrScriptFixture();
        fixture.SnapshotResponses(Ok(Snapshot("CLOSED", Check("engineering", "IN_PROGRESS", null))));
        var result = fixture.RunWatch42();
        Assert.Equal(4, result.ExitCode);
        Assert.Contains("outcome=closed", Text(result.StandardOutput), StringComparison.Ordinal);
    }
    [Fact]
    public void PrWatchTreatsFrozenRequiredSetAsImmutableForTheInvocation()
    {
        using var fixture = new PrScriptFixture();
        fixture.RequiredResponses(Ok(Required("engineering")), Ok(Required("engineering", "late-check")));
        fixture.SnapshotResponses(
            Ok(Snapshot("OPEN", Check("engineering", "IN_PROGRESS", null))),
            Ok(Snapshot("OPEN", Check("engineering", "COMPLETED", "SUCCESS"))));
        Assert.Equal(0, fixture.RunWatch42().ExitCode);
        Assert.Single(fixture.Invocations, invocation => invocation.StartsWith("api repos/", StringComparison.Ordinal));
    }
    [Fact]
    public void PrWatchReturnsGreenWhenEveryFrozenRequiredContextIsTerminalWithoutRed()
    {
        using var fixture = new PrScriptFixture();
        fixture.RequiredResponses(Ok(Required("engineering", "lean-inspect", "admission")));
        fixture.SnapshotResponses(Ok(Snapshot("OPEN", Check("engineering", "COMPLETED", "SUCCESS"),
            Check("lean-inspect", "COMPLETED", "NEUTRAL"), Check("admission", "COMPLETED", "SKIPPED"))));
        Assert.Equal(0, fixture.RunWatch42().ExitCode);
    }
    [Fact]
    public void PrWatchDoesNotReturnGreenForMergedPullRequestWhileRequiredCheckIsPending()
    {
        using var fixture = new PrScriptFixture();
        fixture.SnapshotResponses(Ok(Snapshot("MERGED", Check("engineering", "IN_PROGRESS", null))));
        var result = fixture.RunWatch42WithDeadline();
        Assert.Equal(124, result.ExitCode);
        Assert.Contains("outcome=timeout pending=1 missing=0", Text(result.StandardOutput), StringComparison.Ordinal);
    }
    [Fact]
    public void PrWatchRetriesTransientQueryFailureAndThenDecides()
    {
        using var fixture = new PrScriptFixture();
        fixture.SnapshotResponses(Fail(), Fail(), Ok(Snapshot("OPEN", Check("engineering", "COMPLETED", "SUCCESS"))));
        Assert.Equal(0, fixture.RunWatch42().ExitCode);
    }
    [Fact]
    public void PrOpenArmsAutoMergeOnlyWhenRequestedAndWatchesInOneForegroundProcessPrintingNumberFirst()
    {
        using var fixture = new PrScriptFixture();
        var result = fixture.RunOpen(
            "--head", "topic", "--message-file", fixture.Message("A title\n\nbody text\n"),
            "--auto-merge", "--interval-seconds", "1");
        Assert.Equal(0, result.ExitCode);
        Assert.StartsWith($"42\nPR_WATCH_RESULT pr=42 outcome=green head_sha={HeadSha}\n", Text(result.StandardOutput), StringComparison.Ordinal);
        Assert.Equal(5, fixture.Invocations.Count);
        Assert.EndsWith("|token=none", fixture.Invocations[0], StringComparison.Ordinal);
        Assert.EndsWith("|token=app-token", fixture.Invocations[1], StringComparison.Ordinal);
        Assert.Equal($"pr merge 42 --repo owner/repo --auto --merge --match-head-commit {HeadSha}|token=none", fixture.Invocations[2]);
    }
    [Fact]
    public void PrOpenDoesNotArmAutoMergeByDefault()
    {
        using var fixture = new PrScriptFixture();
        var result = fixture.RunOpen(
            "--head", "topic", "--message-file", fixture.Message("title\n"), "--interval-seconds", "1");
        Assert.Equal(0, result.ExitCode);
        Assert.Equal(4, fixture.Invocations.Count);
        Assert.DoesNotContain(fixture.Invocations, IsAutoMergeInvocation);
        Assert.Contains(fixture.Invocations, IsWatchInvocation);
    }
    [Fact]
    public void PrOpenPropagatesWatchExitCodeAfterPrintingNumber()
    {
        using var fixture = new PrScriptFixture();
        fixture.SnapshotResponses(Ok(Snapshot("OPEN", Check("engineering", "COMPLETED", "FAILURE"))));
        var result = fixture.RunOpen("--head", "topic", "--message-file", fixture.Message("title\n"), "--interval-seconds", "1");
        Assert.Equal(1, result.ExitCode);
        Assert.StartsWith("42\nPR_WATCH_RESULT pr=42 outcome=red", Text(result.StandardOutput), StringComparison.Ordinal);
    }
    [Fact]
    public void PrOpenCreateFailureDoesNotCloseAnything()
    {
        using var fixture = new PrScriptFixture { FailStep = "create" };
        var result = fixture.RunOpen("--head", "topic", "--message-file", fixture.Message("title\n"));
        Assert.NotEqual(0, result.ExitCode);
        Assert.Equal(2, fixture.Invocations.Count);
        Assert.DoesNotContain(fixture.Invocations, IsWatchInvocation);
    }
    [Fact]
    public void PrOpenAutoMergeFailureIsFatal()
    {
        using var fixture = new PrScriptFixture { FailStep = "merge" };
        var result = fixture.RunOpen(
            "--head", "topic", "--message-file", fixture.Message("title\n"), "--auto-merge");
        Assert.NotEqual(0, result.ExitCode);
        Assert.Equal(3, fixture.Invocations.Count);
        Assert.DoesNotContain(fixture.Invocations, IsWatchInvocation);
    }
    [Fact]
    public void PrOpenRejectsUnknownArgumentsWithoutCallingGh()
    {
        using var fixture = new PrScriptFixture();
        var result = fixture.RunOpen(
            "--head", "topic", "--message-file", fixture.Message("title\n"), "--unknown");
        Assert.Equal(2, result.ExitCode);
        Assert.Contains("pr.sh open", Text(result.StandardError), StringComparison.Ordinal);
        Assert.Contains("[--auto-merge]", Text(result.StandardError), StringComparison.Ordinal);
        Assert.Empty(fixture.Invocations);
    }
    [Fact]
    public void PrOpenRejectsMissingRequiredArgumentsAndUnusableMessageFile()
    {
        using var fixture = new PrScriptFixture();
        Assert.Equal(2, fixture.RunOpen("--message-file", fixture.Message("title\n")).ExitCode);
        Assert.Equal(2, fixture.RunOpen("--head", "branch").ExitCode);
        Assert.Equal(2, fixture.RunOpen("--head", "branch", "--message-file", fixture.MissingMessage).ExitCode);
        Assert.Equal(2, fixture.RunOpen("--head", "branch", "--message-file", fixture.Message("")).ExitCode);
        Assert.Equal(2, fixture.RunOpen("--head", "branch", "--message-file", fixture.Message("\n\nbody only\n")).ExitCode);
        Assert.Empty(fixture.Invocations);
    }
    [Fact]
    public void PrOpenSplitsTheMessageFileIntoFirstLineTitleAndRemainingBody()
    {
        using var fixture = new PrScriptFixture();
        var result = fixture.RunOpen(
            "--head", "topic", "--message-file", fixture.Message("a title\n\nfirst body line\n\nsecond body line\n"));
        Assert.Equal(0, result.ExitCode);
        Assert.Contains("--title a title --body-file ", fixture.Invocations[1], StringComparison.Ordinal);
        Assert.Equal("first body line\n\nsecond body line\n", fixture.CreatedBody);
    }
    [Fact]
    public void PrOpenPassesShellMetacharactersInTheTitleThroughVerbatim()
    {
        using var fixture = new PrScriptFixture();
        const string title = "pr: make `pr.sh` fail closed on $(shell echo x) and \"quotes\"";
        var result = fixture.RunOpen("--head", "topic", "--message-file", fixture.Message(title + "\n\nbody\n"));
        Assert.Equal(0, result.ExitCode);
        Assert.Contains("--title " + title + " ", fixture.Invocations[1], StringComparison.Ordinal);
    }
    [Fact]
    public void PrOpenSendsAnEmptyBodyWhenTheMessageFileHasOnlyATitle()
    {
        using var fixture = new PrScriptFixture();
        Assert.Equal(0, fixture.RunOpen("--head", "topic", "--message-file", fixture.Message("only a title\n")).ExitCode);
        Assert.Contains("--title only a title --body-file ", fixture.Invocations[1], StringComparison.Ordinal);
        Assert.Equal("", fixture.CreatedBody);
    }
    [Fact]
    public void PrOpenFallsBackToLocalGhWhenAppTokenFails()
    {
        using var fixture = new PrScriptFixture { AppTokenFails = true };
        Assert.Equal(0, fixture.RunOpen("--head", "topic", "--message-file", fixture.Message("title\n")).ExitCode);
        Assert.EndsWith("|token=none", fixture.Invocations[1], StringComparison.Ordinal);
    }
    [Fact]
    public void PrOpenAndPrWatchDefaultsAreTenSecondsAnd4200SecondsAndThreeFailures()
    {
        var script = File.ReadAllText(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools", "scripts", "pr.sh"), Encoding.UTF8);
        Assert.Contains("PR_WATCH_INTERVAL_SECONDS=\"${PR_WATCH_INTERVAL_SECONDS:-10}\"", script, StringComparison.Ordinal);
        Assert.Contains("PR_WATCH_TIMEOUT_SECONDS=\"${PR_WATCH_TIMEOUT_SECONDS:-4200}\"", script, StringComparison.Ordinal);
        Assert.Contains("PR_WATCH_MAX_FAILURES=3", script, StringComparison.Ordinal);
    }
    [Fact]
    public void PrOpenDefaultsToTheRealRepository()
    {
        var script = File.ReadAllText(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools", "scripts", "pr.sh"),
            Encoding.UTF8);
        Assert.Contains("PR_REPO=\"${PR_OPEN_REPO:-the-omega-institute/trureturing}\"", script, StringComparison.Ordinal);
        Assert.Contains("PR_BASE=\"${PR_OPEN_BASE:-dev}\"", script, StringComparison.Ordinal);
        Assert.Equal(1, script.Split("PR_REPO=").Length - 1);
    }
    [Fact]
    public void PrToolDocumentationNoLongerRequiresCallerPolling()
    {
        var text = File.ReadAllText(
            Path.Combine(TestRepositoryLayout.FindRoot(), "CLAUDE.md"), Encoding.UTF8);
        Assert.Contains("`pr.sh` 为 `open`/`watch` 双动词", text, StringComparison.Ordinal);
        Assert.Contains("缺省不 arm auto-merge", text, StringComparison.Ordinal);
        Assert.DoesNotContain("`make pr-open` 自带 auto-merge", text, StringComparison.Ordinal);
        Assert.DoesNotContain("create → App-token 隔离 → arm auto-merge → 等 required-CI 判词", text, StringComparison.Ordinal);
        Assert.DoesNotContain("需要重复由调用方 shell 循环", text, StringComparison.Ordinal);
        Assert.DoesNotContain("单动词(`update`", text, StringComparison.Ordinal);
    }
    private static bool IsAutoMergeInvocation(string invocation) =>
        invocation.StartsWith("pr merge ", StringComparison.Ordinal);
    private static bool IsWatchInvocation(string invocation) =>
        invocation.StartsWith("api repos/", StringComparison.Ordinal) || IsSnapshotInvocation(invocation);
    private static bool IsSnapshotInvocation(string invocation) =>
        invocation.StartsWith("api graphql ", StringComparison.Ordinal) && invocation.Contains("-F pr=", StringComparison.Ordinal);
    private static string Text(byte[] bytes) => Encoding.UTF8.GetString(bytes);
    private static string HeadResponse(string head) => JsonSerializer.Serialize(new
        { data = new { repository = new { @ref = new { target = new { oid = head } } } } });
    private static string Required(params string[] names) => JsonSerializer.Serialize(new
    {
        @protected = true,
        protection = new { required_status_checks = new { contexts = names, checks = names.Select(context => new { context }) } },
    });
    private static object Check(string name, string status, string? conclusion, string head = HeadSha,
        long checkId = 101, long runId = 201, int runNumber = 1, int runAttempt = 1,
        string app = "MDM6QXBwMTUzNjg=", string workflow = "W_kwDOTUuVMM4VGb-f",
        string eventName = "pull_request", string branch = "lane/governance/sl003-erdos7-339-split-0921") =>
        new { __typename = "CheckRun", databaseId = checkId, name, status, conclusion,
            checkSuite = new { app = new { id = app }, branch = new { id = "ref-" + branch }, commit = new { oid = head },
                workflowRun = new { databaseId = runId, runNumber, runAttempt, @event = eventName, workflow = new { id = workflow } } } };
    private static object Context(string context, string state, string head = HeadSha) =>
        new { __typename = "StatusContext", id = "status-101", context, state, commit = new { oid = head } };
    private static string BoundSnapshot(string prHead, string commitHead, params object[] items) =>
        Snapshot("OPEN", prHead, commitHead, items);
    private static string Snapshot(string state, string prHead, string commitHead, params object[] items) =>
        JsonSerializer.Serialize(new
        {
            data = new { repository = new
            {
                pullRequest = new { state, headRefOid = prHead },
                @object = new { oid = commitHead, statusCheckRollup = new
                {
                    contexts = new { nodes = items, pageInfo = new { hasNextPage = false } },
                } },
            } },
        });
    private static string Snapshot(string state, params object[] items) =>
        Snapshot(state, HeadSha, HeadSha, items);
    private static FakeResponse Ok(string output) => new(0, output, 0);
    private static FakeResponse Fail(int exitCode = 51, int delaySeconds = 0) => new(exitCode, "", delaySeconds);
    private sealed record FakeResponse(int ExitCode, string Output, int DelaySeconds);
    private sealed class PrScriptFixture : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();
        private readonly string bin;
        private readonly string invocations;
        private readonly string responses;
        private readonly string responseEvents;
        private readonly string clock;
        private bool delayedSnapshot;
        private bool useDeadlineClock;
        internal PrScriptFixture()
        {
            bin = Path.Combine(temporary.Path, "bin");
            invocations = Path.Combine(temporary.Path, "gh-invocations");
            responses = Path.Combine(temporary.Path, "responses");
            responseEvents = Path.Combine(temporary.Path, "response-events");
            clock = Path.Combine(temporary.Path, "clock");
            Directory.CreateDirectory(bin);
            Directory.CreateDirectory(responses);
            WriteExecutable(Path.Combine(bin, "gh"), FakeGh);
            WriteExecutable(Path.Combine(bin, "gh-app"), FakeGhApp);
            RequiredResponses(Ok(Required("engineering")));
            HeadResponses(Ok(HeadResponse(HeadSha)));
            SnapshotResponses(Ok(Snapshot("OPEN", Check("engineering", "COMPLETED", "SUCCESS"))));
        }
        private int messageCount;
        internal string MissingMessage => Path.Combine(temporary.Path, "missing.md");
        internal string Message(string content)
        {
            var path = Path.Combine(temporary.Path, $"message{messageCount++}.md");
            File.WriteAllText(path, content, new UTF8Encoding(false));
            return path;
        }
        internal string CreatedBody =>
            File.Exists(invocations + ".body") ? File.ReadAllText(invocations + ".body") : "";
        internal string FailStep { get; set; } = "";
        internal bool AppTokenFails { get; set; }
        internal IReadOnlyList<string> Invocations => File.Exists(invocations) ? File.ReadAllLines(invocations) : [];
        internal ProcessOutput RunOpen(params string[] arguments) => Run(["open", .. arguments]);
        internal ProcessOutput RunWatch(params string[] arguments) => Run(["watch", .. arguments]);
        internal ProcessOutput RunWatch42() => RunWatch("--pr", "42", "--head-sha", HeadSha, "--interval-seconds", "1");
        internal ProcessOutput RunWatch42WithDeadline()
        {
            useDeadlineClock = true;
            Directory.CreateDirectory(clock);
            WriteExecutable(Path.Combine(clock, "launch"), DeadlineClockLauncher);
            var result = RunWatch("--pr", "42", "--head-sha", HeadSha, "--interval-seconds", "1", "--timeout-seconds", DeadlineBehaviorTimeoutSeconds);
            var errors = Text(result.StandardError);
            var events = File.ReadAllLines(responseEvents);
            Assert.Contains("PR_WATCH_PROGRESS pr=42 state=", errors, StringComparison.Ordinal);
            Assert.Contains("snapshot:1:returned", events);
            if (delayedSnapshot)
            {
                Assert.Equal(3, Invocations.Count(IsSnapshotInvocation));
                Assert.Contains("snapshot:2:returned", events);
                Assert.Contains("snapshot:3:started", events);
                Assert.DoesNotContain("snapshot:3:returned", events);
                Assert.Contains("PR_WATCH_PROGRESS pr=42 state=OPEN pending=1 missing=0", errors, StringComparison.Ordinal);
                Assert.Contains("result=timeout", errors, StringComparison.Ordinal);
                Assert.Contains("exit_code=124", errors, StringComparison.Ordinal);
                Assert.Contains("clock:poll:1", events);
                Assert.Contains($"clock:poll:{int.Parse(DeadlineBehaviorTimeoutSeconds) - 1}", events);
                Assert.Contains("clock:api-ready", events);
                Assert.Contains("clock:watchdog-released", events);
            }
            Assert.Contains($"clock:deadline:{DeadlineBehaviorTimeoutSeconds}", events);
            var processes = events.Where(entry => entry.StartsWith("process:", StringComparison.Ordinal))
                .Select(entry => entry["process:".Length..]).Distinct().ToArray();
            Assert.NotEmpty(processes);
            var cleanup = TestProcessRunner.Run("bash",
                ["-c", "for pid in \"$@\"; do if kill -0 \"$pid\" 2>/dev/null; then printf 'still running: %s\\n' \"$pid\" >&2; exit 1; fi; done", "process-cleanup", .. processes],
                temporary.Path, BoundedProcessRunner.HangDetectionBudget, 4096);
            Assert.True(cleanup.ExitCode == 0, Text(cleanup.StandardError));
            return result;
        }
        internal void RequiredResponses(params FakeResponse[] values) => WriteResponses("required", values);
        internal void HeadResponses(params FakeResponse[] values) => WriteResponses("head", values);
        internal void SnapshotResponses(params FakeResponse[] values)
        {
            delayedSnapshot = values.Any(value => value.DelaySeconds > 0);
            WriteResponses("snapshot", values);
        }
        public void Dispose() => temporary.Dispose();
        private ProcessOutput Run(string[] arguments)
        {
            var script = Path.Combine(TestRepositoryLayout.FindRoot(), "tools", "scripts", "pr.sh");
            string[] entry = useDeadlineClock ? ["bash", Path.Combine(clock, "launch"), script] : ["bash", script];
            return TestProcessRunner.Run("env",
                ["GH_TOKEN=caller-token", $"PATH={bin}:/usr/bin:/bin:/usr/sbin:/sbin", "PR_OPEN_REPO=owner/repo",
                    "PR_OPEN_BASE=dev", $"PR_TEST_INVOCATIONS={invocations}",
                    $"PR_TEST_RESPONSES={responses}", $"PR_TEST_RESPONSE_EVENTS={responseEvents}", $"PR_TEST_FAIL_STEP={FailStep}",
                    $"PR_TEST_APP_FAIL={(AppTokenFails ? "1" : "0")}", $"PR_TEST_CLOCK={clock}",
                    $"PR_TEST_DEADLINE={DeadlineBehaviorTimeoutSeconds}", $"PR_TEST_DELAYED_SNAPSHOT={(delayedSnapshot ? "1" : "0")}",
                    .. entry, .. arguments],
                temporary.Path, BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
        }
        private void WriteResponses(string kind, FakeResponse[] values)
        {
            Assert.NotEmpty(values);
            File.WriteAllText(Path.Combine(responses, $"{kind}.count"), values.Length.ToString());
            File.WriteAllText(Path.Combine(responses, $"{kind}.next"), "1");
            for (var i = 0; i < values.Length; i++)
            {
                var prefix = Path.Combine(responses, $"{kind}.{i + 1}");
                File.WriteAllText(prefix + ".out", values[i].Output, new UTF8Encoding(false));
                File.WriteAllText(prefix + ".rc", values[i].ExitCode.ToString());
                File.WriteAllText(prefix + ".delay", values[i].DelaySeconds.ToString());
            }
        }
        private void WriteExecutable(string path, string contents)
        {
            File.WriteAllText(path, contents, new UTF8Encoding(false));
            var chmod = TestProcessRunner.Run(
                "chmod",
                ["+x", path],
                temporary.Path,
                BoundedProcessRunner.HangDetectionBudget,
                4096);
            Assert.Equal(0, chmod.ExitCode);
        }
        private const string FakeGh = """
            #!/usr/bin/env bash
            set -euo pipefail
            printf 'process:%s\n' "$$" >> "$PR_TEST_RESPONSE_EVENTS"
            token="${GH_TOKEN:-none}"
            arguments="$*"
            printf '%s|token=%s\n' "${arguments//$'\n'/ }" "$token" >> "$PR_TEST_INVOCATIONS"
            respond() {
              local kind="$1" index count prefix delay
              index="$(<"$PR_TEST_RESPONSES/$kind.next")"
              count="$(<"$PR_TEST_RESPONSES/$kind.count")"
              printf '%s' "$((index + 1))" > "$PR_TEST_RESPONSES/$kind.next"
              (( index <= count )) || index="$count"
              prefix="$PR_TEST_RESPONSES/$kind.$index"
              printf '%s:%s:started\n' "$kind" "$index" >> "$PR_TEST_RESPONSE_EVENTS"
              delay="$(<"$prefix.delay")"
              (( delay == 0 )) || sleep "$delay"
              cat "$prefix.out"
              printf '%s:%s:returned\n' "$kind" "$index" >> "$PR_TEST_RESPONSE_EVENTS"
              exit "$(<"$prefix.rc")"
            }
            case " $* " in
              *" pr create "*)
                [[ "$PR_TEST_FAIL_STEP" != create ]] || exit 41
                body_file=""; previous=""
                for argument in "$@"; do
                  [[ "$previous" != --body-file ]] || body_file="$argument"
                  previous="$argument"
                done
                [[ -z "$body_file" ]] || cp "$body_file" "$PR_TEST_INVOCATIONS.body"
                printf '%s\n' 'https://github.com/owner/repo/pull/42'
                ;;
              *" pr merge "*) [[ "$PR_TEST_FAIL_STEP" != merge ]] || exit 42 ;;
              *" api repos/"*) respond required ;;
              *" api graphql "*)
                case " $* " in
                  *" -F pr="*) respond snapshot ;;
                  *) respond head ;;
                esac
                ;;
            esac
            """;
        private const string DeadlineClockLauncher = """
            #!/usr/bin/env bash
            set -euo pipefail
            printf '%s\n' "$$" > "$PR_TEST_CLOCK/main"
            printf 'process:%s\n' "$$" >> "$PR_TEST_RESPONSE_EVENTS"
            printf '0\n' > "$PR_TEST_CLOCK/now"
            printf '0\n' > "$PR_TEST_CLOCK/polls"
            mkfifo "$PR_TEST_CLOCK/watchdog" "$PR_TEST_CLOCK/blocked-api"
            date() {
              [[ "$#" == 1 && "$1" == +%s ]] || { command date "$@"; return; }
              printf '%s\n' "$(<"$PR_TEST_CLOCK/now")"
            }
            sleep() {
              local main polls now signal
              main="$(<"$PR_TEST_CLOCK/main")"
              if [[ "$$" == "$main" && "$BASH_SUBSHELL" == 0 ]]; then
                polls="$(<"$PR_TEST_CLOCK/polls")"
                if [[ "$PR_TEST_DELAYED_SNAPSHOT" == 0 ]]; then
                  now="$PR_TEST_DEADLINE"
                elif [[ "$polls" == 0 ]]; then
                  now=1
                elif [[ "$polls" == 1 ]]; then
                  now=$((PR_TEST_DEADLINE - 1))
                else
                  printf 'unexpected deadline-fixture poll\n' >&2; return 1
                fi
                printf '%s\n' "$now" > "$PR_TEST_CLOCK/now"
                printf '%s\n' "$((polls + 1))" > "$PR_TEST_CLOCK/polls"
                printf 'clock:poll:%s\n' "$now" >> "$PR_TEST_RESPONSE_EVENTS"
                if [[ "$now" == "$PR_TEST_DEADLINE" ]]; then
                  printf 'clock:deadline:%s\n' "$now" >> "$PR_TEST_RESPONSE_EVENTS"
                fi
              elif [[ "$$" == "$main" ]]; then
                # This builtin wait lives in the production watchdog itself;
                # cancelling and waiting for that watchdog leaves no sleeper.
                IFS= read -r signal < "$PR_TEST_CLOCK/watchdog"
                [[ "$signal" == ready ]]
                printf 'clock:watchdog-released\n' >> "$PR_TEST_RESPONSE_EVENTS"
              else
                # The third API really remains unfinished until the production
                # watchdog sends TERM. Readiness, not elapsed time, releases it.
                printf 'clock:api-ready\n' >> "$PR_TEST_RESPONSE_EVENTS"
                printf '%s\n' "$PR_TEST_DEADLINE" > "$PR_TEST_CLOCK/now"
                printf 'clock:deadline:%s\n' "$PR_TEST_DEADLINE" >> "$PR_TEST_RESPONSE_EVENTS"
                printf 'ready\n' > "$PR_TEST_CLOCK/watchdog"
                IFS= read -r signal < "$PR_TEST_CLOCK/blocked-api"
                printf 'blocked API unexpectedly resumed\n' >&2; return 1
              fi
            }
            export -f date sleep
            exec bash "$@"
            """;
        private const string FakeGhApp = """
            #!/usr/bin/env bash
            set -euo pipefail
            [[ "${PR_TEST_APP_FAIL:-0}" != 1 ]] || exit 44
            printf '%s\n' 'app-token'
            """;
    }
}
