using StrataLint.Runtime;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;

namespace StrataLint.PrScript.Tests;

public sealed partial class PrOpenScriptTests
{
    private const string DeadlineBehaviorTimeoutSeconds = "30";
    private const string HeadSha = "2222222222222222222222222222222222222222";
    private const string OldHeadSha = "1111111111111111111111111111111111111111";

    [Theory]
    [InlineData("number")]
    [InlineData("repository")]
    public void PrWatchRejectsWrongRequestedPrIdentity(string defect)
    {
        using var fixture = new PrScriptFixture();
        var snapshot = JsonNode.Parse(Snapshot("OPEN", Check("engineering", "COMPLETED", "SUCCESS")))!;
        var repository = snapshot["data"]!["repository"]!;
        if (defect == "number") repository["pullRequest"]!["number"] = 99;
        else repository["nameWithOwner"] = "other/repo";
        fixture.SnapshotResponses(Ok(snapshot.ToJsonString()));

        var result = fixture.RunWatch42();

        Assert.Equal(69, result.ExitCode);
        Assert.DoesNotContain("PR_WATCH_EVIDENCE", Text(result.StandardError), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("COMPLETED", "SUCCESS", 0)]
    [InlineData("COMPLETED", "FAILURE", 1)]
    [InlineData("COMPLETED", "CANCELLED", 1)]
    [InlineData("IN_PROGRESS", null, 124)]
    public void PrWatchRetainsIndependentWorkflowObligations(string status, string? conclusion, int exitCode)
    {
        using var fixture = new PrScriptFixture();
        fixture.RequiredResponses(Ok(Required("engineering", "security")));
        fixture.SnapshotResponses(Ok(Snapshot("OPEN",
            Check("engineering", "COMPLETED", "FAILURE", latest: false),
            Check("engineering", "COMPLETED", "SUCCESS", runId: 202, runNumber: 2),
            Check("security", status, conclusion, runId: 100, runNumber: 1, workflow: "workflow-other"))));

        Assert.Equal(exitCode, (exitCode == 124 ? fixture.RunWatch42WithDeadline() : fixture.RunWatch42()).ExitCode);
    }

    [Theory]
    [InlineData("workflow", "COMPLETED", "FAILURE", 1)]
    [InlineData("external", "COMPLETED", "CANCELLED", 1)]
    [InlineData("external", "IN_PROGRESS", null, 124)]
    [InlineData("status", "COMPLETED", "FAILURE", 1)]
    [InlineData("status", "IN_PROGRESS", "PENDING", 124)]
    public void PrWatchRetainsOtherProducersWithTheSameRequiredName(
        string producer, string status, string? conclusion, int exitCode)
    {
        using var fixture = new PrScriptFixture();
        var other = producer == "status" ? Context("engineering", conclusion!) :
            Check("engineering", status, conclusion, runId: 100,
                workflow: producer == "external" ? null : "workflow-other");
        fixture.SnapshotResponses(Ok(Snapshot("OPEN", other,
            Check("engineering", "COMPLETED", "SUCCESS", runId: 202, runNumber: 2))));

        Assert.Equal(exitCode, (exitCode == 124 ? fixture.RunWatch42WithDeadline() : fixture.RunWatch42()).ExitCode);
    }

    [Theory]
    [InlineData("CANCELLED", "COMPLETED", "SUCCESS", 0)]
    [InlineData("SUCCESS", "COMPLETED", "FAILURE", 1)]
    [InlineData("SUCCESS", "COMPLETED", "CANCELLED", 1)]
    [InlineData("FAILURE", "IN_PROGRESS", null, 124)]
    public void PrWatchUsesGithubLatestCheckWithinApplicableRun(
        string oldConclusion, string status, string? conclusion, int exitCode)
    {
        using var fixture = new PrScriptFixture();
        fixture.SnapshotResponses(Ok(Snapshot("OPEN",
            Check("engineering", status, conclusion, checkId: 100),
            Check("engineering", "COMPLETED", oldConclusion, checkId: 200, latest: false))));

        var result = exitCode == 124 ? fixture.RunWatch42WithDeadline() : fixture.RunWatch42();

        Assert.Equal(exitCode, result.ExitCode);
        Assert.Contains("\"state\":\"" + (conclusion ?? status) + "\"", Text(result.StandardError), StringComparison.Ordinal);
        Assert.DoesNotContain("\"state\":\"" + oldConclusion + "\"", Text(result.StandardError), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("check-id-conflict")]
    [InlineData("latest-missing")]
    [InlineData("latest-truncated")]
    [InlineData("latest-invalid-id")]
    [InlineData("latest-unknown-id")]
    [InlineData("latest-conflict")]
    [InlineData("latest-duplicate-name")]
    public void PrWatchRejectsUnverifiableLatestCheckSelection(string defect)
    {
        using var fixture = new PrScriptFixture();
        var snapshot = JsonNode.Parse(Snapshot("OPEN", Check("engineering", "COMPLETED", "SUCCESS"),
            Check("resolve", "COMPLETED", "SUCCESS")))!;
        var nodes = snapshot["data"]!["repository"]!["object"]!["statusCheckRollup"]!["contexts"]!["nodes"]!;
        var suite = nodes[1]!["checkSuite"]!;
        switch (defect)
        {
            case "check-id-conflict":
                nodes[1]!["databaseId"] = 101;
                nodes[1]!["name"] = "engineering";
                foreach (var node in nodes.AsArray())
                    node!["checkSuite"]!["checkRuns"]!["nodes"] = JsonNode.Parse("""[{"databaseId":101}]""");
                break;
            case "latest-missing": suite.AsObject().Remove("checkRuns"); break;
            case "latest-truncated": suite["checkRuns"]!["pageInfo"]!["hasNextPage"] = true; break;
            case "latest-invalid-id": suite["checkRuns"]!["nodes"]![0]!["databaseId"] = "101"; break;
            case "latest-unknown-id": suite["checkRuns"]!["nodes"]![0]!["databaseId"] = 999; break;
            case "latest-conflict": suite["checkRuns"]!["nodes"]!.AsArray().RemoveAt(0); break;
            case "latest-duplicate-name": nodes[1]!["name"] = "engineering"; break;
        }
        fixture.SnapshotResponses(Ok(snapshot.ToJsonString()));

        var result = fixture.RunWatch42();

        Assert.Equal(69, result.ExitCode);
        Assert.DoesNotContain("PR_WATCH_EVIDENCE", Text(result.StandardError), StringComparison.Ordinal);
    }

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
    [InlineData("missing-status-id")]
    [InlineData("partial-errors")]
    [InlineData("truncated-contexts")]
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
            case "missing-status-id": contexts["nodes"]![1]!.AsObject().Remove("id"); break;
            case "partial-errors": snapshot["errors"] = JsonNode.Parse("""[{"message":"partial failure"}]"""); break;
            case "truncated-contexts": contexts["pageInfo"]!["hasNextPage"] = true; break;
        }
        fixture.SnapshotResponses(Ok(snapshot.ToJsonString()));

        var result = fixture.RunWatch42();

        Assert.Equal(69, result.ExitCode);
        Assert.DoesNotContain("PR_WATCH_EVIDENCE", Text(result.StandardError), StringComparison.Ordinal);
    }

    [Fact]
    public void PrWatchReportsRequiredCheckStatesAndAllowsExternalChecks()
    {
        using var fixture = new PrScriptFixture();
        fixture.RequiredResponses(Ok(Required("engineering", "external", "status")));
        var snapshot = JsonNode.Parse(Snapshot("OPEN", Check("engineering", "COMPLETED", "SUCCESS"),
            Check("external", "COMPLETED", "SUCCESS", workflow: null), Context("status", "SUCCESS")))!;
        fixture.SnapshotResponses(Ok(snapshot.ToJsonString()));

        var result = fixture.RunWatch42();

        Assert.Equal(0, result.ExitCode);
        var line = Text(result.StandardError).Split('\n').Single(value => value.StartsWith("PR_WATCH_EVIDENCE", StringComparison.Ordinal));
        var evidence = JsonNode.Parse(line[(line.IndexOf("checks=", StringComparison.Ordinal) + "checks=".Length)..])!.AsArray();
        Assert.Equal(new[] { "engineering", "external", "status" },
            evidence.Select(item => item!["check"]!.GetValue<string>()));
        Assert.All(evidence, item => Assert.Equal("terminal", item!["kind"]!.GetValue<string>()));
        Assert.All(evidence, item => Assert.Equal("SUCCESS", item!["state"]!.GetValue<string>()));
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
        fixture.SnapshotResponses(Ok(Snapshot("OPEN", Check("engineering", "COMPLETED", "FUTURE_CONCLUSION"))));
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
    [InlineData("ACTION_REQUIRED")]
    [InlineData("STARTUP_FAILURE")]
    [InlineData("STALE")]
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
        Assert.EndsWith("|token=fake-app-credential", fixture.Invocations[1], StringComparison.Ordinal);
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
    [Theory]
    [InlineData("pr", "", false, true)]
    [InlineData("pr-open", "", false, true)]
    [InlineData("pr", "0", false, false)]
    [InlineData("pr-open", "0", false, false)]
    [InlineData("pr", "", true, false)]
    [InlineData("pr-open", "", true, false)]
    [InlineData("pr", "1", true, false)]
    [InlineData("pr-open", "1", true, false)]
    public void MakePrDefaultsToAutoMergeAndHonorsDraftAndOptOut(
        string target, string autoMerge, bool draft, bool expectedAutoMerge)
    {
        using var fixture = new PrScriptFixture();
        var result = fixture.RunMakeOpen(target, autoMerge, draft);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(expectedAutoMerge, fixture.Invocations.Any(IsAutoMergeInvocation));
        Assert.Equal(!draft, fixture.Invocations.Any(IsWatchInvocation));
        Assert.Equal(draft, fixture.LaunchArguments("gh").Contains("--draft", StringComparer.Ordinal));
        if (draft)
        {
            Assert.Equal("42\n", Text(result.StandardOutput));
            Assert.Equal(2, fixture.Invocations.Count);
        }
        else
        {
            Assert.StartsWith($"42\nPR_WATCH_RESULT pr=42 outcome=green head_sha={HeadSha}\n",
                Text(result.StandardOutput), StringComparison.Ordinal);
        }
    }
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void PrOpenDraftReturnsWithoutMergingOrWatchingEvenWhenAutoMergeIsRequested(bool autoMerge)
    {
        using var fixture = new PrScriptFixture();
        var result = fixture.RunOpen([
            "--head", "topic", "--message-file", fixture.Message("Draft title\n\nDraft body\n"),
            "--draft", .. (autoMerge ? new[] { "--auto-merge" } : Array.Empty<string>())]);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal("42\n", Text(result.StandardOutput));
        Assert.Equal(2, fixture.Invocations.Count);
        Assert.Contains("--draft", fixture.LaunchArguments("gh"));
        Assert.DoesNotContain(fixture.Invocations, IsAutoMergeInvocation);
        Assert.DoesNotContain(fixture.Invocations, IsWatchInvocation);
        Assert.Equal("Draft body\n", fixture.CreatedBody);
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
        Assert.Contains("[--draft]", Text(result.StandardError), StringComparison.Ordinal);
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
}
