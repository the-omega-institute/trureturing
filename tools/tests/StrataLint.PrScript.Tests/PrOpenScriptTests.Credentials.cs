using StrataLint.Runtime;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;

namespace StrataLint.PrScript.Tests;

public sealed partial class PrOpenScriptTests
{
    [Fact]
    public void PrOpenFallsBackToLocalGhWhenAppTokenFails()
    {
        using var fixture = new PrScriptFixture { AppTokenFails = true };
        Assert.Equal(0, fixture.RunOpen("--head", "topic", "--message-file", fixture.Message("title\n")).ExitCode);
        Assert.EndsWith("|token=none", fixture.Invocations[1], StringComparison.Ordinal);
    }
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void PrScriptKeepsCredentialsOutOfExternalLaunchArguments(bool create)
    {
        using var fixture = new PrScriptFixture { GithubToken = create ? "" : "supplied-token" };
        const string title = "literal 'single' \"double\" $HOME `exit 91` $(exit 92) *";
        var result = create
            ? fixture.RunOpen("--head", "topic", "--message-file", fixture.Message(title + "\n"))
            : fixture.RunWatch42();

        Assert.Equal(0, result.ExitCode);
        Assert.NotEmpty(fixture.LaunchArguments("env"));
        Assert.NotEmpty(fixture.LaunchArguments("gh-app"));
        if (create) Assert.Contains(title, fixture.LaunchArguments("gh"));
        fixture.AssertNoCredentialEmission(result);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void PrWatchRefreshesExpiringCredentialsAcrossQueriesForOneHeadAndRun(bool throughMake)
    {
        using var fixture = new PrScriptFixture { GithubToken = "renewed-1", RotatingCredentials = true };
        fixture.SnapshotResponses(
            Ok(Snapshot("OPEN", Check("engineering", "IN_PROGRESS", null))),
            Ok(Snapshot("OPEN", Check("engineering", "COMPLETED", "SUCCESS"))));

        var result = throughMake ? fixture.RunMakeWatch42() : fixture.RunWatch42();

        Assert.Equal(0, result.ExitCode);
        Assert.Contains($"PR_WATCH_RESULT pr=42 outcome=green head_sha={HeadSha}", Text(result.StandardOutput), StringComparison.Ordinal);
        Assert.Contains("state=OPEN pending=1 missing=0", Text(result.StandardError), StringComparison.Ordinal);
        Assert.Equal(2, fixture.Invocations.Count(IsSnapshotInvocation));
        Assert.Equal(3, fixture.BrokerCalls.Count);
        Assert.Equal(Enumerable.Range(1, 3).Select(i => $"renewed-{i}"), fixture.GithubCredentials);
        Assert.All(fixture.Invocations, invocation => Assert.EndsWith("|token=none", invocation, StringComparison.Ordinal));
        var evidence = Text(result.StandardError).Split('\n').Where(line => line.StartsWith("PR_WATCH_EVIDENCE", StringComparison.Ordinal)).ToArray();
        Assert.Equal(2, evidence.Length);
        Assert.All(evidence, line => Assert.Contains("\"check\":\"engineering\"", line, StringComparison.Ordinal));
        fixture.AssertNoCredentialEmission(result);
    }

    [Theory]
    [InlineData("available", "supplied-token", "fake-app-credential", 2)]
    [InlineData("failing", "supplied-token", "supplied-token", 2)]
    [InlineData("empty", "supplied-token", "supplied-token", 2)]
    [InlineData("absent", "supplied-token", "supplied-token", 0)]
    [InlineData("available", "", "none", 0)]
    [InlineData("absent", "", "none", 0)]
    [InlineData("available", null, "none", 0)]
    [InlineData("absent", null, "none", 0)]
    public void PrWatchPreservesCredentialModes(string broker, string? supplied, string expected, int brokerCalls)
    {
        using var fixture = new PrScriptFixture { GithubToken = supplied, BrokerMode = broker };
        var result = fixture.RunWatch42();
        Assert.Equal(0, result.ExitCode);
        Assert.Equal(brokerCalls, fixture.BrokerCalls.Count);
        Assert.All(fixture.GithubCredentials, token => Assert.Equal(expected, token));
        Assert.All(fixture.Invocations, invocation => Assert.EndsWith("|token=none", invocation, StringComparison.Ordinal));
        fixture.AssertNoCredentialEmission(result);
    }

    [Theory]
    [InlineData("absent")]
    [InlineData("failing")]
    [InlineData("empty")]
    public void PrWatchUnavailableCredentialsStayQueryUnavailable(string broker)
    {
        using var fixture = new PrScriptFixture
        { GithubToken = "expired-token", BrokerMode = broker, RotatingCredentials = true };
        var result = fixture.RunWatch42();
        Assert.Equal(69, result.ExitCode);
        Assert.Contains("outcome=query-unavailable step=required-set attempts=3", Text(result.StandardOutput), StringComparison.Ordinal);
        Assert.Equal(3, fixture.Invocations.Count);
        Assert.DoesNotContain(fixture.Invocations, IsSnapshotInvocation);
        fixture.AssertNoCredentialEmission(result);
    }

    [Fact]
    public void PrWatchDoesNotAssumeNativeCredentialsWhenOnlyGhTokenIsSupplied()
    {
        using var fixture = new PrScriptFixture { RequireCredential = true };
        var result = fixture.RunWatch42();
        Assert.Equal(69, result.ExitCode);
        Assert.Equal(3, fixture.Invocations.Count);
        Assert.Empty(fixture.BrokerCalls);
        Assert.Contains("authentication required", Text(result.StandardError), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("available", "fake-app-credential")]
    [InlineData("failing", "none")]
    [InlineData("empty", "none")]
    [InlineData("absent", "none")]
    public void PrOpenPreservesCreationIdentityAndLocalAutoMerge(string broker, string createToken)
    {
        using var fixture = new PrScriptFixture { BrokerMode = broker };
        var result = fixture.RunOpen("--head", "topic", "--message-file", fixture.Message("title\n"), "--auto-merge");
        Assert.Equal(0, result.ExitCode);
        Assert.EndsWith("|token=" + createToken, fixture.Invocations[1], StringComparison.Ordinal);
        Assert.EndsWith("|token=none", fixture.Invocations[2], StringComparison.Ordinal);
        Assert.All(fixture.GithubCredentials, token => Assert.Equal("none", token));
        fixture.AssertNoCredentialEmission(result);
    }

    [Fact]
    public void PrOpenRefreshesSuppliedCredentialsWithoutLeakingCreationIdentity()
    {
        using var fixture = new PrScriptFixture { GithubToken = "renewed-1", RotatingCredentials = true };
        var result = fixture.RunOpen("--head", "topic", "--message-file", fixture.Message("title\n"), "--auto-merge");
        Assert.Equal(0, result.ExitCode);
        Assert.Equal(5, fixture.BrokerCalls.Count);
        Assert.EndsWith("|token=renewed-2", fixture.Invocations[1], StringComparison.Ordinal);
        Assert.Equal("renewed-1", fixture.GithubCredentials[1]);
        Assert.EndsWith("|token=none", fixture.Invocations[2], StringComparison.Ordinal);
        Assert.Equal("renewed-3", fixture.GithubCredentials[2]);
        fixture.AssertNoCredentialEmission(result);
    }

    [Theory]
    [InlineData("SUCCESS", "FAILURE", 1)]
    [InlineData("FAILURE", "SUCCESS", 0)]
    public void PrWatchRefreshDoesNotCollapseStaleHeadOrOldCheck(string misleading, string current, int exitCode)
    {
        using var fixture = new PrScriptFixture { GithubToken = "renewed-1", RotatingCredentials = true };
        fixture.SnapshotResponses(
            Ok(BoundSnapshot(OldHeadSha, HeadSha, Check("engineering", "COMPLETED", misleading))),
            Ok(Snapshot("OPEN", Check("engineering", "COMPLETED", misleading, latest: false),
                Check("engineering", "COMPLETED", current, runId: 202, runNumber: 2))));
        var result = fixture.RunWatch42();
        Assert.Equal(exitCode, result.ExitCode);
        Assert.Contains("state=stale", Text(result.StandardError), StringComparison.Ordinal);
        Assert.Equal(2, fixture.Invocations.Count(IsSnapshotInvocation));
        Assert.Contains("\"state\":\"" + current + "\"", Text(result.StandardError), StringComparison.Ordinal);
        Assert.DoesNotContain("\"state\":\"" + misleading + "\"", Text(result.StandardError), StringComparison.Ordinal);
        fixture.AssertNoCredentialEmission(result);
    }

    [Fact]
    public void PrWatchBrokerFailureAfterPendingIsNotCiFailure()
    {
        using var fixture = new PrScriptFixture
        { GithubToken = "renewed-1", RotatingCredentials = true, BrokerFailAt = 3 };
        fixture.SnapshotResponses(Ok(Snapshot("OPEN", Check("engineering", "IN_PROGRESS", null))));
        var result = fixture.RunWatch42();
        Assert.Equal(69, result.ExitCode);
        Assert.Contains("state=OPEN pending=1 missing=0", Text(result.StandardError), StringComparison.Ordinal);
        Assert.Contains("outcome=query-unavailable step=snapshot attempts=3", Text(result.StandardOutput), StringComparison.Ordinal);
        Assert.Equal(5, fixture.BrokerCalls.Count);
        fixture.AssertNoCredentialEmission(result);
    }

    [Fact]
    public void PrOpenKeepsCreationApiBudgetAfterBrokerAcquisition()
    {
        using var fixture = new PrScriptFixture { BrokerAdvanceSeconds = 10 };
        var result = fixture.RunOpen("--head", "topic", "--message-file", fixture.Message("title\n"));
        Assert.Equal(0, result.ExitCode);
        Assert.Contains("step=pr-create timeout_seconds=60", Text(result.StandardError), StringComparison.Ordinal);
        fixture.AssertNoCredentialEmission(result);
    }

    [Fact]
    public void PrWatchSubtractsBrokerTimeFromTheQueryBudget()
    {
        using var fixture = new PrScriptFixture { GithubToken = "supplied-token", BrokerAdvanceSeconds = 10 };
        var result = fixture.RunWatch("--pr", "42", "--head-sha", HeadSha, "--timeout-seconds", "30");
        Assert.Equal(0, result.ExitCode);
        Assert.Contains("step=required-set timeout_seconds=20", Text(result.StandardError), StringComparison.Ordinal);
        fixture.AssertNoCredentialEmission(result);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void PrWatchBrokerTimeoutUsesTheRemainingWatchBudget(bool childProcess)
    {
        using var fixture = new PrScriptFixture
        { GithubToken = "renewed-1", RotatingCredentials = true, BrokerBlockAt = 3, BrokerChildProcess = childProcess };
        fixture.SnapshotResponses(Ok(Snapshot("OPEN", Check("engineering", "IN_PROGRESS", null))));
        var result = fixture.RunWatchWithBlockedBroker();
        Assert.Equal(69, result.ExitCode);
        Assert.Contains("outcome=query-unavailable step=snapshot attempts=1", Text(result.StandardOutput), StringComparison.Ordinal);
        Assert.Contains("step=gh-app-token timeout_seconds=29 result=timeout", Text(result.StandardError), StringComparison.Ordinal);
        Assert.Single(fixture.Invocations, IsSnapshotInvocation);
        Assert.Equal(3, fixture.BrokerCalls.Count);
        fixture.AssertNoCredentialEmission(result);
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
        int checkId = 0, int runId = 201, int runNumber = 1, int runAttempt = 1, string? workflow = "workflow-301", bool latest = true,
        int pr = 42, string eventName = "pull_request") =>
        new { __typename = "CheckRun", databaseId = checkId, name, status, conclusion,
            checkSuite = new { databaseId = runId + 1000, commit = new { oid = head },
                testMembership = new { pr, eventName },
                workflowRun = workflow == null ? null : new { databaseId = runId, runNumber, runAttempt, workflow = new { id = workflow } },
                checkRuns = new { nodes = latest ? new[] { new { databaseId = checkId } } : [],
                    pageInfo = new { hasNextPage = false } } } };
    private static object Context(string context, string state, string head = HeadSha) =>
        new { __typename = "StatusContext", id = "status-101", context, state, commit = new { oid = head } };
    private static string BoundSnapshot(string prHead, string commitHead, params object[] items) =>
        Snapshot("OPEN", prHead, commitHead, items);
    private static string Snapshot(string state, string prHead, string commitHead, params object[] items)
    {
        var nodes = JsonSerializer.SerializeToNode(items)!.AsArray();
        for (var i = 0; i < nodes.Count; i++)
        {
            var node = nodes[i]!;
            if (node["__typename"]!.GetValue<string>() != "CheckRun") continue;
            if (node["databaseId"]!.GetValue<int>() == 0) node["databaseId"] = 101 + i;
            foreach (var latest in node["checkSuite"]!["checkRuns"]!["nodes"]!.AsArray())
                latest!["databaseId"] = node["databaseId"]!.DeepClone();
        }
        foreach (var run in nodes.Where(node => node!["checkSuite"]?["workflowRun"] != null)
                     .GroupBy(node => node!["checkSuite"]!["workflowRun"]!["databaseId"]!.GetValue<int>()))
        {
            var latest = new JsonArray(run.SelectMany(node => node!["checkSuite"]!["checkRuns"]!["nodes"]!.AsArray())
                .Select(node => node!.DeepClone()).ToArray());
            foreach (var node in run) node!["checkSuite"]!["checkRuns"]!["nodes"] = latest.DeepClone();
        }
        return JsonSerializer.Serialize(new
        {
            data = new { repository = new
            {
                nameWithOwner = "owner/repo", pullRequest = new { number = 42, state, headRefOid = prHead },
                @object = new { oid = commitHead, statusCheckRollup = new
                {
                    contexts = new { nodes, pageInfo = new { hasNextPage = false } },
                } },
            } },
        });
    }
    private static string Snapshot(string state, params object[] items) =>
        Snapshot(state, HeadSha, HeadSha, items);
    private static JsonObject RunMetadata(int runId, int runNumber, string head, int pr, string eventName, int runAttempt = 1) =>
        JsonSerializer.SerializeToNode(new
        {
            id = runId, run_number = runNumber, run_attempt = runAttempt, check_suite_id = runId + 1000, head_sha = head,
            path = ".github/workflows/other.yml",
            @event = eventName, repository = new { id = 1, full_name = "owner/repo" },
            pull_requests = new[] { new { id = pr + 1000, number = pr,
                url = $"https://api.github.com/repos/owner/repo/pulls/{pr}",
                head = new { sha = head }, @base = new { repo = new { id = 1 } } } },
        })!.AsObject();
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
            bin = Path.Combine(temporary.Path, "bin with spaces");
            invocations = Path.Combine(temporary.Path, "gh-invocations");
            responses = Path.Combine(temporary.Path, "responses");
            responseEvents = Path.Combine(temporary.Path, "response-events");
            clock = Path.Combine(temporary.Path, "clock");
            Directory.CreateDirectory(bin);
            Directory.CreateDirectory(responses);
            WriteExecutable(Path.Combine(bin, "gh"), FakeGh);
            WriteExecutable(Path.Combine(bin, "gh-app"), FakeGhApp);
            WriteExecutable(Path.Combine(bin, "env"), FakeEnv);
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
        internal string? GithubToken { get; set; }
        internal string BrokerMode { get; set; } = "available";
        internal bool RotatingCredentials { get; set; }
        internal bool RequireCredential { get; set; }
        internal int BrokerFailAt { get; set; }
        internal int BrokerBlockAt { get; set; }
        internal int BrokerAdvanceSeconds { get; set; }
        internal bool BrokerChildProcess { get; set; }
        internal IReadOnlyList<string> BrokerCalls => File.Exists(invocations + ".broker") ? File.ReadAllLines(invocations + ".broker") : [];
        internal IReadOnlyList<string> GithubCredentials => File.Exists(invocations + ".github") ? File.ReadAllLines(invocations + ".github") : [];
        internal IReadOnlyList<string> LaunchArguments(string executable)
        {
            var path = invocations + ".argv-" + executable;
            return File.Exists(path) ? File.ReadAllText(path).Split('\0') : [];
        }
        internal void AssertNoCredentialEmission(ProcessOutput result)
        {
            var output = Text(result.StandardOutput) + Text(result.StandardError);
            Assert.NotEmpty(LaunchArguments("gh"));
            foreach (var token in new[] { "caller-token", "supplied-token", "expired-token", "fake-app-credential", "renewed-", "broker-secret" })
            {
                Assert.DoesNotContain(token, output, StringComparison.Ordinal);
                foreach (var executable in new[] { "env", "gh", "gh-app" })
                    Assert.All(LaunchArguments(executable), argument => Assert.DoesNotContain(token, argument, StringComparison.Ordinal));
            }
            Assert.All(BrokerCalls, call => Assert.Equal("token --auto|stdout=pipe", call));
        }
        internal ProcessOutput RunMakeWatch42() => Run(["make", "pr-watch", "PR=42", "HEAD_SHA=" + HeadSha, "WATCH_INTERVAL_SECONDS=1"]);
        internal ProcessOutput RunMakeOpen(string target, string autoMerge, bool draft) =>
            Run(["make", target, "HEAD=topic", "MESSAGE=" + Message("title\n"),
                .. (autoMerge.Length == 0 ? Array.Empty<string>() : ["AUTO_MERGE=" + autoMerge]),
                .. (draft ? new[] { "DRAFT=1" } : Array.Empty<string>())]);
        internal ProcessOutput RunWatchWithBlockedBroker()
        {
            useDeadlineClock = true;
            delayedSnapshot = true;
            Directory.CreateDirectory(clock);
            WriteExecutable(Path.Combine(clock, "launch"), DeadlineClockLauncher);
            var result = RunWatch("--pr", "42", "--head-sha", HeadSha, "--interval-seconds", "1", "--timeout-seconds", DeadlineBehaviorTimeoutSeconds);
            AssertProcessesStopped(File.ReadAllLines(responseEvents));
            return result;
        }
        internal IReadOnlyList<string> Invocations => File.Exists(invocations) ? File.ReadAllLines(invocations) : [];
        internal ProcessOutput RunOpen(params string[] arguments) => Run(["open", .. arguments]);
        internal ProcessOutput RunWatch(params string[] arguments) => Run(["watch", .. arguments]);
        internal ProcessOutput RunWatch42() => RunWatch("--pr", "42", "--head-sha", HeadSha, "--interval-seconds", "1");
        internal ProcessOutput RunWatch42WithDeadline() => RunWatchWithDeadline(42);
        internal ProcessOutput RunWatchWithDeadline(int pr)
        {
            useDeadlineClock = true;
            Directory.CreateDirectory(clock);
            WriteExecutable(Path.Combine(clock, "launch"), DeadlineClockLauncher);
            var result = RunWatch("--pr", pr.ToString(), "--head-sha", HeadSha, "--interval-seconds", "1", "--timeout-seconds", DeadlineBehaviorTimeoutSeconds);
            var errors = Text(result.StandardError);
            var events = File.ReadAllLines(responseEvents);
            Assert.Contains($"PR_WATCH_PROGRESS pr={pr} state=", errors, StringComparison.Ordinal);
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
            AssertProcessesStopped(events);
            return result;
        }
        private void AssertProcessesStopped(string[] events)
        {
            var processes = events.Where(entry => entry.StartsWith("process:", StringComparison.Ordinal))
                .Select(entry => entry["process:".Length..]).Distinct().ToArray();
            Assert.NotEmpty(processes);
            var cleanup = TestProcessRunner.Run("bash",
                ["-c", "for pid in \"$@\"; do if kill -0 \"$pid\" 2>/dev/null; then printf 'still running: %s\\n' \"$pid\" >&2; exit 1; fi; done", "process-cleanup", .. processes],
                temporary.Path, BoundedProcessRunner.HangDetectionBudget, 4096);
            Assert.True(cleanup.ExitCode == 0, Text(cleanup.StandardError));
        }
        internal void RequiredResponses(params FakeResponse[] values) => WriteResponses("required", values);
        internal void RunResponses(int runId, params FakeResponse[] values) => WriteResponses($"run-{runId}", values);
        internal void HeadResponses(params FakeResponse[] values) => WriteResponses("head", values);
        internal void SnapshotResponses(params FakeResponse[] values)
        {
            delayedSnapshot = values.Any(value => value.DelaySeconds > 0);
            var runs = new Dictionary<int, List<FakeResponse>>();
            var snapshots = values.Select(value =>
            {
                JsonNode? snapshot;
                try { snapshot = JsonNode.Parse(value.Output); }
                catch (JsonException) { return value; }
                var nodes = snapshot?["data"]?["repository"]?["object"]?["statusCheckRollup"]?["contexts"]?["nodes"]?.AsArray();
                var seen = new HashSet<int>();
                foreach (var node in nodes ?? new JsonArray())
                {
                    var suite = node?["checkSuite"];
                    var membership = suite?["testMembership"];
                    if (suite?["workflowRun"]?["databaseId"] is JsonValue id && id.TryGetValue<int>(out var runId) && seen.Add(runId))
                    {
                        if (!runs.TryGetValue(runId, out var responses)) runs[runId] = responses = [];
                        var runNumber = suite["workflowRun"]?["runNumber"] is JsonValue n && n.TryGetValue<int>(out var number) ? number : 1;
                        var runAttempt = suite["workflowRun"]?["runAttempt"] is JsonValue a && a.TryGetValue<int>(out var attempt) ? attempt : 1;
                        var head = suite["commit"]!["oid"]!.GetValue<string>();
                        var pr = membership?["pr"]?.GetValue<int>() ?? 42;
                        var eventName = membership?["eventName"]?.GetValue<string>() ?? "pull_request";
                        // Successful PR executions need the existing native retained-ref contract.
                        var run = eventName == "pull_request" ?
                            RunMetadata(runId, runNumber, head, pr, "pull_request", runAttempt) :
                            RunMetadata(runId, runNumber, head, pr, eventName, runAttempt);
                        responses.Add(Ok(new JsonArray(run).ToJsonString()));
                    }
                    suite?.AsObject().Remove("testMembership");
                }
                return value with { Output = snapshot?.ToJsonString() ?? value.Output };
            }).ToArray();
            foreach (var (id, responses) in runs) RunResponses(id, responses.ToArray());
            WriteResponses("snapshot", snapshots);
        }
        public void Dispose() => temporary.Dispose();
        private ProcessOutput Run(string[] arguments)
        {
            if (BrokerAdvanceSeconds > 0)
            {
                useDeadlineClock = true;
                Directory.CreateDirectory(clock);
                WriteExecutable(Path.Combine(clock, "launch"), DeadlineClockLauncher);
            }
            var root = TestRepositoryLayout.FindRoot();
            var scriptDirectory = Path.Combine(temporary.Path, "checkout with spaces", "tools", "scripts");
            Directory.CreateDirectory(scriptDirectory);
            var script = Path.Combine(scriptDirectory, "pr.sh");
            File.Copy(Path.Combine(root, "tools", "scripts", "pr.sh"), script, true);
            var checkout = Path.GetFullPath(Path.Combine(scriptDirectory, "..", ".."));
            File.Copy(Path.Combine(root, "Makefile"), Path.Combine(checkout, "Makefile"), true);
            var scratch = Path.Combine(temporary.Path, "temp with spaces");
            Directory.CreateDirectory(scratch);
            if (BrokerMode == "absent") File.Delete(Path.Combine(bin, "gh-app"));
            string[] entry = useDeadlineClock ? ["bash", Path.Combine(clock, "launch"), script] : ["bash", script];
            if (arguments[0] == "make")
            {
                entry = ["make", "--no-print-directory", "-C", checkout];
                arguments = arguments[1..];
            }
            return TestProcessRunner.Run("env",
                ["-i", "GH_TOKEN=caller-token", .. (GithubToken is null ? Array.Empty<string>() : [$"GITHUB_TOKEN={GithubToken}"]), $"TMPDIR={scratch}",
                    $"PATH={bin}:/usr/bin:/bin:/usr/sbin:/sbin", "PR_OPEN_REPO=owner/repo",
                    "PR_OPEN_BASE=dev", $"PR_TEST_INVOCATIONS={invocations}",
                    $"PR_TEST_RESPONSES={responses}", $"PR_TEST_RESPONSE_EVENTS={responseEvents}", $"PR_TEST_FAIL_STEP={FailStep}",
                    $"PR_TEST_APP_FAIL={(AppTokenFails || BrokerMode == "failing" ? "1" : "0")}", $"PR_TEST_CLOCK={clock}",
                    $"PR_TEST_APP_EMPTY={(BrokerMode == "empty" ? "1" : "0")}",
                    $"PR_TEST_ROTATE={(RotatingCredentials ? "1" : "0")}", $"PR_TEST_REQUIRE_CREDENTIAL={(RequireCredential ? "1" : "0")}",
                    $"PR_TEST_APP_FAIL_AT={BrokerFailAt}", $"PR_TEST_APP_BLOCK_AT={BrokerBlockAt}",
                    $"PR_TEST_APP_ADVANCE={BrokerAdvanceSeconds}", $"PR_TEST_APP_CHILD={(BrokerChildProcess ? "1" : "0")}",
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
        // Observe the executable boundary before env consumes assignments and
        // execs gh; gh's own argv alone cannot detect an upstream env leak.
        private const string FakeEnv = """
            #!/bin/bash
            set -euo pipefail
            printf '%s\0' "$@" >> "$PR_TEST_INVOCATIONS.argv-env"
            exec /usr/bin/env "$@"
            """;
        private const string FakeGh = """
            #!/usr/bin/env bash
            set -euo pipefail
            printf '%s\0' "$@" >> "$PR_TEST_INVOCATIONS.argv-gh"
            printf 'process:%s\n' "$$" >> "$PR_TEST_RESPONSE_EVENTS"
            token="${GH_TOKEN:-none}"
            printf '%s\n' "${GITHUB_TOKEN:-none}" >> "$PR_TEST_INVOCATIONS.github"
            arguments="$*"
            printf '%s|token=%s\n' "${arguments//$'\n'/ }" "$token" >> "$PR_TEST_INVOCATIONS"
            if [[ "$PR_TEST_REQUIRE_CREDENTIAL" == 1 && -z "${GITHUB_TOKEN:-}" && "$token" == none ]]; then
              printf 'authentication required\n' >&2; exit 4
            fi
            if [[ "$PR_TEST_ROTATE" == 1 ]]; then
              index=0
              [[ ! -f "$PR_TEST_INVOCATIONS.auth" ]] || index="$(<"$PR_TEST_INVOCATIONS.auth")"
              index=$((index + 1))
              printf '%s\n' "$index" > "$PR_TEST_INVOCATIONS.auth"
              [[ "${GH_TOKEN:-${GITHUB_TOKEN:-}}" == "renewed-$index" ]] || { printf 'HTTP 401: expired credential\n' >&2; exit 1; }
            fi
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
              *"/actions/runs/"*)
                for argument in "$@"; do
                  case "$argument" in repos/*/actions/runs/*) respond "run-${argument##*/}" ;; esac
                done
                exit 52 ;;
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
            printf '%s\0' "$@" >> "$PR_TEST_INVOCATIONS.argv-gh-app"
            printf 'process:%s\n' "$$" >> "$PR_TEST_RESPONSE_EVENTS"
            output_kind=pipe
            [[ ! -f /dev/fd/1 ]] || output_kind=file
            printf '%s|stdout=%s\n' "$*" "$output_kind" >> "$PR_TEST_INVOCATIONS.broker"
            index=0
            [[ ! -f "$PR_TEST_INVOCATIONS.broker-count" ]] || index="$(<"$PR_TEST_INVOCATIONS.broker-count")"
            index=$((index + 1))
            printf '%s\n' "$index" > "$PR_TEST_INVOCATIONS.broker-count"
            if [[ "$PR_TEST_APP_FAIL" == 1 ]] || (( PR_TEST_APP_FAIL_AT > 0 && index >= PR_TEST_APP_FAIL_AT )); then
              printf 'broker-secret\n' >&2; printf 'broker-secret\n'; exit 44
            fi
            if (( index == PR_TEST_APP_BLOCK_AT )); then
              if [[ "$PR_TEST_APP_CHILD" == 1 ]]; then bash -c 'sleep 60'
              else sleep 60; fi
            fi
            if (( index == 1 && PR_TEST_APP_ADVANCE > 0 )); then
              printf '%s\n' "$PR_TEST_APP_ADVANCE" > "$PR_TEST_CLOCK/now"
            fi
            [[ "$PR_TEST_APP_EMPTY" != 1 ]] || exit 0
            if [[ "$PR_TEST_ROTATE" == 1 ]]; then printf 'renewed-%s\n' "$index"
            else printf '%s\n' 'fake-app-credential'; fi
            """;
    }
}
