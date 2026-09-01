using System.Text;
using System.Text.Json.Nodes;
using StrataLint.Engine;

namespace StrataLint.Tests;

[System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
public sealed partial class RevertSelfLockProbeScriptTests
{
    [Fact]
    public void PushNeverInvokesTheClassifierOrProbe()
    {
        foreach (var job in new[] { "engineering", "lean", "admission" })
        {
            using var fixture = new OrchestrationFixture();

            var result = fixture.Run("push", job);

            Assert.True(result.ExitCode == 0, Diagnostics(result));
            Assert.Contains("pure_revert_confirmed=false", fixture.OutputLines());
            Assert.Contains("pure_revert_state=not_applicable", fixture.OutputLines());
            Assert.Contains("job_authorized=false", fixture.OutputLines());
            Assert.Contains("run_heavy=true", fixture.OutputLines());
            Assert.Empty(fixture.CallLines());
        }
    }

    [Fact]
    public void MalformedClassifierConclusionIsIndeterminateRatherThanFalse()
    {
        using var fixture = new OrchestrationFixture();
        fixture.ClassifierBody = "printf '%s\\n' 'PURE_REVERT_TRUE malformed'";

        var result = fixture.Run("pull_request_target");

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Contains("pure_revert_confirmed=false", fixture.OutputLines());
        Assert.Contains("pure_revert_state=indeterminate", fixture.OutputLines());
        Assert.Contains("self_lock_decision=not_run", fixture.OutputLines());
        Assert.Equal(["classifier"], fixture.CallLines());
    }

    [Fact]
    public void LogicalClassifierRejectionRunsTheNormalGate()
    {
        using var fixture = new OrchestrationFixture();
        fixture.ClassifierBody = "printf '%s\\n' PURE_REVERT_NOT_INVERSE >&2; exit 5";

        var result = fixture.Run("pull_request_target");

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Contains("pure_revert_confirmed=false", fixture.OutputLines());
        Assert.Contains("pure_revert_state=false", fixture.OutputLines());
        Assert.Contains("self_lock_decision=not_run", fixture.OutputLines());
    }

    [Fact]
    public void ConfirmedProbeBuildsTreeEqualNoopAndPublishesAfterEachExecution()
    {
        using var fixture = new OrchestrationFixture();
        fixture.ProbeDecision = "SELF_LOCK_CONFIRMED";

        var result = fixture.Run("pull_request_target");

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Contains("pure_revert_confirmed=true", fixture.OutputLines());
        Assert.Contains("pure_revert_state=true", fixture.OutputLines());
        Assert.Contains("self_lock_decision=SELF_LOCK_CONFIRMED", fixture.OutputLines());
        Assert.Contains("job_authorized=true", fixture.OutputLines());
        Assert.Contains("run_heavy=false", fixture.OutputLines());
        var calls = fixture.CallLines();
        AssertOrdered(calls, "run-targeted merge", "publish j1");
        AssertOrdered(calls, "run-targeted synthetic_noop", "publish j0");
        AssertOrdered(calls, "publish j0", "evaluate");
        var noop = Assert.Single(calls, line => line.StartsWith("noop ", StringComparison.Ordinal));
        var fields = noop.Split(' ', StringSplitOptions.RemoveEmptyEntries);
        Assert.Equal(fields[1], fields[2]);
        Assert.Equal(fixture.TargetBaseSha, fields[3]);
        var marker = Observation(result);
        Assert.Equal("engineering", marker["job"]!.GetValue<string>());
        Assert.Equal("SELF_LOCK_CONFIRMED", marker["job_decision"]!.GetValue<string>());
        Assert.Equal("SELF_LOCK_CONFIRMED", marker["decisions"]!["engineering"]!.GetValue<string>());
        Assert.Equal("unsupported", marker["decisions"]!["lean"]!.GetValue<string>());
        Assert.Equal("unsupported", marker["decisions"]!["admission"]!.GetValue<string>());
        Assert.Equal(
            ["lean", "admission"],
            marker["unsupported"]!.AsArray().Select(item => item!.GetValue<string>()));
        Assert.Equal(fixture.TargetMergeSha, marker["target_merge_sha"]!.GetValue<string>());
        Assert.Equal(
            marker["j1_evaluator_digest"]!.GetValue<string>(),
            marker["j0_evaluator_digest"]!.GetValue<string>());
        Assert.Matches("^[0-9a-f]{64}$", marker["j1_publication_id"]!.GetValue<string>());
        Assert.Matches("^[0-9a-f]{64}$", marker["j0_publication_id"]!.GetValue<string>());
        Assert.Equal("j1_then_j0", marker["publication_order"]!.GetValue<string>());
        Assert.Equal("test_run_tree", marker["process_tree_barrier"]!.GetValue<string>());
    }

    [Fact]
    public void EngineeringConfirmationKeepsUnsupportedLeanAndAdmissionHeavyWorkEnabled()
    {
        using var engineering = new OrchestrationFixture();
        using var lean = new OrchestrationFixture();
        using var admission = new OrchestrationFixture();

        var engineeringResult = engineering.Run("pull_request_target", "engineering");
        var leanResult = lean.Run("pull_request_target", "lean");
        var admissionResult = admission.Run("pull_request_target", "admission");

        Assert.True(engineeringResult.ExitCode == 0, Diagnostics(engineeringResult));
        Assert.True(leanResult.ExitCode == 0, Diagnostics(leanResult));
        Assert.True(admissionResult.ExitCode == 0, Diagnostics(admissionResult));
        Assert.True(
            engineering.OutputLines().Contains("job_authorized=true"),
            Diagnostics(engineeringResult) + "\ncalls:\n" + string.Join('\n', engineering.CallLines()));
        Assert.Contains("run_heavy=false", engineering.OutputLines());
        Assert.Contains("job_decision=unsupported", lean.OutputLines());
        Assert.Contains("job_authorized=false", lean.OutputLines());
        Assert.Contains("run_heavy=true", lean.OutputLines());
        Assert.Contains("job_decision=unsupported", admission.OutputLines());
        Assert.Contains("job_authorized=false", admission.OutputLines());
        Assert.Contains("run_heavy=true", admission.OutputLines());
        Assert.Empty(lean.CallLines());
        Assert.Empty(admission.CallLines());
    }

    [Fact]
    public void DescendantFailureCannotBindToTheRevertedMerge()
    {
        using var fixture = new OrchestrationFixture(descendantBeforeRevert: true);

        var result = fixture.Run("pull_request_target");

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Contains("self_lock_decision=PROBE_INDETERMINATE", fixture.OutputLines());
        Assert.Contains("run_heavy=true", fixture.OutputLines());
        Assert.DoesNotContain(
            fixture.CallLines(),
            line => line.StartsWith("run-targeted", StringComparison.Ordinal));
    }

    [Fact]
    public void J1CannotChangeTheSealedJ0ControlInputs()
    {
        using var fixture = new OrchestrationFixture();
        fixture.AttemptJ0HeadMutationFromJ1 = true;

        var result = fixture.Run("pull_request_target");

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Contains("j0-mutation-blocked", fixture.CallLines());
        Assert.Contains("self_lock_decision=SELF_LOCK_CONFIRMED", fixture.OutputLines());
    }

    [Fact]
    public void PublisherWaitsForTheCandidateProcessTreeBarrier()
    {
        using var fixture = new OrchestrationFixture();
        fixture.SpawnDelayedJ1Descendant = true;

        var result = fixture.Run("pull_request_target");

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        var calls = fixture.CallLines();
        AssertOrdered(calls, "j1-descendant-finished", "publish j1");
        Assert.DoesNotContain("publisher-before-tree-exit", calls);
    }

    [Fact]
    public void IndeterminateProbeCannotSkipTheNormalGate()
    {
        using var fixture = new OrchestrationFixture();
        fixture.ProbeDecision = "PROBE_INDETERMINATE";

        var result = fixture.Run("pull_request_target");

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Contains("pure_revert_confirmed=false", fixture.OutputLines());
        Assert.Contains("pure_revert_state=true", fixture.OutputLines());
        Assert.Contains("self_lock_decision=PROBE_INDETERMINATE", fixture.OutputLines());
    }

    [Fact]
    public void WritableAuthorityCommonDirectoryMakesProbeIndeterminate()
    {
        using var fixture = new OrchestrationFixture();
        fixture.AllowAuthorityCanaryWrite = true;

        var result = fixture.Run("pull_request_target");

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Contains("pure_revert_confirmed=false", fixture.OutputLines());
        Assert.Contains("pure_revert_state=true", fixture.OutputLines());
        Assert.Contains("self_lock_decision=PROBE_INDETERMINATE", fixture.OutputLines());
        Assert.DoesNotContain(
            fixture.CallLines(),
            line => line.StartsWith("run-targeted", StringComparison.Ordinal));
    }

    [Fact]
    public void RunnerOwnedControlStorageIsWriteCanariedOutsideCandidateZone()
    {
        using var fixture = new OrchestrationFixture();

        var result = fixture.Run("pull_request_target");

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        var canaries = fixture.CallLines()
            .Where(line => line.StartsWith("canary ", StringComparison.Ordinal))
            .ToArray();
        Assert.Equal(4, canaries.Length);
        var control = Assert.Single(
            canaries,
            line => line.EndsWith("/probe/control", StringComparison.Ordinal));
        Assert.DoesNotContain("/candidate-zone/", control, StringComparison.Ordinal);
    }

    private static void AssertOrdered(string[] calls, string before, string after)
    {
        var beforeIndex = Array.FindIndex(calls, line => line == before);
        var afterIndex = Array.FindIndex(calls, line => line == after);
        Assert.True(beforeIndex >= 0, $"missing call: {before}");
        Assert.True(afterIndex > beforeIndex, $"{after} did not follow {before}");
    }

    private static JsonObject Observation(ProcessOutput result)
    {
        const string prefix = "REVERT_SELF_LOCK_PROBE_OBSERVATION ";
        var line = Assert.Single(
            Encoding.UTF8.GetString(result.StandardOutput)
                .Split('\n', StringSplitOptions.RemoveEmptyEntries),
            value => value.StartsWith(prefix, StringComparison.Ordinal));
        return JsonNode.Parse(line[prefix.Length..])!.AsObject();
    }

    private static string Diagnostics(ProcessOutput result) =>
        "stdout:\n" + Encoding.UTF8.GetString(result.StandardOutput)
        + "\nstderr:\n" + Encoding.UTF8.GetString(result.StandardError);
}
