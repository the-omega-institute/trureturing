using System.Text.Json.Nodes;
using Microsoft.Build.Framework;
using StrataLint.JudgeSeed;
using Xunit;

namespace JudgeSeedTask.Tests;

public sealed class CscExecutionLoggerTests
{
    [Fact]
    public void FailedBuildStillReportsStartedCompilerTasksWithoutReportingSuccess()
    {
        using var output = new StringWriter();
        var events = new BuildEvents();
        var logger = new CscExecutionLogger(output);
        logger.Initialize(events);

        events.Task("JudgeSeedInputs", "library.csproj");
        events.Task("Csc", "library.csproj");
        events.Finish(false);
        logger.Shutdown();

        var result = Last(output);
        Assert.Equal("complete", result["status"]!.GetValue<string>());
        Assert.Equal(1, result["count"]!.GetValue<int>());
        Assert.False(result["build_succeeded"]!.GetValue<bool>());
    }

    [Fact]
    public void InterruptedObservationCannotClaimZeroCompiles()
    {
        using var output = new StringWriter();
        var logger = new CscExecutionLogger(output);
        logger.Initialize(new BuildEvents());

        logger.Shutdown();

        AssertUnavailable(output);
    }

    [Fact]
    public void MissingTaskProjectCannotBecomeACompleteCount()
    {
        using var output = new StringWriter();
        var events = new BuildEvents();
        var logger = new CscExecutionLogger(output);
        logger.Initialize(events);

        events.Task("Csc", "");
        events.Finish(true);
        logger.Shutdown();

        AssertUnavailable(output);
    }

    [Fact]
    public void ObservationWriteFailureDoesNotThrowIntoTheBuildOrClaimZero()
    {
        using var output = new FailingWriter();
        var events = new BuildEvents();
        var logger = new CscExecutionLogger(output);
        logger.Initialize(events);

        events.Task("Csc", "library.csproj");
        events.Finish(true);
        logger.Shutdown();

        AssertUnavailable(output);
    }

    [Fact]
    public void CompilerReasonsFollowNativeTargetContextAndIgnoreOtherMessages()
    {
        using var output = new StringWriter();
        var events = new BuildEvents();
        var logger = new CscExecutionLogger(output);
        logger.Initialize(events);
        var first = new BuildEventContext(1, 2, 3, 4);
        var other = new BuildEventContext(2, 2, 3, 4);
        events.Target(first);
        events.Target(other);
        events.Message(first, "Output file library.dll does not exist.");
        events.Message(other, "other project reason");
        events.Message(first, "normal detail", MessageImportance.Normal);
        events.Task("Csc", "library.csproj", first);
        events.Message(first, "after compilation began");
        events.Finish(true);
        logger.Shutdown();

        var started = Started(output);
        Assert.Equal("captured", started["reasons_status"]!.GetValue<string>());
        Assert.Equal(new[] { "Output file library.dll does not exist." }, Reasons(started));
        Assert.False(started["reasons_truncated"]!.GetValue<bool>());
        Assert.Equal(1, Last(output)["count"]!.GetValue<int>());
    }

    [Fact]
    public void CompilerReasonLimitsAreExplicitAndUtf8Bounded()
    {
        using var output = new StringWriter();
        var events = new BuildEvents();
        var logger = new CscExecutionLogger(output);
        logger.Initialize(events);
        var context = new BuildEventContext(1, 2, 3, 4);
        events.Target(context);
        events.Message(context, string.Concat(Enumerable.Repeat("🙂", 1024)));
        for (var i = 1; i <= 9; i++) events.Message(context, "reason " + i);
        events.Task("Csc", "library.csproj", context);
        events.Finish(true);
        logger.Shutdown();

        var started = Started(output);
        var reasons = Reasons(started);
        Assert.Equal(8, reasons.Length);
        Assert.Equal(string.Concat(Enumerable.Repeat("🙂", 512)), reasons[0]);
        Assert.All(reasons, message => Assert.InRange(System.Text.Encoding.UTF8.GetByteCount(message), 0, 2048));
        Assert.Equal("reason 7", reasons[7]);
        Assert.True(started["reasons_truncated"]!.GetValue<bool>());
        Assert.True(Last(output)["build_succeeded"]!.GetValue<bool>());
    }

    [Fact]
    public void FinishedSkippedTargetCannotLeakReasonsIntoLaterCompile()
    {
        using var output = new StringWriter();
        var events = new BuildEvents();
        var logger = new CscExecutionLogger(output);
        logger.Initialize(events);
        var context = new BuildEventContext(1, 2, 3, 4);
        events.Target(context);
        events.Message(context, "old skipped target inputs");
        events.EndTarget(context);
        Assert.DoesNotContain("old skipped", output.ToString(), StringComparison.Ordinal);
        events.Task("Csc", "library.csproj", context);
        events.Finish(true);
        logger.Shutdown();

        var started = Started(output);
        Assert.Equal("unavailable", started["reasons_status"]!.GetValue<string>());
        Assert.Empty(Reasons(started));
        Assert.Equal(1, Last(output)["count"]!.GetValue<int>());
    }

    [Fact]
    public void MissingTargetContextCannotInventCompilerReasons()
    {
        using var output = new StringWriter();
        var events = new BuildEvents();
        var logger = new CscExecutionLogger(output);
        logger.Initialize(events);
        events.Message(null, "unbound input is newer");
        events.Task("Csc", "library.csproj");
        events.Finish(false);
        logger.Shutdown();

        var started = Started(output);
        Assert.Equal("unavailable", started["reasons_status"]!.GetValue<string>());
        Assert.Empty(Reasons(started));
        Assert.False(Last(output)["build_succeeded"]!.GetValue<bool>());
        Assert.Equal(1, Last(output)["count"]!.GetValue<int>());
    }

    private static JsonNode Started(StringWriter output) => Assert.Single(output.ToString()
        .Split('\n', StringSplitOptions.RemoveEmptyEntries)
        .Select(line => JsonNode.Parse(line["JUDGE_CSC ".Length..])!),
        row => row["status"]!.GetValue<string>() == "task-started");

    private static string[] Reasons(JsonNode row) => row["reasons"]!.AsArray()
        .Select(item => item!.GetValue<string>()).ToArray();

    private static void AssertUnavailable(StringWriter output)
    {
        var result = Last(output);
        Assert.Equal("unavailable", result["status"]!.GetValue<string>());
        Assert.Null(result["count"]);
    }

    private static JsonNode Last(StringWriter output) => JsonNode.Parse(output.ToString()
        .Split('\n', StringSplitOptions.RemoveEmptyEntries).Last()["JUDGE_CSC ".Length..])!;

    private sealed class FailingWriter : StringWriter
    {
        private bool first = true;
        public override void WriteLine(string? value)
        {
            if (first) { first = false; throw new IOException("fixture observation unavailable"); }
            base.WriteLine(value);
        }
    }

    private sealed class BuildEvents : IEventSource
    {
        public event TaskStartedEventHandler? TaskStarted;
        public event BuildFinishedEventHandler? BuildFinished;
        internal void Task(string name, string project, BuildEventContext? context = null) => TaskStarted?.Invoke(this,
            new TaskStartedEventArgs("", "", project, "", name) { BuildEventContext = context });
        internal void Target(BuildEventContext context) => TargetStarted?.Invoke(this,
            new TargetStartedEventArgs("", "", "_JudgeSdkCoreCompile", "library.csproj", "JudgeSeed.targets") { BuildEventContext = context });
        internal void EndTarget(BuildEventContext context) => TargetFinished?.Invoke(this,
            new TargetFinishedEventArgs("", "", "_JudgeSdkCoreCompile", "library.csproj", "JudgeSeed.targets", true) { BuildEventContext = context });
        internal void Message(BuildEventContext? context, string text, MessageImportance importance = MessageImportance.Low) => MessageRaised?.Invoke(this,
            new BuildMessageEventArgs(text, "", "fixture", importance) { BuildEventContext = context });
        internal void Finish(bool succeeded) => BuildFinished?.Invoke(this, new BuildFinishedEventArgs("", "", succeeded));
        public event AnyEventHandler AnyEventRaised { add { } remove { } }
        public event BuildStartedEventHandler BuildStarted { add { } remove { } }
        public event CustomBuildEventHandler CustomEventRaised { add { } remove { } }
        public event BuildErrorEventHandler ErrorRaised { add { } remove { } }
        public event BuildMessageEventHandler? MessageRaised;
        public event ProjectFinishedEventHandler ProjectFinished { add { } remove { } }
        public event ProjectStartedEventHandler ProjectStarted { add { } remove { } }
        public event BuildStatusEventHandler StatusEventRaised { add { } remove { } }
        public event TargetFinishedEventHandler? TargetFinished;
        public event TargetStartedEventHandler? TargetStarted;
        public event TaskFinishedEventHandler TaskFinished { add { } remove { } }
        public event BuildWarningEventHandler WarningRaised { add { } remove { } }
    }
}
