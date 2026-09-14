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
        internal void Task(string name, string project) => TaskStarted?.Invoke(this, new TaskStartedEventArgs("", "", project, "", name));
        internal void Finish(bool succeeded) => BuildFinished?.Invoke(this, new BuildFinishedEventArgs("", "", succeeded));
        public event AnyEventHandler AnyEventRaised { add { } remove { } }
        public event BuildStartedEventHandler BuildStarted { add { } remove { } }
        public event CustomBuildEventHandler CustomEventRaised { add { } remove { } }
        public event BuildErrorEventHandler ErrorRaised { add { } remove { } }
        public event BuildMessageEventHandler MessageRaised { add { } remove { } }
        public event ProjectFinishedEventHandler ProjectFinished { add { } remove { } }
        public event ProjectStartedEventHandler ProjectStarted { add { } remove { } }
        public event BuildStatusEventHandler StatusEventRaised { add { } remove { } }
        public event TargetFinishedEventHandler TargetFinished { add { } remove { } }
        public event TargetStartedEventHandler TargetStarted { add { } remove { } }
        public event TaskFinishedEventHandler TaskFinished { add { } remove { } }
        public event BuildWarningEventHandler WarningRaised { add { } remove { } }
    }
}
