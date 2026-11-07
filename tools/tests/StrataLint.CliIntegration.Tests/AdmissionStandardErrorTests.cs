using System.Globalization;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using Xunit.Sdk;

namespace StrataLint.CliIntegration.Tests;

[Collection(AdmissionStandardErrorConsoleCollection.Name)]
public sealed class AdmissionStandardErrorTests
{
    private const string TimingEvent = """
        {"event":"gate_stage_timing","level":"information","scope":"admission-check","stage":"repository-read","status":"passed","elapsed_seconds":1}
        """;

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SuccessfulDeltaAcceptsStandardErrorRegardlessOfInjectedPhaseTime(bool emitTiming)
    {
        const string document = "docs/develop/theory/Fixture.MD";
        var fixture = new RuleFixture();
        fixture.Files[document] = "theory\n";
        static RawRepositorySnapshot Snapshot(Dictionary<string, string> files) =>
            RawRepositorySnapshot.Create(files.Select(static pair => RawRepositoryEntry.FromText(pair.Key, pair.Value)));
        var gateway = new FakeRepositoryGateway(
            RawChangeSet.Create([document]), Snapshot(fixture.Files), Snapshot(fixture.Baseline));
        var environment = new ProductionCliEnvironment(
            "/fixture", gateway, new FakeLeanReportSource(null),
            scribeEmissionVerifier: null, new FirstPhaseTimeProvider(emitTiming));
        using var output = new StringWriter(CultureInfo.InvariantCulture);
        using var error = new StringWriter(CultureInfo.InvariantCulture);
        var originalOutput = Console.Out;
        var originalError = Console.Error;
        int exitCode;
        try
        {
            Console.SetOut(output);
            Console.SetError(error);
            exitCode = CliApplication.Run(
                ["check-delta", "--protected-base", new string('a', 40)], environment, new SystemCliConsole());
        }
        finally
        {
            Console.SetOut(originalOutput);
            Console.SetError(originalError);
        }

        Assert.Equal(0, exitCode);
        using var verdict = JsonDocument.Parse(output.ToString());
        Assert.Equal(["SL-003", "SL-015"], verdict.RootElement.GetProperty("executed")
            .EnumerateArray().Select(static value => value.GetString()!).ToArray());
        var standardError = Encoding.UTF8.GetBytes(error.ToString());
        if (emitTiming)
        {
            var line = Assert.Single(error.ToString().Split('\n', StringSplitOptions.RemoveEmptyEntries));
            using var timing = JsonDocument.Parse(line);
            Assert.Equal("gate_stage_timing", timing.RootElement.GetProperty("event").GetString());
            Assert.Equal("repository-read", timing.RootElement.GetProperty("stage").GetString());
            Assert.Equal(1, timing.RootElement.GetProperty("elapsed_seconds").GetDouble());
        }
        else
        {
            Assert.Empty(standardError);
        }

        AdmissionStandardError.AssertOnlyTimingEvents(standardError);
        Assert.ThrowsAny<XunitException>(() => AdmissionStandardError.AssertOnlyTimingEvents(
            Encoding.UTF8.GetBytes(error.ToString() + "unexpected stderr\n")));
    }

    [Theory]
    [InlineData("passed")]
    [InlineData("failed")]
    public void TimingPhaseStatusIsInformationalAndMultipleEventsAreAccepted(string status)
    {
        var line = TimingEvent.Replace("passed", status, StringComparison.Ordinal);
        AdmissionStandardError.AssertOnlyTimingEvents(Encoding.UTF8.GetBytes(line + "\r\n" + line + "\n"));
    }

    public static TheoryData<string> UnexpectedStandardError => new()
    {
        "unexpected stderr\n",
        "gate_stage_timing\n",
        "{\n",
        "null\n",
        "[]\n",
        "\n",
        TimingEvent + "\nunexpected stderr\n",
        "unexpected stderr\n" + TimingEvent,
        TimingEvent.Replace("gate_stage_timing", "other_event", StringComparison.Ordinal),
        TimingEvent.Replace("information", "warning", StringComparison.Ordinal),
        TimingEvent.Replace("admission-check", "other-scope", StringComparison.Ordinal),
        TimingEvent.Replace("repository-read", "", StringComparison.Ordinal),
        TimingEvent.Replace("passed", "unknown", StringComparison.Ordinal),
        TimingEvent.Replace(":1}", ":-1}", StringComparison.Ordinal),
        TimingEvent.Replace(":1}", ":0.5}", StringComparison.Ordinal),
        TimingEvent.Replace(":1}", ":1e999}", StringComparison.Ordinal),
        TimingEvent.Replace(":1}", ":\"1\"}", StringComparison.Ordinal),
        TimingEvent.Replace(":1}", ":1,\"message\":\"warning\"}", StringComparison.Ordinal),
        TimingEvent.Replace("\"elapsed_seconds\":1", "\"message\":\"warning\"", StringComparison.Ordinal),
        TimingEvent.Replace("\"level\":\"information\"", "\"level\":null", StringComparison.Ordinal),
    };

    [Theory]
    [MemberData(nameof(UnexpectedStandardError))]
    public void NonTimingStandardErrorStillFails(string error) =>
        Assert.ThrowsAny<XunitException>(() => AdmissionStandardError.AssertOnlyTimingEvents(Encoding.UTF8.GetBytes(error)));

    private sealed class FirstPhaseTimeProvider(bool emitTiming) : TimeProvider
    {
        private bool started;

        public override long TimestampFrequency => TimeSpan.TicksPerSecond;

        public override long GetTimestamp()
        {
            if (!started)
            {
                started = true;
                return 0;
            }

            return emitTiming ? AdmissionCheckTiming.ReportingThreshold.Ticks : 0;
        }
    }
}

[CollectionDefinition(Name, DisableParallelization = true)]
public sealed class AdmissionStandardErrorConsoleCollection
{
    public const string Name = "Admission standard error console";
}
