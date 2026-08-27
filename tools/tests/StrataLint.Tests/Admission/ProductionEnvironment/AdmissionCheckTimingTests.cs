using System.Collections.Immutable;
using System.Globalization;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

[Collection(AdmissionCheckTimingConsoleCollection.Name)]
public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void CheckWritesOneTimingEventForEveryExecutedAdmissionPhase()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = TrustedFrozenFixture();
        var currentRaw = Snapshot(fixture.Files);
        var baselineRaw = Snapshot(fixture.Baseline);
        var gateway = new FakeRepositoryGateway(
            RawChangeSet.CreateWithKinds([(RuleFixture.RingPath, RawChangeKind.Modified)]),
            currentRaw,
            baselineRaw);
        var ledger = new ProductionFrozenLedgerAdmissionServices(
            "/repo",
            ImmutableHashSet<string>.Empty);
        var candidateReport = Path.Combine(temporary.Path, "candidate.json");
        File.WriteAllBytes(
            candidateReport,
            RawLeanReportArtifact.Write(
                Decode(currentRaw),
                LeanAxiomReport.Create(fixture.Reports)).AsSpan());
        using var timingOutput = new StringWriter(CultureInfo.InvariantCulture);
        var originalError = Console.Error;
        AdmissionOutcome outcome;
        try
        {
            Console.SetError(timingOutput);
            var environment = new ProductionCliEnvironment(
                "/repo",
                gateway,
                new FakeLeanReportSource(null),
                scribeEmissionVerifier: null,
                ledger);

            outcome = environment.Check([
                "--candidate-lean-report", candidateReport,
            ]);
        }
        finally
        {
            Console.SetError(originalError);
        }

        var admitted = Assert.IsType<AdmissionOutcome.Admitted>(outcome);
        var events = timingOutput.ToString()
            .Split('\n', StringSplitOptions.RemoveEmptyEntries)
            .Select(static line => JsonDocument.Parse(line))
            .ToArray();
        try
        {
            AssertRuleTimingEvents(events, admitted.Certificate.ExecutedRules);
            Assert.Equal(
                [
                    "repository-prepare",
                    "snapshot-load",
                    "lean-report-load",
                    "scribe-verify",
                    "policy-load",
                    "lean-closure",
                    "rule-passes",
                    "frozen-ledger-prepare",
                    "frozen-ledger-scope",
                    "frozen-ledger-catalog",
                    "frozen-ledger-delta",
                ],
                events
                    .Select(static document => document.RootElement.GetProperty("stage").GetString())
                    .Where(static stage => !stage!.StartsWith("rule-sl-", StringComparison.Ordinal)));
            foreach (var document in events)
            {
                var root = document.RootElement;
                Assert.Equal("gate_stage_timing", root.GetProperty("event").GetString());
                Assert.Equal("admission-check", root.GetProperty("scope").GetString());
                Assert.Equal("passed", root.GetProperty("status").GetString());
                Assert.True(root.GetProperty("elapsed_seconds").GetDouble() >= 0);
            }
        }
        finally
        {
            foreach (var document in events)
            {
                document.Dispose();
            }
        }
    }

    [Fact]
    public void CheckWritesOneFailedTimingEventPerExecutedRuleForRejectingRule()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = new RuleFixture();
        fixture.Apply("badge");
        var changes = RawChangeSet.Create([RuleFixture.BlueprintPath]);
        var expectedExecutedRules = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.Build(changes))).Capability.ExecutedRules;
        var gateway = new FakeRepositoryGateway(
            changes,
            Snapshot(fixture.Files),
            Snapshot(fixture.Baseline));
        var candidateReport = Path.Combine(temporary.Path, "candidate.json");
        File.WriteAllBytes(
            candidateReport,
            RawLeanReportArtifact.Write(
                Decode(Snapshot(fixture.Files)),
                LeanAxiomReport.Create(fixture.Reports)).AsSpan());
        using var timingOutput = new StringWriter(CultureInfo.InvariantCulture);
        var originalError = Console.Error;
        AdmissionOutcome outcome;
        try
        {
            Console.SetError(timingOutput);
            var environment = new ProductionCliEnvironment(
                "/repo",
                gateway,
                new FakeLeanReportSource(null));

            outcome = environment.Check([
                "--candidate-lean-report", candidateReport,
            ]);
        }
        finally
        {
            Console.SetError(originalError);
        }

        Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        var events = timingOutput.ToString()
            .Split('\n', StringSplitOptions.RemoveEmptyEntries)
            .Select(static line => JsonDocument.Parse(line))
            .ToArray();
        try
        {
            AssertRuleTimingEvents(events, expectedExecutedRules);
            var rejectedRuleEvent = Assert.Single(
                events,
                static document => document.RootElement.GetProperty("stage").GetString()
                    == "rule-sl-006");
            Assert.Equal("failed", rejectedRuleEvent.RootElement.GetProperty("status").GetString());
        }
        finally
        {
            foreach (var document in events)
            {
                document.Dispose();
            }
        }
    }

    private static void AssertRuleTimingEvents(
        IReadOnlyCollection<JsonDocument> events,
        ImmutableArray<RuleId> executedRules)
    {
        var ruleEvents = events
            .Where(static document => document.RootElement.GetProperty("stage").GetString()
                ?.StartsWith("rule-sl-", StringComparison.Ordinal) is true)
            .ToArray();
        var expectedStages = executedRules
            .Select(static rule => "rule-" + rule.Value.ToLowerInvariant())
            .Order(StringComparer.Ordinal)
            .ToArray();
        var actualStages = ruleEvents
            .Select(static document => document.RootElement.GetProperty("stage").GetString()!)
            .Order(StringComparer.Ordinal)
            .ToArray();

        Assert.Equal(expectedStages, actualStages);
        Assert.Equal(actualStages.Length, actualStages.Distinct(StringComparer.Ordinal).Count());
        foreach (var document in events)
        {
            var root = document.RootElement;
            Assert.Equal("gate_stage_timing", root.GetProperty("event").GetString());
            Assert.Equal("admission-check", root.GetProperty("scope").GetString());
            Assert.True(root.GetProperty("elapsed_seconds").GetDouble() >= 0);
        }
    }
}

[CollectionDefinition(Name, DisableParallelization = true)]
public sealed class AdmissionCheckTimingConsoleCollection
{
    public const string Name = "Admission check timing console";
}
