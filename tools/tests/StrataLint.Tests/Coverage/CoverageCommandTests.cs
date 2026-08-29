using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class CoverageCommandTests
{
    private const string DescriptorSelector = "D5/S0/Tower/Fixture.lean";

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ProductionCommandEmitsIdenticalBytesAcrossTwoRuns(bool json)
    {
        using var directory = new TemporaryDirectory();
        var raw = Snapshot();
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), raw, null);
        var source = new FakeLeanReportSource(Report());
        var environment = new ProductionCliEnvironment(directory.Path, gateway, source);
        var arguments = json ? new[] { "coverage", "--json" } : new[] { "coverage" };

        var first = new BufferedConsole();
        var second = new BufferedConsole();
        var firstExit = CliApplication.Run(arguments, environment, first);
        var secondExit = CliApplication.Run(arguments, environment, second);

        Assert.True(firstExit == 0, first.Error);
        Assert.True(secondExit == 0, second.Error);
        Assert.Equal(string.Empty, first.Error);
        Assert.Equal(string.Empty, second.Error);
        Assert.Equal(first.Output, second.Output);
        if (json)
        {
            using var document = JsonDocument.Parse(first.Output);
            Assert.Equal(1, document.RootElement.GetProperty("schema_version").GetInt32());
        }
        else
        {
            Assert.StartsWith("HARNESS_COVERAGE schema=1\n", first.Output, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void CoverageCommandTrustsAcceptedEventHashWithoutReplayingIt()
    {
        using var directory = new TemporaryDirectory();
        var recordedHash = "sha256:" + new string('e', 64);
        var gateway = new FakeRepositoryGateway(
            RawChangeSet.Create([]),
            Snapshot(recordedHash),
            null);
        var source = new FakeLeanReportSource(Report());
        var environment = new ProductionCliEnvironment(directory.Path, gateway, source);
        var console = new BufferedConsole();

        var exit = CliApplication.Run(["coverage"], environment, console);

        Assert.True(exit == 0, console.Error);
        Assert.StartsWith("HARNESS_COVERAGE schema=1\n", console.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void CoverageCommandTrustsAcceptedEventShapeWithoutReplayingIt()
    {
        using var directory = new TemporaryDirectory();
        var gateway = new FakeRepositoryGateway(
            RawChangeSet.Create([]),
            Snapshot(terminateAcceptedEvent: false),
            null);
        var source = new FakeLeanReportSource(Report());
        var environment = new ProductionCliEnvironment(directory.Path, gateway, source);
        var console = new BufferedConsole();

        var exit = CliApplication.Run(["coverage"], environment, console);

        Assert.True(exit == 0, console.Error);
        Assert.StartsWith("HARNESS_COVERAGE schema=1\n", console.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void AcceptedEventWriteGateRejectsMismatchedCandidateEventHash()
    {
        var recordedHash = "sha256:" + new string('e', 64);
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(Snapshot(recordedHash))).Snapshot;
        var accepted = Assert.Single(
            snapshot.Files.Values,
            file => FrozenLedgerChangeClassifier.IsAcceptedEventPath(file.Path.Value));

        var outcome = FrozenAcceptedEventLoader.LoadFiles([accepted]);

        var invalid = Assert.IsType<DagLedgerFilesLoadOutcome.Invalid>(outcome);
        Assert.Contains("event_hash", invalid.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void AcceptedEventWriteGateRejectsCandidateShapeViolation()
    {
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(Snapshot(terminateAcceptedEvent: false))).Snapshot;
        var accepted = Assert.Single(
            snapshot.Files.Values,
            file => FrozenLedgerChangeClassifier.IsAcceptedEventPath(file.Path.Value));

        var outcome = FrozenAcceptedEventLoader.LoadFiles([accepted]);

        var invalid = Assert.IsType<DagLedgerFilesLoadOutcome.Invalid>(outcome);
        Assert.Contains("LF-terminated", invalid.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void AcceptedEventImplementationChangeTrustsStoredEventWithoutReplayingWriteGate()
    {
        var decoded = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(Snapshot(terminateAcceptedEvent: false))).Snapshot;
        var accepted = Assert.Single(
            decoded.Files.Values,
            file => FrozenLedgerChangeClassifier.IsAcceptedEventPath(file.Path.Value));
        var fixture = new RuleFixture();
        fixture.Files[accepted.Path.Value] = accepted.Text;
        fixture.Baseline[accepted.Path.Value] = accepted.Text;
        fixture.ForkPoint[accepted.Path.Value] = accepted.Text;

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(19),
            fixture.Build(RawChangeSet.Create(
                ["tools/StrataLint.Engine/Ledger/FrozenAcceptedEventLoader.cs"])));

        Assert.DoesNotContain(evaluation.Diagnostics, diagnostic =>
            diagnostic.Path == accepted.Path.Value
            && diagnostic.Message.Contains("accepted-event write gate", StringComparison.OrdinalIgnoreCase));
    }

    [Fact]
    public void TopLevelUsageNamesCoverage()
    {
        var console = new BufferedConsole();

        var exit = CliApplication.Run(
            [],
            new StubCliEnvironment(new AdmissionOutcome.InfrastructureFailure("unused")),
            console);

        Assert.Equal(2, exit);
        Assert.Contains(
            "|coverage|",
            console.Error,
            StringComparison.Ordinal);
    }

    private static RawRepositorySnapshot Snapshot(
        string? recordedHash = null,
        bool terminateAcceptedEvent = true)
    {
        var anchor = FrozenLedgerCanonicalWriter.WriteDagEvent(
            "Freeze",
            JsonSerializer.SerializeToElement(new
            {
                declaration_statement_ids = Array.Empty<object>(),
                descriptor_selector = DescriptorSelector,
                prerequisite_frozen_node_ids = Array.Empty<string>(),
                statement_id = "sha256:" + new string('d', 64),
            }));
        var eventHash = recordedHash ?? anchor.Hash;
        var eventBytes = Encoding.UTF8.GetString(anchor.Bytes.AsSpan()).Replace(
            anchor.Hash,
            eventHash,
            StringComparison.Ordinal);
        if (!terminateAcceptedEvent)
        {
            eventBytes = eventBytes.TrimEnd('\n');
        }
        var files = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [RuleFixture.WorkflowPath] = """
                jobs:
                  baseline-admission:
                    name: Content-addressed dev baseline admission
                """,
            ["Meta/domains.yaml"] = TestRegistry.Domains,
            ["Meta/registry.yaml"] = TestRegistry.Canonical,
            [DescriptorSelector] = "theorem fixture : True := by trivial\n",
            [FrozenLedgerChangeClassifier.AcceptedRoot
                + "/" + eventHash[7..] + ".json"] = eventBytes,
            [RuleFixture.TowerManifestPath] = TowerYaml.Replace(
                "sha256:fc2ee6be0dd3cabb9b6a9118592671c9d5a81f691b7b4ad07674d9c3037ce262",
                eventHash,
                StringComparison.Ordinal),
        };
        return RawRepositorySnapshot.Create(
            files.Select(static item => RawRepositoryEntry.FromText(item.Key, item.Value)));
    }

    private static LeanAxiomReport Report() => LeanAxiomReport.Create(
        new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
        {
            [DescriptorSelector] = new(
                [],
                [new LeanDeclaration("fixture", "theorem", "statement-v1(True)", [])
                {
                    NameKey = "ns(n0,7:fixture)",
                }]),
        });

    private const string TowerYaml = """
        schema_version: 1
        components:
          - id: dev-baseline
            kind: ci-jobs
            members:
              - baseline-admission
            judged_by:
              - bootstrap-pr-1
            verification: verified
        bootstrap:
          id: bootstrap-pr-1
          judge: open
          reason: "Godel boundary: the trust root cannot prove its own consistency."
          genesis_event: sha256:fc2ee6be0dd3cabb9b6a9118592671c9d5a81f691b7b4ad07674d9c3037ce262
          commit: f3f471846dd81cfcc39ecaa386966fcf0b058464
          pull_request: 1
          verification: ASSUMED-UNVERIFIED
        """;
}
