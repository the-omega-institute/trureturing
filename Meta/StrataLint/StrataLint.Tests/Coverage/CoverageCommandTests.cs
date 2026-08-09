using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class CoverageCommandTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ProductionCommandEmitsIdenticalBytesAcrossTwoRuns(bool json)
    {
        using var directory = new TemporaryDirectory();
        var raw = Snapshot();
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), raw, null);
        var source = new FakeLeanReportSource(LeanAxiomReport.Create(
            ImmutableDictionary<string, LeanFileReport>.Empty));
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

    private static RawRepositorySnapshot Snapshot()
    {
        var genesis = FrozenLedgerCanonicalWriter.WriteDagEvent(
            "Genesis",
            JsonSerializer.SerializeToElement(new { }));
        var files = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [RuleFixture.WorkflowPath] = """
                jobs:
                  baseline-admission:
                    name: Content-addressed dev baseline admission
                """,
            ["Meta/domains.yaml"] = TestRegistry.Domains,
            ["Meta/registry.yaml"] = TestRegistry.Canonical,
            [FrozenLedgerChangeClassifier.AcceptedRoot
                + "/" + genesis.Hash[7..] + ".json"] = Encoding.UTF8.GetString(genesis.Bytes.AsSpan()),
            [RuleFixture.TowerManifestPath] = TowerYaml.Replace(
                "sha256:fc2ee6be0dd3cabb9b6a9118592671c9d5a81f691b7b4ad07674d9c3037ce262",
                genesis.Hash,
                StringComparison.Ordinal),
        };
        return RawRepositorySnapshot.Create(
            files.Select(static item => RawRepositoryEntry.FromText(item.Key, item.Value)));
    }

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
