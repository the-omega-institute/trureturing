using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class CoverageCommandTests
{
    private const string DescriptorSelector = "D5/S0/Tower/Fixture.lean";
    private const string StateDescriptorSelector = "D5/S0/Tower/StateFixture.lean";

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
    public void CoverageUsesFrozenStateMembershipInsteadOfAcceptedEvents()
    {
        using var directory = new TemporaryDirectory();
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), Snapshot(), null);
        var source = new FakeLeanReportSource(Report());
        var environment = new ProductionCliEnvironment(directory.Path, gateway, source);
        var console = new BufferedConsole();

        var exit = CliApplication.Run(["coverage", "--json"], environment, console);

        Assert.True(exit == 0, console.Error);
        using var document = JsonDocument.Parse(console.Output);
        var artifacts = document.RootElement.GetProperty("artifacts").EnumerateArray().ToArray();
        var acceptedOnly = Assert.Single(
            artifacts,
            artifact => artifact.GetProperty("path").GetString() == DescriptorSelector);
        var stateMember = Assert.Single(
            artifacts,
            artifact => artifact.GetProperty("path").GetString() == StateDescriptorSelector);
        Assert.Equal(JsonValueKind.Null, acceptedOnly.GetProperty("ledger_state").ValueKind);
        Assert.Equal("frozen", stateMember.GetProperty("ledger_state").GetString());
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
        var files = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [RuleFixture.WorkflowPath] = """
                on: {pull_request: {branches: [dev]}, push: {branches: [dev]}}
                jobs:
                  current:
                    name: current
                    steps:
                      - run: dotnet judge.dll check-delta
                """,
            ["Meta/domains.yaml"] = TestFileMap.Domains,
            ["Meta/FILEMAP.toml"] = TestFileMap.Canonical,
            [DescriptorSelector] = "theorem fixture : True := by trivial\n",
            [StateDescriptorSelector] = "theorem stateFixture : True := by trivial\n",
            ["Golden/Frozen/state/D5/S0/Tower/StateFixture.lean.json"] =
                "{\"statement_id\":\"sha256:" + new string('c', 64) + "\",\"declarations\":[]}\n",
            [RuleFixture.TowerManifestPath] = TowerYaml,
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
            [StateDescriptorSelector] = new(
                [],
                [new LeanDeclaration("stateFixture", "theorem", "statement-v1(True)", [])
                {
                    NameKey = "ns(n0,12:stateFixture)",
                }]),
        });

    private const string TowerYaml = """
        schema_version: 1
        components:
          - id: dev-baseline
            kind: ci-jobs
            members:
              - current
            judged_by:
              - bootstrap-pr-1
            verification: verified
        bootstrap:
          id: bootstrap-pr-1
          judge: open
          reason: "Godel boundary: the trust root cannot prove its own consistency."
          commit: f3f471846dd81cfcc39ecaa386966fcf0b058464
          pull_request: 1
          verification: ASSUMED-UNVERIFIED
        """;
}
