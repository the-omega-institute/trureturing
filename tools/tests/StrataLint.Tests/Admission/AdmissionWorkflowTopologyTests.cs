using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class AdmissionWorkflowTopologyTests
{
    [Fact]
    public void PullRequestDeltaJobActivatesAdmissionUsingStructuredYaml()
    {
        var bytes = Encoding.UTF8.GetBytes("""
            'on': {pull_request: {branches: [dev, integration-**]}}
            jobs: {current: {runs-on: fixture, steps: [{run: 'dotnet judge.dll check-delta'}]}}
            """);

        Assert.True(AdmissionWorkflowTopology.HasRequiredBaseGate(bytes, "dev"));
    }

    [Theory]
    [InlineData("pull_request_target", "dev", "current", "current", "check-delta")]
    [InlineData("push", "dev", "current", "current", "check-delta")]
    [InlineData("pull_request", "main", "current", "current", "check-delta")]
    [InlineData("pull_request", "dev", "baseline-admission", "current", "check-delta")]
    [InlineData("pull_request", "dev", "current", "renamed", "check-delta")]
    [InlineData("pull_request", "dev", "current", "current", "check-current")]
    public void OtherEventsBranchesAndJobsDoNotActivateAdmission(
        string trigger, string branch, string job, string name, string command)
    {
        var bytes = Encoding.UTF8.GetBytes($$"""
            on: { {{trigger}}: {branches: [{{branch}}]} }
            jobs: { {{job}}: {name: '{{name}}', runs-on: fixture, steps: [{run: 'dotnet judge.dll {{command}}'}]} }
            """);

        Assert.False(AdmissionWorkflowTopology.HasRequiredBaseGate(bytes, "dev"));
    }

    [Theory]
    [InlineData("on: [")]
    [InlineData("on: {}\njobs: []")]
    [InlineData("on: {}\njobs: {}\n---\njobs: {}")]
    public void MalformedDocumentsDoNotActivateAdmission(string yaml) =>
        Assert.False(AdmissionWorkflowTopology.HasRequiredBaseGate(Encoding.UTF8.GetBytes(yaml), "dev"));

    [Theory]
    [InlineData(".github/workflows/ci-current.yml", true)]
    [InlineData(".github/workflows/ci-tests-fixture.yml", true)]
    [InlineData(".github/workflows/ci-publication-verify.yml", true)]
    [InlineData(".github/workflows/ci-publication-verify-extra.yml", true)]
    [InlineData(".github/workflows/lean-analysis-fixtures.yml", true)]
    [InlineData(".github/workflows/ci.yml", false)]
    [InlineData(".github/workflows/ci-tests_fixture.yml", false)]
    [InlineData(".github/workflows/ci-Tests.yml", false)]
    [InlineData(".github/workflows/ci-tests-fixture.yaml", false)]
    [InlineData(".github/scripts/harness-gate.sh", false)]
    public void ControlPathRegistrationKeepsOnlyTheRequiredGateTransition(string value, bool accepted)
    {
        var policy = new RuleFixture().Build().Policy;
        Assert.True(RepoPath.TryCreate(value, out var path));

        Assert.Equal(accepted, RepositoryPathPolicy.Validate(path!, policy) is null);
    }

    [Theory]
    [InlineData(".github/workflows/ci-tests-fixture.yml")]
    [InlineData(".github/workflows/ci-current.yml")]
    [InlineData("tools/scripts/workflow/ci-entry.sh")]
    [InlineData("tools/scripts/worktree/lean_actions.py")]
    [InlineData("tools/scripts/report/lean-report-input.sh")]
    [InlineData("tools/StrataLint.Cli/Admission/ProductionCliEnvironment.Checks.cs")]
    public void SharedStageDefinitionChangesWakeDeltaDefinitionValidation(string path) =>
        Assert.True(FrozenLedgerDeltaPredicate.IsDeltaDefinitionInput(path));
}
