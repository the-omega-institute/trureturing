using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class AdmissionWorkflowTopologyTests
{
    [Fact]
    public void TargetDeltaJobActivatesAdmissionUsingStructuredYaml()
    {
        var bytes = Encoding.UTF8.GetBytes("""
            'on': {pull_request_target: {branches: [dev, integration-**]}}
            jobs: {delta: {runs-on: fixture}}
            """);

        Assert.True(AdmissionWorkflowTopology.HasRequiredBaseGate(bytes, "dev"));
    }

    [Theory]
    [InlineData("pull_request", "dev", "delta", "delta")]
    [InlineData("push", "dev", "delta", "delta")]
    [InlineData("pull_request_target", "main", "delta", "delta")]
    [InlineData("pull_request_target", "dev", "baseline-admission", "delta")]
    [InlineData("pull_request_target", "dev", "delta", "renamed")]
    public void OtherEventsBranchesAndJobsDoNotActivateAdmission(
        string trigger, string branch, string job, string name)
    {
        var bytes = Encoding.UTF8.GetBytes($$"""
            on: { {{trigger}}: {branches: [{{branch}}]} }
            jobs: { {{job}}: {name: '{{name}}', runs-on: fixture} }
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
    [InlineData(".github/workflows/ci-pr.yml", true)]
    [InlineData(".github/workflows/ci-push.yml", true)]
    [InlineData(".github/workflows/lean-analysis-fixtures.yml", true)]
    [InlineData(".github/workflows/ci.yml", false)]
    // Remove this allowance with the gate after ci-push/ci-pr and required-set migration.
    [InlineData(".github/scripts/harness-gate.sh", true)]
    public void ControlPathRegistrationKeepsOnlyTheRequiredGateTransition(string value, bool accepted)
    {
        var policy = new RuleFixture().Build().Policy;
        Assert.True(RepoPath.TryCreate(value, out var path));

        Assert.Equal(accepted, RepositoryPathPolicy.Validate(path!, policy) is null);
    }

    [Theory]
    [InlineData(".github/workflows/ci-push.yml")]
    [InlineData(".github/workflows/ci-pr.yml")]
    [InlineData("tools/scripts/ci-stage.sh")]
    [InlineData("tools/scripts/ci-build-outputs.targets")]
    [InlineData("tools/scripts/workflow/ci.py")]
    [InlineData("tools/StrataLint.EngineeringScope/CommonStages.cs")]
    public void SharedStageDefinitionChangesWakeDeltaDefinitionValidation(string path) =>
        Assert.True(FrozenLedgerDeltaPredicate.IsDeltaDefinitionInput(path));
}
