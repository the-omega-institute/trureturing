using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ReviewRegressionTests
{
    [Theory]
    [InlineData(".github/workflows/diagnostics.yml", "failure()", "Retain current failure diagnostics")]
    [InlineData(".github/workflows/alternate.yaml", "${{ failure() }}", "Collect exception details")]
    [InlineData(".github/workflows/diagnostics.yml", "${{ always() && steps.check.outcome == 'failure' }}", "Inspect anomalies")]
    [InlineData(".github/workflows/diagnostics.yml", "'failure() {anomaly}'", "'Retain current failure diagnostics {anomaly}'")]
    [InlineData(".github/workflows/diagnostics.yml", "'failure() \"anomaly\"'", "'Retain current failure diagnostics \"anomaly\"'")]
    [InlineData(".github/workflows/diagnostics.yml", "'failure() {\"note\":\"drift\"'", "'Retain current failure diagnostics {\"note\":\"drift\"'")]
    [InlineData(".github/workflows/diagnostics.yml", "'failure() {\"note\":\"ok\"}'", "'Retain current failure diagnostics {\"note\":\"ok\"}'")]
    public void Sl019AcceptsActionsStepConditionsAndLabels(string path, string condition, string label)
    {
        var fixture = new RuleFixture();
        fixture.Files[path] = $"""
            jobs:
              verify:
                runs-on: ubuntu-latest
                steps:
                  - run: echo ready
                  - if: {condition}
                    name: {label}
                    run: echo diagnostics
              inspect:
                runs-on: ubuntu-latest
                steps:
                  - if: {condition}
                    name: {label}
                    run: echo diagnostics
            """ + "\n";

        var evaluation = RuleCatalog.Default.EvaluateCurrentSingle(
            RuleId.CreateKnown(19), fixture.Build().CurrentFacts);

        Assert.Empty(evaluation.Diagnostics);
    }

    [Theory]
    [InlineData("if", "'{\"anomaly\":\"drift\"}'", "unledgered anomaly")]
    [InlineData("name", "'Retain current failure diagnostics {\"anomaly\":\"drift\"}'", "unledgered anomaly")]
    [InlineData("if", "'Retain current failure diagnostics {\"anomaly\":\"drift\"'", "unknown anomaly-bearing schema")]
    [InlineData("name", "'Retain current failure diagnostics {\"anomaly\":\"drift\"'", "unknown anomaly-bearing schema")]
    [InlineData("if", "'{\"exception\":\"drift\"'", "unknown anomaly-bearing schema")]
    [InlineData("name", "'{\"exception\":\"drift\"'", "unknown anomaly-bearing schema")]
    [InlineData("if", "'{\"failure\":\"drift\"'", "unknown anomaly-bearing schema")]
    [InlineData("name", "'{\"failure\":\"drift\"'", "unknown anomaly-bearing schema")]
    [InlineData("if", "'{\"tension\":\"drift\"'", "unknown anomaly-bearing schema")]
    [InlineData("name", "'{\"tension\":\"drift\"'", "unknown anomaly-bearing schema")]
    [InlineData("if", "'{\"unresolved\":true'", "unknown anomaly-bearing schema")]
    [InlineData("name", "'{\"unresolved\":true'", "unknown anomaly-bearing schema")]
    [InlineData("if", "'{\"anomalies\":[\"drift\"]'", "unknown anomaly-bearing schema")]
    [InlineData("name", "'{\"anomalies\":[\"drift\"]'", "unknown anomaly-bearing schema")]
    [InlineData("if", "'{\"exceptions\":[\"drift\"]'", "unknown anomaly-bearing schema")]
    [InlineData("name", "'{\"exceptions\":[\"drift\"]'", "unknown anomaly-bearing schema")]
    [InlineData("if", "'{\"failures\":[\"drift\"]'", "unknown anomaly-bearing schema")]
    [InlineData("name", "'{\"failures\":[\"drift\"]'", "unknown anomaly-bearing schema")]
    [InlineData("if", "'{\"tensions\":[\"drift\"]'", "unknown anomaly-bearing schema")]
    [InlineData("name", "'{\"tensions\":[\"drift\"]'", "unknown anomaly-bearing schema")]
    [InlineData("name", "'Retain failure {\"kind\":\"failure\",\"state\":\"unresolved\"}'", "unledgered anomaly")]
    [InlineData("if", "'{\"kind\":\"failure\",\"state\":\"unexpected\"}'", "unknown anomaly-bearing schema")]
    [InlineData("name", "'{\"category\":\"failure\"}'", "unknown anomaly-bearing schema")]
    [InlineData("name", "'Retain failure \"kind\":broken'", "unknown anomaly-bearing schema")]
    [InlineData("if", "'{\"kind\":\"failure\"'", "unknown anomaly-bearing schema")]
    [InlineData("if", "\n          anomaly: drift", "unledgered anomaly")]
    [InlineData("name", "\n          kind: failure\n          state: unresolved", "unledgered anomaly")]
    [InlineData("name", "\n          category: failure", "unknown anomaly-bearing schema")]
    [InlineData("payload", "failure", "unknown anomaly-bearing schema")]
    [InlineData("payload", "'Retain current failure diagnostics {\"anomaly\":\"drift\"'", "unknown anomaly-bearing schema")]
    public void Sl019StillChecksAnomalyDataInsideActionsSteps(string field, string value, string message)
    {
        var fixture = new RuleFixture();
        const string path = ".github/workflows/diagnostics.yml";
        fixture.Files[path] = "jobs:\n  verify:\n    steps:\n      - " + field + ": " + value + "\n";
        fixture.Files[path] = fixture.Files[path].Replace(": \n", ":\n", StringComparison.Ordinal);

        var evaluation = RuleCatalog.Default.EvaluateCurrentSingle(
            RuleId.CreateKnown(19), fixture.Build().CurrentFacts);

        var diagnostic = Assert.Single(evaluation.Diagnostics, item => item.Path == path);
        Assert.Equal(message + " at $.jobs.verify.steps[0]." + field, diagnostic.Message);
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
    }

    [Theory]
    [InlineData(".github/settings.yml", "jobs:\n  verify:\n    steps:\n      - name: failure\n")]
    [InlineData(".github/workflows/diagnostics.yml", "name: failure\n")]
    [InlineData(".github/workflows/diagnostics.yml", "outer:\n  jobs:\n    verify:\n      steps:\n        - name: failure\n")]
    [InlineData(".github/workflows/diagnostics.yml", "jobs:\n  - steps:\n      - name: failure\n")]
    [InlineData(".github/workflows/diagnostics.yml", "jobs:\n  verify:\n    steps:\n      name: failure\n")]
    [InlineData(".github/workflows/diagnostics.yml", "jobs:\n  verify:\n    steps:\n      - env:\n          name: failure\n")]
    [InlineData(".github/workflows/diagnostics.yml", "jobs:\n  verify:\n    steps:\n      - name:\n          - failure\n")]
    [InlineData(".github/workflows/diagnostics.yml", "jobs:\n  verify:\n    steps:\n      - name: '{\"jobs\":{\"verify\":{\"steps\":[{\"name\":\"failure\"}]}}}'\n")]
    public void Sl019DoesNotTreatOtherPositionsAsActionsStepScalars(string path, string content)
    {
        var fixture = new RuleFixture();
        fixture.Files[path] = content;

        var evaluation = RuleCatalog.Default.EvaluateCurrentSingle(
            RuleId.CreateKnown(19), fixture.Build().CurrentFacts);

        var diagnostic = Assert.Single(evaluation.Diagnostics, item => item.Path == path);
        Assert.Contains("unknown anomaly-bearing schema", diagnostic.Message, StringComparison.Ordinal);
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
    }
}
