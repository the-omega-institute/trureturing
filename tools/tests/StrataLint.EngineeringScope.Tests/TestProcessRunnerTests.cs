using StrataLint.EngineeringScope;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed class TestProcessRunnerTests
{
    [Fact]
    public void InfrastructureSkipMakesTrxEvidenceFailClosed()
    {
        var resultsDirectory = Path.Combine(
            Path.GetDirectoryName(typeof(TestProcessRunnerTests).Assembly.Location)!,
            "Fixtures");

        var failure = Assert.Throws<InfrastructureUnresolvedException>(
            () => TestResultEvidence.Load(resultsDirectory));

        Assert.Contains("INFRASTRUCTURE_UNRESOLVED count=1", failure.Message, StringComparison.Ordinal);
        Assert.Contains("Synthetic.Hung", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void RuntimeConditionalSkipMessageIsRetainedAsIdentityEvidence()
    {
        var resultsDirectory = Path.Combine(
            Path.GetDirectoryName(typeof(TestProcessRunnerTests).Assembly.Location)!,
            "Fixtures",
            "runtime-conditional-skip");

        var evidence = TestResultEvidence.Load(resultsDirectory);

        Assert.Equal(1, evidence.Executed);
        Assert.Equal(
            "Live raw Lean report is absent; document graph verification requires that report.",
            evidence.NotExecutedTests[("Synthetic.Tests", "LiveTests.RuntimeConditional")]);
    }
}
