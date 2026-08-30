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
}
