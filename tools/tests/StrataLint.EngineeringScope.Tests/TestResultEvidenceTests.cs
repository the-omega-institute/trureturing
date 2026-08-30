using StrataLint.EngineeringScope;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed class TestResultEvidenceTests
{
    [Fact]
    public void CountAssemblyFiltersExecutedIdentitiesCaseInsensitively()
    {
        var evidence = new TestResultEvidence(
            3,
            new HashSet<(string Assembly, string Id)>
            {
                ("StrataLint.EngineeringScope.Tests", "First"),
                ("stratalint.engineeringscope.tests", "Second"),
                ("StrataLint.Tests", "Third"),
            });
        var counts = new[]
        {
            "STRATALINT.ENGINEERINGSCOPE.TESTS",
            "StrataLint.Scribe.Tests",
        }.Select(evidence.CountAssembly).ToArray();

        Assert.Equal([2, 0], counts);
    }
}
