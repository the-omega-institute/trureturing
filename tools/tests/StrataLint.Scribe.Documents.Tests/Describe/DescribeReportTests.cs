using System.Text.Json;
using StrataLint.Engine;
using static StrataLint.TestSupport.DescribeReportRepositoryFixture;

namespace StrataLint.Scribe.Tests;

public sealed class DescribeReportTests
{
    [Fact]
    public void DescribeReportCliReturnsJsonRedAndExitOneForInvalidDoi()
    {
        WithRepository(
            root =>
            {
                var output = new StringWriter();
                var error = new StringWriter();

                var exit = ScribeCli.Run(DocumentAssembly.Value,
                    ["describe-report", "--json"],
                    root,
                    output,
                    error,
                    LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>()));

                Assert.Equal(1, exit);
                Assert.Equal(string.Empty, error.ToString());
                using var document = JsonDocument.Parse(output.ToString());
                Assert.Contains(
                    document.RootElement.GetProperty("red_findings").EnumerateArray(),
                    finding => finding.GetProperty("code").GetString() == "invalid-doi");
            },
            doi: "not-a-doi");
    }
}
