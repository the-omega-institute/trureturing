using StrataLint.EngineeringScope;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using System.Xml.Linq;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.NativeTransportIntegration.Tests;

[Collection("Native transport process boundary")]
public sealed class SelectedReportTransportTests(Xunit.Abstractions.ITestOutputHelper testOutput)
{
    [Fact]
    public void SelectedReportTransportAcceptsProducedDeclaredMaterial()
    {
        using var fixture = new ResourceFixture(["lean-report"]);
        var produced = NativeReportFixture.ProduceReport(fixture.Root);
        testOutput.WriteLine(produced.Text);
        Assert.True(produced.Exit == 0, produced.Text);
        fixture.CommitPlan();
        fixture.Processes(prepareReport: false);
        using var output = new StringWriter();
        Assert.True(fixture.Run("current", output) == 0, output.ToString());
        Assert.Equal(0, Program.Run(["transport-pack", "--repository", fixture.Root, "--stage", "current",
            "--commit", fixture.Commit, "--run-id", "17", "--run-attempt", "2", "--archive", Path.Combine(fixture.Root, "build/current.tgz")],
            TestResultEvidence.Load, output, output));
        Assert.Equal(0, Program.Run(["transport-verify", "--repository", fixture.Root, "--stage", "current",
            "--commit", fixture.Commit, "--run-id", "17", "--run-attempt", "2"],
            TestResultEvidence.Load, output, output));
        Assert.Equal(new[] { "make --no-print-directory lean-report" }, File.ReadAllLines(Path.Combine(fixture.Root, "build/launched")));
    }

}
