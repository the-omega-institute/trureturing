using System.Xml.Linq;
using StrataLint.TestSupport;
using Xunit;
using EvidenceProgram = StrataLint.TestEvidence.Program;

namespace StrataLint.TestEvidence.Tests;

public sealed class TestEvidenceCommandTests
{
    [Theory]
    [InlineData("passed", 0)]
    [InlineData("summary-passed", 0)]
    [InlineData("ordinary-skip", 0)]
    [InlineData("hang-guard", 2)]
    [InlineData("missing", 2)]
    [InlineData("zero", 2)]
    [InlineData("failed-summary", 2)]
    [InlineData("failed-test", 2)]
    [InlineData("unknown-outcome", 2)]
    [InlineData("executed-mismatch", 2)]
    [InlineData("passed-mismatch", 2)]
    [InlineData("failed-counter", 2)]
    [InlineData("missing-definition", 2)]
    [InlineData("missing-storage", 2)]
    [InlineData("duplicate-result", 2)]
    [InlineData("invalid-root", 2)]
    public void VerifierRequiresSuccessfulConsistentTrx(string scenario, int expectedExit)
    {
        using var fixture = new TemporaryDirectory();
        var document = PassedTrx();
        var results = document.Root!.Element("Results")!;
        var definitions = document.Root.Element("TestDefinitions")!;
        var summary = document.Root.Element("ResultSummary")!;
        var counters = summary.Element("Counters")!;
        switch (scenario)
        {
            case "summary-passed": summary.SetAttributeValue("outcome", "Passed"); break;
            case "ordinary-skip" or "hang-guard":
                results.Add(new XElement("UnitTestResult", new XAttribute("testId", "skip"),
                    new XAttribute("testName", "Fixture.Skips"), new XAttribute("outcome", "NotExecuted"),
                    new XElement("Output", new XElement("ErrorInfo", new XElement("Message",
                        scenario == "hang-guard" ? "infrastructure-hang-guard expired: fixture" : "ordinary skip")))));
                definitions.Add(new XElement("UnitTest", new XAttribute("id", "skip")));
                break;
            case "zero":
                results.RemoveNodes(); definitions.RemoveNodes();
                counters.SetAttributeValue("executed", 0); counters.SetAttributeValue("passed", 0);
                break;
            case "failed-summary": summary.SetAttributeValue("outcome", "Failed"); break;
            case "failed-test": results.Element("UnitTestResult")!.SetAttributeValue("outcome", "Failed"); break;
            case "unknown-outcome": results.Element("UnitTestResult")!.SetAttributeValue("outcome", "Unknown"); break;
            case "executed-mismatch": counters.SetAttributeValue("executed", 2); break;
            case "passed-mismatch": counters.SetAttributeValue("passed", 2); break;
            case "failed-counter": counters.SetAttributeValue("failed", 1); break;
            case "missing-definition": definitions.RemoveNodes(); break;
            case "missing-storage": definitions.Element("UnitTest")!.Attribute("storage")!.Remove(); break;
            case "duplicate-result": results.Add(new XElement(results.Element("UnitTestResult")!)); break;
            case "invalid-root": document.Root.Name = "Other"; break;
        }
        if (scenario != "missing") document.Save(Path.Combine(fixture.Path, "run.trx"));
        using var output = new StringWriter();
        using var error = new StringWriter();
        var exit = EvidenceProgram.Run(["verify-trx", "--results-directory", fixture.Path,
            "--required-assembly", "fixture"], fixture.Path, output, error);
        Assert.Equal(expectedExit, exit);
        if (expectedExit == 0)
        {
            Assert.Equal("", error.ToString());
            Assert.Contains("TEST_ASSEMBLY_EVIDENCE_ACCEPTED assembly=fixture evidence=trx executed=1", output.ToString(), StringComparison.Ordinal);
        }
        else
        {
            Assert.StartsWith("TEST_EVIDENCE_FAILED ", error.ToString(), StringComparison.Ordinal);
            Assert.DoesNotContain("TEST_ASSEMBLY_EVIDENCE_ACCEPTED", output.ToString(), StringComparison.Ordinal);
            if (scenario == "hang-guard") Assert.Contains("INFRASTRUCTURE_UNRESOLVED", error.ToString(), StringComparison.Ordinal);
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void EveryTrxMustSucceedAndEachRequiredAssemblyMustExecute(bool corruptSecondRun)
    {
        using var fixture = new TemporaryDirectory();
        PassedTrx().Save(Path.Combine(fixture.Path, "first.trx"));
        var second = PassedTrx();
        second.Root!.Element("TestDefinitions")!.Element("UnitTest")!.SetAttributeValue("storage", "Other.dll");
        if (corruptSecondRun) second.Root.Element("ResultSummary")!.SetAttributeValue("outcome", "Failed");
        second.Save(Path.Combine(fixture.Path, "second.trx"));
        using var output = new StringWriter();
        using var error = new StringWriter();
        Assert.Equal(corruptSecondRun ? 2 : 0, EvidenceProgram.Run(["verify-trx", "--results-directory", fixture.Path,
            "--required-assembly", "Fixture", "--required-assembly", "Other"], fixture.Path, output, error));
        if (!corruptSecondRun)
        {
            Assert.Contains("assembly=Fixture evidence=trx executed=1", output.ToString(), StringComparison.Ordinal);
            Assert.Contains("assembly=Other evidence=trx executed=1", output.ToString(), StringComparison.Ordinal);
            Assert.Equal(2, EvidenceProgram.Run(["verify-trx", "--results-directory", fixture.Path,
                "--required-assembly", "Absent"], fixture.Path, output, error));
            Assert.Contains("TRX has no executed identity from required assembly Absent", error.ToString(), StringComparison.Ordinal);
        }
    }

    [Theory]
    [InlineData("verify-trx", "--results-directory")]
    [InlineData("verify-trx", "--unknown", "value")]
    [InlineData("list-test-owner-assemblies", "--filtered", "yes")]
    [InlineData("list-test-owner-assemblies", "--target")]
    [InlineData("list-test-owner-assemblies", "--unknown", "value")]
    [InlineData("compile-proof")]
    [InlineData("compile-proof", "unknown")]
    [InlineData("compile-proof", "capability-proof", "extra")]
    [InlineData("unknown")]
    public void InvalidCommandArgumentsFailClosed(params string[] arguments)
    {
        using var output = new StringWriter();
        using var error = new StringWriter();
        Assert.Equal(2, EvidenceProgram.Run(arguments, ".", output, error));
        Assert.NotEmpty(error.ToString());
        Assert.DoesNotContain("EXPECTED_DIAGNOSTIC", output.ToString(), StringComparison.Ordinal);
    }

    private static XDocument PassedTrx() => XDocument.Parse("""
        <TestRun><Results><UnitTestResult testId="one" testName="Fixture.Runs" outcome="Passed" /></Results>
        <TestDefinitions><UnitTest id="one" storage="Fixture.dll"><TestMethod className="Fixture" name="Runs" /></UnitTest></TestDefinitions>
        <ResultSummary outcome="Completed"><Counters executed="1" passed="1" failed="0" error="0" timeout="0" aborted="0" /></ResultSummary></TestRun>
        """);
}
