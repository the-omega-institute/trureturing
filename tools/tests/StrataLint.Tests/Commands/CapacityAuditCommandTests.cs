using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class CapacityAuditCommandTests
{
    [Fact]
    public void CapacityAuditAllowsTwentyFour()
    {
        var files = Enumerable.Range(0, RepositoryRules.DirectoryToleranceLimit)
            .Select(static index => ($"Synthetic/Bucket/File{index}.cs", "x"))
            .ToArray();

        var findings = RepositoryCapacityAudit.InspectFiles(files);

        Assert.Empty(findings);
    }

    [Fact]
    public void CapacityAuditRejectsTwentyFive()
    {
        var files = Enumerable.Range(0, RepositoryRules.DirectoryToleranceLimit + 1)
            .Select(static index => ($"Synthetic/Bucket/File{index}.cs", "x"))
            .ToArray();

        var finding = Assert.Single(RepositoryCapacityAudit.InspectFiles(files));

        Assert.Equal("Synthetic/Bucket", finding.Path);
        Assert.Contains("tolerance", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CapacityAuditCommandPropagatesViolationExitCode()
    {
        var console = new BufferedConsole();
        var environment = new StubCliEnvironment(
            new AdmissionOutcome.InfrastructureFailure("unused"),
            capacityAudit: CapacityAuditCommand.Render(
            [
                new RepositoryCapacityFinding(
                    "Synthetic/Bucket",
                    "directory contains 25 files"),
            ]));

        var exitCode = CliApplication.Run(["capacity-audit"], environment, console);

        Assert.Equal(1, exitCode);
        Assert.Contains("Synthetic/Bucket", console.Output, StringComparison.Ordinal);
        Assert.Empty(console.Error);
    }
}
