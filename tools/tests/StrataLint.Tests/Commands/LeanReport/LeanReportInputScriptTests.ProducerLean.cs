namespace StrataLint.Tests;

public sealed partial class LeanReportInputScriptTests
{
    [Fact]
    public void SupportingLeanEditRejectsProducerBaselineReuse()
    {
        using var fixture = new LeanReportInputFixture();
        const string supporting = "tools/lean-inspector/LeanInformationAudit/Nested/Registry.lean";
        fixture.WriteSource(supporting, "def companion := 1\n");
        Assert.Equal(0, fixture.CaptureProductionInput().ExitCode);
        Assert.Equal(0, fixture.Verify().ExitCode);
        fixture.WriteSource("tools/lean-inspector/README.md", "documentation only\n");
        Assert.Equal(0, fixture.Verify().ExitCode);
        fixture.Append(supporting, "def changedCompanion := 2\n");
        Assert.Equal(2, fixture.Verify().ExitCode);
    }

    [Theory]
    [InlineData("producer-paths")]
    [InlineData("scribe-producer-paths")]
    public void ProducerClosureIncludesNestedLeanOnly(string command)
    {
        using var fixture = new LeanReportInputFixture();
        const string source = "tools/lean-inspector/LeanInformationAudit/Nested/Registry.lean";
        const string readme = "tools/lean-inspector/README.md";
        fixture.WriteSource(source, "def companion := 1\n");
        fixture.WriteSource(readme, "documentation only\n");
        var result = fixture.RunCommand(command);
        Assert.Equal(0, result.ExitCode);
        Assert.Contains(source, Lines(result));
        Assert.DoesNotContain(readme, Lines(result));
    }

}
