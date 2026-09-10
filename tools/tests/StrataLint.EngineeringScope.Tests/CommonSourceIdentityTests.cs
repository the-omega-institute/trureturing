using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed class CommonSourceIdentityTests
{
    [Theory]
    [InlineData(".sshx-extra.cs", false)]
    [InlineData("local/Other.cs", false)]
    [InlineData("release/Conditional.cs", true)]
    public void UnrepresentedEvaluatedCompileInputCannotReceiveCandidateEvidence(string source, bool releaseOnly)
    {
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        WriteProject(fixture.Root, releaseOnly);
        TemporaryFileSystem.File.AppendAllText(Path.Combine(fixture.Root, ".gitignore"),
            ".sshx-*\nlocal/\nrelease/\n**/obj/\n**/bin/\n");
        var before = CommonExecutionEvidence.Candidate(fixture.Root);
        var path = Path.Combine(fixture.Root, "tools/tests/First", source);
        TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(path)!);
        TemporaryFileSystem.File.WriteAllText(path, "public class AdditionalSource { }\n");

        var error = Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.Candidate(fixture.Root));

        Assert.Contains("Compile input is absent from candidate source", error.Message, StringComparison.Ordinal);
        Assert.Contains(source, error.Message, StringComparison.Ordinal);
        TemporaryFileSystem.File.Delete(path);
        Assert.Equal(before, CommonExecutionEvidence.Candidate(fixture.Root));
    }

    [Fact]
    public void DirtyRepresentedSourceChangesIdentityAndUnconsumedIgnoredFileDoesNot()
    {
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        WriteProject(fixture.Root, false);
        TemporaryFileSystem.File.AppendAllText(Path.Combine(fixture.Root, ".gitignore"), "local/\n");
        var before = CommonExecutionEvidence.Candidate(fixture.Root);
        var path = Path.Combine(fixture.Root, "tools/tests/First/Additional.cs");
        TemporaryFileSystem.File.WriteAllText(path, "public class AdditionalSource { }\n");
        var dirty = CommonExecutionEvidence.Candidate(fixture.Root);
        Assert.NotEqual(before, dirty);
        TemporaryFileSystem.Directory.CreateDirectory(Path.Combine(fixture.Root, "local"));
        TemporaryFileSystem.File.WriteAllText(Path.Combine(fixture.Root, "local/Unconsumed.cs"), "class Unconsumed { }");
        Assert.Equal(dirty, CommonExecutionEvidence.Candidate(fixture.Root));
        Assert.Equal(0, Program.RunCurrentTests(fixture.Root, (_, results) =>
        {
            fixture.WriteTrx(results, "Passed");
            return 0;
        }, TextWriter.Null));
        CommonExecutionEvidence.ValidateTests(fixture.Root);
        TemporaryFileSystem.File.AppendAllText(path, "// dirty edit\n");
        Assert.NotEqual(dirty, CommonExecutionEvidence.Candidate(fixture.Root));
        Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.ValidateTests(fixture.Root));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void EngineeringSealRejectsChangedStageStartEvenAfterNewTestsPass(bool modeOnly)
    {
        if (modeOnly && OperatingSystem.IsWindows()) return;
        using var fixture = new CurrentExecutionContractTests.CandidateFixture();
        var candidate = CommonExecutionEvidence.Candidate(fixture.Root);
        var source = Path.Combine(fixture.Root, CurrentExecutionContractTests.CandidateFixture.First);
        if (modeOnly) File.SetUnixFileMode(source, File.GetUnixFileMode(source) | UnixFileMode.UserExecute);
        else TemporaryFileSystem.File.AppendAllText(source, "\n");
        Assert.Equal(0, Program.RunCurrentTests(fixture.Root, (_, results) =>
        {
            fixture.WriteTrx(results, "Passed");
            return 0;
        }, TextWriter.Null));
        const string log = CommonExecutionEvidence.RootPath + "/fixture.log";
        TemporaryFileSystem.File.WriteAllText(Path.Combine(fixture.Root, log), "executed\n");
        var steps = CommonExecutionEvidence.EngineeringSteps
            .Select(name => new StageStep(name, 0, 0, "executed", log)).ToArray();

        var error = Assert.Throws<InvalidDataException>(() =>
            CommonExecutionEvidence.SealEngineering(fixture.Root, candidate, [log], steps));

        Assert.Equal("candidate changed during engineering", error.Message);
        Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.EngineeringPath)));
    }

    private static void WriteProject(string root, bool releaseOnly) => TemporaryFileSystem.File.WriteAllText(
        Path.Combine(root, CurrentExecutionContractTests.CandidateFixture.First),
        "<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup><TargetFramework>net10.0</TargetFramework>"
        + "<IsTestProject>true</IsTestProject></PropertyGroup>"
        + (releaseOnly ? "<ItemGroup><Compile Remove=\"release/**/*.cs\" />"
            + "<Compile Include=\"release/**/*.cs\" Condition=\"'$(Configuration)' == 'Release'\" /></ItemGroup>" : "")
        + "</Project>\n");
}
