using StrataLint.Runtime;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ScribeScopePathsScriptTests
{
    [Theory]
    [InlineData("")]
    [InlineData("Blueprint/D5/with spaces.scribe.cs\0deleted path.md\0Blueprint/D5/with spaces.scribe.cs\0")]
    public void ExistingChangedPathsAreReturnedByteForByte(string paths)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ScopeFixture();
        fixture.WriteChangedPaths(paths);

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(Encoding.UTF8.GetBytes(paths), result.StandardOutput);
    }

    [Fact]
    public void MissingChangedPathsReturnFirstParentChanges()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ScopeFixture();
        fixture.Track("Blueprint/D5/changed.scribe.cs");
        fixture.Track("Blueprint/D5/unchanged.scribe.cs");
        fixture.Track("other tracked file.txt");
        fixture.Commit("Initial files");
        fixture.Track("Blueprint/D5/changed.scribe.cs", "changed fixture\n");
        fixture.Track("Blueprint/D5/new with spaces.scribe.cs");
        fixture.Commit("Changed and added files");
        fixture.WriteUntracked("Blueprint/D5/untracked.scribe.cs");

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(Encoding.UTF8.GetBytes(
            "Blueprint/D5/changed.scribe.cs\0Blueprint/D5/new with spaces.scribe.cs\0"),
            result.StandardOutput);
    }

    [Fact]
    public void RootCommitWithoutChangedPathsFailsWithNamedDiagnostic()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ScopeFixture();
        fixture.Track("root.txt");
        fixture.Commit("Root commit");

        var result = fixture.Run();

        Assert.Equal(2, result.ExitCode);
        Assert.Empty(result.StandardOutput);
        Assert.Contains("SCRIBE_SCOPE_FIRST_PARENT_MISSING", Encoding.UTF8.GetString(result.StandardError));
    }

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private sealed class ScopeFixture : IDisposable
    {
        private const string ScriptPath = "tools/scripts/workflow/scribe-scope-paths.sh";
        private readonly TemporaryDirectory temporary = new();
        private readonly string repository;
        private readonly string changedPaths;

        internal ScopeFixture()
        {
            repository = Path.Combine(temporary.Path, "candidate with spaces");
            changedPaths = Path.Combine(temporary.Path, "changed paths");
            ScriptHarnessScratch.CopyScriptInto(
                Path.Combine(TestRepositoryLayout.FindRoot(), ScriptPath), Path.Combine(repository, ScriptPath));
            Assert.Equal(0, Git("init", "--quiet").ExitCode);
        }

        internal void WriteChangedPaths(string paths) => ScriptHarnessScratch.WriteScratchText(changedPaths, paths);

        internal void WriteUntracked(string path, string contents = "fixture\n")
        {
            var absolutePath = Path.Combine(repository, path);
            ScriptHarnessScratch.EnsureDirectory(Path.GetDirectoryName(absolutePath)!);
            ScriptHarnessScratch.WriteScratchText(absolutePath, contents);
        }

        internal void Track(string path, string contents = "fixture\n")
        {
            WriteUntracked(path, contents);
            Assert.Equal(0, Git("add", "--", path).ExitCode);
        }

        internal void Commit(string message) => Assert.Equal(0, Git(
            "-c", "user.name=Scope Fixture", "-c", "user.email=scope-fixture@example.test",
            "-c", "commit.gpgsign=false", "commit", "--quiet", "-m", message).ExitCode);

        internal ProcessOutput Run() => TestProcessRunner.Run(
            "/bin/bash", ["--noprofile", "--norc", Path.Combine(repository, ScriptPath), changedPaths],
            temporary.Path, TestBudgets.ScriptProcessHangGuard, 1024 * 1024);

        private ProcessOutput Git(params string[] arguments) => TestProcessRunner.Run(
            "git", arguments, repository, TestBudgets.ScriptProcessHangGuard, 1024 * 1024);

        public void Dispose() => temporary.Dispose();
    }
}
