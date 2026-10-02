using System.Text;
using StrataLint.Engine;

namespace StrataLint.WorkflowScript.Tests;

public sealed class ScribeReleaseScriptTests
{
    [Theory]
    [InlineData("hidden", "UntrackedFiles")]
    [InlineData("untracked", "UntrackedFiles")]
    [InlineData("ignored-blueprint", "UntrackedReleaseInput")]
    [InlineData("ignored-projection", "UntrackedReleaseInput")]
    [InlineData("staged", "SourceContentMismatch")]
    [InlineData("unstaged", "SourceContentMismatch")]
    [InlineData("assume-unchanged", "SourceContentMismatch")]
    [InlineData("skip-worktree", "SourceContentMismatch")]
    public void DirtyRepositoryNeverInvokesRelease(string change, string reason)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ReleaseFixture();
        fixture.Change(change);
        var result = fixture.Run();
        Assert.Equal(1, result.ExitCode);
        Assert.Contains(reason + ":", Encoding.UTF8.GetString(result.StandardError), StringComparison.Ordinal);
        Assert.DoesNotContain("release", fixture.Calls);
        Assert.DoesNotContain("verify-release", fixture.Calls);
    }

    [Fact]
    public void CleanRepositoryReleasesAndVerifiesHeadDefinitionPathsThenRemovesList()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ReleaseFixture();
        var result = fixture.Run();
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        Assert.Equal(new[] { "verify-source", "release", "verify-release" }, fixture.Calls);
        Assert.Equal(ReleaseFixture.Definition + "\n", fixture.ExpectedPaths);
        Assert.False(File.Exists(fixture.PathsFile));
    }

    [Fact]
    public void StagedOnlyChangeWithHeadBytesOnDiskReachesRelease()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ReleaseFixture();
        fixture.Change("staged-only");
        var result = fixture.Run();
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        Assert.Equal(new[] { "verify-source", "release", "verify-release" }, fixture.Calls);
    }

    [Fact]
    public void ReplacedCommitWithMatchingDiskNeverInvokesRelease()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ReleaseFixture();
        fixture.Change("replace");
        var result = fixture.Run();
        Assert.Equal(1, result.ExitCode);
        Assert.Contains("SourceContentMismatch:", Encoding.UTF8.GetString(result.StandardError), StringComparison.Ordinal);
        Assert.DoesNotContain("release", fixture.Calls);
        Assert.DoesNotContain("verify-release", fixture.Calls);
    }

    [Theory]
    [InlineData("temporary-1", "DefinitionPathsTemporaryFileFailed")]
    [InlineData("temporary-2", "SourceCommitTemporaryFileFailed")]
    [InlineData("temporary-3", "SourceTreeTemporaryFileFailed")]
    [InlineData("commit-read", "GitSourceCommitFailed")]
    [InlineData("tree-read", "GitSourceTreeFailed")]
    [InlineData("definition-paths", "GitDefinitionPathsFailed")]
    [InlineData("verify-source", "SourceContentMismatch")]
    [InlineData("release", "ReleaseFailed")]
    [InlineData("verify-release", "VerificationFailed")]
    public void FailureLeavesNoTemporaryFiles(string failure, string reason)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ReleaseFixture();
        fixture.FailAt(failure);
        var result = fixture.Run();
        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains(reason, Encoding.UTF8.GetString(result.StandardError), StringComparison.Ordinal);
    }

    private sealed class ReleaseFixture : IDisposable
    {
        internal const string Definition = "Blueprint/D5/S0/Test/Neutral.scribe.cs";
        private const string Script = "tools/scripts/scribe-release.sh";
        private readonly TemporaryDirectory scratch = new();
        private readonly string root;
        private readonly string bin;
        private readonly string calls;
        private readonly string pathsCopy;
        private readonly string pathsFile;
        private readonly string temporary;
        private readonly string gitExecutable;
        private string failure = "";

        internal ReleaseFixture()
        {
            if (OperatingSystem.IsWindows()) throw new PlatformNotSupportedException();
            root = Path.Combine(scratch.Path, "repository");
            gitExecutable = OperatingSystem.IsMacOS()
                ? Encoding.UTF8.GetString(TestProcessRunner.Run("xcrun", ["--find", "git"], scratch.Path,
                    TestBudgets.ScriptProcessHangGuard, 64 * 1024).StandardOutput).Trim()
                : "/usr/bin/git";
            bin = Path.Combine(scratch.Path, "bin");
            calls = Path.Combine(scratch.Path, "calls");
            pathsCopy = Path.Combine(scratch.Path, "paths-copy");
            pathsFile = Path.Combine(scratch.Path, "paths-file");
            temporary = Path.Combine(scratch.Path, "temporary");
            ScriptHarnessScratch.EnsureDirectory(root);
            ScriptHarnessScratch.EnsureDirectory(bin);
            ScriptHarnessScratch.EnsureDirectory(temporary);
            ScriptHarnessScratch.CopyScriptInto(Path.Combine(TestRepositoryLayout.FindRoot(), Script), Path.Combine(root, Script));
            Write("global.json", "{}\n");
            Write("tools/StrataLint.Scribe.Documents/StrataLint.Scribe.Documents.csproj", "<Project />\n");
            Write(Definition, "neutral definition\n");
            Write("Blueprint/neutral.txt", "tracked non-definition\n");
            Write("nested/neutral.txt", "nested file\n");
            Write("executable", "#!/bin/sh\nexit 0\n");
            File.SetUnixFileMode(Path.Combine(root, "executable"), UnixFileMode.UserRead
                | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
            File.CreateSymbolicLink(Path.Combine(root, "link"), "nested/neutral.txt");
            Write("Golden/Projection/neutral.json", "{}\n");
            Write(".gitignore", "*.ignored\nGenerated/\n");
            Git("init", "-q");
            Git("config", "--local", "user.name", "Neutral Fixture");
            Git("config", "--local", "user.email", "neutral@example.invalid");
            Git("add", ".");
            Git("commit", "-qm", "Neutral fixture");
            ScriptHarnessScratch.WriteExecutableStub(Path.Combine(bin, "dotnet"), """
                if [[ "$1" == --version ]]; then printf '10.0.100\n'; exit 0; fi
                while [[ "$1" != resources ]]; do shift; done
                shift
                command="$1"
                shift
                if [[ "$command" == "$RELEASE_FAIL_COMMAND" ]]; then exit 92; fi
                if [[ "$command" == verify-source ]]; then
                  printf '%s\n' "$command" >> "$RELEASE_CALLS"
                  exec "$RELEASE_DOTNET" "$RELEASE_HOST" resources verify-source "$@"
                fi
                printf '%s\n' "$command" >> "$RELEASE_CALLS"
                while [[ $# -gt 0 ]]; do
                  case "$1" in
                    --out) directory="$2" ;;
                    --paths-from) paths="$2" ;;
                  esac
                  shift 2
                done
                if [[ "$command" == release ]]; then
                  mkdir -p "$directory"
                  printf '{}\n' > "$directory/identity.json"
                else
                  [[ -n "${paths:-}" ]] || exit 91
                  cat "$paths" > "$RELEASE_PATHS_COPY"
                  printf '%s' "$paths" > "$RELEASE_PATHS_FILE"
                fi
                """);
        }

        internal void FailAt(string stage)
        {
            if (OperatingSystem.IsWindows()) throw new PlatformNotSupportedException();
            failure = stage;
            ScriptHarnessScratch.WriteExecutableStub(Path.Combine(bin, "mktemp"), """
                count=0
                [[ ! -f "$RELEASE_MKTEMP_COUNT" ]] || read -r count < "$RELEASE_MKTEMP_COUNT"
                count=$((count + 1))
                printf '%s\n' "$count" > "$RELEASE_MKTEMP_COUNT"
                [[ "$RELEASE_FAIL_COMMAND" != "temporary-$count" ]] || exit 93
                exec /usr/bin/mktemp "$@"
                """);
            ScriptHarnessScratch.WriteExecutableStub(Path.Combine(bin, "git"), """
                case "$RELEASE_FAIL_COMMAND:$1:${2:-}" in
                  commit-read:cat-file:*|tree-read:ls-tree:-r)
                    [[ "$RELEASE_FAIL_COMMAND" != tree-read || "$3" == -z ]] && exit 94 ;;
                  definition-paths:ls-tree:-r) [[ "$3" != --name-only ]] || exit 95 ;;
                esac
                exec "$RELEASE_GIT" "$@"
                """);
        }

        internal string[] Calls => ScriptHarnessScratch.ReadRecordedCalls(calls);
        internal string ExpectedPaths => ScriptHarnessScratch.ReadScratchText(pathsCopy);
        internal string PathsFile => ScriptHarnessScratch.ReadScratchText(pathsFile);

        internal void Change(string change)
        {
            switch (change)
            {
                case "hidden":
                    Git("config", "--local", "status.showUntrackedFiles", "no");
                    Write("Blueprint/D5/S0/Test/Additional.scribe.cs", "neutral definition\n");
                    break;
                case "untracked": Write("neutral.txt", "untracked\n"); break;
                case "ignored-blueprint": Write("Blueprint/neutral.ignored", "ignored\n"); break;
                case "ignored-projection": Write("Golden/Projection/neutral.ignored", "ignored\n"); break;
                case "staged":
                    Write(Definition, "staged definition\n");
                    Git("add", Definition);
                    break;
                case "staged-only":
                    Write(Definition, "staged definition\n");
                    Git("add", Definition);
                    Write(Definition, "neutral definition\n");
                    break;
                case "assume-unchanged":
                case "skip-worktree":
                    Git("update-index", "--" + change, Definition);
                    Write(Definition, "modified definition\n");
                    break;
                case "unstaged": Write(Definition, "unstaged definition\n"); break;
                case "replace":
                    Git("branch", "original", "HEAD");
                    Write(Definition, "replacement definition\n");
                    Git("add", Definition);
                    Git("commit", "-qm", "Alternative fixture");
                    Git("branch", "alternative", "HEAD");
                    Git("reset", "--hard", "original");
                    Git("replace", "original", "alternative");
                    Write(Definition, "replacement definition\n");
                    break;
            }
        }

        internal ProcessOutput Run()
        {
            var result = TestProcessRunner.Run("env",
            [$"PATH={bin}:{Environment.GetEnvironmentVariable("PATH")}", $"TMPDIR={temporary}", $"RELEASE_CALLS={calls}",
                $"RELEASE_DOTNET={Path.Combine(Environment.GetEnvironmentVariable("DOTNET_ROOT")!, "dotnet")}",
                $"RELEASE_HOST={Path.Combine(TestRepositoryLayout.FindRoot(), "tools/StrataLint.Scribe.Documents/bin/Release/net10.0/StrataLint.Scribe.Documents.dll")}",
                $"RELEASE_PATHS_COPY={pathsCopy}", $"RELEASE_PATHS_FILE={pathsFile}",
                $"RELEASE_FAIL_COMMAND={failure}", $"RELEASE_MKTEMP_COUNT={Path.Combine(scratch.Path, "temporary-count")}",
                $"RELEASE_GIT={gitExecutable}",
                "/bin/bash", Path.Combine(root, Script)],
            root, TestBudgets.ScriptProcessHangGuard, 64 * 1024);
            Assert.Empty(Directory.EnumerateFileSystemEntries(temporary));
            return result;
        }

        private void Git(params string[] arguments)
        {
            var result = TestProcessRunner.Run(gitExecutable, arguments, root, TestBudgets.ScriptProcessHangGuard, 64 * 1024);
            Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        }

        private void Write(string relative, string text)
        {
            var path = Path.Combine(root, relative);
            ScriptHarnessScratch.EnsureDirectory(Path.GetDirectoryName(path)!);
            ScriptHarnessScratch.WriteScratchText(path, text);
        }

        public void Dispose() => scratch.Dispose();
    }
}
