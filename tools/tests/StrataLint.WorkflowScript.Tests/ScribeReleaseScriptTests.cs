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
    [InlineData("staged", "DirtyIndex")]
    [InlineData("unstaged", "DirtyTrackedWorktree")]
    public void DirtyRepositoryNeverInvokesRelease(string change, string reason)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ReleaseFixture();
        fixture.Change(change);
        var result = fixture.Run();
        Assert.Equal(1, result.ExitCode);
        Assert.Contains(reason + ":", Encoding.UTF8.GetString(result.StandardError), StringComparison.Ordinal);
        Assert.Empty(fixture.Calls);
    }

    [Fact]
    public void CleanRepositoryReleasesAndVerifiesHeadDefinitionPathsThenRemovesList()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ReleaseFixture();
        var result = fixture.Run();
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        Assert.Equal(new[] { "release", "verify-release" }, fixture.Calls);
        Assert.Equal(ReleaseFixture.Definition + "\n", fixture.ExpectedPaths);
        Assert.False(File.Exists(fixture.PathsFile));
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

        internal ReleaseFixture()
        {
            if (OperatingSystem.IsWindows()) throw new PlatformNotSupportedException();
            root = Path.Combine(scratch.Path, "repository");
            bin = Path.Combine(scratch.Path, "bin");
            calls = Path.Combine(scratch.Path, "calls");
            pathsCopy = Path.Combine(scratch.Path, "paths-copy");
            pathsFile = Path.Combine(scratch.Path, "paths-file");
            ScriptHarnessScratch.EnsureDirectory(root);
            ScriptHarnessScratch.EnsureDirectory(bin);
            ScriptHarnessScratch.CopyScriptInto(Path.Combine(TestRepositoryLayout.FindRoot(), Script), Path.Combine(root, Script));
            Write("global.json", "{}\n");
            Write("tools/StrataLint.Scribe.Documents/StrataLint.Scribe.Documents.csproj", "<Project />\n");
            Write(Definition, "neutral definition\n");
            Write("Blueprint/neutral.txt", "tracked non-definition\n");
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
                case "unstaged": Write(Definition, "unstaged definition\n"); break;
            }
        }

        internal ProcessOutput Run() => TestProcessRunner.Run("env",
            [$"PATH={bin}:{Environment.GetEnvironmentVariable("PATH")}", $"RELEASE_CALLS={calls}",
                $"RELEASE_PATHS_COPY={pathsCopy}", $"RELEASE_PATHS_FILE={pathsFile}", "/bin/bash", Path.Combine(root, Script)],
            root, TestBudgets.ScriptProcessHangGuard, 64 * 1024);

        private void Git(params string[] arguments)
        {
            var result = TestProcessRunner.Run("git", arguments, root, TestBudgets.ScriptProcessHangGuard, 64 * 1024);
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
