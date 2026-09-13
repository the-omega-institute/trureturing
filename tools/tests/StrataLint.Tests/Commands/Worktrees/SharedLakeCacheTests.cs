using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

[Collection("Lean cache environment")]
public sealed class SharedLakeCacheTests
{
    [Theory]
    [InlineData("", "true", "false")]
    [InlineData("false", "true", "false")]
    [InlineData("true", "true", "false")]
    public void CanonicalEnvironmentEnablesWritesAndClearsInheritedLegacyRouting(
        string githubActions, string expectedRestore, string inheritedRestore)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new SharedLakeFixture();
        using var inherited = fixture.InheritWriterEnvironment(githubActions, inheritedRestore);
        var result = fixture.Command(fixture.Reader, "with-cache", "--", "/bin/sh", "-c", """
            printf '%s\n' "MATHLIB_CACHE_DIR=$MATHLIB_CACHE_DIR" "LAKE_CACHE_DIR=${LAKE_CACHE_DIR-unset}" \
              "LAKE_ARTIFACT_CACHE=$LAKE_ARTIFACT_CACHE" "LAKE_RESTORE_ARTIFACTS=$LAKE_RESTORE_ARTIFACTS" \
              "ELAN_TOOLCHAIN=$ELAN_TOOLCHAIN" "LEAN_PATH=${LEAN_PATH-}" \
              "LAKE_CACHE_ARTIFACT_ENDPOINT=${LAKE_CACHE_ARTIFACT_ENDPOINT-}" "LAKE_NO_CACHE=$LAKE_NO_CACHE"
            """);
        Assert.True(result.Success, result.Error);
        Assert.Contains("MATHLIB_CACHE_DIR=" + fixture.Reader + "/.lake/mathlib-cache\n", result.Output);
        Assert.Contains("LAKE_CACHE_DIR=unset\n", result.Output);
        Assert.DoesNotContain("inherited-writer", result.Output);
        Assert.Contains("LAKE_ARTIFACT_CACHE=true", result.Output);
        Assert.Contains("LAKE_RESTORE_ARTIFACTS=" + expectedRestore, result.Output);
        Assert.Contains("LAKE_NO_CACHE=true", result.Output);
        Assert.Contains("official-writable", result.Error);
        Assert.DoesNotContain("LEAN_CACHE", result.Output);
    }

    [Fact]
    public void CommandPreservesJsonStdoutAndExactFailureExit()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new SharedLakeFixture();
        var result = fixture.Command(fixture.Reader, "with-cache", "--", "/bin/sh", "-c",
            "printf '{\"artifact\":42}'; exit 17");
        Assert.False(result.Success);
        Assert.Equal(17, result.ExitCode);
        Assert.Equal("{\"artifact\":42}", result.Output);
    }

    [Fact]
    public void WarmBuildsSelectedDirtyCheckoutWithoutGitSynchronization()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new SharedLakeFixture();
        File.WriteAllText(Path.Combine(fixture.Reader, "untracked"), "owned edit");
        var result = fixture.Command(fixture.Reader, "warm-cache");
        Assert.True(result.Success, result.Error);
        Assert.Equal("built\n", File.ReadAllText(Path.Combine(fixture.Reader, ".lake/build/built")));
        Assert.False(Directory.Exists(Path.Combine(fixture.Main, ".git/stratalint-lake")));
        File.WriteAllText(fixture.Lake, "#!/bin/sh\necho 'Lake version 5.0.0 (Lean version 4.32.0)'\n");
        Assert.Contains("does not match lean-toolchain", fixture.Command(fixture.Reader, "warm-cache").Error);
    }

    [Theory]
    [InlineData("ensure-cache")]
    [InlineData("warm-cache")]
    public void WorktreeWriterGuardExcludesConcurrentPreparationAndWarming(string verb)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new SharedLakeFixture();
        using var guard = LeanCacheWriterGuard.TryAcquire(Path.Combine(fixture.Reader, ".lake"), fixture.LockDirectory);
        Assert.NotNull(guard);
        Assert.Contains("busy", fixture.Command(fixture.Reader, verb).Error);
    }

    [Fact]
    public void OldCacheAliasesArePreservedWithoutAdmissionOrMigration()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new SharedLakeFixture();
        var old = Path.Combine(fixture.Reader, ".git/stratalint-lake");
        Directory.CreateDirectory(old);
        File.WriteAllText(Path.Combine(old, "retained"), "old cache");
        File.CreateSymbolicLink(Path.Combine(old, "alias"), "retained");
        var result = fixture.Command(fixture.Reader, "ensure-cache");
        Assert.True(result.Success, result.Error);
        Assert.Equal("old cache", File.ReadAllText(Path.Combine(old, "retained")));
        Assert.Equal("retained", new FileInfo(Path.Combine(old, "alias")).LinkTarget);
    }

    [Fact]
    public void EnsureRejectsAliasedMutableBuildDirectoryBeforeWriting()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new SharedLakeFixture();
        var target = Path.Combine(fixture.Main, "untouched");
        Directory.CreateDirectory(target);
        Directory.CreateDirectory(Path.Combine(fixture.Reader, ".lake"));
        Directory.CreateSymbolicLink(Path.Combine(fixture.Reader, ".lake/build"), target);
        Assert.False(fixture.Command(fixture.Reader, "ensure-cache").Success);
        Assert.Empty(Directory.EnumerateFileSystemEntries(target));
    }
}

internal sealed class SharedLakeFixture : IDisposable
{
    private readonly TemporaryDirectory directory = new();
    private readonly string? previousLake = Environment.GetEnvironmentVariable("LAKE_BIN");
    internal string Main { get; }
    internal string Reader { get; }
    internal string Lake { get; }
    internal string LockDirectory => Path.Combine(Reader, ".git", "stratalint-lake-locks");

    internal SharedLakeFixture(bool native = false)
    {
        Main = Path.Combine(directory.Path, "main with spaces");
        Reader = Path.Combine(directory.Path, "reader");
        Directory.CreateDirectory(Main);
        Git(Main, "init", "-b", "dev");
        Git(Main, "config", "user.email", "fixture@example.invalid");
        Git(Main, "config", "user.name", "Fixture");
        File.WriteAllText(Path.Combine(Main, "lean-toolchain"), "leanprover/lean4:v4.33.0\n");
        File.WriteAllText(Path.Combine(Main, "lake-manifest.json"), "{\"version\":\"1.2.0\",\"packages\":[]}\n");
        File.WriteAllText(Path.Combine(Main, "lakefile.toml"), "name = \"fixture\"\n"
            + (native ? "defaultTargets = [\"Fixture\"]\n[[lean_lib]]\nname = \"Fixture\"\n" : ""));
        if (native) File.WriteAllText(Path.Combine(Main, "Fixture.lean"), "def answer : Nat := 42\n");
        File.WriteAllText(Path.Combine(Main, ".gitignore"), ".lake/\n");
        Git(Main, "add", ".");
        Git(Main, "commit", "-m", "fixture");
        Directory.CreateDirectory(Reader);
        foreach (var file in Directory.GetFiles(Main))
            File.Copy(file, Path.Combine(Reader, Path.GetFileName(file)));
        Git(Reader, "init", "-b", "fixture");
        Git(Reader, "config", "user.email", "fixture@example.invalid");
        Git(Reader, "config", "user.name", "Fixture");
        Git(Reader, "add", ".");
        Git(Reader, "commit", "-m", "fixture");
        if (native)
        {
            Assert.True(LeanLakeExecutable.TryResolve(out var executable, out var reason), reason);
            Lake = executable;
            return;
        }
        Lake = Path.Combine(directory.Path, "lake");
        File.WriteAllText(Lake, """
            #!/bin/sh
            if [ "$1" = --version ]; then
              echo 'Lake version 5.0.0 (Lean version 4.33.0)'
            elif [ "$1" = env ]; then
              echo "LAKE_CACHE_DIR=$PWD/.lake/fixture-official-cache"
            elif [ "$1" = build ]; then
              mkdir -p .lake/build
              echo built > .lake/build/built
            fi
            """ + "\n");
        if (!OperatingSystem.IsWindows())
            File.SetUnixFileMode(Lake, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        Environment.SetEnvironmentVariable("LAKE_BIN", Lake);
    }

    internal CommandResult Command(string root, params string[] arguments) =>
        WorktreeCommand.Run(root, [arguments[0], "--path", root, .. arguments.Skip(1)]);

    internal void Git(string root, params string[] arguments)
    {
        var result = TestProcessRunner.Run("git", arguments, root,
            BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
    }

    internal IDisposable InheritWriterEnvironment(string githubActions, string inheritedRestore) => new InheritedEnvironment(new Dictionary<string, string>
    {
        ["GITHUB_ACTIONS"] = githubActions,
        ["LAKE_ARTIFACT_CACHE"] = "true", ["LAKE_CACHE_DIR"] = "inherited-writer",
        ["LAKE_RESTORE_ARTIFACTS"] = inheritedRestore, ["MATHLIB_CACHE_DIR"] = "inherited-writer",
        ["ELAN_TOOLCHAIN"] = "inherited-writer", ["LEAN_PATH"] = "inherited-writer",
        ["LAKE_CACHE_ARTIFACT_ENDPOINT"] = "inherited-writer", ["LAKE_CONFIG"] = "inherited-writer",
    });

    public void Dispose()
    {
        Environment.SetEnvironmentVariable("LAKE_BIN", previousLake);
        directory.Dispose();
    }

    private sealed class InheritedEnvironment : IDisposable
    {
        private readonly Dictionary<string, string?> previous;
        internal InheritedEnvironment(Dictionary<string, string> values)
        {
            previous = values.Keys.ToDictionary(name => name, Environment.GetEnvironmentVariable);
            foreach (var (key, value) in values) Environment.SetEnvironmentVariable(key, value);
        }
        public void Dispose()
        {
            foreach (var (key, value) in previous) Environment.SetEnvironmentVariable(key, value);
        }
    }
}
