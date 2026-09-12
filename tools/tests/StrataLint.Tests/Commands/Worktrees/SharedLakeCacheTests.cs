using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

[Collection("Lean cache environment")]
public sealed class SharedLakeCacheTests
{
    [Fact]
    public void ReaderClearsInheritedWriterPathsAndUsesPrivateDownloads()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new SharedLakeFixture();
        using var environment = fixture.InheritWriterEnvironment();
        var result = fixture.Command(fixture.Reader, "with-cache-reader", "--", "/bin/sh", "-c", """
            printf '%s\n' "MATHLIB_CACHE_DIR=$MATHLIB_CACHE_DIR" "LAKE_CACHE_DIR=$LAKE_CACHE_DIR" \
              "LAKE_ARTIFACT_CACHE=${LAKE_ARTIFACT_CACHE-}" "LAKE_RESTORE_ARTIFACTS=$LAKE_RESTORE_ARTIFACTS" \
              "ELAN_TOOLCHAIN=$ELAN_TOOLCHAIN" "LEAN_PATH=${LEAN_PATH-}" \
              "LAKE_CACHE_ARTIFACT_ENDPOINT=${LAKE_CACHE_ARTIFACT_ENDPOINT-}" "LAKE_CONFIG=$LAKE_CONFIG"
            """);
        Assert.True(result.Success, result.Error);
        Assert.Contains("MATHLIB_CACHE_DIR=" + fixture.Reader + "/.lake/mathlib-cache\n", result.Output);
        Assert.Contains("LAKE_CACHE_DIR=" + fixture.Reader + "/.lake/artifact-cache\n", result.Output);
        Assert.DoesNotContain("inherited-writer", result.Output);
        Assert.DoesNotContain("LAKE_ARTIFACT_CACHE=true", result.Output);
        Assert.Contains("LAKE_RESTORE_ARTIFACTS=true", result.Output);
        Assert.False(Directory.Exists(Path.Combine(fixture.Main, ".git", "stratalint-lake")));
    }

    [Fact]
    public void ReaderAllowsLocalMissAndPropagatesCommandFailure()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new SharedLakeFixture();
        var built = fixture.Command(fixture.Reader, "with-cache-reader", "--", "lake", "build");
        Assert.True(built.Success, built.Error);
        Assert.True(File.Exists(Path.Combine(fixture.Reader, ".lake", "build", "built")));
        var failed = fixture.Command(fixture.Reader, "with-cache-reader", "--", "/bin/sh", "-c", "exit 17");
        Assert.False(failed.Success);
        Assert.Equal(17, failed.ExitCode);
    }

    [Fact]
    public void WarmingRejectsLinkedDevDirtyMainAndWrongExecutable()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new SharedLakeFixture();
        fixture.Git(fixture.Main, "checkout", "-b", "other");
        fixture.Git(fixture.Reader, "checkout", "dev");
        Assert.Contains("physical main", fixture.Command(fixture.Reader, "warm-cache").Error);
        fixture.Git(fixture.Reader, "checkout", "--detach");
        fixture.Git(fixture.Main, "checkout", "dev");
        File.WriteAllText(Path.Combine(fixture.Main, "dirty"), "dirty");
        Assert.Contains("clean checkout", fixture.Command(fixture.Main, "warm-cache").Error);
        File.Delete(Path.Combine(fixture.Main, "dirty"));
        File.WriteAllText(fixture.Lake, "#!/bin/sh\necho 'Lake version 5.0.0 (Lean version 4.32.0)'\n");
        if (OperatingSystem.IsMacOS())
            Assert.Contains("does not match lean-toolchain", fixture.Command(fixture.Main, "warm-cache").Error);
        Assert.False(Directory.Exists(Path.Combine(fixture.Main, ".git", "stratalint-lake")));
    }

    [Fact]
    public void ReaderCannotWriteSharedFilesOrHardlinkThroughDescendants()
    {
        if (!OperatingSystem.IsMacOS()) return;
        using var fixture = new SharedLakeFixture();
        var shared = Path.Combine(fixture.Main, ".git", "stratalint-lake");
        Directory.CreateDirectory(shared);
        var source = Path.Combine(shared, "immutable");
        File.WriteAllText(source, "original");
        Assert.True(fixture.Command(fixture.Reader, "with-cache-reader", "--", "/bin/cat", source).Success);
        var result = fixture.Command(fixture.Reader, "with-cache-reader", "--", "/bin/sh", "-c",
            "(echo changed > \"$1\"); /bin/ln \"$1\" \"$2\"", "probe", source,
            Path.Combine(fixture.Reader, "link"));
        Assert.False(result.Success);
        Assert.Equal("original", File.ReadAllText(source));
        Assert.False(File.Exists(Path.Combine(fixture.Reader, "link")));
    }

    [Fact]
    public void PrivateWriterGuardExcludesEnsureAndReaderCommands()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new SharedLakeFixture();
        using var guard = LeanCacheWriterGuard.TryAcquire(Path.Combine(fixture.Reader, ".lake"), fixture.LockDirectory);
        Assert.NotNull(guard);
        Assert.False(fixture.Command(fixture.Reader, "ensure-cache").Success);
        Assert.False(fixture.Command(fixture.Reader, "with-cache-reader", "--", "lake", "build").Success);
    }

    [Fact]
    public void WarmingPublishesDetachedArtifactsAndPreservesPriorMapsOnFailure()
    {
        if (!OperatingSystem.IsMacOS()) return;
        using var fixture = new SharedLakeFixture();
        var warmed = fixture.Command(fixture.Main, "warm-cache");
        Assert.True(warmed.Success, warmed.Error);
        var shared = Path.Combine(fixture.Main, ".git", "stratalint-lake");
        var artifact = Assert.Single(Directory.GetFiles(shared, "*.art", SearchOption.AllDirectories));
        var mapping = Assert.Single(Directory.GetFiles(shared, "*.json", SearchOption.AllDirectories));
        var oldMap = File.ReadAllBytes(mapping);
        File.WriteAllText(Path.Combine(fixture.Main, ".lake", "build", "built"), "mutated donor");
        Assert.Equal("built\n", File.ReadAllText(artifact));
        File.WriteAllText(Path.Combine(fixture.Main, ".lake", "fail-publication"), "fail");
        var failed = fixture.Command(fixture.Main, "warm-cache");
        Assert.False(failed.Success);
        Assert.Equal(oldMap, File.ReadAllBytes(mapping));
        Assert.Equal("built\n", File.ReadAllText(artifact));
        Assert.Empty(Directory.GetDirectories(Path.Combine(fixture.Main, ".lake"), "cache-stage-*"));
        Assert.Empty(Directory.GetDirectories(Path.Combine(fixture.Main, ".git"), ".stratalint-lake-publish-*"));
    }

    [Fact]
    public void SharedWarmerLockDoesNotBlockReaderAndRejectsOverlappingWarmer()
    {
        if (!OperatingSystem.IsMacOS()) return;
        using var fixture = new SharedLakeFixture();
        using var held = LeanCacheWriterGuard.TryAcquire(Path.Combine(fixture.Main, ".git", "stratalint-lake"), fixture.LockDirectory);
        Assert.NotNull(held);
        var rejected = fixture.Command(fixture.Main, "warm-cache");
        Assert.False(rejected.Success);
        Assert.Contains("busy", rejected.Error);
        Assert.True(fixture.Command(fixture.Reader, "with-cache-reader", "--", "lake", "build").Success);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void TemporaryDirectoryOverridesCannotBypassWriterLocks(bool warming)
    {
        if (!OperatingSystem.IsMacOS()) return;
        using var fixture = new SharedLakeFixture();
        var target = warming ? Path.Combine(fixture.Main, ".git", "stratalint-lake")
            : Path.Combine(fixture.Reader, ".lake");
        using var held = LeanCacheWriterGuard.TryAcquire(target, fixture.LockDirectory);
        Assert.NotNull(held);
        var previous = Environment.GetEnvironmentVariable("TMPDIR");
        var alternate = Path.Combine(fixture.Main, ".git", "alternate-tmp");
        Directory.CreateDirectory(alternate);
        try
        {
            Environment.SetEnvironmentVariable("TMPDIR", alternate);
            var result = warming ? fixture.Command(fixture.Main, "warm-cache")
                : fixture.Command(fixture.Reader, "ensure-cache");
            Assert.False(result.Success);
            Assert.Contains("busy", result.Error);
        }
        finally
        {
            Environment.SetEnvironmentVariable("TMPDIR", previous);
        }
    }

    [Fact]
    public void DeniedPackageOptInRetriesLakeBuildWithAPrivateCache()
    {
        if (!OperatingSystem.IsMacOS()) return;
        using var fixture = new SharedLakeFixture();
        Assert.True(fixture.Command(fixture.Main, "warm-cache").Success);
        Assert.True(fixture.Command(fixture.Reader, "ensure-cache").Success);
        File.WriteAllText(Path.Combine(fixture.Reader, ".lake", "optin"), "true");
        var built = fixture.Command(fixture.Reader, "with-cache-reader", "--", "lake", "build");
        Assert.True(built.Success, built.Error);
        Assert.Contains("LEAN_CACHE_FALLBACK", built.Output);
        Assert.True(File.Exists(Path.Combine(fixture.Reader, ".lake", "artifact-cache", "artifacts", "optin.art")));
        Assert.Empty(Directory.GetFiles(Path.Combine(fixture.Main, ".git", "stratalint-lake"),
            "optin.art", SearchOption.AllDirectories));
    }

    [Fact]
    public void EnsureRejectsSharedLakeAndBuildSymlinksBeforeWriting()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new SharedLakeFixture();
        var target = Path.Combine(fixture.Main, "untouched");
        Directory.CreateDirectory(target);
        var lake = Path.Combine(fixture.Reader, ".lake");
        Directory.CreateSymbolicLink(lake, target);
        Assert.False(fixture.Command(fixture.Reader, "ensure-cache").Success);
        Directory.Delete(lake);
        Directory.CreateDirectory(lake);
        Directory.CreateSymbolicLink(Path.Combine(lake, "build"), target);
        Assert.False(fixture.Command(fixture.Reader, "ensure-cache").Success);
        Assert.Empty(Directory.EnumerateFileSystemEntries(target));
    }

    [Fact]
    public void MetadataChangesKeepTheSharedNamespaceAndPrivateBuildOutputs()
    {
        if (!OperatingSystem.IsMacOS()) return;
        using var fixture = new SharedLakeFixture();
        Assert.True(fixture.Command(fixture.Main, "warm-cache").Success);
        Assert.True(fixture.Command(fixture.Reader, "with-cache-reader", "--", "lake", "build").Success);
        var before = fixture.Command(fixture.Reader, "ensure-cache");
        File.AppendAllText(Path.Combine(fixture.Reader, "lake-manifest.json"), " \n");
        File.AppendAllText(Path.Combine(fixture.Reader, "lakefile.toml"), "keywords = [\"metadata\"]\n");
        var after = fixture.Command(fixture.Reader, "ensure-cache");
        Assert.True(after.Success, after.Error);
        Assert.Equal(before.Output, after.Output);
        Assert.Equal("built\n", File.ReadAllText(Path.Combine(fixture.Reader, ".lake", "build", "built")));
    }
}

internal sealed class SharedLakeFixture : IDisposable
{
    private readonly TemporaryDirectory directory = new();
    private readonly string? previousLake = Environment.GetEnvironmentVariable("LAKE_BIN");
    internal string Main { get; }
    internal string Reader { get; }
    internal string Lake { get; }
    internal string LockDirectory => Path.Combine(Main, ".git", "stratalint-lake-locks");

    internal SharedLakeFixture()
    {
        Main = Path.Combine(directory.Path, "main with spaces");
        Reader = Path.Combine(directory.Path, "reader");
        Directory.CreateDirectory(Main);
        Git(Main, "init", "-b", "dev");
        Git(Main, "config", "user.email", "fixture@example.invalid");
        Git(Main, "config", "user.name", "Fixture");
        File.WriteAllText(Path.Combine(Main, "lean-toolchain"), "leanprover/lean4:v4.33.0\n");
        File.WriteAllText(Path.Combine(Main, "lake-manifest.json"), "{\"version\":\"1.2.0\",\"packages\":[]}\n");
        File.WriteAllText(Path.Combine(Main, "lakefile.toml"), "name = \"fixture\"\n");
        File.WriteAllText(Path.Combine(Main, ".gitignore"), ".lake/\n");
        Git(Main, "add", ".");
        Git(Main, "commit", "-m", "fixture");
        var remote = Path.Combine(directory.Path, "remote.git");
        Git(Main, "init", "--bare", remote);
        Git(Main, "remote", "add", "origin", remote);
        Git(Main, "push", "-u", "origin", "dev");
        Git(Main, "worktree", "add", "--detach", Reader);
        Lake = Path.Combine(directory.Path, "lake");
        File.WriteAllText(Lake, """
            #!/bin/sh
            if [ "$1" = --version ]; then
              echo 'Lake version 5.0.0 (Lean version 4.33.0)'
            elif [ "$1" = build ]; then
              mkdir -p .lake/build
              echo built > .lake/build/built
              if [ -f .lake/optin ]; then
                mkdir -p "$LAKE_CACHE_DIR/artifacts" 2>/dev/null
                if ! (echo optin > "$LAKE_CACHE_DIR/artifacts/optin.art") 2>/dev/null; then
                  printf 'error: failed to cache artifact: operation not permitted (error code: 1)\n  file: %s/artifacts/optin.art\n' "$LAKE_CACHE_DIR" >&2
                  exit 1
                fi
              fi
              if [ "${LAKE_ARTIFACT_CACHE:-}" = true ]; then
                mkdir -p "$LAKE_CACHE_DIR/artifacts" "$LAKE_CACHE_DIR/outputs/fixture"
                rm -f "$LAKE_CACHE_DIR/artifacts/fixture.art"
                ln .lake/build/built "$LAKE_CACHE_DIR/artifacts/fixture.art"
                if [ -f .lake/fail-publication ]; then
                  echo incomplete > "$LAKE_CACHE_DIR/outputs/fixture/fixture.json"
                else
                  echo '{"schemaVersion":"2026-02-25","service":null,"data":[]}' > "$LAKE_CACHE_DIR/outputs/fixture/fixture.json"
                fi
              fi
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

    internal IDisposable InheritWriterEnvironment() => new InheritedEnvironment(new Dictionary<string, string>
    {
        ["LAKE_ARTIFACT_CACHE"] = "true", ["LAKE_CACHE_DIR"] = "inherited-writer",
        ["LAKE_RESTORE_ARTIFACTS"] = "false", ["MATHLIB_CACHE_DIR"] = "inherited-writer",
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
