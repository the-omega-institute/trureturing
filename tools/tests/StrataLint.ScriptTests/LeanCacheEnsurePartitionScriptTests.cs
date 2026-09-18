using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.EngineeringScope;

namespace StrataLint.Tests;

[Collection("Lean cache partition environment")]
public sealed class LeanCacheEnsurePartitionScriptTests
{
    [Fact]
    public void SameMathlibMetadataChangesReuseNativeCacheAndIsolateReaderBuilds()
    {
        using var fixture = new LeanCachePartitionFixture();
        var donorCache = Path.Combine(fixture.Main, ".lake");
        var warmed = fixture.Command(fixture.Main, "with-cache-writer", "--", "lake", "build");
        Assert.True(warmed.ExitCode == 0, Diagnostic(warmed));
        var donorBefore = Snapshot(donorCache);
        var mainSource = File.ReadAllBytes(Path.Combine(fixture.Main, "Fixture.lean"));
        var mainOlean = Path.Combine(fixture.Main, ".lake", "build", "lib", "lean", "Fixture.olean");
        var mainBuild = File.ReadAllBytes(mainOlean);
        var pins = LeanPinSet.TryReadWorktree(fixture.Reader, out var reason);
        Assert.NotNull(pins);
        File.AppendAllText(Path.Combine(fixture.Reader, "lake-manifest.json"), " \n");
        var config = Path.Combine(fixture.Reader, "lakefile.toml");
        File.WriteAllText(config, "keywords = [\"metadata-only\"]\n" + File.ReadAllText(config));
        var changedPins = LeanPinSet.TryReadWorktree(fixture.Reader, out reason);
        Assert.NotNull(changedPins);
        Assert.True(pins.SamePartition(changedPins));
        Assert.False(pins.HasSameBytes(changedPins));

        var restored = fixture.Command(fixture.Reader, "with-cache-reader", "--", "lake", "build", "-v");

        Assert.True(restored.ExitCode == 0, Diagnostic(restored));
        var restoredOutput = Encoding.UTF8.GetString(restored.StandardOutput);
        Assert.True(restoredOutput.Contains("\"status\":\"seeded\"", StringComparison.Ordinal), Diagnostic(restored));
        Assert.DoesNotContain("Built Fixture", restoredOutput);
        Assert.Equal(mainBuild, File.ReadAllBytes(Path.Combine(fixture.Reader, ".lake", "build", "lib", "lean", "Fixture.olean")));
        Assert.Equal(donorBefore, Snapshot(donorCache));

        File.WriteAllText(Path.Combine(fixture.Reader, "Fixture.lean"), "def answer : Nat := 43\n");
        var rebuilt = fixture.Command(fixture.Reader, "with-cache-reader", "--", "lake", "build", "-v");

        Assert.True(rebuilt.ExitCode == 0, Diagnostic(rebuilt));
        Assert.Contains("Built Fixture", Encoding.UTF8.GetString(rebuilt.StandardOutput));
        Assert.Equal(mainSource, File.ReadAllBytes(Path.Combine(fixture.Main, "Fixture.lean")));
        Assert.Equal(mainBuild, File.ReadAllBytes(mainOlean));
        Assert.Equal(donorBefore, Snapshot(donorCache));
    }

    private static string Diagnostic(ProcessOutput result) =>
        Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError);

    private static string[] Snapshot(string root) => Directory.Exists(root)
        ? Directory.GetFiles(root, "*", SearchOption.AllDirectories).Order(StringComparer.Ordinal)
            .Select(path => Path.GetRelativePath(root, path) + ":" + Convert.ToHexString(SHA256.HashData(File.ReadAllBytes(path))))
            .ToArray()
        : [];
}

[CollectionDefinition("Lean cache partition environment", DisableParallelization = true)]
public sealed class LeanCachePartitionEnvironmentCollectionDefinition;

internal sealed class LeanCachePartitionFixture : IDisposable
{
    private readonly TemporaryDirectory temporary = new();
    internal string Main { get; }
    internal string Reader { get; }

    internal LeanCachePartitionFixture()
    {
        Main = Path.Combine(temporary.Path, "main");
        Reader = Path.Combine(temporary.Path, "reader");
        var mathlib = Path.Combine(temporary.Path, "mathlib");
        Directory.CreateDirectory(Main);
        Directory.CreateDirectory(mathlib);
        Initialize(mathlib);
        File.WriteAllText(Path.Combine(mathlib, "lakefile.toml"), "name = \"mathlib\"\n");
        Git(mathlib, "add", ".");
        Git(mathlib, "commit", "-m", "empty pinned dependency");
        var revision = Git(mathlib, "rev-parse", "HEAD");
        Initialize(Main);
        File.WriteAllText(Path.Combine(Main, "lean-toolchain"), "leanprover/lean4:v4.33.0\n");
        File.WriteAllText(Path.Combine(Main, "Fixture.lean"), "def answer : Nat := 42\n");
        File.WriteAllText(Path.Combine(Main, ".gitignore"), ".lake/\n");
        File.WriteAllText(Path.Combine(Main, "lakefile.toml"),
            "name = \"fixture\"\ndefaultTargets = [\"Fixture\"]\n[[lean_lib]]\nname = \"Fixture\"\n"
            + "[[require]]\nname = \"mathlib\"\ngit = " + JsonSerializer.Serialize(mathlib)
            + "\nrev = " + JsonSerializer.Serialize(revision) + "\n");
        Assert.True(LeanLakeExecutable.TryResolve(out var lake, out var reason), reason);
        RequireSuccess(Run(lake, ["update"], Main));
        // The tiny dependency has no cache executable. Register its real Lake
        // checkout as the donor seed using the production stamp writer.
        LeanCacheStamp.Write(Path.Combine(Main, ".lake"), LeanPinSet.TryReadWorktree(Main, out _)!);
        Git(Main, "add", ".");
        Git(Main, "commit", "-m", "native cache fixture");
        var remote = Path.Combine(temporary.Path, "origin.git");
        Git(Main, "init", "--bare", remote);
        Git(Main, "remote", "add", "origin", remote);
        Git(Main, "push", "-u", "origin", "dev");
        Git(Main, "worktree", "add", "--detach", Reader);
    }

    internal ProcessOutput Command(string root, params string[] arguments) =>
        Run("/usr/bin/env", ["STRATALINT_ACCEPT_COLD_BUILD=1", "dotnet",
            typeof(WorktreeCommand).Assembly.Location, "worktree", arguments[0],
            "--path", root, .. arguments.Skip(1)], root);

    private static void Initialize(string root)
    {
        Git(root, "init", "--initial-branch=dev");
        Git(root, "config", "user.email", "fixture@example.invalid");
        Git(root, "config", "user.name", "Fixture");
    }

    private static string Git(string root, params string[] arguments)
    {
        var result = Run("git", arguments, root);
        RequireSuccess(result);
        return Encoding.UTF8.GetString(result.StandardOutput).Trim();
    }

    private static ProcessOutput Run(string file, IReadOnlyList<string> arguments, string root) =>
        TestProcessRunner.Run(file, arguments, root, TestBudgets.LeanProcessHangGuard, 1024 * 1024);

    private static void RequireSuccess(ProcessOutput result) =>
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));

    public void Dispose() => temporary.Dispose();
}
