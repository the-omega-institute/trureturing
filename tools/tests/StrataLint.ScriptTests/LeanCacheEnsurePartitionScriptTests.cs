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
    public void SameMathlibMetadataChangesStillCopyPrivateDonorCache()
    {
        const string toolchain = "leanprover/lean4:v4.31.0\n";
        const string manifest = "{\"version\":\"1.1.0\",\"packages\":[{\"name\":\"mathlib\",\"rev\":\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"}]}\n";
        const string targetName = "metadata-target";
        using var repository = new LeanCachePartitionFixture(toolchain, manifest);
        var target = repository.AddWorktree(targetName);
        var targetManifest = repository.ReadBytes(Path.Combine(targetName, "lake-manifest.json"));
        ScriptHarnessScratch.WriteScratchText(Path.Combine(repository.Root, "lake-manifest.json"), manifest + "\n");
        repository.Git("add", "lake-manifest.json");
        repository.Git("commit", "-m", "change pin bytes only");
        var donorManifest = repository.ReadBytes("lake-manifest.json");
        repository.WriteCache("same partition seed\n", LeanPinSet.Create(Encoding.UTF8.GetBytes(toolchain), donorManifest));
        var runner = new LeanCachePartitionProcessRunner();

        using (var targetJson = JsonDocument.Parse(targetManifest))
        using (var donorJson = JsonDocument.Parse(donorManifest))
        {
            Assert.Equal(
                targetJson.RootElement.GetProperty("version").GetString(),
                donorJson.RootElement.GetProperty("version").GetString());
        }
        Assert.False(targetManifest.AsSpan().SequenceEqual(donorManifest));

        var result = WorktreeCommand.Run(
            repository.Root,
            ["ensure-cache", "--path", target],
            runner);

        Assert.True(result.Success, result.Error);
        Assert.Empty(result.Error);
        Assert.Equal("same partition seed\n",
            repository.ReadText(Path.Combine(targetName, ".lake", "build", "cache.bin")));
        Assert.False(TemporaryFileSystem.File.Exists(Path.Combine(target, ".lake", "cache-get.marker")));
        Assert.Equal("same partition seed\n",
            repository.ReadText(Path.Combine(".lake", "build", "cache.bin")));
        Assert.DoesNotContain(runner.Executables, static executable => Path.GetFileName(executable) == "lake");
    }
}

[CollectionDefinition("Lean cache partition environment", DisableParallelization = true)]
public sealed class LeanCachePartitionEnvironmentCollectionDefinition;

internal sealed class LeanCachePartitionFixture : IDisposable
{
    private readonly TemporaryDirectory temporary = new();
    private readonly string? previousDonors = Environment.GetEnvironmentVariable("STRATALINT_LEAN_CACHE_DONORS");
    private readonly string? previousLake = Environment.GetEnvironmentVariable("LAKE_BIN");

    internal LeanCachePartitionFixture(string toolchain, string manifest)
    {
        try
        {
            Git("init", "--initial-branch=dev");
            Git("config", "user.email", "stratalint@example.invalid");
            Git("config", "user.name", "StrataLint Tests");
            ScriptHarnessScratch.WriteScratchText(Path.Combine(Root, "lean-toolchain"), toolchain);
            ScriptHarnessScratch.WriteScratchText(Path.Combine(Root, "lake-manifest.json"), manifest);
            Git("add", "lean-toolchain", "lake-manifest.json");
            Git("commit", "-m", "fixture baseline");
            var lakeExecutable = Path.Combine(Root, "lake");
            if (OperatingSystem.IsWindows())
                ScriptHarnessScratch.WriteScratchText(lakeExecutable, string.Empty);
            else
                ScriptHarnessScratch.WriteExecutableStub(lakeExecutable, "exit 91");
            Environment.SetEnvironmentVariable("LAKE_BIN", lakeExecutable);
            Environment.SetEnvironmentVariable("STRATALINT_LEAN_CACHE_DONORS", Root);
        }
        catch
        {
            Dispose();
            throw;
        }
    }

    internal string Root => temporary.Path;

    internal byte[] ReadBytes(string relativePath) =>
        ScriptHarnessScratch.ReadScratchBytes(temporary, relativePath);

    internal string ReadText(string relativePath) =>
        ScriptHarnessScratch.ReadScratchText(temporary, relativePath);

    internal string AddWorktree(string name)
    {
        var target = Path.Combine(Root, name);
        Git("worktree", "add", "--detach", target, "HEAD");
        return target;
    }

    internal void Git(params string[] arguments)
    {
        var result = TestProcessRunner.Run("git", arguments, Root, TestBudgets.WorkflowProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
    }

    internal void WriteCache(string contents, LeanPinSet pins)
    {
        var lake = Path.Combine(Root, ".lake");
        ScriptHarnessScratch.EnsureDirectory(Path.Combine(lake, "build"));
        ScriptHarnessScratch.WriteScratchText(Path.Combine(lake, "build", "cache.bin"), contents);
        var mathlib = Path.Combine(lake, "packages", "mathlib");
        foreach (var module in new[] { "Mathlib/Algebra/Basic", "Mathlib/Topology/Basic" })
        {
            var source = Path.Combine(mathlib, module + ".lean");
            var olean = Path.Combine(mathlib, ".lake", "build", "lib", "lean", module + ".olean");
            ScriptHarnessScratch.EnsureDirectory(Path.GetDirectoryName(source)!);
            ScriptHarnessScratch.EnsureDirectory(Path.GetDirectoryName(olean)!);
            ScriptHarnessScratch.WriteScratchText(source, "-- fixture\n");
            ScriptHarnessScratch.WriteScratchText(olean, "fixture\n");
        }
        LeanCacheStamp.Write(lake, pins);
    }

    public void Dispose()
    {
        Environment.SetEnvironmentVariable("STRATALINT_LEAN_CACHE_DONORS", previousDonors);
        Environment.SetEnvironmentVariable("LAKE_BIN", previousLake);
        temporary.Dispose();
    }
}

internal sealed class LeanCachePartitionProcessRunner : IWorktreeProcessRunner
{
    internal List<string> Executables { get; } = [];

    public ProcessOutput Run(string fileName, IReadOnlyList<string> arguments, string workingDirectory, TimeSpan timeout)
    {
        Executables.Add(fileName);
        if (fileName == "lsof") return new ProcessOutput(0, [], []);
        if (fileName is "git" or "cp")
            return TestProcessRunner.Run(fileName, arguments, workingDirectory, timeout, 1024 * 1024);
        if (Path.GetFileName(fileName) == "lake")
        {
            ScriptHarnessScratch.EnsureDirectory(Path.Combine(workingDirectory, ".lake"));
            ScriptHarnessScratch.WriteScratchText(Path.Combine(workingDirectory, ".lake", "cache-get.marker"), "unexpected fetch\n");
            return new ProcessOutput(1, [], Encoding.UTF8.GetBytes("unexpected cache fetch"));
        }
        throw new InvalidOperationException($"unexpected fixture process: {fileName}");
    }
}
