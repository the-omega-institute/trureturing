using System.Globalization;
using System.Text.Json;
using StrataLint.Cli;
using ScratchFile = StrataLint.TestSupport.TemporaryFileSystem.File;

namespace StrataLint.Tests;

[Collection("Lean cache environment")]
public sealed class LeanCacheStampPersistenceTests
{
    [Theory]
    [InlineData(0)]
    [InlineData(23)]
    public void CorruptStampPersistenceRunsProducerAndUsesItsVerdict(int producerExit)
    {
        if (OperatingSystem.IsWindows()) return;

        using var repository = new TemporaryDirectory();
        ScriptHarnessScratch.WriteScratchText(
            Path.Combine(repository.Path, "lean-toolchain"), "leanprover/lean4:v4.31.0\n");
        ScriptHarnessScratch.WriteScratchText(
            Path.Combine(repository.Path, "lake-manifest.json"), LeanCacheFixtureFile.Manifest());
        var lake = Path.Combine(repository.Path, ".lake");
        ScriptHarnessScratch.EnsureDirectory(LeanCacheStamp.PathFor(lake));
        var olean = ProjectOleanFixture.Write(repository.Path, "Preserved");
        var producer = Path.Combine(repository.Path, "fixture-producer");
        ScriptHarnessScratch.WriteScratchText(producer, """
            #!/usr/bin/env bash
            set -euo pipefail
            if [[ "$*" == "exe cache get" ]]; then
              printf 'cache-get\n' >> cache-calls
              exit 0
            fi
            [[ "$1" == "build" ]]
            [[ -f .lake/build/lib/lean/Preserved.olean ]]
            printf 'build\n' >> producer-calls
            printf 'producer output\n'
            printf 'producer diagnostic\n' >&2
            exit "$2"
            """);
        File.SetUnixFileMode(producer, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var runner = new RecordingWorktreeProcessRunner();
        var cloner = new RecordingDirectoryCloner();

        var result = LeanCacheEnsureCommand.RunWithWriter(
            repository.Path,
            ["--", producer, "build", producerExit.ToString(CultureInfo.InvariantCulture)],
            runner,
            cloner);

        Assert.True(File.Exists(Path.Combine(repository.Path, "producer-calls")), result.Output + result.Error);
        Assert.Equal("build\n", ScriptHarnessScratch.ReadScratchText(repository, "producer-calls"));
        Assert.Equal(producerExit == 0, result.Success);
        Assert.EndsWith("producer output\n", result.Output, StringComparison.Ordinal);
        Assert.Equal("producer diagnostic\n", result.Error);
        Assert.Equal("cache-get\n", ScriptHarnessScratch.ReadScratchText(repository, "cache-calls"));
        Assert.Equal("Preserved\n", ScratchFile.ReadAllText(olean));
        Assert.True(Directory.Exists(LeanCacheStamp.PathFor(lake)));
        Assert.Equal(LeanCacheStampState.Corrupt,
            LeanCacheStamp.Inspect(lake, LeanPinSet.TryReadWorktree(repository.Path, out _)!).State);
        Assert.Empty(cloner.Invocations);
        Assert.Equal(2, runner.Invocations.Count);
        using var receipt = JsonDocument.Parse(
            result.Output["LEAN_CACHE ".Length..result.Output.IndexOf('\n', StringComparison.Ordinal)]);
        Assert.Equal("degraded", receipt.RootElement.GetProperty("status").GetString());
        Assert.Equal("cache-get", receipt.RootElement.GetProperty("method").GetString());
        Assert.Equal("corrupt", receipt.RootElement.GetProperty("stamp_miss").GetString());
        Assert.Equal("warm", receipt.RootElement.GetProperty("project_olean_state").GetString());
        var reason = receipt.RootElement.GetProperty("reason").GetString()!;
        Assert.Contains("stamp is not a regular file", reason, StringComparison.Ordinal);
        Assert.Contains("stamp publication failed", reason, StringComparison.Ordinal);
        using var released = LeanCacheWriterGuard.TryAcquire(lake);
        Assert.NotNull(released);
    }
}
