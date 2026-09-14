using System.Globalization;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;

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
        using var fixture = new PrivateReaderFixture();
        var root = fixture.Reader;
        var lake = Path.Combine(root, ".lake");
        File.Delete(LeanCacheStamp.PathFor(lake));
        Directory.CreateDirectory(LeanCacheStamp.PathFor(lake));
        var retained = Path.Combine(lake, "build", "retained");
        Directory.CreateDirectory(Path.GetDirectoryName(retained)!);
        File.WriteAllText(retained, "preserved");

        File.WriteAllText(fixture.Lake, "#!/bin/sh\nif [ \"$1\" = exe ]; then exit 0; fi\n"
            + "printf 'producer output\\n'; printf 'producer diagnostic\\n' >&2; exit \"$1\"\n");
        var result = LeanCacheEnsureCommand.RunWithWriter(root,
            ["--", fixture.Lake, producerExit.ToString(CultureInfo.InvariantCulture)],
            new ProductionWorktreeProcessRunner(), new ApfsDirectoryCloner());

        Assert.Equal(producerExit == 0, result.Success);
        Assert.EndsWith("producer output\n", result.Output, StringComparison.Ordinal);
        Assert.Equal("producer diagnostic\n", result.Error);
        Assert.Equal(producerExit, result.ExitCode);
        Assert.Equal("preserved", File.ReadAllText(retained));
        Assert.True(Directory.Exists(LeanCacheStamp.PathFor(lake)));
        Assert.Equal(LeanCacheStampState.Corrupt,
            LeanCacheStamp.Inspect(lake, LeanPinSet.TryReadWorktree(root, out _)!).State);
        using var receipt = JsonDocument.Parse(
            result.Output["LEAN_CACHE ".Length..result.Output.IndexOf('\n', StringComparison.Ordinal)]);
        Assert.Equal("degraded", receipt.RootElement.GetProperty("status").GetString());
        Assert.Contains("stamp publication failed", receipt.RootElement.GetProperty("reason").GetString()!, StringComparison.Ordinal);
        using var released = LeanCacheWriterGuard.TryAcquire(lake);
        Assert.NotNull(released);
    }

    [Fact]
    public void MetadataAndToolchainBytesDoNotChangeTheMathlibStampPartition()
    {
        using var directory = new TemporaryDirectory();
        var original = LeanPinSet.Create(Encoding.UTF8.GetBytes("leanprover/lean4:v4.33.0\n"),
            Encoding.UTF8.GetBytes(LeanCacheFixtureFile.Manifest()));
        var changed = LeanPinSet.Create(Encoding.UTF8.GetBytes("leanprover/lean4:v4.34.0\n"),
            Encoding.UTF8.GetBytes(LeanCacheFixtureFile.Manifest() + " \n"));
        LeanCacheStamp.Write(directory.Path, original);

        Assert.True(original.SamePartition(changed));
        Assert.Equal(original.Sha256, changed.Sha256);
        Assert.False(original.HasSameBytes(changed));
        Assert.Equal(LeanCacheStampState.Match, LeanCacheStamp.Inspect(directory.Path, changed).State);
    }

    [Fact]
    public void MathlibRevisionChangeInvalidatesTheStampPartition()
    {
        using var directory = new TemporaryDirectory();
        var toolchain = Encoding.UTF8.GetBytes("leanprover/lean4:v4.33.0\n");
        var original = LeanPinSet.Create(toolchain, Encoding.UTF8.GetBytes(LeanCacheFixtureFile.Manifest()));
        var changed = LeanPinSet.Create(toolchain, Encoding.UTF8.GetBytes(LeanCacheFixtureFile.Manifest('f')));
        LeanCacheStamp.Write(directory.Path, original);

        Assert.False(original.SamePartition(changed));
        Assert.NotEqual(original.Sha256, changed.Sha256);
        Assert.Equal(LeanCacheStampState.Mismatch, LeanCacheStamp.Inspect(directory.Path, changed).State);
    }
}
