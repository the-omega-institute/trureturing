using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.AtomContextFixture;

namespace StrataLint.Tests;

public sealed class AtomContextCommandTests
{
    [Fact]
    public void AtomContextCommandRejectsInvalidArguments()
    {
        var fixture = Create();
        foreach (var arguments in new string[][] { [], ["--atom-id"], ["--atom-id", ""],
                     ["--atom-id", "bad"], ["--atom-id", Id(fixture.Atomized.Claims[0]), "--extra"] })
        {
            var result = fixture.Environment().AtomContext(arguments);
            Assert.False(result.Success);
            Assert.Empty(result.Output);
            Assert.StartsWith("ATOM_CONTEXT_INVALID ARGUMENTS_INVALID ", result.Error, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void AtomContextCommandRendersTypedRejection()
    {
        var fixture = Create();
        var console = new BufferedConsole();
        var exit = CliApplication.Run(["atom-context", "--atom-id", new string('0', 64)], fixture.Environment(), console);
        Assert.NotEqual(0, exit);
        Assert.Empty(console.Output);
        Assert.StartsWith("ATOM_CONTEXT_INVALID ATOM_ABSENT ", console.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void AtomContextCommandRendersSentinelsAndTexts()
    {
        var fixture = Create();
        var claims = fixture.Atomized.Claims;
        var result = fixture.Environment().AtomContext(["--atom-id", Id(claims[1])]);
        Assert.True(result.Success, result.Error);
        Assert.Empty(result.Error);
        Assert.Equal(
            $"ATOM_CONTEXT atom_id={Id(claims[1])} source_id=source source_path=docs/source.md atomizer=generic-v1 index=2/3\n"
            + $"PREVIOUS atom_id={Id(claims[0])} state=residual-open\n"
            + $"CURRENT atom_id={Id(claims[1])} state=residual-open\n"
            + $"NEXT atom_id={Id(claims[2])} state=residual-open\n"
            + "BEGIN_PREVIOUS_TEXT\n## Before\n\nBefore.\n\nEND_PREVIOUS_TEXT\n"
            + "BEGIN_CURRENT_TEXT\n## Middle\n\nMiddle.\n\nEND_CURRENT_TEXT\n"
            + "BEGIN_NEXT_TEXT\n## After\n\nAfter.\nEND_NEXT_TEXT\n", result.Output);
    }

    [Fact]
    public void AtomContextCommandRendersBoundariesAndOmitsAbsentTextBlocks()
    {
        var fixture = Create("## Alone\n\nOnly.");
        var result = fixture.Environment().AtomContext(["--atom-id", Id(fixture.Atomized.Claims.Single())]);
        Assert.True(result.Success, result.Error);
        Assert.Contains("PREVIOUS none reason=source-start\n", result.Output, StringComparison.Ordinal);
        Assert.Contains("NEXT none reason=source-end\n", result.Output, StringComparison.Ordinal);
        Assert.DoesNotContain("BEGIN_PREVIOUS_TEXT", result.Output, StringComparison.Ordinal);
        Assert.DoesNotContain("BEGIN_NEXT_TEXT", result.Output, StringComparison.Ordinal);
        Assert.Contains("Only.\nEND_CURRENT_TEXT\n", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void AtomContextCommandWritesNothing()
    {
        var fixture = Create(ListClaims, expand: true);
        using var temporary = new TemporaryDirectory();
        var raw = fixture.RawSnapshot();
        foreach (var entry in raw.Entries)
        {
            var path = Path.Combine(temporary.Path, entry.Path);
            TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            TemporaryFileSystem.File.WriteAllBytes(path, entry.Bytes.ToArray());
        }
        var before = Bytes(temporary);
        var result = fixture.Environment(temporary.Path).AtomContext(
            ["--atom-id", Id(fixture.Atomized.ClausePlans.Single().Children[1])]);
        Assert.True(result.Success, result.Error);
        Assert.Equal(before, Bytes(temporary));
        Assert.Equal(raw.Entries.Select(static entry => (entry.Path, Convert.ToHexString(entry.Bytes.AsSpan()))),
            fixture.RawSnapshot().Entries.Select(static entry => (entry.Path, Convert.ToHexString(entry.Bytes.AsSpan()))));
    }

    [Fact]
    public void AtomContextCliDispatchesToProductionEnvironment()
    {
        var fixture = Create();
        var console = new BufferedConsole();
        var exit = CliApplication.Run(["atom-context", "--atom-id", Id(fixture.Atomized.Claims[1])],
            fixture.Environment(), console);
        Assert.Equal(0, exit);
        Assert.Empty(console.Error);
        Assert.StartsWith("ATOM_CONTEXT ", console.Output, StringComparison.Ordinal);
    }

    private static string[] Bytes(TemporaryDirectory temporary) => Directory.EnumerateFiles(temporary.Path, "*", SearchOption.AllDirectories)
        .Order(StringComparer.Ordinal).Select(path => Path.GetRelativePath(temporary.Path, path) + ":"
            + Convert.ToHexString(TemporaryFileSystem.File.ReadAllBytes(path))).ToArray();
}
