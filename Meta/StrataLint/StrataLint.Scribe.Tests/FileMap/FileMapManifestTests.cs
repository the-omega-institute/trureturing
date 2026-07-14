using System.Text;

namespace StrataLint.Scribe.Tests;

public sealed class FileMapManifestTests
{
    [Fact]
    public void CanonicalManifestLoadsAllFiveKindsAndMatchesRepositoryGlobs()
    {
        var manifest = FileMapLoader.Parse(Encoding.UTF8.GetBytes("""
            schema_version = 1

            [[files]]
            pattern = "Blueprint/**/*.md"
            kind = "generated"
            produced_by = "ScribeEmitter"
            consumed_by = ["reader"]
            verified_by = ["emit-check"]

            [[files]]
            pattern = "D5/**/*.lean"
            kind = "truth"
            produced_by = "none"
            consumed_by = ["lake"]
            verified_by = ["lean-build"]

            [[files]]
            pattern = "Golden/Frozen/**/*.jsonl"
            kind = "ledger"
            produced_by = "FrozenLedgerCanonicalWriter"
            consumed_by = ["FrozenLedger"]
            verified_by = ["SL-008"]

            [[files]]
            pattern = "Golden/cases/**/*.toml"
            kind = "data"
            produced_by = "none"
            consumed_by = ["TomlGoldenLoader"]
            verified_by = ["TomlGoldenLoader"]

            [[files]]
            pattern = "Meta/StrataLint/StrataLint.*/**"
            kind = "program"
            produced_by = "none"
            consumed_by = ["dotnet"]
            verified_by = ["dotnet-test"]
            """ + "\n"), "fixture.toml");

        Assert.Equal(5, manifest.Entries.Length);
        Assert.Equal(FileMapKind.Generated, Assert.Single(
            manifest.Match("Blueprint/D5/S0/Carrier/Ring.md")).Kind);
        Assert.Equal(FileMapKind.Truth, Assert.Single(
            manifest.Match("D5/S0/Carrier/Ring.lean")).Kind);
        Assert.Equal(FileMapKind.Ledger, Assert.Single(
            manifest.Match("Golden/Frozen/events.jsonl")).Kind);
        Assert.Equal(FileMapKind.Data, Assert.Single(
            manifest.Match("Golden/cases/structure.toml")).Kind);
        Assert.Equal(FileMapKind.Program, Assert.Single(
            manifest.Match("Meta/StrataLint/StrataLint.Engine/Rules/RuleCatalog.cs")).Kind);
        Assert.Empty(manifest.Match("unclassified.bin"));
    }

    [Theory]
    [InlineData("extra = true\n", "unknown keys")]
    [InlineData("", "produced_by must name a producer")]
    public void InvalidGeneratedDeclarationIsRejectedByTheRedFixture(
        string extra,
        string expectedMessage)
    {
        var producedBy = extra.Length == 0 ? "none" : "ScribeEmitter";
        var source = $$"""
            schema_version = 1
            {{extra}}
            [[files]]
            pattern = "Generated/**/*.md"
            kind = "generated"
            produced_by = "{{producedBy}}"
            consumed_by = ["reader"]
            verified_by = ["emit-check"]
            """ + "\n";

        var exception = Assert.Throws<FormatException>(() =>
            FileMapLoader.Parse(Encoding.UTF8.GetBytes(source), "fixture.toml"));

        Assert.Contains(expectedMessage, exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void GeneratedDeclarationMustNameEmitCheck()
    {
        var source = """
            schema_version = 1

            [[files]]
            pattern = "Generated/**/*.md"
            kind = "generated"
            produced_by = "FileMapEmitter"
            consumed_by = ["reader"]
            verified_by = ["dotnet-test"]
            """ + "\n";

        var exception = Assert.Throws<FormatException>(() =>
            FileMapLoader.Parse(Encoding.UTF8.GetBytes(source), "fixture.toml"));

        Assert.Contains("emit-check", exception.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("D5/**/../Ring.lean")]
    [InlineData("/D5/**/*.lean")]
    [InlineData("D5\\**\\*.lean")]
    public void UnsafePatternIsRejectedByTheRedFixture(string pattern)
    {
        var source = $$"""
            schema_version = 1

            [[files]]
            pattern = "{{pattern.Replace("\\", "\\\\", StringComparison.Ordinal)}}"
            kind = "truth"
            produced_by = "none"
            consumed_by = ["lake"]
            verified_by = ["lean-build"]
            """ + "\n";

        var exception = Assert.Throws<FormatException>(() =>
            FileMapLoader.Parse(Encoding.UTF8.GetBytes(source), "fixture.toml"));
        Assert.Contains("unsafe FILEMAP pattern", exception.Message, StringComparison.Ordinal);
    }
}
