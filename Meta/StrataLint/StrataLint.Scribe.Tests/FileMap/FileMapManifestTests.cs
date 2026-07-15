using System.Text;

namespace StrataLint.Scribe.Tests;

public sealed class FileMapManifestTests
{
    [Fact]
    public void RepositoryManifestClassifiesDigestionCasAsAnAppendOnlyLedger()
    {
        var manifest = FileMapLoader.LoadRepository(FindRepositoryRoot());
        var entry = Assert.Single(manifest.Match(
            "Meta/Digestion/atoms/sha256/" + new string('a', 64)));

        Assert.Equal(FileMapKind.Ledger, entry.Kind);
        Assert.Equal("IngestCommand", entry.ProducedBy);
        Assert.Equal(["DigestionCasStore"], entry.ConsumedBy.ToArray());
        Assert.Equal(["DigestionCasStore"], entry.VerifiedBy.ToArray());
        Assert.False(entry.ResidenceViolation);
    }

    private const string BlueprintPath = "Blueprint/D5/S0/Carrier/Ring.md";
    private const string FormalPath = "D5/S0/Carrier/Ring.lean";
    private const string FrozenLedgerPath = "Meta/StrataLint/Golden/Frozen/events.jsonl";
    private const string RuleCatalogPath =
        "Meta/StrataLint/StrataLint.Engine/Rules/RuleCatalog.cs";

    [Fact]
    public void CanonicalManifestLoadsAllFiveKindsAndMatchesRepositoryGlobs()
    {
        var manifest = FileMapLoader.Parse(Encoding.UTF8.GetBytes("""
            schema_version = 1

            [residence_policy]
            case_id = "RESIDENCE-EPOCH"
            desired = "data-must-live-outside-Meta/StrataLint"
            known_violation_count = 1
            status = "known-violations-frozen-under-monitoring"

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
            pattern = "Meta/StrataLint/Golden/Frozen/**/*.jsonl"
            kind = "ledger"
            produced_by = "FrozenLedgerCanonicalWriter"
            consumed_by = ["FrozenLedger"]
            verified_by = ["SL-008"]

            [[files]]
            pattern = "Meta/StrataLint/Golden/cases/**/*.toml"
            kind = "data"
            produced_by = "none"
            consumed_by = ["TomlGoldenLoader"]
            verified_by = ["TomlGoldenLoader"]
            residence_violation = true

            [[files]]
            pattern = "Meta/StrataLint/StrataLint.*/**"
            kind = "program"
            produced_by = "none"
            consumed_by = ["dotnet"]
            verified_by = ["dotnet-test"]
            """ + "\n"), "fixture.toml");

        Assert.Equal(5, manifest.Entries.Length);
        Assert.Equal("RESIDENCE-EPOCH", manifest.ResidencePolicy.CaseId);
        Assert.Equal("data-must-live-outside-Meta/StrataLint", manifest.ResidencePolicy.Desired);
        Assert.Equal(1, manifest.ResidencePolicy.KnownViolationCount);
        Assert.Equal(
            "known-violations-frozen-under-monitoring",
            manifest.ResidencePolicy.Status);
        Assert.Equal(FileMapKind.Generated, Assert.Single(
            manifest.Match(BlueprintPath)).Kind);
        Assert.Equal(FileMapKind.Truth, Assert.Single(
            manifest.Match(FormalPath)).Kind);
        Assert.Equal(FileMapKind.Ledger, Assert.Single(
            manifest.Match(FrozenLedgerPath)).Kind);
        Assert.Equal(FileMapKind.Data, Assert.Single(
            manifest.Match("Meta/StrataLint/Golden/cases/structure.toml")).Kind);
        Assert.True(Assert.Single(
            manifest.Match("Meta/StrataLint/Golden/cases/structure.toml")).ResidenceViolation);
        Assert.Equal(FileMapKind.Program, Assert.Single(
            manifest.Match(RuleCatalogPath)).Kind);
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
            [residence_policy]
            case_id = "RESIDENCE-EPOCH"
            desired = "data-must-live-outside-Meta/StrataLint"
            known_violation_count = 0
            status = "known-violations-frozen-under-monitoring"

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

            [residence_policy]
            case_id = "RESIDENCE-EPOCH"
            desired = "data-must-live-outside-Meta/StrataLint"
            known_violation_count = 0
            status = "known-violations-frozen-under-monitoring"

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
    [InlineData("program", "true", "valid only for data entries")]
    [InlineData("data", "false", "canonical boolean true")]
    public void InvalidResidenceMarkerIsRejectedByTheRedFixture(
        string kind,
        string marker,
        string expectedMessage)
    {
        var source = $$"""
            schema_version = 1

            [residence_policy]
            case_id = "RESIDENCE-EPOCH"
            desired = "data-must-live-outside-Meta/StrataLint"
            known_violation_count = 0
            status = "known-violations-frozen-under-monitoring"

            [[files]]
            pattern = "Meta/StrataLint/fixture.toml"
            kind = "{{kind}}"
            residence_violation = {{marker}}
            produced_by = "none"
            consumed_by = ["reader"]
            verified_by = ["SnapshotDecoder"]
            """ + "\n";

        var exception = Assert.Throws<FormatException>(() =>
            FileMapLoader.Parse(Encoding.UTF8.GetBytes(source), "fixture.toml"));

        Assert.Contains(expectedMessage, exception.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("D5/**/../Ring.lean")]
    [InlineData("/D5/**/*.lean")]
    [InlineData("D5\\**\\*.lean")]
    public void UnsafePatternIsRejectedByTheRedFixture(string pattern)
    {
        var source = $$"""
            schema_version = 1

            [residence_policy]
            case_id = "RESIDENCE-EPOCH"
            desired = "data-must-live-outside-Meta/StrataLint"
            known_violation_count = 0
            status = "known-violations-frozen-under-monitoring"

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

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, FileMapLoader.RelativePath)))
            {
                return current.FullName;
            }
        }

        throw new DirectoryNotFoundException("Could not locate repository FILEMAP.");
    }
}
