using System.Text;

namespace StrataLint.Scribe.Tests;

public sealed class FileMapManifestTests
{
    [Theory]
    [InlineData("extra = true\n", "unknown keys")]
    [InlineData("", "runtime_disposition")]
    [InlineData("runtime_disposition = \"temporary\"\n", "runtime_disposition")]
    public void SchemaTwoDispositionFieldsFailClosed(string dispositionLine, string expectedMessage)
    {
        var source = $$"""
            schema_version = 2

            [residence_policy]
            case_id = "RESIDENCE-EPOCH"
            desired = "data-must-live-outside-Meta/StrataLint"
            known_violation_count = 0
            status = "closed"

            [[files]]
            pattern = "Generated/output.md"
            kind = "generated"
            produced_by = "OutputEmitter"
            consumed_by = ["reader"]
            verified_by = ["OutputEmitter"]
            authority = "self"
            artifact_id = "A-OUTPUT"
            {{dispositionLine}}
            """ + "\n";

        var exception = Assert.Throws<FormatException>(() =>
            FileMapLoader.Parse(Encoding.UTF8.GetBytes(source), "fixture.toml"));

        Assert.Contains(expectedMessage, exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void DuplicateArtifactIdIsRejected()
    {
        var source = """
            schema_version = 2

            [residence_policy]
            case_id = "RESIDENCE-EPOCH"
            desired = "data-must-live-outside-Meta/StrataLint"
            known_violation_count = 0
            status = "closed"

            [[files]]
            pattern = "Generated/a.md"
            kind = "generated"
            produced_by = "OutputEmitter"
            consumed_by = ["reader"]
            verified_by = ["OutputEmitter"]
            authority = "self"
            runtime_disposition = "run-local"
            artifact_id = "A-OUTPUT"
            mode = "100644"
            history_requirement = "not-required"

            [[files]]
            pattern = "Generated/b.md"
            kind = "generated"
            produced_by = "OutputEmitter"
            consumed_by = ["reader"]
            verified_by = ["OutputEmitter"]
            authority = "self"
            runtime_disposition = "run-local"
            artifact_id = "A-OUTPUT"
            mode = "100644"
            history_requirement = "not-required"
            """ + "\n";

        var exception = Assert.Throws<FormatException>(() =>
            FileMapLoader.Parse(Encoding.UTF8.GetBytes(source), "fixture.toml"));

        Assert.Contains("artifact_id", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void RepositoryManifestClassifiesDigestionCasAsAnAppendOnlyLedger()
    {
        var manifest = FileMapLoader.LoadRepository(RepositoryAccessor.Discover().Root.FullPath);
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
            schema_version = 2

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
            verified_by = ["ScribeEmitter"]
            authority = "self"
            runtime_disposition = "committed-source"
            artifact_id = "none"

            [[files]]
            pattern = "D5/**/*.lean"
            kind = "truth"
            produced_by = "none"
            consumed_by = ["lake"]
            verified_by = ["lean-build"]
            authority = "self"
            runtime_disposition = "committed-source"
            artifact_id = "none"

            [[files]]
            pattern = "Meta/StrataLint/Golden/Frozen/**/*.jsonl"
            kind = "ledger"
            produced_by = "FrozenLedgerCanonicalWriter"
            consumed_by = ["FrozenLedger"]
            verified_by = ["SL-008"]
            authority = "self"
            runtime_disposition = "committed-ledger"
            artifact_id = "none"

            [[files]]
            pattern = "Meta/StrataLint/Golden/cases/**/*.toml"
            kind = "data"
            produced_by = "none"
            consumed_by = ["TomlGoldenLoader"]
            verified_by = ["TomlGoldenLoader"]
            residence_violation = true
            authority = "self"
            runtime_disposition = "committed-source"
            artifact_id = "none"

            [[files]]
            pattern = "Meta/StrataLint/StrataLint.*/**"
            kind = "program"
            produced_by = "none"
            consumed_by = ["dotnet"]
            verified_by = ["dotnet-test"]
            authority = "self"
            runtime_disposition = "committed-source"
            artifact_id = "none"
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
            schema_version = 2
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
            verified_by = ["ScribeEmitter"]
            authority = "self"
            runtime_disposition = "committed-source"
            artifact_id = "none"
            """ + "\n";

        var exception = Assert.Throws<FormatException>(() =>
            FileMapLoader.Parse(Encoding.UTF8.GetBytes(source), "fixture.toml"));

        Assert.Contains(expectedMessage, exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void GeneratedDeclarationMustNameItsProducer()
    {
        var source = """
            schema_version = 2

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
            authority = "self"
            runtime_disposition = "committed-source"
            artifact_id = "none"
            """ + "\n";

        var exception = Assert.Throws<FormatException>(() =>
            FileMapLoader.Parse(Encoding.UTF8.GetBytes(source), "fixture.toml"));

        Assert.Contains("its producer", exception.Message, StringComparison.Ordinal);
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
            schema_version = 2

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
            authority = "self"
            runtime_disposition = "committed-source"
            artifact_id = "none"
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
            schema_version = 2

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
            authority = "self"
            runtime_disposition = "committed-source"
            artifact_id = "none"
            """ + "\n";

        var exception = Assert.Throws<FormatException>(() =>
            FileMapLoader.Parse(Encoding.UTF8.GetBytes(source), "fixture.toml"));
        Assert.Contains("unsafe FILEMAP pattern", exception.Message, StringComparison.Ordinal);
    }
}
