using System.Text;

namespace StrataLint.Scribe.Tests;

public sealed class FileMapManifestTests
{
    [Fact]
    public void DataKeyedGeneratedRunLocalSetUsesTheNineKeyShape()
    {
        var manifest = FileMapLoader.Parse(Encoding.UTF8.GetBytes(DataKeyedRunLocalEntry()), "fixture.toml");

        Assert.Equal("run-local", Assert.Single(manifest.Entries).RuntimeDisposition);
    }

    [Fact]
    public void DataKeyedGeneratedRunLocalSetRejectsProjectionFields()
    {
        var source = DataKeyedRunLocalEntry().Replace(
            "runtime_disposition = \"run-local\"\n",
            "runtime_disposition = \"run-local\"\nmode = \"100644\"\n",
            StringComparison.Ordinal);

        var exception = Assert.Throws<FormatException>(() =>
            FileMapLoader.Parse(Encoding.UTF8.GetBytes(source), "fixture.toml"));

        Assert.Contains("unknown keys", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void LiteralGeneratedRunLocalEntryWithoutArtifactIdRemainsRejected()
    {
        var source = DataKeyedRunLocalEntry().Replace(
            "Generated/partitions/*.md",
            "Generated/partitions/source-a.md",
            StringComparison.Ordinal);

        var exception = Assert.Throws<FormatException>(() =>
            FileMapLoader.Parse(Encoding.UTF8.GetBytes(source), "fixture.toml"));

        Assert.Contains("mode", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void InventoryBackedRunLocalEntryRetainsTheElevenKeyShape()
    {
        var source = DataKeyedRunLocalEntry()
            .Replace("Generated/partitions/*.md", "Generated/output.md", StringComparison.Ordinal)
            .Replace("artifact_id = \"none\"", "artifact_id = \"A-OUTPUT\"", StringComparison.Ordinal)
            .Replace(
                "runtime_disposition = \"run-local\"\n",
                "runtime_disposition = \"run-local\"\nmode = \"100644\"\nhistory_requirement = \"not-required\"\n",
                StringComparison.Ordinal);

        var manifest = FileMapLoader.Parse(Encoding.UTF8.GetBytes(source), "fixture.toml");

        Assert.Equal("run-local", Assert.Single(manifest.Entries).RuntimeDisposition);
    }

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
            desired = "data-must-live-outside-tools"
            known_violation_count = 0
            status = "closed"

            [[files]]
            pattern = "Generated/output.md"
            kind = "generated"
            admission_plane = "content"
            produced_by = "OutputEmitter"
            consumed_by = ["reader"]
            verified_by = ["OutputEmitter"]
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
            desired = "data-must-live-outside-tools"
            known_violation_count = 0
            status = "closed"

            [[files]]
            pattern = "Generated/a.md"
            kind = "generated"
            admission_plane = "content"
            produced_by = "OutputEmitter"
            consumed_by = ["reader"]
            verified_by = ["OutputEmitter"]
            runtime_disposition = "run-local"
            artifact_id = "A-OUTPUT"
            mode = "100644"
            history_requirement = "not-required"

            [[files]]
            pattern = "Generated/b.md"
            kind = "generated"
            admission_plane = "content"
            produced_by = "OutputEmitter"
            consumed_by = ["reader"]
            verified_by = ["OutputEmitter"]
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
        var manifest = FileMapLoader.LoadRepository(RepositoryAccessor.Discover(RepositoryRootCriterion.FileMapDirectoryNotFound).Root.FullPath);
        var entry = Assert.Single(manifest.Match(
            "Meta/Digestion/atoms/sha256/" + new string('a', 64)));

        Assert.Equal(FileMapKind.Ledger, entry.Kind);
        Assert.Equal("IngestCommand", entry.ProducedBy);
        Assert.Equal(["DigestionCasStore"], entry.ConsumedBy.ToArray());
        Assert.Equal(["DigestionCasStore"], entry.VerifiedBy.ToArray());
        Assert.False(entry.ResidenceViolation);
    }

    private const string GeneratedPath = "Artifacts/Ring.md";
    private const string FormalPath = "D5/S0/Carrier/Ring.lean";
    private const string FrozenLedgerPath =
        "Golden/Frozen/accepted/aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.json";
    private const string RuleCatalogPath =
        "tools/StrataLint.Engine/Rules/RuleCatalog.cs";

    [Fact]
    public void CanonicalManifestLoadsAllFiveKindsAndMatchesRepositoryGlobs()
    {
        var manifest = FileMapLoader.Parse(Encoding.UTF8.GetBytes("""
            schema_version = 2

            [residence_policy]
            case_id = "RESIDENCE-EPOCH"
            desired = "data-must-live-outside-tools"
            known_violation_count = 1
            status = "known-violations-frozen-under-monitoring"

            [[files]]
            pattern = "Artifacts/**/*.md"
            kind = "generated"
            admission_plane = "content"
            produced_by = "ScribeEmitter"
            consumed_by = ["reader"]
            verified_by = ["ScribeEmitter"]
            runtime_disposition = "committed-source"
            artifact_id = "none"

            [[files]]
            pattern = "D5/**/*.lean"
            kind = "truth"
            admission_plane = "content"
            produced_by = "none"
            consumed_by = ["lake"]
            verified_by = ["lean-build"]
            runtime_disposition = "committed-source"
            artifact_id = "none"

            [[files]]
            pattern = "Golden/Frozen/accepted/*.json"
            kind = "ledger"
            admission_plane = "content"
            produced_by = "FrozenLedgerCanonicalWriter"
            consumed_by = ["FrozenLedger"]
            verified_by = ["SL-008"]
            runtime_disposition = "committed-ledger"
            artifact_id = "none"

            [[files]]
            pattern = "tools/FixtureData/*.toml"
            kind = "data"
            admission_plane = "judge"
            produced_by = "none"
            consumed_by = ["TomlGoldenLoader"]
            verified_by = ["TomlGoldenLoader"]
            residence_violation = true
            runtime_disposition = "committed-source"
            artifact_id = "none"

            [[files]]
            pattern = "tools/StrataLint.*/**"
            kind = "program"
            admission_plane = "judge"
            produced_by = "none"
            consumed_by = ["dotnet"]
            verified_by = ["dotnet-test"]
            runtime_disposition = "committed-source"
            artifact_id = "none"
            """ + "\n"), "fixture.toml");

        Assert.Equal(5, manifest.Entries.Length);
        Assert.Equal("RESIDENCE-EPOCH", manifest.ResidencePolicy.CaseId);
        Assert.Equal("data-must-live-outside-tools", manifest.ResidencePolicy.Desired);
        Assert.Equal(1, manifest.ResidencePolicy.KnownViolationCount);
        Assert.Equal(
            "known-violations-frozen-under-monitoring",
            manifest.ResidencePolicy.Status);
        Assert.Equal(FileMapKind.Generated, Assert.Single(
            manifest.Match(GeneratedPath)).Kind);
        Assert.Equal(FileMapKind.Truth, Assert.Single(
            manifest.Match(FormalPath)).Kind);
        Assert.Equal(FileMapKind.Ledger, Assert.Single(
            manifest.Match(FrozenLedgerPath)).Kind);
        Assert.Equal(FileMapKind.Data, Assert.Single(
            manifest.Match("tools/FixtureData/fixture.toml")).Kind);
        Assert.True(Assert.Single(
            manifest.Match("tools/FixtureData/fixture.toml")).ResidenceViolation);
        Assert.Equal(FileMapKind.Program, Assert.Single(
            manifest.Match(RuleCatalogPath)).Kind);
        Assert.Empty(manifest.Match("unclassified.bin"));
    }

    private static string DataKeyedRunLocalEntry() => """
        schema_version = 2

        [residence_policy]
        case_id = "RESIDENCE-EPOCH"
        desired = "data-must-live-outside-tools"
        known_violation_count = 0
        status = "closed"

        [[files]]
        pattern = "Generated/partitions/*.md"
        kind = "generated"
        admission_plane = "content"
        produced_by = "PartitionEmitter"
        consumed_by = ["reader"]
        verified_by = ["PartitionEmitter"]
        artifact_id = "none"
        runtime_disposition = "run-local"
        """ + "\n";

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
            desired = "data-must-live-outside-tools"
            known_violation_count = 0
            status = "known-violations-frozen-under-monitoring"

            [[files]]
            pattern = "Generated/**/*.md"
            kind = "generated"
            admission_plane = "content"
            produced_by = "{{producedBy}}"
            consumed_by = ["reader"]
            verified_by = ["ScribeEmitter"]
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
            desired = "data-must-live-outside-tools"
            known_violation_count = 0
            status = "known-violations-frozen-under-monitoring"

            [[files]]
            pattern = "Generated/**/*.md"
            kind = "generated"
            admission_plane = "content"
            produced_by = "FileMapEmitter"
            consumed_by = ["reader"]
            verified_by = ["dotnet-test"]
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
            desired = "data-must-live-outside-tools"
            known_violation_count = 0
            status = "known-violations-frozen-under-monitoring"

            [[files]]
            pattern = "tools/fixture.toml"
            kind = "{{kind}}"
            admission_plane = "judge"
            residence_violation = {{marker}}
            produced_by = "none"
            consumed_by = ["reader"]
            verified_by = ["SnapshotDecoder"]
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
        AssertUnsafePatternRejected(pattern);
    }

    [Fact]
    public void QuestionMarkPatternIsRejectedByTheStrictLoader()
    {
        AssertUnsafePatternRejected("x/?.txt");
        AssertUnsafePatternRejected("x/??.txt");
    }

    private static void AssertUnsafePatternRejected(string pattern)
    {
        var source = $$"""
            schema_version = 2

            [residence_policy]
            case_id = "RESIDENCE-EPOCH"
            desired = "data-must-live-outside-tools"
            known_violation_count = 0
            status = "known-violations-frozen-under-monitoring"

            [[files]]
            pattern = "{{pattern.Replace("\\", "\\\\", StringComparison.Ordinal)}}"
            kind = "truth"
            admission_plane = "content"
            produced_by = "none"
            consumed_by = ["lake"]
            verified_by = ["lean-build"]
            runtime_disposition = "committed-source"
            artifact_id = "none"
            """ + "\n";

        var exception = Assert.ThrowsAny<FormatException>(() =>
            FileMapLoader.Parse(Encoding.UTF8.GetBytes(source), "fixture.toml"));
        Assert.Contains("unsafe FILEMAP pattern", exception.Message, StringComparison.Ordinal);
    }
}
