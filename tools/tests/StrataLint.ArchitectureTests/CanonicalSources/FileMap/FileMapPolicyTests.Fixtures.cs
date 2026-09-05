using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.ArchitectureTests;

// FileMapPolicyTests 的后半:红绿夹具一族。
// 余量:宿主原 777 行,离 SL-003 的 800 行硬线 23 行(由 headroom.sh 列出)。
// 该类本就是 partial;切点 = 缩进 4 的真方法收尾 ∧ 后空行 ∧ 再后是缩进 4 的特性行
//(36 处候选取中点)。

public sealed partial class FileMapPolicyTests
{
    [Fact]
    public void MissingReviewScaffoldIgnoreIsRejectedByTheRedFixture()
    {
        var finding = Assert.Single(FileMapPolicy.InspectGitIgnore(
            ["/Generated/echo-residuals/", ".caller-review-prompt.md", ".echo-review.md"]));

        Assert.Equal("FILEMAP-GITIGNORE", finding.Code);
        Assert.Equal(".gitignore", finding.Path);
        Assert.Contains(".sshx-*", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CompleteReviewScaffoldIgnoresAreAcceptedByTheGreenFixture()
    {
        Assert.Empty(FileMapPolicy.InspectGitIgnore(
            ["/Generated/echo-residuals/", ".sshx-*", ".echo-review.md", ".caller-review-prompt.md"]));
    }

    [Fact]
    public void EchoResidualRegistryAndBroadFileMapPatternAreRejectedByTheRedFixture()
    {
        var manifest = Parse(Entry(
            "Generated/**/*.md",
            "generated",
            "EchoVerifyCommand",
            "reader",
            "EchoVerifyCommand"));

        var findings = FileMapPolicy.InspectProjectionRegistrations(
            manifest,
            ["Generated/echo-residuals/source.md"]);

        Assert.Contains(findings, static finding => finding.Code == "FILEMAP-PROJECTION-SHARD");
        Assert.Contains(findings, static finding => finding.Code == "FILEMAP-PROJECTION-REGISTRY");
    }

    [Fact]
    public void EchoResidualLiteralFileMapPatternAndAbsentRegistryEntryAreAcceptedByTheGreenFixture()
    {
        var manifest = Parse(Entry(
            "Generated/echo-residuals/*.md",
            "generated",
            "EchoVerifyCommand",
            "reader",
            "EchoVerifyCommand").Replace(
                "runtime_disposition = \"committed-source\"",
                "runtime_disposition = \"run-local\"",
                StringComparison.Ordinal));

        Assert.Empty(FileMapPolicy.InspectProjectionRegistrations(manifest, []));
    }

    [Fact]
    public void DataWithoutAnExistingLoaderIsRejectedByTheRedFixture()
    {
        var manifest = Parse(Entry(
            "Data/**/*.toml",
            "data",
            "none",
            "MissingLoader",
            "MissingLoader"));

        var finding = Assert.Single(FileMapPolicy.InspectDataVerifiers(
            manifest,
            new HashSet<string>(StringComparer.Ordinal)));

        Assert.Equal("FILEMAP-DATA-VERIFIER", finding.Code);
    }

    // 存量证据:#1116 删掉 emit-check 之后,`Library/*/*.md` 仍写着它,而
    // InspectDataVerifiers 的 `.Any(...)` 因同条目还留着 LibraryNoteCatalog 而放行。
    [Fact]
    public void DataVerifierNameThatIsNeitherALoaderNorARuleIdIsRejectedByTheRedFixture()
    {
        var manifest = Parse(DataEntryVerifiedBy(
            "Library/*/*.md",
            "LibraryNoteCatalog",
            "emit-check"));

        var finding = Assert.Single(FileMapPolicy.InspectDataVerifierNames(
            manifest,
            new HashSet<string>(StringComparer.Ordinal) { "LibraryNoteCatalog" }));

        Assert.Equal("FILEMAP-DATA-VERIFIER-DANGLING", finding.Code);
        Assert.Contains("emit-check", finding.Message, StringComparison.Ordinal);
    }

    // 反证:规则号是刻意的非类型名,不得被这条新检查误伤。
    [Fact]
    public void DataVerifierNamedByARuleIdIsAccepted()
    {
        var manifest = Parse(DataEntryVerifiedBy(
            "Library/**/*.yaml",
            "SL-017",
            "YamlSubsetParser"));

        Assert.Empty(FileMapPolicy.InspectDataVerifierNames(
            manifest,
            new HashSet<string>(StringComparer.Ordinal) { "YamlSubsetParser" }));
    }

    [Fact]
    public void GeneratedFileWithoutProducerInventoryIsRejectedByTheRedFixture()
    {
        var manifest = Parse(DispositionEntry(
            "Generated/output.json",
            "generated",
            "JsonEmitter",
            "reader",
            "JsonEmitter",
            "committed-source",
            "A-OUTPUT"));

        var finding = Assert.Single(FileMapPolicy.InspectGeneratedInventory(
            manifest,
            ["Generated/output.json"],
            []));

        Assert.Equal("FILEMAP-GENERATED-INVENTORY", finding.Code);
    }

    [Fact]
    public void DataKeyedGeneratedGlobWithoutProducerInventoryIsAccepted()
    {
        var manifest = Parse(Entry(
            "Generated/partitions/*.json",
            "generated",
            "PartitionEmitter",
            "reader",
            "PartitionEmitter"));

        var findings = FileMapPolicy.InspectGeneratedInventory(
            manifest,
            ["Generated/partitions/source-a.json"],
            []);

        Assert.Empty(findings);
    }

    [Fact]
    public void GeneratedGlobWithArtifactIdStillRequiresProducerInventory()
    {
        var manifest = Parse(DispositionEntry(
            "Generated/partitions/*.json",
            "generated",
            "PartitionEmitter",
            "reader",
            "PartitionEmitter",
            "committed-source",
            "A-PARTITION"));

        var finding = Assert.Single(FileMapPolicy.InspectGeneratedInventory(
            manifest,
            ["Generated/partitions/source-a.json"],
            []));

        Assert.Equal("FILEMAP-GENERATED-INVENTORY", finding.Code);
    }

    [Fact]
    public void GeneratedLiteralWithoutArtifactIdStillRequiresProducerInventory()
    {
        var manifest = Parse(Entry(
            "Generated/output.json",
            "generated",
            "JsonEmitter",
            "reader",
            "JsonEmitter"));

        var finding = Assert.Single(FileMapPolicy.InspectGeneratedInventory(
            manifest,
            ["Generated/output.json"],
            []));

        Assert.Equal("FILEMAP-GENERATED-INVENTORY", finding.Code);
    }

    [Fact]
    public void InventoryBackedAggregateRemainsAccepted()
    {
        var aggregateManifest = Parse(DispositionEntry(
            "Generated/summary.json",
            "generated",
            "SummaryEmitter",
            "reader",
            "SummaryEmitter",
            "committed-source",
            "A-SUMMARY"));
        var aggregate = new GeneratedArtifactIdentity(
            "Generated/summary.json",
            "SummaryEmitter",
            "A-SUMMARY");

        Assert.Empty(FileMapPolicy.InspectGeneratedInventory(
            aggregateManifest,
            [aggregate.Path],
            [aggregate]));
    }

    [Fact]
    public void GeneratedDeclarationWithoutProducerIsRejectedByTheRedFixture()
    {
        var source = Entry(
            "Generated/output.json",
            "generated",
            "none",
            "reader",
            "MissingProducer");

        var exception = Assert.Throws<FormatException>(() => Parse(source));

        Assert.Contains("produced_by must name a producer", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void GeneratedProducerMismatchIsRejectedByTheRedFixture()
    {
        var manifest = Parse(Entry(
            "Generated/output.json",
            "generated",
            "JsonEmitter",
            "reader",
            "JsonEmitter"));
        var inventory = new GeneratedArtifactIdentity(
            "Generated/output.json",
            "OtherEmitter");

        var finding = Assert.Single(FileMapPolicy.InspectGeneratedInventory(
            manifest,
            ["Generated/output.json"],
            [inventory]));

        Assert.Equal("FILEMAP-GENERATED-PRODUCER", finding.Code);
    }

    [Theory]
    [InlineData("Generated/manual.md", "data", "FILEMAP-DIRECTORY-KIND")]
    [InlineData("tools/cases.toml", "data", "FILEMAP-DATA-RESIDENCE")]
    public void ClassDirectoryMixingIsRejectedByTheRedFixture(
        string path,
        string kind,
        string expectedCode)
    {
        var manifest = Parse(Entry(path, kind, "none", "reader", "SnapshotDecoder"));

        var finding = Assert.Single(FileMapPolicy.InspectDirectoryKinds(manifest, [path]));

        Assert.Equal(expectedCode, finding.Code);
    }

    [Fact]
    public void DataAndLeanGeneratedDependenciesAreRejectedByTheRedFixture()
    {
        var manifest = Parse(
            Entry("Data/**/*.toml", "data", "none", "loader", "SnapshotDecoder"),
            Entry("Generated/**/*.json", "generated", "JsonEmitter", "program", "JsonEmitter"),
            Entry("Generated/**/*.lean", "generated", "LeanEmitter", "lake", "LeanEmitter"),
            Entry("Main.lean", "truth", "none", "lake", "lean-build"));
        var files = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["Data/input.toml"] = "projection = \"Generated/output.json\"\n",
            ["Generated/output.json"] = "{}\n",
            ["Generated/Proof.lean"] = "def generated : Nat := 0\n",
            ["Main.lean"] = "import Generated.Proof\n",
        };

        var findings = FileMapPolicy.InspectDependencies(manifest, files);

        Assert.Contains(findings, static finding => finding.Code == "FILEMAP-DATA-GENERATED-DEPENDENCY");
        Assert.Contains(findings, static finding => finding.Code == "FILEMAP-LEAN-GENERATED-IMPORT");
    }

    private static FileMapManifest Parse(params string[] entries) => Parse(0, entries);

    private static RegistryLoadOutcome.Accepted SyntheticRegistry(string? governanceDocument = null)
    {
        var governanceDocuments = new[]
        {
            "Generated/FILEMAP.md",
            "Generated/truth-graph.v1.json",
            "Meta/Digestion/atomizers.toml",
            "Meta/FILEMAP.toml",
            "docs/CONTRIBUTING.md",
            "docs/GOVERNANCE.md",
            "docs/develop/spec/golden-ledger-repo-spec.md",
            "tools/Generated/scribe-emissions.v1.json",
        }.Append(governanceDocument)
            .Where(static path => path is not null)
            .Order(StringComparer.Ordinal)
            .Select(static path => $"  - \"{path}\"");
        var registry = """
            schema_version: 1
            root_files:
              - "README.md"
            governance_documents:
            """ + "\n" + string.Join('\n', governanceDocuments) + """

            agent_files:
              - "CONTEXT.md"
            artifact_kinds:
              json:
                profile: structured-json
                selectors:
                  - "result"
                path_selectors:
                  - "formal"
            """ + "\n";
        const string domains = """
            domains:
              Carrier:
                stratum: S0
                definition: Synthetic carrier domain.
            """ + "\n";
        return RegistryLoadAssert.Accepted(RegistryLoader.Load(
            Encoding.UTF8.GetBytes(registry),
            Encoding.UTF8.GetBytes(domains)));
    }

    private static FileMapManifest Parse(int knownViolationCount, params string[] entries) =>
        FileMapLoader.Parse(
            Encoding.UTF8.GetBytes(
                $$"""
                schema_version = 2

                [residence_policy]
                case_id = "RESIDENCE-EPOCH"
                desired = "data-must-live-outside-tools"
                known_violation_count = {{knownViolationCount}}
                status = "known-violations-frozen-under-monitoring"

                """ + string.Join("\n", entries)),
            "fixture.toml");

    private static string ResidenceEntry(string pattern) =>
        Entry(pattern, "data", "none", "reader", "SnapshotDecoder")
        + "residence_violation = true\n";

    private static string DataEntryVerifiedBy(string pattern, params string[] verifiedBy) => $$"""
        [[files]]
        pattern = "{{pattern}}"
        kind = "data"
        admission_plane = "content"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = [{{string.Join(", ", verifiedBy.Select(static name => $"\"{name}\""))}}]
        runtime_disposition = "committed-source"
        artifact_id = "none"
        """ + "\n";

    private static string Entry(
        string pattern,
        string kind,
        string producedBy,
        string consumedBy,
        string verifiedBy) => $$"""
        [[files]]
        pattern = "{{pattern}}"
        kind = "{{kind}}"
        admission_plane = "judge"
        produced_by = "{{producedBy}}"
        consumed_by = ["{{consumedBy}}"]
        verified_by = ["{{verifiedBy}}"]
        runtime_disposition = "{{(kind == "ledger" ? "committed-ledger" : "committed-source")}}"
        artifact_id = "none"
        """ + "\n";

    private static string DispositionEntry(
        string pattern,
        string kind,
        string producedBy,
        string consumedBy,
        string verifiedBy,
        string runtimeDisposition,
        string artifactId) => $$"""
        [[files]]
        pattern = "{{pattern}}"
        kind = "{{kind}}"
        admission_plane = "judge"
        produced_by = "{{producedBy}}"
        consumed_by = ["{{consumedBy}}"]
        verified_by = ["{{verifiedBy}}"]
        runtime_disposition = "{{runtimeDisposition}}"
        artifact_id = "{{artifactId}}"
        mode = "100644"
        history_requirement = "not-required"
        """ + "\n";
}
