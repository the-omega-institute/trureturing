using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.Scribe;
using StrataLint.Tests;

namespace StrataLint.ArchitectureTests;

public sealed class FileMapPolicyTests
{
    [Fact]
    public void RepositoryFilesConformToTheCanonicalFileMap()
    {
        var findings = FileMapPolicy.InspectRepository(RepositoryLayout.FindRoot());

        Assert.True(
            findings.Count == 0,
            string.Join(
                Environment.NewLine,
                findings.Select(static finding =>
                    $"{finding.Code} {finding.Path}: {finding.Message}")));
    }

    [Fact]
    public void ReviewScaffoldPatternsRemainInTheRepositoryGitignore()
    {
        var root = RepositoryLayout.FindRoot();
        var lines = File.ReadAllLines(Path.Combine(root, ".gitignore"));

        Assert.Contains(".caller-review-prompt.md", lines, StringComparer.Ordinal);
        Assert.Contains(".echo-review.md", lines, StringComparer.Ordinal);
        Assert.Contains(".sshx-*", lines, StringComparer.Ordinal);
    }

    [Fact]
    public void ResidenceEpochIsClosedWithNoProtectedSurfaceData()
    {
        var root = RepositoryLayout.FindRoot();
        var manifest = FileMapLoader.LoadRepository(root);

        var actual = FileMapPolicy.ResidenceViolations(root);

        Assert.Empty(actual);
        Assert.Equal("RESIDENCE-EPOCH", manifest.ResidencePolicy.CaseId);
        Assert.Equal("data-must-live-outside-Meta/StrataLint", manifest.ResidencePolicy.Desired);
        Assert.Equal(0, manifest.ResidencePolicy.KnownViolationCount);
        Assert.Equal("closed", manifest.ResidencePolicy.Status);
        Assert.Equal(FileMapKind.Data, Assert.Single(manifest.Match("Golden/fixture-registry.yaml")).Kind);
    }

    [Fact]
    public void ComputationalProjectionRegistrationsAgreeAcrossCanonicalSources()
    {
        var expectedPaths = new HashSet<string>(
            [
                ScribeEmitter.AttestationRelativePath,
                "Generated/truth-graph.v1.json",
            ],
            StringComparer.Ordinal);
        var root = RepositoryLayout.FindRoot();
        var manifest = FileMapLoader.LoadRepository(root);
        var registry = RegistryLoadAssert.Accepted(
            RegistryLoader.Load(
                File.ReadAllBytes(Path.Combine(root, "Meta", "registry.yaml")),
                File.ReadAllBytes(Path.Combine(root, "Meta", "domains.yaml"))));
        var artifacts = GeneratedArtifactInventory.All
            .Where(artifact => expectedPaths.Contains(artifact.Path))
            .ToArray();

        Assert.Equal(expectedPaths.Count, artifacts.Length);
        Assert.All(artifacts, artifact =>
        {
            var entry = Assert.Single(manifest.Match(artifact.Path));
            Assert.Equal(FileMapKind.Generated, entry.Kind);
            Assert.Equal(artifact.Producer, entry.ProducedBy);
            Assert.Contains(artifact.Producer, entry.VerifiedBy, StringComparer.Ordinal);
        });

        var topLevelProjectionPaths = expectedPaths
            .Where(static path => path.StartsWith("Generated/", StringComparison.Ordinal))
            .Select(RepoPath.CreateKnown)
            .ToArray();
        Assert.All(topLevelProjectionPaths, path =>
            Assert.Contains(path, registry.Policy.GovernanceDocuments));

    }

    [Fact]
    public void PerformanceBudgetsHaveARegisteredGoldenDataResidence()
    {
        const string value = "Golden/perf-budgets.toml";
        var root = RepositoryLayout.FindRoot();
        var manifest = FileMapLoader.LoadRepository(root);
        var registry = RegistryLoadAssert.Accepted(
            RegistryLoader.Load(
                File.ReadAllBytes(Path.Combine(root, "Meta", "registry.yaml")),
                File.ReadAllBytes(Path.Combine(root, "Meta", "domains.yaml"))));
        var path = RepoPath.CreateKnown(value);

        var entry = Assert.Single(manifest.Match(value));
        Assert.Equal(FileMapKind.Data, entry.Kind);
        Assert.Equal("PerfBudgetLoader", Assert.Single(entry.ConsumedBy));
        Assert.Equal("PerfBudgetLoader", Assert.Single(entry.VerifiedBy));
        Assert.Contains(path, registry.Policy.GovernanceDocuments);
        Assert.Null(RepositoryPathPolicy.Validate(path, registry.Policy));
        Assert.IsType<BootstrapOutcome.Clear>(
            BootstrapGate.Evaluate(RawChangeSet.Create([value])));
    }

    [Fact]
    public void DevloopPlanDocumentsAreAdmittedByRepositoryPathPolicy()
    {
        // Self-driving devloop plan documents are emitted under docs/devloop/plans/
        // with dynamically generated names (one per prove-task), so they cannot be
        // enumerated individually in registry.yaml governance_documents. The
        // RepositoryPathPolicy admits the whole docs/devloop/ prefix; SL-000 must
        // not reject dynamically generated plans as unknown top-level artifacts.
        const string value = "docs/devloop/plans/synthetic-prove-task-plan.md";
        var root = RepositoryLayout.FindRoot();
        var registry = RegistryLoadAssert.Accepted(
            RegistryLoader.Load(
                File.ReadAllBytes(Path.Combine(root, "Meta", "registry.yaml")),
                File.ReadAllBytes(Path.Combine(root, "Meta", "domains.yaml"))));
        var path = RepoPath.CreateKnown(value);

        Assert.Null(RepositoryPathPolicy.Validate(path, registry.Policy));
    }

    [Fact]
    public void CodexSkillPackagesAreAdmittedByRepositoryPathPolicy()
    {
        // A Codex skill package is a directory containing SKILL.md, whose file
        // names cannot be enumerated individually in registry.yaml.
        const string value = ".codex/skills/synthetic-skill/SKILL.md";
        var root = RepositoryLayout.FindRoot();
        var registry = RegistryLoadAssert.Accepted(
            RegistryLoader.Load(
                File.ReadAllBytes(Path.Combine(root, "Meta", "registry.yaml")),
                File.ReadAllBytes(Path.Combine(root, "Meta", "domains.yaml"))));
        var path = RepoPath.CreateKnown(value);

        Assert.Null(RepositoryPathPolicy.Validate(path, registry.Policy));
    }

    [Fact]
    public void CodexArtifactsOutsideSkillsAreRefusedByRepositoryPathPolicy()
    {
        const string value = ".codex/settings.toml";
        var root = RepositoryLayout.FindRoot();
        var registry = RegistryLoadAssert.Accepted(
            RegistryLoader.Load(
                File.ReadAllBytes(Path.Combine(root, "Meta", "registry.yaml")),
                File.ReadAllBytes(Path.Combine(root, "Meta", "domains.yaml"))));
        var path = RepoPath.CreateKnown(value);

        var issue = Assert.IsType<RepositoryPathIssue>(
            RepositoryPathPolicy.Validate(path, registry.Policy));
        Assert.Equal("SL-000", issue.RuleId.Value);
        Assert.Equal("unknown top-level artifact", issue.Message);
    }

    [Fact]
    public void SkillPackagesAreAdmittedByRepositoryPathPolicy()
    {
        // A skill package is a directory holding SKILL.md, whose file names cannot be enumerated in registry.yaml.
        const string value = "skills/synthetic-skill/SKILL.md";
        var root = RepositoryLayout.FindRoot();
        var registry = RegistryLoadAssert.Accepted(
            RegistryLoader.Load(
                File.ReadAllBytes(Path.Combine(root, "Meta", "registry.yaml")),
                File.ReadAllBytes(Path.Combine(root, "Meta", "domains.yaml"))));
        var path = RepoPath.CreateKnown(value);

        Assert.Null(RepositoryPathPolicy.Validate(path, registry.Policy));
    }

    [Fact]
    public void SkillsPrefixWithoutSeparatorIsRefusedByRepositoryPathPolicy()
    {
        const string value = "skills.md";
        var root = RepositoryLayout.FindRoot();
        var registry = RegistryLoadAssert.Accepted(
            RegistryLoader.Load(
                File.ReadAllBytes(Path.Combine(root, "Meta", "registry.yaml")),
                File.ReadAllBytes(Path.Combine(root, "Meta", "domains.yaml"))));
        var path = RepoPath.CreateKnown(value);

        var issue = Assert.IsType<RepositoryPathIssue>(
            RepositoryPathPolicy.Validate(path, registry.Policy));
        Assert.Equal("SL-000", issue.RuleId.Value);
        Assert.Equal("unknown top-level artifact", issue.Message);
    }

    [Fact]
    public void LibrarySplitBucketsAreClassifiedAsData()
    {
        var manifest = FileMapLoader.LoadRepository(RepositoryLayout.FindRoot());

        Assert.Equal(
            FileMapKind.Data,
            Assert.Single(manifest.Match("Library/Weil/sample2026paper.md")).Kind);
    }

    [Fact]
    public void LibrarySplitLedgerIsClassifiedAsLedger()
    {
        var manifest = FileMapLoader.LoadRepository(RepositoryLayout.FindRoot());

        Assert.Equal(
            FileMapKind.Ledger,
            Assert.Single(manifest.Match("Library/MAP.md")).Kind);
    }

    [Fact]
    public void ResidenceMarkerOutsideTheProtectedSurfaceIsRejected()
    {
        const string path = "Data/known.toml";
        var manifest = Parse(ResidenceEntry(path));

        var finding = Assert.Single(FileMapPolicy.InspectDirectoryKinds(manifest, [path]));

        Assert.Equal("FILEMAP-RESIDENCE-MARKER", finding.Code);
    }

    [Fact]
    public void ProjectionFixtureDirectoryRejectsNonDataEntries()
    {
        const string path = "Golden/Projection/x.json";
        var manifest = Parse(Entry(path, "program", "none", "reader", "SnapshotDecoder"));

        var finding = Assert.Single(FileMapPolicy.InspectDirectoryKinds(manifest, [path]));

        Assert.Equal("FILEMAP-DIRECTORY-KIND", finding.Code);
    }

    [Fact]
    public void ExactProtectedResidenceCountIsAccepted()
    {
        const string path = "Meta/StrataLint/Golden/cases/known.toml";
        var manifest = Parse(1, ResidenceEntry(path));

        Assert.Empty(FileMapPolicy.InspectDirectoryKinds(manifest, [path]));
    }

    [Fact]
    public void AdditionalProtectedResidenceViolationIsRejected()
    {
        var manifest = Parse(
            1,
            ResidenceEntry("Meta/StrataLint/Golden/cases/**/*.toml"));

        var finding = Assert.Single(FileMapPolicy.InspectDirectoryKinds(
            manifest,
            [
                "Meta/StrataLint/Golden/cases/known.toml",
                "Meta/StrataLint/Golden/cases/new.toml",
            ]));

        Assert.Equal("FILEMAP-RESIDENCE-DRIFT", finding.Code);
    }

    [Fact]
    public void MissingProtectedResidenceViolationIsRejected()
    {
        const string path = "Meta/StrataLint/Golden/cases/known.toml";
        var manifest = Parse(2, ResidenceEntry(path));

        var finding = Assert.Single(FileMapPolicy.InspectDirectoryKinds(manifest, [path]));

        Assert.Equal("FILEMAP-RESIDENCE-DRIFT", finding.Code);
    }

    [Fact]
    public void ResidenceInventoryIncludesOnlyMarkedProtectedData()
    {
        const string externalPath = "Data/known.toml";
        const string unmarkedPath = "Meta/StrataLint/Golden/other.toml";
        const string markedPath = "Meta/StrataLint/Golden/values.toml";
        var manifest = Parse(
            ResidenceEntry(externalPath),
            Entry(unmarkedPath, "data", "none", "reader", "SnapshotDecoder"),
            ResidenceEntry(markedPath));

        var violations = FileMapPolicy.ResidenceViolations(
            manifest,
            [externalPath, markedPath, unmarkedPath]);

        Assert.Equal([markedPath], violations);
    }

    [Fact]
    public void UnclassifiedFileIsRejectedByTheRedFixture()
    {
        var manifest = Parse(Entry("D5/**/*.lean", "truth", "none", "lake", "lean-build"));

        var finding = Assert.Single(FileMapPolicy.InspectCoverage(
            manifest,
            ["D5/S0/Ring.lean", "README.md"]));

        Assert.Equal("FILEMAP-UNCLASSIFIED", finding.Code);
        Assert.Equal("README.md", finding.Path);
    }

    [Fact]
    public void OverlappingPatternsAreRejectedByTheRedFixture()
    {
        var manifest = Parse(
            Entry("D5/**/*.lean", "truth", "none", "lake", "lean-build"),
            Entry("D5/S0/**/*.lean", "truth", "none", "lake", "lean-build"));

        var finding = Assert.Single(FileMapPolicy.InspectCoverage(
            manifest,
            ["D5/S0/Ring.lean"]));

        Assert.Equal("FILEMAP-AMBIGUOUS", finding.Code);
        Assert.Contains("D5/**/*.lean", finding.Message, StringComparison.Ordinal);
        Assert.Contains("D5/S0/**/*.lean", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void RegistryAndTrackedRootDriftIsRejectedByTheRedFixture()
    {
        var finding = Assert.Single(FileMapPolicy.InspectRegistryRootAlignment(
            ["README.md"],
            ["Makefile", "README.md"]));

        Assert.Equal("FILEMAP-REGISTRY-ALIGNMENT", finding.Code);
        Assert.Contains("Makefile", finding.Message, StringComparison.Ordinal);
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
    public void InventoryBackedBlueprintGlobAndAggregateRemainAccepted()
    {
        var blueprintManifest = Parse(Entry(
            "Blueprint/**/*.md",
            "generated",
            "ScribeEmitter",
            "reader",
            "ScribeEmitter"));
        var blueprint = new GeneratedArtifactIdentity(
            "Blueprint/Foundations/example.md",
            "ScribeEmitter");
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
            blueprintManifest,
            [blueprint.Path],
            [blueprint]));
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
    [InlineData("run-local", false)]
    [InlineData("committed-source", true)]
    public void UntrackedGeneratedInventoryRespectsRuntimeDisposition(
        string runtimeDisposition,
        bool expectsStaleFinding)
    {
        var manifest = Parse(DispositionEntry(
            "Generated/output.json",
            "generated",
            "JsonEmitter",
            "reader",
            "JsonEmitter",
            runtimeDisposition,
            "A-OUTPUT"));
        var inventory = new GeneratedArtifactIdentity(
            "Generated/output.json", "JsonEmitter", "A-OUTPUT");

        var findings = FileMapPolicy.InspectGeneratedInventory(manifest, [], [inventory]);

        Assert.Equal(
            expectsStaleFinding,
            findings.Any(static finding => finding.Code == "FILEMAP-GENERATED-STALE-INVENTORY"));
    }

    [Fact]
    public void TrackedRunLocalGeneratedArtifactMustBeRemovedFromTheIndex()
    {
        const string artifactPath = "SyntheticArtifacts/output.json";
        var manifest = Parse(DispositionEntry(
            artifactPath, "generated", "SyntheticEmitter", "reader", "SyntheticEmitter",
            "run-local", "A-SYNTHETIC-OUTPUT"));
        var inventory = new GeneratedArtifactIdentity(
            artifactPath, "SyntheticEmitter", "A-SYNTHETIC-OUTPUT");

        var finding = Assert.Single(FileMapPolicy.InspectGeneratedInventory(
            manifest, [artifactPath], [inventory]));

        Assert.Equal("FILEMAP-RUN-LOCAL-TRACKED", finding.Code);
        Assert.Contains("remove", finding.Message, StringComparison.OrdinalIgnoreCase);
        Assert.Contains("index", finding.Message, StringComparison.OrdinalIgnoreCase);
        Assert.Contains("must not be changed", finding.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Theory]
    [InlineData("run-local", false)]
    [InlineData("committed-source", true)]
    public void ValidGeneratedDispositionDoesNotProduceDispositionFinding(
        string runtimeDisposition,
        bool isTracked)
    {
        const string artifactPath = "SyntheticArtifacts/output.json";
        var manifest = Parse(DispositionEntry(
            artifactPath, "generated", "SyntheticEmitter", "reader", "SyntheticEmitter",
            runtimeDisposition, "A-SYNTHETIC-OUTPUT"));
        var inventory = new GeneratedArtifactIdentity(
            artifactPath, "SyntheticEmitter", "A-SYNTHETIC-OUTPUT");
        var trackedPaths = isTracked ? new[] { artifactPath } : [];

        var findings = FileMapPolicy.InspectGeneratedInventory(manifest, trackedPaths, [inventory]);

        Assert.DoesNotContain(findings, static finding =>
            finding.Code is "FILEMAP-GENERATED-DISPOSITION" or "FILEMAP-RUN-LOCAL-TRACKED");
    }

    [Fact]
    public void UntrackedRunLocalWithWrongProducerIsRejectedByTheRedFixture()
    {
        var manifest = Parse(DispositionEntry(
            "Generated/output.json", "generated", "WrongEmitter", "reader", "WrongEmitter",
            "run-local", "A-OUTPUT"));
        var inventory = new GeneratedArtifactIdentity(
            "Generated/output.json", "JsonEmitter", "A-OUTPUT");

        var findings = FileMapPolicy.InspectGeneratedInventory(manifest, [], [inventory]);

        Assert.Contains(findings, static finding => finding.Code == "FILEMAP-GENERATED-PRODUCER");
        Assert.Contains(findings, static finding => finding.Code == "FILEMAP-GENERATED-STALE-INVENTORY");
    }

    [Fact]
    public void UntrackedRunLocalWithBroadGlobIsRejectedByTheRedFixture()
    {
        var manifest = Parse(DispositionEntry(
            "Generated/*.json", "generated", "JsonEmitter", "reader", "JsonEmitter",
            "run-local", "A-OUTPUT"));
        var inventory = new GeneratedArtifactIdentity(
            "Generated/output.json", "JsonEmitter", "A-OUTPUT");

        var findings = FileMapPolicy.InspectGeneratedInventory(manifest, [], [inventory]);

        Assert.Contains(findings, static finding => finding.Code == "FILEMAP-GENERATED-LITERAL");
        Assert.Contains(findings, static finding => finding.Code == "FILEMAP-GENERATED-STALE-INVENTORY");
    }

    [Fact]
    public void RunLocalEntryMissingRequiredFieldIsRejectedByTheRedFixture()
    {
        var source = DispositionEntry(
            "Generated/output.json", "generated", "JsonEmitter", "reader", "JsonEmitter",
            "run-local", "A-OUTPUT").Replace("mode = \"100644\"\n", string.Empty, StringComparison.Ordinal);

        var exception = Assert.Throws<FormatException>(() => Parse(source));

        Assert.Contains("mode", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CommittedGeneratedEntryMissingModeIsRejectedByTheRedFixture()
    {
        var source = DispositionEntry(
            "Generated/output.json", "generated", "JsonEmitter", "reader", "JsonEmitter",
            "committed-source", "A-OUTPUT").Replace("mode = \"100644\"\n", string.Empty, StringComparison.Ordinal);

        var exception = Assert.Throws<FormatException>(() => Parse(source));

        Assert.Contains("mode", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void WrongDeclaredCommittedModeIsRejectedByTheRedFixture()
    {
        var manifest = Parse(DispositionEntry(
            "Generated/output.json", "generated", "JsonEmitter", "reader", "JsonEmitter",
            "committed-source", "A-OUTPUT").Replace("100644", "100755", StringComparison.Ordinal));

        var finding = Assert.Single(FileMapPolicy.InspectDeclaredModes(
            manifest,
            new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["Generated/output.json"] = "100644",
            }));

        Assert.Equal("FILEMAP-GENERATED-MODE", finding.Code);
    }

    [Theory]
    [InlineData("Generated/manual.md", "data", "FILEMAP-DIRECTORY-KIND")]
    [InlineData("Meta/StrataLint/cases.toml", "data", "FILEMAP-DATA-RESIDENCE")]
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

    private static FileMapManifest Parse(int knownViolationCount, params string[] entries) =>
        FileMapLoader.Parse(
            Encoding.UTF8.GetBytes(
                $$"""
                schema_version = 2

                [residence_policy]
                case_id = "RESIDENCE-EPOCH"
                desired = "data-must-live-outside-Meta/StrataLint"
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
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = [{{string.Join(", ", verifiedBy.Select(static name => $"\"{name}\""))}}]
        authority = "self"
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
        produced_by = "{{producedBy}}"
        consumed_by = ["{{consumedBy}}"]
        verified_by = ["{{verifiedBy}}"]
        authority = "self"
        runtime_disposition = "committed-source"
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
        produced_by = "{{producedBy}}"
        consumed_by = ["{{consumedBy}}"]
        verified_by = ["{{verifiedBy}}"]
        authority = "self"
        runtime_disposition = "{{runtimeDisposition}}"
        artifact_id = "{{artifactId}}"
        mode = "100644"
        history_requirement = "not-required"
        """ + "\n";
}
