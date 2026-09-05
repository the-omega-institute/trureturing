using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.ArchitectureTests;

public sealed partial class FileMapPolicyTests
{
    [Fact]
    public void ComputationalProjectionsHaveCanonicalFileMapEntries()
    {
        var expectedPaths = new HashSet<string>(
            [
                ScribeEmitter.AttestationRelativePath,
                "Generated/truth-graph.v1.json",
            ],
            StringComparer.Ordinal);
        var root = RepositoryLayout.FindRoot();
        var manifest = FileMapLoader.LoadRepository(root);
        // 文档已迁出本程序集(住 StrataLint.Scribe.Documents),而本测试判的是 FILEMAP 声明
        // 与发射器产物身份的一致性,不判语料内容。故喂一条与下方 manifest.Match 同一字面的
        // 文档路径即可:六个固定工件与文档集无关,Blueprint/**/*.md 那条只需一个同形路径。
        var inventory = GeneratedArtifactInventory.Create(
            ["Blueprint/D5/S0/Carrier/Ring.md"]);
        var artifacts = inventory
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
        const string pattern = "Blueprint/**/*.md";
        var entry = Assert.Single(manifest.Match("Blueprint/D5/S0/Carrier/Ring.md"));

        Assert.Equal(pattern, entry.Pattern);
        Assert.Equal(FileMapKind.Generated, entry.Kind);
        Assert.Equal("ScribeEmitter", entry.ProducedBy);
        Assert.Equal(
            ["ScribeEmitter", "reader"],
            entry.ConsumedBy.ToArray());
        Assert.Equal(["ScribeEmitter"], entry.VerifiedBy.ToArray());
        Assert.Contains(
            inventory,
            artifact => entry.Matches(artifact.Path));
        Assert.DoesNotContain(
            FileMapPolicy.InspectRepository(root),
            finding => finding.Path == pattern);
    }

    [Fact]
    public void AgentReportsAreAdmittedByRepositoryPathPolicy()
    {
        // Agent-written reports have generated names, cannot be enumerated in
        // registry.yaml governance_documents, so RepositoryPathPolicy admits the
        // docs/reports/ prefix and SL-000 must not reject them.
        const string value = "docs/reports/diag-lane-a/synthetic-open-report.md";
        var registry = SyntheticRegistry();
        var path = RepoPath.CreateKnown(value);

        Assert.Null(RepositoryPathPolicy.Validate(path, registry.Policy));
    }

    [Fact]
    public void DevelopmentSpecDocumentsAreAdmittedByRepositoryPathPolicy()
    {
        // Spec drafts have author-chosen names that cannot be enumerated in
        // registry.yaml governance_documents ahead of time, exactly as theory
        // volumes and agent reports cannot. Enumerating them there made adding
        // one document require a harness edit, and that edit could not ship:
        // the admission-plane gate refuses a PR that touches both the judge
        // plane (registry.yaml) and the content plane (the document), so the
        // pair could never land together, while either half alone was rejected
        // by FILEMAP-REGISTRY-DANGLING or SL-000 respectively.
        const string value = "docs/develop/spec/synthetic-unregistered-spec.md";
        var registry = SyntheticRegistry();
        var path = RepoPath.CreateKnown(value);

        Assert.Null(RepositoryPathPolicy.Validate(path, registry.Policy));
    }

    [Fact]
    public void DevelopmentDirectoriesOutsideSpecAndTheoryAreRefusedByRepositoryPathPolicy()
    {
        // Reverse nail: the admitted prefix is docs/develop/spec/, not the
        // broader docs/develop/. A sibling directory must still be refused,
        // so widening the prefix by mistake turns this test red.
        const string value = "docs/develop/scratch/synthetic-note.md";
        var registry = SyntheticRegistry();
        var path = RepoPath.CreateKnown(value);

        var issue = RepositoryPathPolicy.Validate(path, registry.Policy);

        Assert.NotNull(issue);
        Assert.Contains("unknown top-level artifact", issue!.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CodexSkillPackagesAreAdmittedByRepositoryPathPolicy()
    {
        // A Codex skill package is a directory containing SKILL.md, whose file
        // names cannot be enumerated individually in registry.yaml.
        const string value = ".codex/skills/synthetic-skill/SKILL.md";
        var registry = SyntheticRegistry();
        var path = RepoPath.CreateKnown(value);

        Assert.Null(RepositoryPathPolicy.Validate(path, registry.Policy));
    }

    [Fact]
    public void CodexArtifactsOutsideSkillsAreRefusedByRepositoryPathPolicy()
    {
        const string value = ".codex/settings.toml";
        var registry = SyntheticRegistry();
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
        var registry = SyntheticRegistry();
        var path = RepoPath.CreateKnown(value);

        Assert.Null(RepositoryPathPolicy.Validate(path, registry.Policy));
    }

    [Fact]
    public void SkillsPrefixWithoutSeparatorIsRefusedByRepositoryPathPolicy()
    {
        const string value = "skills.md";
        var registry = SyntheticRegistry();
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
    public void EmptyCommittedPatternIsRejectedByTheRedFixture()
    {
        const string pattern = "Data/retired/*.json";
        var manifest = Parse(Entry(pattern, "data", "none", "reader", "SnapshotDecoder"));

        var finding = Assert.Single(FileMapPolicy.InspectPatternPopulation(manifest, []));

        Assert.Equal("FILEMAP-PATTERN-EMPTY", finding.Code);
        Assert.Equal(pattern, finding.Path);
    }

    [Fact]
    public void PopulatedCommittedPatternIsAcceptedByTheGreenFixture()
    {
        var manifest = Parse(Entry(
            "Data/current/*.json",
            "data",
            "none",
            "reader",
            "SnapshotDecoder"));

        Assert.Empty(FileMapPolicy.InspectPatternPopulation(
            manifest,
            ["Data/current/object.json"]));
    }

    [Fact]
    public void EmptyRunLocalPatternIsAcceptedByTheExemptFixture()
    {
        var manifest = Parse(DispositionEntry(
            "Generated/retired.json",
            "generated",
            "SyntheticEmitter",
            "reader",
            "SyntheticEmitter",
            "run-local",
            "A-SYNTHETIC-RETIRED"));

        Assert.Empty(FileMapPolicy.InspectPatternPopulation(manifest, []));
    }

    [Fact]
    public void EmptyFrozenStatePatternIsRejectedLikeAnyOtherCommittedPattern()
    {
        var manifest = Parse(Entry(
            "Golden/Frozen/state/**/*.json",
            "data",
            "FrozenStateWriter",
            "FrozenStateCatalog",
            "FrozenStateRecordLoader"));

        var finding = Assert.Single(FileMapPolicy.InspectPatternPopulation(manifest, []));
        Assert.Equal("FILEMAP-PATTERN-EMPTY", finding.Code);
        Assert.Equal("Golden/Frozen/state/**/*.json", finding.Path);
    }

    [Fact]
    public void DanglingGeneratedAndDataActorsAreRejectedByTheRedFixture()
    {
        const string pattern = "Generated/output.json";
        var manifest = Parse(Entry(
            pattern,
            "generated",
            "MissingEmitter",
            "reader",
            "MissingEmitter"));

        var findings = FileMapPolicy.InspectDeclaredActors(
            manifest,
            new HashSet<string>(StringComparer.Ordinal),
            "fixture-root");

        Assert.Equal(2, findings.Count);
        Assert.All(findings, finding =>
        {
            Assert.Equal("FILEMAP-ACTOR-DANGLING", finding.Code);
            Assert.Contains("MissingEmitter", finding.Message, StringComparison.Ordinal);
        });
        var declaredTypes = new HashSet<string>(StringComparer.Ordinal) { "ScribeEmitter" };
        var danglingProducer = Assert.Single(FileMapPolicy.InspectDeclaredActors(
            Parse(Entry(pattern, "data", "MissingEmitter", "reader", "ScribeEmitter")),
            declaredTypes,
            "fixture-root"));
        var danglingConsumer = Assert.Single(FileMapPolicy.InspectDeclaredActors(
            Parse(Entry(pattern, "data", "none", "DigestionStatusEvaluator", "ScribeEmitter")),
            declaredTypes,
            "fixture-root"));

        Assert.Contains("produced_by names MissingEmitter", danglingProducer.Message, StringComparison.Ordinal);
        Assert.Contains(
            "consumed_by names DigestionStatusEvaluator",
            danglingConsumer.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void DeclaredGeneratedActorIsAcceptedByTheGreenFixture()
    {
        var manifest = Parse(Entry(
            "Generated/output.json",
            "generated",
            "FixtureEmitter",
            "reader",
            "FixtureEmitter"));

        Assert.Empty(FileMapPolicy.InspectDeclaredActors(
            manifest,
            new HashSet<string>(StringComparer.Ordinal) { "FixtureEmitter" },
            "fixture-root"));
    }

    [Theory]
    [InlineData("ledger")]
    [InlineData("truth")]
    public void DanglingLedgerAndTruthActorsAreRejectedByTheRedFixture(string kind)
    {
        var manifest = Parse(Entry(
            $"Synthetic/{kind}.txt",
            kind,
            "none",
            "MissingConsumer",
            "MissingVerifier"));

        var findings = FileMapPolicy.InspectDeclaredActors(
            manifest,
            new HashSet<string>(StringComparer.Ordinal),
            "fixture-root");

        Assert.Collection(
            findings,
            finding =>
            {
                Assert.Equal("FILEMAP-ACTOR-DANGLING", finding.Code);
                Assert.Contains("consumed_by names MissingConsumer", finding.Message, StringComparison.Ordinal);
            },
            finding =>
            {
                Assert.Equal("FILEMAP-ACTOR-DANGLING", finding.Code);
                Assert.Contains("verified_by names MissingVerifier", finding.Message, StringComparison.Ordinal);
            });
    }

    [Fact]
    public void LedgerVerifierNamedByARuleIdIsAcceptedByTheGreenFixture()
    {
        var manifest = Parse(Entry(
            "Synthetic/ledger.md",
            "ledger",
            "none",
            "reader",
            "SL-008"));

        Assert.Empty(FileMapPolicy.InspectDeclaredActors(
            manifest,
            new HashSet<string>(StringComparer.Ordinal),
            "fixture-root"));
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
    public void MatchingRegistryAndTrackedRootsAreAcceptedByTheGreenFixture()
    {
        Assert.Empty(FileMapPolicy.InspectRegistryRootAlignment(
            ["Makefile", "README.md"],
            ["README.md", "Makefile"]));
    }
}
