using System.Text;
using StrataLint.FileMap;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.RepositoryFileMap.Tests;

[Collection(nameof(CanonicalFileMapCollection))]
public sealed partial class FileMapPolicyTests(CanonicalFileMapFixture fixture)
{
    [Theory]
    [InlineData("lean-report-inputs.json", "LeanReportSelection", "lean-report")]
    [InlineData("Meta/ci-cache-paths.json", "NativeArchivePaths", "test-cache")]
    public void RuntimeManifestIsAdmittedWithItsRuntimeVerifier(string path, string verifier, string resource)
    {
        var root = TestRepositoryLayout.FindRoot();
        var registry = Assert.IsType<RegistryLoadOutcome.Accepted>(RegistryLoader.Load(
            File.ReadAllBytes(Path.Combine(root, "Meta/registry.yaml")),
            File.ReadAllBytes(Path.Combine(root, "Meta/domains.yaml"))));
        Assert.Null(RepositoryPathPolicy.Validate(RepoPath.CreateKnown(path), registry.Policy));
        var manifest = FileMapLoader.LoadRepository(root);
        var entry = Assert.Single(manifest.Match(path));
        Assert.Equal(FileMapKind.Data, entry.Kind);
        Assert.Equal(FileMapAdmissionPlane.Judge, entry.AdmissionPlane);
        Assert.Equal(verifier, Assert.Single(entry.VerifiedBy));
        Assert.Contains(resource, entry.Require);
        Assert.DoesNotContain(fixture.Findings, finding =>
            finding.Path == path && finding.Code is "FILEMAP-ACTOR-DANGLING"
                or "FILEMAP-DATA-VERIFIER" or "FILEMAP-DATA-VERIFIER-DANGLING");
    }

    [Fact]
    public void CommonExecutionManifestsHaveRegisteredDataVerifiers()
    {
        var root = TestRepositoryLayout.FindRoot();
        var manifest = FileMapLoader.LoadRepository(root);
        string[] paths = ["Meta/ci-checks.json", "Meta/engineering-projects.json"];
        Assert.All(paths, path =>
        {
            var entry = Assert.Single(manifest.Match(path));
            Assert.Equal(FileMapKind.Data, entry.Kind);
            Assert.Contains("CommonExecutionEvidence", entry.VerifiedBy);
        });

        var findings = fixture.Findings;

        Assert.DoesNotContain(findings, finding =>
            paths.Contains(finding.Path, StringComparer.Ordinal)
            && finding.Code is "FILEMAP-DATA-VERIFIER" or "FILEMAP-DATA-VERIFIER-DANGLING");
    }

    [Theory]
    [InlineData("lean-report")]
    [InlineData("scribe-content")]
    public void ReportProducerScopesHaveRegisteredDataVerifier(string scope)
    {
        var root = TestRepositoryLayout.FindRoot();
        var manifest = FileMapLoader.LoadRepository(root);
        var entry = Assert.Single(manifest.Match($"Meta/ReportProducers/{scope}.json"));

        Assert.Equal(FileMapKind.Data, entry.Kind);
        Assert.Equal(FileMapAdmissionPlane.Judge, entry.AdmissionPlane);
        Assert.Equal("CommonExecutionEvidence", Assert.Single(entry.VerifiedBy));
        Assert.Equal("committed-source", entry.RuntimeDisposition);
    }

    [Theory]
    [InlineData("lean-report")]
    [InlineData("scribe-content")]
    public void ReportConsumerScopesAreAdmittedByRegisteredRepositoryPolicy(string scope)
    {
        var root = TestRepositoryLayout.FindRoot();
        var registry = Assert.IsType<RegistryLoadOutcome.Accepted>(RegistryLoader.Load(
            File.ReadAllBytes(Path.Combine(root, "Meta/registry.yaml")),
            File.ReadAllBytes(Path.Combine(root, "Meta/domains.yaml"))));
        var path = $"Meta/ReportConsumers/{scope}.json";

        Assert.Null(RepositoryPathPolicy.Validate(RepoPath.CreateKnown(path), registry.Policy));
        var entry = Assert.Single(FileMapLoader.LoadRepository(root).Match(path));
        Assert.Equal(FileMapKind.Data, entry.Kind);
        Assert.Equal(FileMapAdmissionPlane.Judge, entry.AdmissionPlane);
        Assert.Equal("CommonExecutionEvidence", Assert.Single(entry.VerifiedBy));
    }

    [Theory]
    [InlineData("Meta/ReportConsumers/unregistered.json")]
    [InlineData("Meta/ReportConsumers/nested/lean-report.json")]
    [InlineData("Meta/unregistered.json")]
    public void UnregisteredMetaArtifactsRemainRejected(string path)
    {
        var root = TestRepositoryLayout.FindRoot();
        var registry = Assert.IsType<RegistryLoadOutcome.Accepted>(RegistryLoader.Load(
            File.ReadAllBytes(Path.Combine(root, "Meta/registry.yaml")),
            File.ReadAllBytes(Path.Combine(root, "Meta/domains.yaml"))));

        var issue = RepositoryPathPolicy.Validate(RepoPath.CreateKnown(path), registry.Policy);

        Assert.NotNull(issue);
        Assert.Equal("SL-000", issue.RuleId.Value);
        Assert.Equal("unknown Meta artifact", issue.Message);
    }

    [Fact]
    public void ComputationalProjectionsHaveCanonicalFileMapEntries()
    {
        var expectedPaths = new HashSet<string>(
            [
                ScribeEmitter.AttestationRelativePath,
                "Generated/truth-graph.v1.json",
            ],
            StringComparer.Ordinal);
        var root = TestRepositoryLayout.FindRoot();
        var manifest = FileMapLoader.LoadRepository(root);
        // 文档已迁出本程序集(住 StrataLint.Scribe.Documents),而本测试判的是 FILEMAP 声明
        // 与发射器产物身份的一致性,不判语料内容。故喂一条与下方 manifest.Match 同一字面的
        // 文档路径即可:六个固定工件与文档集无关,文档分区只需一个同形路径。
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
        const string pattern = "Blueprint/D5/S0/**/*.md";
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
            fixture.Findings,
            finding => finding.Path == pattern);
    }

    [Fact]
    public void LibrarySplitBucketsAreClassifiedAsData()
    {
        var manifest = FileMapLoader.LoadRepository(TestRepositoryLayout.FindRoot());

        Assert.Equal(
            FileMapKind.Data,
            Assert.Single(manifest.Match("Library/Weil/sample2026paper.md")).Kind);
    }

}
