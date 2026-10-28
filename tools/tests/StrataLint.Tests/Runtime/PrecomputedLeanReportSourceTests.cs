using StrataLint.Cli;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.Tests;

[Collection("Lean report environment")]
public sealed class PrecomputedLeanReportSourceTests
{
    [Fact]
    public void ExplicitScopeReadsOnlyItsBundleAndFullConsumersRejectIt()
    {
        using var repository = new TemporaryDirectory();
        var selected = RawRepositoryEntry.FromText("D5/Selected.lean", "prelude\n");
        var sibling = RawRepositoryEntry.FromText("D5/Sibling.lean", "prelude\n");
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create([selected, sibling]))).Snapshot;
        var selectedSnapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create([selected]))).Snapshot;
        var reportPath = Path.Combine(repository.Path, "scoped-report.json");
        RawLeanReportArtifact.WriteFile(reportPath, selectedSnapshot,
            LeanAxiomReport.Create(new Dictionary<string, LeanFileReport> { [selected.Path] = new([], []) }));
        File.WriteAllText(reportPath, File.ReadAllText(reportPath).Replace(
            "stratalint-raw-lean-report-v3", "stratalint-scoped-lean-report-v1", StringComparison.Ordinal));
        var previous = Environment.GetEnvironmentVariable("STRATALINT_LEAN_REPORT");
        Environment.SetEnvironmentVariable("STRATALINT_LEAN_REPORT", reportPath);
        try
        {
            var source = new PrecomputedLeanReportSource(repository.Path);
            var report = LeanReportSourceScope.Load(source, snapshot, [RepoPath.CreateKnown(selected.Path)]);

            Assert.Equal(selected.Path, Assert.Single(report.Files).Key.Value);
            Assert.True(report.IsScoped);
            Assert.Throws<FormatException>(() => source.Load(snapshot));
        }
        finally
        {
            Environment.SetEnvironmentVariable("STRATALINT_LEAN_REPORT", previous);
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void FullBundleCanSupplyScopeOnlyAfterValidatingEverySource(bool corruptSibling)
    {
        using var repository = new TemporaryDirectory();
        var selected = RawRepositoryEntry.FromText("D5/Selected.lean", "prelude\n");
        var sibling = RawRepositoryEntry.FromText("D5/Sibling.lean", "prelude\n");
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create([selected, sibling]))).Snapshot;
        var path = Path.Combine(repository.Path, "full-report.json");
        RawLeanReportArtifact.WriteFile(path, snapshot, LeanAxiomReport.Create(
            new Dictionary<string, LeanFileReport> { [selected.Path] = new([], []), [sibling.Path] = new([], []) }));
        var current = corruptSibling ? Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create([selected, RawRepositoryEntry.FromText(sibling.Path, "prelude\n-- changed\n")]))).Snapshot : snapshot;
        var previous = Environment.GetEnvironmentVariable("STRATALINT_LEAN_REPORT");
        Environment.SetEnvironmentVariable("STRATALINT_LEAN_REPORT", path);
        try
        {
            var source = new PrecomputedLeanReportSource(repository.Path);
            if (corruptSibling)
            {
                var error = Assert.Throws<FormatException>(() =>
                    LeanReportSourceScope.Load(source, current, [RepoPath.CreateKnown(selected.Path)]));
                Assert.Contains(sibling.Path, error.Message, StringComparison.Ordinal);
            }
            else
            {
                var report = LeanReportSourceScope.Load(source, current, [RepoPath.CreateKnown(selected.Path)]);
                Assert.True(report.IsScoped);
                Assert.Equal(selected.Path, Assert.Single(report.Files).Key.Value);
            }
        }
        finally
        {
            Environment.SetEnvironmentVariable("STRATALINT_LEAN_REPORT", previous);
        }
    }

    [Theory]
    [InlineData("none")]
    [InlineData("imports")]
    [InlineData("statement")]
    public void FullBundleProjectionRetainsScopedIdentityAndImportChecks(string defect)
    {
        using var repository = new TemporaryDirectory();
        var selected = RawRepositoryEntry.FromText("D5/Selected.lean", "prelude\ntheorem selected : True := by trivial\n");
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create([selected]))).Snapshot;
        var path = Path.Combine(repository.Path, "full-report.json");
        RawLeanReportArtifact.WriteFile(path, snapshot, LeanAxiomReport.Create(
            new Dictionary<string, LeanFileReport> { [selected.Path] = new([], [new("selected", "theorem", "True", [])]) }));
        var document = System.Text.Json.Nodes.JsonNode.Parse(File.ReadAllText(path))!;
        var module = document["modules"]![0]!;
        if (defect == "imports") module["imports"] = new System.Text.Json.Nodes.JsonArray("Mathlib");
        else if (defect == "statement") module["declarations"]![0]!["statement_id"] = "sha256:" + new string('0', 64);
        File.WriteAllBytes(path, StructuredCanonicalWriter.WriteJson(document.ToJsonString()).ToArray());
        var previous = Environment.GetEnvironmentVariable("STRATALINT_LEAN_REPORT");
        Environment.SetEnvironmentVariable("STRATALINT_LEAN_REPORT", path);
        try
        {
            var source = new PrecomputedLeanReportSource(repository.Path);
            if (defect == "none")
            {
                var scoped = LeanReportSourceScope.Load(source, snapshot, [RepoPath.CreateKnown(selected.Path)]);
                Assert.Equal("True", Assert.Single(Assert.Single(scoped.Files).Value.Declarations).LoadTypeRepresentation());
                return;
            }
            var error = Assert.ThrowsAny<Exception>(() =>
                LeanReportSourceScope.Load(source, snapshot, [RepoPath.CreateKnown(selected.Path)]));
            Assert.Contains(defect == "imports" ? "imports do not match source" : "statement identity does not match material",
                error.Message, StringComparison.Ordinal);
        }
        finally
        {
            Environment.SetEnvironmentVariable("STRATALINT_LEAN_REPORT", previous);
        }
    }

    [Fact]
    public void ScopedAdapterClassifiesInvalidJsonAsUnusableReport()
    {
        using var repository = new TemporaryDirectory();
        var selected = RawRepositoryEntry.FromText("D5/Selected.lean", "prelude\n");
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create([selected]))).Snapshot;
        var path = Path.Combine(repository.Path, "invalid-report.json");
        File.WriteAllText(path, "{invalid");
        var previous = Environment.GetEnvironmentVariable("STRATALINT_LEAN_REPORT");
        Environment.SetEnvironmentVariable("STRATALINT_LEAN_REPORT", path);
        try
        {
            var source = new PrecomputedLeanReportSource(repository.Path);
            var error = Assert.Throws<FormatException>(() =>
                LeanReportSourceScope.Load(source, snapshot, [RepoPath.CreateKnown(selected.Path)]));
            Assert.Equal("Raw Lean report is not valid JSON.", error.Message);
        }
        finally
        {
            Environment.SetEnvironmentVariable("STRATALINT_LEAN_REPORT", previous);
        }
    }

    [Fact]
    public void ConfiguredReportPathOverridesTheCanonicalArtifact()
    {
        using var repository = new TemporaryDirectory();
        var configured = Path.Combine(repository.Path, "private-report.json");
        var previous = Environment.GetEnvironmentVariable("STRATALINT_LEAN_REPORT");
        Environment.SetEnvironmentVariable("STRATALINT_LEAN_REPORT", configured);

        try
        {
            var source = new PrecomputedLeanReportSource(repository.Path);
            var exception = Assert.ThrowsAny<IOException>(() => source.Load((RepositorySnapshot)null!));

            Assert.Contains(configured, exception.Message, StringComparison.Ordinal);
        }
        finally
        {
            Environment.SetEnvironmentVariable("STRATALINT_LEAN_REPORT", previous);
        }
    }
}

[CollectionDefinition("Lean report environment", DisableParallelization = true)]
public sealed class LeanReportEnvironmentCollection;
