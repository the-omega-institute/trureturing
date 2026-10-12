using StrataLint.Cli;
using StrataLint.Engine;

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
