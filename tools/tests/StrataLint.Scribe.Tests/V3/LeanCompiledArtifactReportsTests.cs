using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class LeanCompiledArtifactReportsTests
{
    [Fact]
    public void MissingRawLeanReportFailsWithProducerInstruction()
    {
        var root = Path.Combine(
            Path.GetTempPath(),
            "stratalint-scribe-" + Guid.NewGuid().ToString("N"));
        TemporaryFileSystem.Directory.CreateDirectory(root);

        try
        {
            var exception = Assert.Throws<InvalidOperationException>(
                () => LeanCompiledArtifactReports.ReadRepositoryFiles(root));

            Assert.Contains("raw Lean report", exception.Message, StringComparison.Ordinal);
            Assert.Contains("inspect.sh", exception.Message, StringComparison.Ordinal);
        }
        finally
        {
            TemporaryFileSystem.Directory.Delete(root, recursive: true);
        }
    }

    [Fact]
    public void ConfiguredReportPathOverridesTheCanonicalArtifact()
    {
        var repositoryRoot = RepositoryAccessor.Discover(RepositoryRootCriterion.ClaudeDirectoryNotFound).Root.FullPath;
        var configured = Path.Combine(
            Path.GetTempPath(),
            "stratalint-configured-report-" + Guid.NewGuid().ToString("N") + ".json");
        var exception = Assert.Throws<InvalidOperationException>(
            () => LeanCompiledArtifactReports.ReadRepositoryFiles(repositoryRoot, configured));

        Assert.Contains(configured, exception.Message, StringComparison.Ordinal);
    }
    [Fact]
    public void FileReportReadsAllReportModulesWithoutReadingOtherFiles()
    {
        using var root = new TemporaryRoot();
        var entries = new[]
        {
            RawRepositoryEntry.FromText("Trureturing.lean", "-- root\n"),
            RawRepositoryEntry.FromText("D5/S0/Synthetic/Probe.lean", "-- content\n"),
            RawRepositoryEntry.FromText("Reg/D5/S0/Synthetic/Probe.lean", "-- registration\n"),
        };
        foreach (var entry in entries)
            File.WriteAllBytes(root.Resolve(entry.Path), entry.Bytes.AsSpan());
        File.WriteAllBytes(root.Resolve("Blueprint/unrelated.md"), [0xff]);
        File.WriteAllBytes(root.Resolve("tools/unrelated.lean"), [0xff]);
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(RawRepositorySnapshot.Create(entries))).Snapshot;
        var reportPath = root.Resolve("report.json");
        RawLeanReportArtifact.WriteFile(reportPath, snapshot, LeanAxiomReport.Create(
            entries.ToDictionary(entry => entry.Path, _ => new LeanFileReport([], []))));

        var report = LeanCompiledArtifactReports.ReadRepositoryFiles(root.Path, "report.json");

        Assert.False(Directory.Exists(root.Resolve(".git")));
        Assert.Equal(entries.Select(entry => entry.Path).Order(StringComparer.Ordinal),
            report.Files.Keys.Select(path => path.Value).Order(StringComparer.Ordinal));
        File.WriteAllText(root.Resolve("Reg/Additional.lean"), "-- new module\n");
        Assert.Contains("Raw Lean report is missing modules: Reg/Additional.lean",
            Assert.Throws<FormatException>(() => LeanCompiledArtifactReports.ReadRepositoryFiles(root.Path, "report.json")).Message,
            StringComparison.Ordinal);
        File.Delete(root.Resolve("Reg/Additional.lean"));
        File.Delete(root.Resolve("Trureturing.lean"));
        Assert.Contains("Raw Lean report contains unknown module Trureturing",
            Assert.Throws<FormatException>(() => LeanCompiledArtifactReports.ReadRepositoryFiles(root.Path, "report.json")).Message,
            StringComparison.Ordinal);
    }

}
