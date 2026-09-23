using StrataLint.EngineeringScope;
using static StrataLint.TestSupport.TransportFixture;
using static StrataLint.TestSupport.ExecutionFixture;
using System.Diagnostics;
using System.Formats.Tar;
using System.IO.Compression;
using System.Security.Cryptography;
using System.Text.Json;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.TransportIntegration.Tests;

[Collection("StrataLint.TransportIntegration.Tests process boundary")]
public sealed partial class CiTransportTests
{

    [Theory]
    [InlineData("build")]
    [InlineData("engineering")]
    [InlineData("current")]
    [InlineData("engineering-seed")]
    [InlineData("current-seed")]
    public void NativeTransportSharesRequiredPayloadsAndRestoresIndependentFiles(string stage)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ExecutionFixture();
        var root = fixture.Root;
        Prepare(fixture, stage.StartsWith("current", StringComparison.Ordinal));
        var owner = stage.Replace("-seed", "", StringComparison.Ordinal);
        var original = CommonExecutionEvidence.Read<CommonStageRecord>(root, "build/ci/" + owner + ".json");
        var equal = original.Materials.GroupBy(material => material.Sha256)
            .First(group => group.Count() > 1).Take(2).ToArray();
        File.SetLastWriteTimeUtc(Path.Combine(root, equal[0].Path), new DateTime(2020, 1, 2, 3, 4, 5, DateTimeKind.Utc));
        File.SetLastWriteTimeUtc(Path.Combine(root, equal[1].Path), new DateTime(2021, 2, 3, 4, 5, 6, DateTimeKind.Utc));
        if (owner == "current")
            File.SetUnixFileMode(Path.Combine(root, CommonExecutionEvidence.ReportPath + ".input.attestation"),
                UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var commit = Git(root, "rev-parse", "HEAD");
        var archive = Path.Combine(root, "build/alias.tgz");
        Assert.Equal(0, Run("transport-pack", root, stage, commit, "17", "2", archive));
        var manifest = CommonExecutionEvidence.Read<CiTransportRecord>(root, CiTransport.ManifestPath(stage));
        var entries = new Dictionary<string, (TarEntryType Type, string Link, UnixFileMode Mode, DateTimeOffset Modified, long Length)>(StringComparer.Ordinal);
        using (var input = new GZipStream(File.OpenRead(archive), CompressionMode.Decompress))
        using (var reader = new TarReader(input))
            while (reader.GetNextEntry() is { } entry)
                entries.Add(entry.Name, (entry.EntryType, entry.LinkName, entry.Mode, entry.ModificationTime, entry.Length));
        var seed = stage.EndsWith("-seed", StringComparison.Ordinal);
        var groups = manifest.Materials.GroupBy(material => (material.Sha256, material.Mode)).ToArray();
        Assert.Contains(groups, group => group.Count() > 1);
        foreach (var group in groups)
        {
            var paths = group.Select(material => material.Path).Order(StringComparer.Ordinal).ToArray();
            var regular = paths.Where(path => entries[path].Type is TarEntryType.RegularFile or TarEntryType.V7RegularFile).ToArray();
            Assert.True(regular.Length == (seed ? paths.Length : 1),
                $"{stage}: expected {(seed ? paths.Length : 1)} regular payloads for {group.Key}, actual {regular.Length}");
            foreach (var path in paths)
            {
                Assert.Equal((UnixFileMode)group.Key.Mode, entries[path].Mode);
                Assert.Equal(new DateTimeOffset(File.GetLastWriteTimeUtc(Path.Combine(root, path))).ToUnixTimeSeconds(),
                    entries[path].Modified.ToUnixTimeSeconds());
                if (seed || path == regular[0]) continue;
                Assert.Equal(TarEntryType.HardLink, entries[path].Type);
                Assert.Equal(regular[0], entries[path].Link);
                Assert.Equal(0, entries[path].Length);
            }
        }
        Assert.Equal(TarEntryType.RegularFile, entries[CiTransport.ManifestPath(stage)].Type);
        if (seed) return; // Optional seed consumers retain the existing regular-file format.
        if (owner == "current") Assert.Contains(manifest.Materials.GroupBy(material => material.Sha256),
            group => group.Select(material => material.Mode).Distinct().Count() > 1);
        var target = Path.Combine(root, "build/destination");
        Git(root, "clone", "--quiet", "--no-hardlinks", root, target);
        if (stage == "engineering")
        {
            var buildArchive = Path.Combine(root, "build/shared.tgz");
            Assert.Equal(0, Run("transport-pack", root, "build", commit, "17", "2", buildArchive));
            var shared = Extract(target, buildArchive, "build");
            Assert.True(shared.Exit == 0, shared.Text);
        }
        var restored = Extract(target, archive, stage);
        Assert.True(restored.Exit == 0, restored.Text);
        Assert.Equal(0, Run("transport-verify", target, stage, commit, "17", "2"));
        foreach (var material in manifest.Materials)
        {
            var source = Path.Combine(root, material.Path);
            var destination = Path.Combine(target, material.Path);
            Assert.Equal(File.ReadAllBytes(source), File.ReadAllBytes(destination));
            Assert.Equal(File.GetUnixFileMode(source), File.GetUnixFileMode(destination));
            Assert.Equal(entries[material.Path].Modified.ToUnixTimeSeconds(),
                new DateTimeOffset(File.GetLastWriteTimeUtc(destination)).ToUnixTimeSeconds());
            if (equal.Any(original => original.Path == material.Path))
                Assert.Equal(File.GetLastWriteTimeUtc(source), File.GetLastWriteTimeUtc(destination));
            Assert.Null(new FileInfo(destination).LinkTarget);
        }
        var pair = groups.First(group => group.Count() > 1).Take(2).Select(material => Path.Combine(target, material.Path)).ToArray();
        var untouched = File.ReadAllBytes(pair[1]);
        File.WriteAllText(pair[0], "independent mutation\n");
        Assert.Equal(untouched, File.ReadAllBytes(pair[1]));
    }

    [Theory]
    [InlineData("valid")]
    [InlineData("missing")]
    [InlineData("escape")]
    [InlineData("absolute")]
    [InlineData("self")]
    [InlineData("chain")]
    [InlineData("directory")]
    [InlineData("symlink")]
    [InlineData("manifest-target")]
    [InlineData("manifest-alias")]
    [InlineData("hash-association")]
    [InlineData("mode-association")]
    [InlineData("header-mode")]
    [InlineData("target-content")]
    public void DeclaredArchiveAliasesAreValidatedBeforeAnyMaterialIsWritten(string defect)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ExecutionFixture();
        var root = fixture.Root;
        Prepare(fixture, current: false);
        var commit = Git(root, "rev-parse", "HEAD");
        var archive = Path.Combine(root, "build/original.tgz");
        Assert.Equal(0, Run("transport-pack", root, "build", commit, "17", "2", archive));
        var manifestPath = CiTransport.ManifestPath("build");
        var manifest = CommonExecutionEvidence.Read<CiTransportRecord>(root, manifestPath);
        var pair = manifest.Materials.GroupBy(material => (material.Sha256, material.Mode))
            .First(group => group.Count() > 1).OrderBy(material => material.Path, StringComparer.Ordinal).Take(2).ToArray();
        var first = pair[0].Path;
        var alias = pair[1].Path;
        if (defect is "hash-association" or "mode-association")
            manifest = manifest with { Materials = manifest.Materials.Select(material => material.Path != alias ? material
                : defect == "hash-association" ? material with { Sha256 = new string('0', 64) }
                : material with { Mode = material.Mode ^ (int)UnixFileMode.UserExecute }).ToArray() };
        CommonExecutionEvidence.Write(root, manifestPath, manifest);
        var crafted = Path.Combine(root, "build/crafted.tgz");
        using (var output = new GZipStream(File.Create(crafted), CompressionLevel.Fastest))
        using (var writer = new TarWriter(output))
            foreach (var path in manifest.Materials.Select(material => material.Path).Append(manifestPath))
            {
                var type = path == alias || path == first && defect == "chain" || path == manifestPath && defect == "manifest-alias"
                    ? TarEntryType.HardLink : path == first && defect == "directory" ? TarEntryType.Directory
                    : path == first && defect == "symlink" ? TarEntryType.SymbolicLink : TarEntryType.RegularFile;
                var entry = new PaxTarEntry(type, path) { Mode = File.GetUnixFileMode(Path.Combine(root, path)),
                    ModificationTime = File.GetLastWriteTimeUtc(Path.Combine(root, path)) };
                if (type is TarEntryType.HardLink or TarEntryType.SymbolicLink)
                    entry.LinkName = path != alias ? alias : defect switch { "missing" => "build/ci/absent",
                        "escape" => "../escaped", "absolute" => "/escaped", "self" => alias,
                        "manifest-target" => manifestPath, _ => first };
                else if (type == TarEntryType.RegularFile)
                    entry.DataStream = new MemoryStream(path == first && defect == "target-content" ? "corrupt target"u8.ToArray()
                        : File.ReadAllBytes(Path.Combine(root, path)));
                if (path == alias && defect == "header-mode") entry.Mode ^= UnixFileMode.UserExecute;
                writer.WriteEntry(entry);
            }
        var target = Path.Combine(root, "build/empty-destination");
        Directory.CreateDirectory(target);
        if (defect == "target-content") Git(root, "clone", "--quiet", "--no-hardlinks", root, target);
        var extracted = Extract(target, crafted, "build");
        if (defect is not ("valid" or "target-content"))
        {
            Assert.True(extracted.Exit != 0, defect + ": " + extracted.Text);
            Assert.Empty(Directory.GetFileSystemEntries(target));
            return;
        }
        Assert.True(extracted.Exit == 0, extracted.Text);
        if (defect == "target-content")
        {
            Assert.Equal(commit, Git(target, "rev-parse", "HEAD"));
            Assert.Equal(2, Run("transport-verify", target, "build", commit, "17", "2"));
            Assert.Contains("artifact integrity mismatch: " + first,
                Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.ValidateBuild(target)).Message, StringComparison.Ordinal);
            return;
        }
        foreach (var material in manifest.Materials)
            Assert.Equal(File.ReadAllBytes(Path.Combine(root, material.Path)), File.ReadAllBytes(Path.Combine(target, material.Path)));
        var original = File.ReadAllBytes(Path.Combine(target, first));
        File.WriteAllText(Path.Combine(target, alias), "independent alias\n");
        Assert.Equal(original, File.ReadAllBytes(Path.Combine(target, first)));
    }

    private static (int Exit, string Text) Extract(string root, string archive, string stage) =>
        EngineeringProcess.Process(root, "python3", ["-B", "-c",
            "import pathlib,sys; sys.path.insert(0,sys.argv[1]); import ci; ci.extract(pathlib.Path(sys.argv[2]),pathlib.Path(sys.argv[3]),sys.argv[4])",
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/workflow"), root, archive, stage],
            hangGuard: TestBudgets.WorkflowProcessHangGuard);

    [Fact]
    public void CurrentSealRequiresThePublishedProvenanceCompanion()
    {
        using var fixture = new ExecutionFixture();
        Prepare(fixture, current: false);
        Report(fixture.Root);
        TemporaryFileSystem.File.Delete(Path.Combine(fixture.Root, CommonExecutionEvidence.ReportPath + ".provenance.json"));
        Assert.ThrowsAny<IOException>(() => CommonExecutionEvidence.SealCurrent(fixture.Root, CommonExecutionEvidence.ValidateBuild(fixture.Root), Steps(CommonExecutionEvidence.CurrentSteps)));
    }

    [Theory]
    [InlineData("build")]
    [InlineData("engineering")]
    [InlineData("current")]
    public void CompleteNulListedBundleMovesAcrossRootsAndPreservesExecutableModes(string stage)
    {
        using var fixture = new ExecutionFixture();
        Prepare(fixture, stage == "current");
        var commit = Git(fixture.Root, "rev-parse", "HEAD");
        var archive = Path.Combine(fixture.Root, "build", "transfer.tgz");
        Assert.Equal(0, Run("transport-pack", fixture.Root, stage, commit, "17", "2", archive));
        var target = Path.Combine(fixture.Root, "build", "destination");
        Git(fixture.Root, "clone", "--quiet", "--no-hardlinks", fixture.Root, target);
        if (stage == "engineering")
        {
            var buildArchive = Path.Combine(fixture.Root, "build", "build.tgz");
            Assert.Equal(0, Run("transport-pack", fixture.Root, "build", commit, "17", "2", buildArchive));
            using var shared = new GZipStream(File.OpenRead(buildArchive), CompressionMode.Decompress);
            TarFile.ExtractToDirectory(shared, target, overwriteFiles: true);
        }
        using (var input = new GZipStream(File.OpenRead(archive), CompressionMode.Decompress))
            TarFile.ExtractToDirectory(input, target, overwriteFiles: true);
        Assert.Equal(0, Run("transport-verify", target, stage, commit, "17", "2"));
        Assert.Equal(stage == "engineering", TemporaryFileSystem.File.Exists(Path.Combine(target, CommonExecutionEvidence.EngineeringPath)));
        Assert.Equal(stage == "engineering", TemporaryFileSystem.File.Exists(Path.Combine(target, CommonExecutionEvidence.TestsPath)));
        Assert.Equal(stage == "current", TemporaryFileSystem.File.Exists(Path.Combine(target, CommonExecutionEvidence.CurrentPath)));
        if (!OperatingSystem.IsWindows())
            Assert.NotEqual(0, (int)(File.GetUnixFileMode(Path.Combine(target, Log)) & UnixFileMode.UserExecute));
        if (stage == "current")
            foreach (var suffix in new[] { "", ".sha256", ".input.attestation", ".provenance.json", ".materials.zip" })
                Assert.Equal(TemporaryFileSystem.File.ReadAllBytes(Path.Combine(fixture.Root, CommonExecutionEvidence.ReportPath + suffix)),
                    TemporaryFileSystem.File.ReadAllBytes(Path.Combine(target, CommonExecutionEvidence.ReportPath + suffix)));
        Assert.Equal(2, Run("transport-verify", target, stage, commit, "18", "2"));
        Assert.Equal(2, Run("transport-verify", target, stage, commit, "17", "3"));
        Assert.Equal(2, Run("transport-verify", target, stage, new string('a', 40), "17", "2"));
        TemporaryFileSystem.File.AppendAllText(Path.Combine(target, Log), "corrupt");
        Assert.Equal(2, Run("transport-verify", target, stage, commit, "17", "2"));
    }

    [Theory]
    [InlineData("candidate")]
    [InlineData("failed-evidence")]
    [InlineData("missing-report")]
    [InlineData("missing-provenance")]
    public void RequiredTransportCannotSealStaleOrIncompleteProduction(string defect)
    {
        using var fixture = new ExecutionFixture();
        Prepare(fixture, current: true);
        switch (defect)
        {
            case "candidate": TemporaryFileSystem.File.AppendAllText(Path.Combine(fixture.Root, ExecutionFixture.First), "\n"); break;
            case "failed-evidence":
                var record = CommonExecutionEvidence.Read<CommonStageRecord>(fixture.Root, CommonExecutionEvidence.CurrentPath);
                CommonExecutionEvidence.Write(fixture.Root, CommonExecutionEvidence.CurrentPath,
                    record with { Steps = record.Steps.Select(step => step with { Exit = 1 }).ToArray() });
                break;
            case "missing-report": TemporaryFileSystem.File.Delete(Path.Combine(fixture.Root, CommonExecutionEvidence.ReportPath)); break;
            case "missing-provenance": TemporaryFileSystem.File.Delete(Path.Combine(fixture.Root, CommonExecutionEvidence.ReportPath + ".provenance.json")); break;
        }
        Assert.Equal(2, Run("transport-pack", fixture.Root, "current", Git(fixture.Root, "rev-parse", "HEAD"), "17", "2", Path.Combine(fixture.Root, "build", "bad.tgz")));
    }


}
