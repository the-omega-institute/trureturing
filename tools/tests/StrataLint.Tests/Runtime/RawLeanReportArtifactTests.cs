using System.Text;
using System.Security.Cryptography;
using System.IO.Compression;
using System.Collections.Concurrent;
using System.Runtime.CompilerServices;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class RawLeanReportArtifactTests
{
    private const string Source = "axiom probe : False\n";

    private const string CanonicalReport =
        "{\"modules\": [{\"declarations\": [{\"axioms\": [], \"include_in_statement\": true, "
        + "\"kind\": \"axiom\", \"name\": \"probe\", \"name_key\": \"ns(n0,5:probe)\", "
        + "\"statement_id\": \"sha256:452d97f1469d85ac204ab83dbbb919e19289c28674b14ab9df96586c535b1763\", "
        + "\"type_sha256\": \"sha256:5f53330fdefb1897242ca642a5528fb5eefbf7ae094afd313bb56570e981095a\"}], "
        + "\"imports\": [], \"module\": \"Trureturing\", "
        + "\"source_path\": \"Trureturing.lean\", \"source_sha256\": "
        + "\"sha256:da33f5efbd5a92bd6c18a7a11a36dfbcd0ac00fbe05c267a85dec98370deadd4\"}], "
        + "\"schema\": \"stratalint-raw-lean-report-v2\"}\n";

    [Fact]
    public void CanonicalReportFeedsLeanFileReportAndTheExistingStatementWriter()
    {
        var snapshot = Snapshot();

        var report = RawLeanReportArtifact.Read(
            Encoding.UTF8.GetBytes(CanonicalReport),
            snapshot);

        Assert.True(RepoPath.TryCreate("Trureturing.lean", out var path));
        var file = Assert.Single(report.Files).Value;
        var declaration = Assert.Single(file.Declarations);
        Assert.Equal("probe", declaration.Name);
        Assert.Equal(
            "sha256:5f53330fdefb1897242ca642a5528fb5eefbf7ae094afd313bb56570e981095a",
            declaration.StatementTypeAddress);
        var statement = Assert.Single(CanonicalStatementWriter.DeclarationStatementIds(path, file));
        Assert.Equal(
            "sha256:452d97f1469d85ac204ab83dbbb919e19289c28674b14ab9df96586c535b1763",
            statement.StatementId.Value);
        Assert.Contains(
            "material source",
            Assert.Throws<InvalidDataException>(() => _ = declaration.LoadTypeRepresentation()).Message,
            StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void WriterIsByteStableAndUsesTheStructuredCanonicalJsonShape()
    {
        var snapshot = Snapshot();
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>
        {
            ["Trureturing.lean"] = new(
                [],
                [new LeanDeclaration("probe", "axiom", "statement-v1(test)", [])
                {
                    NameKey = "ns(n0,5:probe)",
                }]),
        });

        var first = RawLeanReportArtifact.Write(snapshot, report);
        var second = RawLeanReportArtifact.Write(snapshot, report);

        var actual = Encoding.UTF8.GetString(first.AsSpan());
        Assert.True(
            string.Equals(CanonicalReport, actual, StringComparison.Ordinal),
            $"expected:\n{CanonicalReport}\nactual:\n{actual}");
        Assert.True(first.AsSpan().SequenceEqual(second.AsSpan()));
        Assert.Matches("^sha256:[0-9a-f]{64}$", RawLeanReportArtifact.ContentAddress(first.AsSpan()));

        using var temporary = new TemporaryDirectory();
        var path = Path.Combine(temporary.Path, "raw-lean-report.json");
        RawLeanReportArtifact.WriteFile(path, snapshot, report);
        var fromDisk = RawLeanReportArtifact.ReadFile(path, snapshot);
        Assert.Equal(
            "statement-v1(test)",
            fromDisk.Files.Single().Value.Declarations.Single().LoadTypeRepresentation());

        var materialArchive = RawLeanReportArtifact.MaterialsPath(path);
        using (var archive = ZipFile.Open(materialArchive, ZipArchiveMode.Update))
        {
            var entry = Assert.Single(archive.Entries);
            var name = entry.FullName;
            entry.Delete();
            var replacement = archive.CreateEntry(name, CompressionLevel.SmallestSize);
            using var writer = new StreamWriter(
                replacement.Open(), new UTF8Encoding(false), leaveOpen: false);
            writer.Write("statement-v1(tampered)");
        }
        var tampered = RawLeanReportArtifact.ReadFile(path, snapshot);
        Assert.Contains(
            "hash",
            Assert.Throws<InvalidDataException>(() =>
                _ = tampered.Files.Single().Value.Declarations.Single().LoadTypeRepresentation()).Message,
            StringComparison.OrdinalIgnoreCase);
        using (var archive = ZipFile.Open(materialArchive, ZipArchiveMode.Update))
        {
            Assert.Single(archive.Entries).Delete();
        }
        var missingReport = RawLeanReportArtifact.ReadFile(path, snapshot);
        var missingMaterial = missingReport.Files.Single().Value.Declarations.Single();
        Assert.Contains(
            "missing",
            Assert.Throws<InvalidDataException>(() => missingMaterial.LoadTypeRepresentation()).Message,
            StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void MaterialBundleIsOneArchiveAndItsAbsenceFailsOnFirstMaterialUse()
    {
        using var temporary = new TemporaryDirectory();
        var path = Path.Combine(temporary.Path, "raw-lean-report.json");
        var snapshot = Snapshot();
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>
        {
            ["Trureturing.lean"] = new(
                [],
                [new LeanDeclaration("probe", "axiom", "statement-v1(test)", [])
                {
                    NameKey = "ns(n0,5:probe)",
                }]),
        });

        RawLeanReportArtifact.WriteFile(path, snapshot, report);

        var archive = RawLeanReportArtifact.MaterialsPath(path);
        Assert.True(File.Exists(archive), $"material archive is absent: {archive}");
        Assert.False(Directory.Exists(archive), $"material bundle is still a directory: {archive}");
        File.Delete(archive);
        var reportFromMissingArchive = RawLeanReportArtifact.ReadFile(path, snapshot);
        var declaration = reportFromMissingArchive.Files.Single().Value.Declarations.Single();
        var exception = Assert.Throws<InvalidDataException>(() => declaration.LoadTypeRepresentation());
        Assert.Contains("material archive", exception.Message, StringComparison.OrdinalIgnoreCase);
        Assert.Contains("missing", exception.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void FullMaterialValidationDoesNotPopulateTheDemandReadCache()
    {
        using var temporary = new TemporaryDirectory();
        var path = Path.Combine(temporary.Path, "raw-lean-report.json");
        var address = WriteMaterialFixture(path, "statement-v1(test)");
        var read = RawLeanReportArtifact.OpenStatementMaterialSource(path, [address, address]);

        // Inspect reachable material directly: GC timing and machine speed must
        // not decide whether full validation retains every expanded string.
        var archive = read.Target!;
        ValidateAllMaterials(archive);
        var cache = MaterialCache(archive);
        Assert.Empty(cache);

        var value = read(address);
        Assert.Equal("statement-v1(test)", value);
        Assert.Same(value, read(address));
        Assert.Single(cache);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MaterialValidationPreservesUnicodeAndLazyReads(bool validateMaterials)
    {
        const string material = "statement-v1(∀ α, Ω𝒪😀)";
        using var temporary = new TemporaryDirectory();
        var path = Path.Combine(temporary.Path, "raw-lean-report.json");
        WriteMaterialFixture(path, material);

        var report = RawLeanReportArtifact.ReadFile(path, Snapshot(), validateMaterials);
        var declaration = Assert.Single(Assert.Single(report.Files).Value.Declarations);
        Assert.Equal(material, declaration.LoadTypeRepresentation());
        Assert.Same(declaration.LoadTypeRepresentation(), declaration.LoadTypeRepresentation());
    }

    [Theory]
    [InlineData("hash", "hash mismatch")]
    [InlineData("utf8", "strict UTF-8")]
    [InlineData("missing", "missing")]
    [InlineData("extra", "unreferenced")]
    [InlineData("duplicate", "duplicate")]
    [InlineData("address", "malformed")]
    [InlineData("truncated", "invalid")]
    public void FullMaterialValidationRejectsCorruptionBeforeAnyDemandRead(string corruption, string diagnostic)
    {
        using var temporary = new TemporaryDirectory();
        var path = Path.Combine(temporary.Path, "raw-lean-report.json");
        WriteMaterialFixture(path, "statement-v1(test)");
        var materials = RawLeanReportArtifact.MaterialsPath(path);
        if (corruption == "truncated")
        {
            var bytes = TemporaryFileSystem.File.ReadAllBytes(materials);
            File.WriteAllBytes(materials, bytes[..^8]);
        }
        else
        {
            using var archive = ZipFile.Open(materials, ZipArchiveMode.Update);
            var entry = Assert.Single(archive.Entries);
            var name = entry.FullName;
            if (corruption is "hash" or "utf8" or "missing" or "address") entry.Delete();
            if (corruption != "missing")
            {
                var replacement = archive.CreateEntry(corruption switch
                {
                    "extra" => "sha256/" + new string('0', 64),
                    "address" => "sha256/not-an-address",
                    _ => name,
                });
                using var stream = replacement.Open();
                stream.Write(corruption == "utf8" ? [0xff] : Encoding.UTF8.GetBytes("statement-v1(changed)"));
            }
        }

        var exception = Assert.Throws<InvalidDataException>(() =>
            RawLeanReportArtifact.ReadFile(path, Snapshot(), validateMaterials: true));
        Assert.Contains(diagnostic, exception.ToString(), StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void ReaderRejectsSemanticallyValidButNoncanonicalJsonBytes()
    {
        var noncanonical = CanonicalReport.Replace(": ", ":", StringComparison.Ordinal);

        var exception = Assert.Throws<FormatException>(() =>
            RawLeanReportArtifact.Read(Encoding.UTF8.GetBytes(noncanonical), Snapshot()));

        Assert.Contains("canonical", exception.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void ReaderRejectsAReportWhoseSourceHashDoesNotMatchTheSnapshot()
    {
        var raw = RawRepositorySnapshot.Create(new[]
        {
            RawRepositoryEntry.FromText("Trureturing.lean", "axiom changed : False\n"),
        });
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;

        var exception = Assert.Throws<FormatException>(() =>
            RawLeanReportArtifact.Read(Encoding.UTF8.GetBytes(CanonicalReport), snapshot));

        Assert.Contains("source hash", exception.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void ReaderRejectsAPoisonedCachedModuleWhoseKeyWasIncorrectlyReused()
    {
        var poisoned = CanonicalReport.Replace(
            "da33f5efbd5a92bd6c18a7a11a36dfbcd0ac00fbe05c267a85dec98370deadd4",
            "0a33f5efbd5a92bd6c18a7a11a36dfbcd0ac00fbe05c267a85dec98370deadd4",
            StringComparison.Ordinal);

        var exception = Assert.Throws<FormatException>(() =>
            RawLeanReportArtifact.Read(Encoding.UTF8.GetBytes(poisoned), Snapshot()));

        Assert.Contains("source hash", exception.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void ReaderRejectsACachedReportMissingAManagedModule()
    {
        var raw = RawRepositorySnapshot.Create(new[]
        {
            RawRepositoryEntry.FromText("Trureturing.lean", Source),
            RawRepositoryEntry.FromText("D5/Extra.lean", "def extra : Nat := 1\n"),
        });
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;

        var exception = Assert.Throws<FormatException>(() =>
            RawLeanReportArtifact.Read(Encoding.UTF8.GetBytes(CanonicalReport), snapshot));

        Assert.Contains("module", exception.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void StandaloneLeanInspectorWritesAConsumerAcceptedArtifact()
    {
        const string unicodeSource = "def term𝒪φ : Nat := 1\n";
        using var repository = new TemporaryDirectory();
        File.WriteAllText(
            Path.Combine(repository.Path, "lakefile.toml"),
            "name = \"producer_probe\"\nversion = \"0.1.0\"\ndefaultTargets = [\"Trureturing\"]\n\n[[lean_lib]]\nname = \"Trureturing\"\n",
            new UTF8Encoding(false));
        File.WriteAllText(
            Path.Combine(repository.Path, "lean-toolchain"),
            "leanprover/lean4:v4.31.0\n",
            new UTF8Encoding(false));
        File.WriteAllText(
            Path.Combine(repository.Path, "Trureturing.lean"),
            unicodeSource,
            new UTF8Encoding(false));
        var build = TestProcessRunner.Run(
            "lake",
            ["build"],
            repository.Path,
            TestBudgets.LeanProcessHangGuard,
            8 * 1024 * 1024);
        Assert.True(
            build.ExitCode == 0,
            Encoding.UTF8.GetString(build.StandardOutput) + Encoding.UTF8.GetString(build.StandardError));
        var output = Path.Combine(repository.Path, "raw-lean-report.json");
        var spoolReport = output + ".spool.json";
        var spoolMaterials = output + ".spool-materials";
        var inspector = Path.Combine(
            TestRepositoryLayout.FindRoot(),
            "tools", "lean-inspector",
            "Inspector.lean");
        var sourceHash = "sha256:" + Convert.ToHexStringLower(
            SHA256.HashData(Encoding.UTF8.GetBytes(unicodeSource)));

        var inspected = TestProcessRunner.Run(
            "lake",
            [
                "env", "lean", "--run", inspector,
                "--output", spoolReport,
                "--material-spool", spoolMaterials,
                "Trureturing", "Trureturing.lean", sourceHash,
            ],
            repository.Path,
            TestBudgets.LeanProcessHangGuard,
            8 * 1024 * 1024);

        Assert.True(
            inspected.ExitCode == 0,
            Encoding.UTF8.GetString(inspected.StandardOutput)
                + Encoding.UTF8.GetString(inspected.StandardError));
        var compacted = TestProcessRunner.Run(
            "python3",
            [
                Path.Combine(TestRepositoryLayout.FindRoot(), "tools", "lean-inspector", "materials.py"),
                "compact", spoolReport, spoolMaterials, output,
            ],
            repository.Path,
            TestBudgets.LeanProcessHangGuard,
            8 * 1024 * 1024);
        Assert.True(
            compacted.ExitCode == 0,
            Encoding.UTF8.GetString(compacted.StandardOutput)
                + Encoding.UTF8.GetString(compacted.StandardError));
        var raw = RawRepositorySnapshot.Create(new[]
        {
            RawRepositoryEntry.FromText("Trureturing.lean", unicodeSource),
        });
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
        var report = RawLeanReportArtifact.ReadFile(output, snapshot);
        Assert.Contains(
            report.Files.Single().Value.Declarations,
            declaration => declaration.Name == "term𝒪φ");
    }

    // Fixed CLR member access keeps the observed object and operations explicit;
    // it neither discovers members nor dispatches through a reflection wrapper.
    private const string MaterialArchiveType =
        "StrataLint.Engine.RawLeanReportArtifact+StatementMaterialArchive, StrataLint.Engine";

    [UnsafeAccessor(UnsafeAccessorKind.Method, Name = "ValidateAll")]
    private static extern void ValidateAllMaterials([UnsafeAccessorType(MaterialArchiveType)] object archive);

    [UnsafeAccessor(UnsafeAccessorKind.Field, Name = "material")]
    private static extern ref ConcurrentDictionary<string, Lazy<string>> MaterialCache(
        [UnsafeAccessorType(MaterialArchiveType)] object archive);

    private static string WriteMaterialFixture(string path, string material)
    {
        var declaration = new LeanDeclaration("probe", "axiom", material, [])
        {
            NameKey = "ns(n0,5:probe)",
        };
        RawLeanReportArtifact.WriteFile(path, Snapshot(), LeanAxiomReport.Create(
            new Dictionary<string, LeanFileReport> { ["Trureturing.lean"] = new([], [declaration]) }));
        return declaration.StatementTypeAddress;
    }

    private static RepositorySnapshot Snapshot()
    {
        var raw = RawRepositorySnapshot.Create(new[]
        {
            RawRepositoryEntry.FromText("Trureturing.lean", Source),
        });
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
    }

}
