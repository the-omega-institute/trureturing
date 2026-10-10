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
        + "\"imports\": [], \"information_registration_errors\": [], \"module\": \"Trureturing\", "
        + "\"source_path\": \"Trureturing.lean\", \"source_sha256\": "
        + "\"sha256:da33f5efbd5a92bd6c18a7a11a36dfbcd0ac00fbe05c267a85dec98370deadd4\"}], "
        + "\"schema\": \"stratalint-raw-lean-report-v3\"}\n";

    [Fact]
    public void PreviousReportFormatIsRejected()
    {
        // The strict reader accepts only the current extraction format.
        var previous = CanonicalReport.Replace("stratalint-raw-lean-report-v3",
            "stratalint-raw-lean-report-v2", StringComparison.Ordinal);
        Assert.Throws<FormatException>(() =>
            RawLeanReportArtifact.Read(Encoding.UTF8.GetBytes(previous), Snapshot()));
    }

    [Fact]
    public void ScopedSchemaIsReadOnlyThroughTheScopedConsumer()
    {
        var snapshot = Snapshot();
        var scope = LeanReportScope.Create(snapshot, [RepoPath.CreateKnown("Trureturing.lean")]);
        var scoped = CanonicalReport.Replace(
            "stratalint-raw-lean-report-v3",
            "stratalint-scoped-lean-report-v1",
            StringComparison.Ordinal).Replace("\"imports\": []", "\"imports\": [\"Init\"]", StringComparison.Ordinal);

        var report = RawLeanReportArtifact.ReadForScope(
            Encoding.UTF8.GetBytes(scoped), scope);

        Assert.True(report.IsScoped);
        Assert.Throws<FormatException>(() =>
            RawLeanReportArtifact.Read(Encoding.UTF8.GetBytes(scoped), snapshot));
    }

    [Theory]
    [InlineData("missing")]
    [InlineData("stale")]
    [InlineData("material")]
    [InlineData("statement")]
    [InlineData("imports")]
    public void ScopedReportRejectsInvalidMembersSourcesMaterialsAndImports(string defect)
    {
        using var temporary = new TemporaryDirectory();
        var path = Path.Combine(temporary.Path, "scoped.json");
        WriteMaterialFixture(path, "statement-v1(test)");
        var bytes = File.ReadAllText(path).Replace(RawLeanReportArtifact.Schema,
            RawLeanReportArtifact.ScopedSchema, StringComparison.Ordinal)
            .Replace("\"imports\": []", "\"imports\": [\"Init\"]", StringComparison.Ordinal);
        var snapshot = Snapshot();
        switch (defect)
        {
            case "missing":
                bytes = "{\"modules\": [], \"schema\": \"stratalint-scoped-lean-report-v1\"}\n";
                break;
            case "stale":
                snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
                    RawRepositorySnapshot.Create([RawRepositoryEntry.FromText("Trureturing.lean", Source + "-- changed\n")]))).Snapshot;
                break;
            case "material":
                File.WriteAllBytes(RawLeanReportArtifact.MaterialsPath(path), [0xff]);
                break;
            case "statement":
                bytes = bytes.Replace("sha256:452d97f1469d85ac204ab83dbbb919e19289c28674b14ab9df96586c535b1763",
                    "sha256:" + new string('0', 64), StringComparison.Ordinal);
                break;
            case "imports":
                bytes = bytes.Replace("\"imports\": [\"Init\"]", "\"imports\": [\"Init\", \"Mathlib\"]", StringComparison.Ordinal);
                break;
        }
        File.WriteAllText(path, bytes);
        var scope = LeanReportScope.Create(snapshot, [RepoPath.CreateKnown("Trureturing.lean")]);

        Assert.ThrowsAny<Exception>(() => RawLeanReportArtifact.ReadFileForScope(path, scope, validateMaterials: true));
    }

    [Fact]
    public void ScopedReportRequiresIndependentNonemptyResolvableTargets()
    {
        Assert.Throws<ArgumentException>(() => LeanReportScope.Create(Snapshot(), []));
        Assert.Throws<InvalidOperationException>(() => LeanReportScope.Create(Snapshot(), [RepoPath.CreateKnown("D5/Missing.lean")]));
    }

    [Fact]
    public void ScopeIncludesRefutationClaimInputsAndTheirImports()
    {
        var fixture = UtilityAdmissionTestSupport.InstanceFixture(
            "kind=certified-instance; basis=refutes=gid:D5/S0/Carrier/Claim.claim; "
            + "result=D5/S0/Carrier/Ring.refuted_law; claim=D5/S0/Carrier/Claim.claim");
        fixture.Files["D5/S0/Carrier/Claim.lean"] = "import D5.S0.Carrier.ClaimSupport\ndef claim : Prop := False\n";
        fixture.Files["D5/S0/Carrier/ClaimSupport.lean"] = "def support : Nat := 0\n";
        fixture.Files["D5/S0/Carrier/Sibling.lean"] = "def sibling : Nat := 0\n";
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            UtilityAdmissionTestSupport.Raw(fixture.Files))).Snapshot;

        var scope = LeanReportScope.Create(snapshot, [RepoPath.CreateKnown(RuleFixture.RingPath)]);

        Assert.Contains(RepoPath.CreateKnown("D5/S0/Carrier/Claim.lean"), scope.Paths);
        Assert.Contains(RepoPath.CreateKnown("D5/S0/Carrier/ClaimSupport.lean"), scope.Paths);
        Assert.DoesNotContain(RepoPath.CreateKnown("D5/S0/Carrier/Sibling.lean"), scope.Paths);
    }

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
        File.WriteAllText(Path.Combine(repository.Path, "lakefile.toml"),
            "name = \"producer_probe\"\nversion = \"0.1.0\"\ndefaultTargets = [\"Trureturing\"]\n\n[[lean_lib]]\nname = \"Trureturing\"\n",
            new UTF8Encoding(false));
        File.Copy(Path.Combine(TestRepositoryLayout.FindRoot(), "lean-toolchain"),
            Path.Combine(repository.Path, "lean-toolchain"));
        var raw = RawRepositorySnapshot.Create(new[]
        {
            RawRepositoryEntry.FromText("Trureturing.lean", unicodeSource),
        });
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
        var report = new StandaloneLeanInspectorTests.TestLeanReportProducer(repository.Path).Inspect(snapshot);
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
