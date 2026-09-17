using System.IO.Compression;
using StrataLint.Engine;
using StrataLint.EngineeringScope;
using StrataLint.TestSupport;

namespace StrataLint.Tests;

public sealed partial class CommonCurrentEvidenceValidationTests
{
    [Theory]
    [InlineData("checks")]
    [InlineData("program-projects")]
    [InlineData("materials")]
    [InlineData("material-excludes")]
    [InlineData("path-inventory")]
    [InlineData("report-inputs")]
    [InlineData("report-materials")]
    public void ManifestDeclarationsCannotMutateValidatedRegistration(string damage)
    {
        using var fixture = new EvidenceFixture();
        var path = Path.Combine(fixture.Root, CommonExecutionEvidence.CheckManifestPath);
        var manifest = System.Text.Json.Nodes.JsonNode.Parse(File.ReadAllText(path))!;
        var row = manifest["checks"]!.AsArray().Single(item => item!["id"]!.ToString() == "SL-001")!;
        row["materials"] = new System.Text.Json.Nodes.JsonArray("global.json");
        row["material_excludes"] = new System.Text.Json.Nodes.JsonArray("ignored/**");
        row["path_inventory"] = new System.Text.Json.Nodes.JsonArray("global.json");
        File.WriteAllText(path, manifest.ToJsonString());
        var validation = CommonExecutionEvidence.ValidationScope.Create(fixture.Root);
        var declarations = validation.CheckManifest();
        var original = System.Text.Json.JsonSerializer.Serialize(declarations);
        var check = declarations.Single(item => item.Id == "SL-001");
        switch (damage)
        {
            case "checks": Assert.IsAssignableFrom<IList<RegisteredCommonCheck>>(declarations)[0] = check with { Id = "damaged" }; break;
            case "program-projects": check.ProgramProjects[0] = "damaged"; break;
            case "materials": check.Materials[0] = "damaged"; break;
            case "material-excludes": check.MaterialExcludes[0] = "damaged"; break;
            case "path-inventory": check.PathInventory[0] = "damaged"; break;
            case "report-inputs": check.ReportInputs[0] = check.ReportInputs[0] with { Producer = "damaged" }; break;
            case "report-materials": check.ReportInputs[0].Materials[0] = "damaged"; break;
        }
        Assert.Equal(original, System.Text.Json.JsonSerializer.Serialize(validation.CheckManifest()));
        Assert.Equal(original, System.Text.Json.JsonSerializer.Serialize(validation.Fresh().CheckManifest()));
    }

    [Fact]
    public void NewSnapshotRejectsRegistrationChangedAfterPreviousValidation()
    {
        using var fixture = new EvidenceFixture();
        var validation = CommonExecutionEvidence.ValidationScope.Create(fixture.Root);
        var original = System.Text.Json.JsonSerializer.Serialize(validation.CheckManifest());
        File.WriteAllText(Path.Combine(fixture.Root, CommonExecutionEvidence.CheckManifestPath), "{}");
        Assert.Equal(original, System.Text.Json.JsonSerializer.Serialize(validation.CheckManifest()));
        Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.ValidationScope.Create(fixture.Root).CheckManifest());
    }

    [Fact]
    public void CheckSealRejectsSourceChangedDuringCallback()
    {
        using var fixture = new EvidenceFixture();
        var checks = BeginRunChecks(fixture);
        checks.Run("SL-001", () => PassingPredicate("SL-001"));
        checks.Run("SL-002", () =>
        {
            File.AppendAllText(Path.Combine(fixture.Root, "fixtures/Producer.csproj"), "<!-- changed -->\n");
            return PassingPredicate("SL-002");
        });
        var error = Assert.Throws<InvalidDataException>(() => checks.Seal());
        Assert.Contains("candidate identity", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CheckRunSharesSuccessfulReportButHashesEveryMaterialAfterEachCallback()
    {
        using var fixture = new EvidenceFixture();
        var checks = BeginRunChecks(fixture);
        var previousReading = RawLeanReportArtifact.Reading.Value;
        var previousHashing = CommonExecutionEvidence.Hashing.Value;
        var reads = 0;
        var hashes = new Dictionary<string, int>(StringComparer.Ordinal);
        try
        {
            RawLeanReportArtifact.Reading.Value = () => reads++;
            CommonExecutionEvidence.Hashing.Value = path => hashes[path] = hashes.GetValueOrDefault(path) + 1;
            var first = checks.Run("SL-001", () => PassingPredicate("SL-001"));
            Assert.Equal(1, reads);
            AssertReportHashes(fixture, first, hashes);
            hashes.Clear();
            var second = checks.Run("SL-002", () => PassingPredicate("SL-002"));
            AssertReportHashes(fixture, second, hashes);
            Assert.Equal(first.Report, second.Report);
            Assert.Equal(1, reads);
            Assert.Equal(2, checks.Completed.Count);
        }
        finally
        {
            RawLeanReportArtifact.Reading.Value = previousReading;
            CommonExecutionEvidence.Hashing.Value = previousHashing;
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CheckRunNewExecutionValidatesReportAgain(bool newSnapshot)
    {
        using var fixture = new EvidenceFixture();
        var snapshot = CommonExecutionEvidence.Snapshot(fixture.Root);
        var first = BeginRunChecks(fixture, snapshot);
        var second = BeginRunChecks(fixture, newSnapshot ? CommonExecutionEvidence.Snapshot(fixture.Root) : snapshot);
        var previous = RawLeanReportArtifact.Reading.Value;
        var reads = 0;
        try
        {
            RawLeanReportArtifact.Reading.Value = () => reads++;
            first.Run("SL-001", () => PassingPredicate("SL-001"));
            second.Run("SL-001", () => PassingPredicate("SL-001"));
            Assert.Equal(2, reads);
        }
        finally { RawLeanReportArtifact.Reading.Value = previous; }
    }

    [Theory]
    [InlineData("raw")]
    [InlineData("zip")]
    public void CheckRunRejectsChangedReportImmediatelyAndNeverCachesFailedValidation(string damage)
    {
        using var fixture = new EvidenceFixture();
        var checks = BeginRunChecks(fixture);
        var first = checks.Run("SL-001", () => PassingPredicate("SL-001"));
        var path = Path.Combine(fixture.Root, first.Report! + (damage == "zip" ? ".materials.zip" : ""));
        var original = File.ReadAllBytes(path);
        var previous = RawLeanReportArtifact.Reading.Value;
        var reads = 0;
        try
        {
            RawLeanReportArtifact.Reading.Value = () => reads++;
            var error = Assert.ThrowsAny<Exception>(() => checks.Run("SL-002", () =>
            {
                if (damage == "raw")
                {
                    var text = File.ReadAllText(path);
                    Assert.Contains("evidence", text, StringComparison.Ordinal);
                    File.WriteAllText(path, text.Replace("evidence", "modified", StringComparison.Ordinal));
                }
                else
                {
                    using var archive = ZipFile.Open(path, ZipArchiveMode.Update);
                    var old = Assert.Single(archive.Entries);
                    var name = old.FullName;
                    var timestamp = old.LastWriteTime;
                    old.Delete();
                    var replacement = archive.CreateEntry(name, CompressionLevel.SmallestSize);
                    replacement.LastWriteTime = timestamp;
                    using var stream = replacement.Open();
                    stream.Write("Int"u8); // Same expanded and compressed length as the original Nat.
                }
                return PassingPredicate("SL-002");
            }));
            Assert.Equal(original.Length, File.ReadAllBytes(path).Length);
            Assert.Contains(damage == "raw" ? "original common report differs" : "statement material hash mismatch",
                error.Message, StringComparison.Ordinal);
            Assert.Equal(1, reads);
            Assert.Single(checks.Completed);
            Assert.ThrowsAny<Exception>(() => checks.Run("SL-002", () => PassingPredicate("SL-002")));
            if (damage == "zip") Assert.Equal(2, reads);
            Assert.Single(checks.Completed);
            File.WriteAllBytes(path, original);
            checks.Run("SL-002", () => PassingPredicate("SL-002"));
            Assert.Equal(2, checks.Completed.Count);
        }
        finally { RawLeanReportArtifact.Reading.Value = previous; }
    }

    [Theory]
    [InlineData("")]
    [InlineData(".materials.zip")]
    public void CheckRunRejectsMissingReportInputBeforeCompletingUnit(string suffix)
    {
        using var fixture = new EvidenceFixture();
        var checks = BeginRunChecks(fixture);
        var first = checks.Run("SL-001", () => PassingPredicate("SL-001"));
        Assert.Throws<FileNotFoundException>(() => checks.Run("SL-002", () =>
        {
            File.Delete(Path.Combine(fixture.Root, first.Report! + suffix));
            File.Delete(Path.Combine(fixture.Root, CommonExecutionEvidence.ReportPath + suffix));
            return PassingPredicate("SL-002");
        }));
        Assert.Single(checks.Completed);
    }

    [Theory]
    [InlineData("")]
    [InlineData(".materials.zip")]
    [InlineData(".sha256")]
    [InlineData(".input.attestation")]
    [InlineData(".provenance.json")]
    public void CheckRunFreshValidationRejectsEveryMaterialsContradictoryDigest(string suffix)
    {
        using var fixture = new EvidenceFixture();
        var checks = BeginRunChecks(fixture);
        var first = checks.Run("SL-001", () => PassingPredicate("SL-001"));
        var path = Path.GetFullPath(Path.Combine(fixture.Root, first.Report! + suffix));
        var previous = CommonExecutionEvidence.Hashing.Value;
        var hashes = 0;
        try
        {
            CommonExecutionEvidence.Hashing.Value = current =>
            {
                // First read records this unit's material. The second must freshly
                // validate that recorded digest even after an earlier Run succeeded.
                if (current == path && ++hashes == 2) File.AppendAllText(path, "changed before validation");
            };
            var error = Assert.Throws<InvalidDataException>(() => checks.Run("SL-002", () => PassingPredicate("SL-002")));
            Assert.Contains("artifact integrity mismatch", error.Message, StringComparison.Ordinal);
            Assert.Equal(2, hashes);
            Assert.Single(checks.Completed);
        }
        finally { CommonExecutionEvidence.Hashing.Value = previous; }
    }

    private static CommonExecutionEvidence.CheckExecution BeginRunChecks(EvidenceFixture fixture, RepositorySnapshot? snapshot = null) =>
        CommonExecutionEvidence.BeginChecks(fixture.Root, "current", CommonExecutionEvidence.ValidateBuild(fixture.Root), TextWriter.Null,
            ["SL-001", "SL-002"], snapshot is null ? null : new CommonExecutionEvidence.ValidationScope(snapshot));

    private static CheckWork PassingPredicate(string id) => new([new(id, 0, CommonCheckRegistrationFixture.Predicate(id))]);

    private static void AssertReportHashes(EvidenceFixture fixture, CheckUnitResult unit, IReadOnlyDictionary<string, int> hashes)
    {
        foreach (var path in CommonExecutionEvidence.ReportPaths)
        {
            var full = Path.GetFullPath(Path.Combine(fixture.Root, unit.Report! + path[CommonExecutionEvidence.ReportPath.Length..]));
            Assert.Equal(2, hashes[full]); // Material production and a fresh validation scope.
        }
    }
}
