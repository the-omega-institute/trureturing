using StrataLint.Engine;
using StrataLint.EngineeringScope;

namespace StrataLint.Tests;

public sealed partial class CommonCurrentEvidenceValidationTests
{
    [Fact]
    public void SeedImportValidatesSharedReportOncePerReadOnlyPhase()
    {
        using var fixture = new EvidenceFixture();
        fixture.Run("export");
        var record = CommonExecutionEvidence.Read<CommonCheckRecord>(fixture.Root, CommonExecutionEvidence.ChecksPath("current"));
        var shared = Assert.Single(record.Units.Where(unit => unit.Report is not null).Select(unit => unit.Report).Distinct());
        File.Delete(Path.Combine(fixture.Root, shared!));
        var previous = RawLeanReportArtifact.Reading.Value;
        var reads = 0;
        try
        {
            RawLeanReportArtifact.Reading.Value = () => reads++;
            AssertSeedUnits(Import(fixture), record.Units.Length);
            Assert.Equal(3, reads); // Current input, seed source, copied destination.
            AssertSeedUnits(Import(fixture), record.Units.Length);
            Assert.Equal(6, reads); // A new entry cannot inherit earlier validation.
        }
        finally { RawLeanReportArtifact.Reading.Value = previous; }
        Assert.Equal(File.ReadAllBytes(Path.Combine(fixture.Root, CommonExecutionEvidence.CheckSeedPath("current"), shared!)),
            File.ReadAllBytes(Path.Combine(fixture.Root, shared!)));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SeedImportRestoresMissingDestinationButNeverOverwritesConflict(bool corrupt)
    {
        using var fixture = new EvidenceFixture();
        fixture.Run("export");
        var record = CommonExecutionEvidence.Read<CommonCheckRecord>(fixture.Root, CommonExecutionEvidence.ChecksPath("current"));
        var reports = record.Units.Where(unit => unit.Report is not null).ToArray();
        var shared = Assert.Single(reports.Select(unit => unit.Report).Distinct());
        var destination = Path.Combine(fixture.Root, shared!);
        var original = File.ReadAllBytes(destination);
        if (corrupt) File.WriteAllText(destination, "conflicting destination");
        else File.Delete(destination);
        var output = Import(fixture);
        AssertSeedUnits(output, record.Units.Length - (corrupt ? reports.Length : 0));
        foreach (var unit in reports)
            Assert.Contains($"COMMON_CHECK_{(corrupt ? "SEED_MISS" : "REUSED")} id={unit.Id} ", output, StringComparison.Ordinal);
        if (corrupt) Assert.Equal("conflicting destination", File.ReadAllText(destination));
        else Assert.Equal(original, File.ReadAllBytes(destination));
    }

    [Fact]
    public void SeedImportChecksEachSharedMaterialsExpectedDigest()
    {
        using var fixture = new EvidenceFixture();
        fixture.Run("export");
        var seed = Path.Combine(fixture.Root, CommonExecutionEvidence.CheckSeedPath("current"));
        var record = CommonExecutionEvidence.Read<CommonCheckRecord>(seed, "checks.json");
        CommonExecutionEvidence.Write(seed, "checks.json", record with
        {
            Units = record.Units.Select(unit => unit.Id != "SL-002" ? unit : unit with
            {
                Materials = unit.Materials.Select(material => material.Path != unit.Report ? material
                    : material with { Sha256 = new string('0', 64) }).ToArray(),
            }).ToArray(),
        });
        var output = Import(fixture);
        AssertSeedUnits(output, record.Units.Length - 1);
        Assert.Contains("COMMON_CHECK_REUSED id=SL-001 ", output, StringComparison.Ordinal);
        Assert.Contains("COMMON_CHECK_SEED_MISS id=SL-002 ", output, StringComparison.Ordinal);
        Assert.Contains("artifact integrity mismatch", output, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SeedImportFinishesValidationBeforeNotificationAndNextImportRejectsDamage(bool damageSeed)
    {
        using var fixture = new EvidenceFixture();
        fixture.Run("export");
        var record = CommonExecutionEvidence.Read<CommonCheckRecord>(fixture.Root, CommonExecutionEvidence.ChecksPath("current"));
        var reports = record.Units.Where(unit => unit.Report is not null).ToArray();
        var shared = Assert.Single(reports.Select(unit => unit.Report).Distinct());
        var materialRoot = damageSeed ? Path.Combine(fixture.Root, CommonExecutionEvidence.CheckSeedPath("current")) : fixture.Root;
        using var observer = new ImportObserver(() => File.AppendAllText(Path.Combine(materialRoot, shared!), "damage"));
        AssertSeedUnits(Import(fixture, observer), record.Units.Length);
        Assert.True(observer.Observed);
        var next = Import(fixture);
        AssertSeedUnits(next, record.Units.Length - reports.Length);
        foreach (var unit in reports)
            Assert.Contains($"COMMON_CHECK_SEED_MISS id={unit.Id} ", next, StringComparison.Ordinal);
    }

    private static string Import(EvidenceFixture fixture, StringWriter? observer = null)
    {
        using var ordinary = new StringWriter();
        var output = observer ?? ordinary;
        Assert.Equal(0, CommonExecutionEvidence.CheckSeedCommand(
            ["check-seed-import", "--repository", fixture.Root, "--stage", "current"], output));
        return output.ToString();
    }

    private static void AssertSeedUnits(string output, int expected) =>
        Assert.Contains($"COMMON_CHECK_SEED_IMPORTED stage=current units={expected}\n", output.Replace("\r\n", "\n", StringComparison.Ordinal), StringComparison.Ordinal);

    private sealed class ImportObserver(Action observed) : StringWriter
    {
        internal bool Observed { get; private set; }
        public override void Write(string? value) { base.Write(value); Observe(value); }
        public override void WriteLine(string? value) { base.WriteLine(value); Observe(value); }
        private void Observe(string? value)
        {
            if (Observed || value?.Contains("COMMON_CHECK_REUSED", StringComparison.Ordinal) != true) return;
            Observed = true;
            observed();
        }
    }
}
