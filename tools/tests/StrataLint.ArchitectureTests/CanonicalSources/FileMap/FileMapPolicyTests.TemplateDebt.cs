using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.ArchitectureTests;

public sealed partial class FileMapPolicyTests
{
    [Fact]
    public void EmptyDebtPartitionsRemainRegisteredWithTheirActivationAuthority()
    {
        foreach (var suffix in "0123456789abcdef")
        {
            var manifest = DebtManifest("Golden/InformationTemplateDebt/*" + suffix + ".json");
            Assert.True(FileMapPolicy.InspectPatternPopulation(manifest,
                [InformationTemplateDebtStore.ActivationPath]).Count == 0,
                "[FAIL] declared_debt_empty_partition_reserved");
        }
    }

    [Theory]
    [InlineData("Golden/InformationTemplateDebt/*00.json", "InformationTemplateDebtWriter", true)]
    [InlineData("Golden/InformationTemplateDebt/*g.json", "InformationTemplateDebtWriter", true)]
    [InlineData("Golden/OtherDebt/*0.json", "InformationTemplateDebtWriter", true)]
    [InlineData("Golden/InformationTemplateDebt/*0.json", "OtherWriter", true)]
    [InlineData("Golden/InformationTemplateDebt/*0.json", "InformationTemplateDebtWriter", false)]
    public void EmptyDebtReservationRequiresExactPartitionAndAuthority(string pattern, string producer, bool authority)
    {
        var manifest = DebtManifest(pattern, producer);
        var findings = FileMapPolicy.InspectPatternPopulation(manifest,
            authority ? [InformationTemplateDebtStore.ActivationPath] : []);
        Assert.True(findings.Any(f => f.Path == pattern && f.Code == "FILEMAP-PATTERN-EMPTY"),
            "[FAIL] declared_debt_reservation_boundary");
    }

    [Fact]
    public void DebtVerifiersResolveToTheirProductionImplementations()
    {
        var findings = FileMapPolicy.InspectRepository(RepositoryLayout.FindRoot());
        Assert.True(!findings.Any(f => f.Path.StartsWith("Golden/InformationTemplateDebt/", StringComparison.Ordinal)
            && f.Code.StartsWith("FILEMAP-DATA-VERIFIER", StringComparison.Ordinal)),
            "[FAIL] declared_debt_verifiers_registered");
    }

    private static FileMapManifest DebtManifest(string pattern, string producer = "InformationTemplateDebtWriter")
    {
        FileMapEntry Entry(string path, FileMapAdmissionPlane plane) => new(path, FileMapKind.Data,
            plane, producer, ["DeclaredTemplateBindingRule", "InformationTemplateDebtStore"],
            ["DeclaredTemplateBindingRule", "InformationTemplateDebtStore"], false, "none", null,
            "committed-source", null, null);
        return new(new("fixture", "no data in programs", 0, "closed"),
            [Entry(pattern, FileMapAdmissionPlane.Content),
             Entry(InformationTemplateDebtStore.ActivationPath, FileMapAdmissionPlane.Judge)]);
    }

}
