using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.ArchitectureTests;

public sealed partial class FileMapPolicyTests
{
    [Fact]
    public void EmptyDebtPartitionsRemainRegisteredWithTheirActivationAuthority()
    {
        var manifest = DebtManifest("Golden/InformationTemplateDebt/rows/*.json");
        Assert.True(FileMapPolicy.InspectPatternPopulation(manifest,
            [InformationTemplateDebtStore.ActivationPath]).Count == 0,
            "[FAIL] declared_debt_empty_partition_reserved");
    }

    [Theory]
    [InlineData("Golden/InformationTemplateDebt/*00.json", "InformationTemplateDebtWriter", true)]
    [InlineData("Golden/InformationTemplateDebt/*g.json", "InformationTemplateDebtWriter", true)]
    [InlineData("Golden/OtherDebt/*0.json", "InformationTemplateDebtWriter", true)]
    [InlineData("Golden/InformationTemplateDebt/rows/*.json", "OtherWriter", true)]
    [InlineData("Golden/InformationTemplateDebt/rows/*.json", "InformationTemplateDebtWriter", false)]
    public void EmptyDebtReservationRequiresExactPartitionAndAuthority(string pattern, string producer, bool authority)
    {
        var manifest = DebtManifest(pattern, producer);
        var findings = FileMapPolicy.InspectPatternPopulation(manifest,
            authority ? [InformationTemplateDebtStore.ActivationPath] : []);
        Assert.True(findings.Any(f => f.Path == pattern && f.Code == "FILEMAP-PATTERN-EMPTY"),
            "[FAIL] declared_debt_reservation_boundary");
    }

    [Theory]
    [InlineData("InformationTemplateDebtStore", "tools/StrataLint.Engine/RepositoryIo/InformationTemplateDebtStore.cs")]
    [InlineData("DeclaredTemplateBindingRule", "tools/StrataLint.Engine/Rules/TheoryGeneration/DeclaredTemplateBindingRule.cs")]
    public void DebtVerifiersResolveToTheirProductionImplementations(string verifier, string source)
    {
        var program = new FileMapEntry(source, FileMapKind.Program, FileMapAdmissionPlane.Judge,
            "none", ["compiler"], ["compiler"], false, "none", null, "committed-source", null, [], null);
        var debt = DebtManifest("Golden/InformationTemplateDebt/rows/*.json");
        var manifest = new FileMapManifest(debt.ResidencePolicy, debt.Entries.Add(program), debt.Resources);
        Assert.Contains(verifier, FileMapPolicy.AvailableDataVerifiers(manifest,
            new HashSet<string>(StringComparer.Ordinal) { source }));
        Assert.DoesNotContain(verifier, FileMapPolicy.AvailableDataVerifiers(manifest,
            new HashSet<string>(StringComparer.Ordinal)));
        Assert.DoesNotContain(verifier, FileMapPolicy.AvailableDataVerifiers(debt,
            new HashSet<string>(StringComparer.Ordinal) { source }));
    }

    private static FileMapManifest DebtManifest(string pattern, string producer = "InformationTemplateDebtWriter")
    {
        FileMapEntry Entry(string path, FileMapAdmissionPlane plane) => new(path, FileMapKind.Data,
            plane, producer, ["DeclaredTemplateBindingRule", "InformationTemplateDebtStore"],
            ["DeclaredTemplateBindingRule", "InformationTemplateDebtStore"], false, "none", null,
            "committed-source", null, [], null);
        return new(new("fixture", "no data in programs", 0, "closed"),
            [Entry(pattern, FileMapAdmissionPlane.Content),
             Entry(InformationTemplateDebtStore.ActivationPath, FileMapAdmissionPlane.Judge)], []);
    }

}
