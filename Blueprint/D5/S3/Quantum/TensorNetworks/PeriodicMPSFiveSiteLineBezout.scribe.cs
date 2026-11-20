using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSFiveSiteLineBezoutDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteLineBezout";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bézout identity for the two line polynomials",
        H("Bézout identity for the two line polynomials"),
        Blocks(
            Claim("coprime_line_restrictions", "The two explicit residue-field polynomials satisfy a Bézout identity checked coefficient by coefficient."))));

    private static DocumentBlock Claim(string name, string prose) =>
        Describe.Lean(DescribeId.Create("periodicmpsfivesitelinebezout-" + name.ToLowerInvariant().Replace('₂', '2').Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H("Proof"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
