using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSFiveSiteProjectiveLineDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteProjectiveLine";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lifting the full-degree resultant",
        H("Lifting the full-degree resultant"),
        Blocks(
            Claim("integral_certificate_of_point_values", "The 76 residue evaluations determine both restrictions and give a nonzero integral Sylvester determinant."),
            Claim("charZero_certificate_of_integral", "The integral certificate gives relatively prime univariate restrictions over every characteristic-zero field."))));

    private static DocumentBlock Claim(string name, string prose) =>
        Describe.Lean(DescribeId.Create("periodicmpsfivesiteprojectiveline-" + name.ToLowerInvariant().Replace('₂', '2').Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H("Proof"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
