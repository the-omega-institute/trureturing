using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSFourSiteResidualFormulaDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualFormula";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The determinant divisor in a four-site pencil sextic",
        H("The determinant divisor in a four-site pencil sextic"),
        Blocks(
            Claim("four_mul_sextic", "A determinant expression for the sextic",
                "Four times the necklace sextic is the negative square of the triplet determinant plus the singlet times the adjugate singlet, corrected by the cube of the singlet times the triplet determinant."),
            Claim("cleared_pencil_minor", "The mixed adjugate minor",
                "The cyclic vector and Hankel moments express the relevant functionals as a bilinear pairing. The two-by-two minor yields a factor of the triplet determinant over the coefficient ring."),
            Claim("residual_conic_zero_of_sextic", "The residual conic for an invertible factor",
                "The mixed minor gives a determinant-free formula after clearing the constants from the two linear systems. When the cubic and the sextic vanish and the determinant divisor is nonzero, the residual conic vanishes."))));

    private static DocumentBlock Claim(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("periodic-four-site-residualformula-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
