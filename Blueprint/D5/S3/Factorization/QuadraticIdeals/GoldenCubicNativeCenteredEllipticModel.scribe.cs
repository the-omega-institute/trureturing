using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class GoldenCubicNativeCenteredEllipticModelDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeCenteredEllipticModel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The centered native cubic is Eisenstein and gives exact elliptic model coefficients.",
        H("The centered cubic chart for the native elliptic curve"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("wss-native-centered-eisenstein"),
                DeclarationHandle.Create(Module + "native_centered_eisenstein"),
                H("The cubic centered at the actual Lucas coordinate is Eisenstein at three"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The centered cubic is z cubed plus three L z squared minus nine z minus three L. The "
                    + "native Lucas coordinate is a unit modulo three."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-native-centered-coefficient-identities"),
                DeclarationHandle.Create(Module + "local_model_coefficients"),
                H("The actual centered root gives exact model coefficient identities"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Translation by L plus the root and scaling by its square produces the displayed four "
                    + "transformed coefficient and discriminant identities. No valuation-extension or "
                    + "arithmetic inertia theorem is asserted by this endpoint."))),
                DescribeRole.Theorem))));
}
