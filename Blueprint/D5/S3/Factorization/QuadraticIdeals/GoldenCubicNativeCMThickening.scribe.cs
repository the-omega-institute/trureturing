using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class GoldenCubicNativeCMThickeningDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeCMThickening.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact integral CM model contact sees the earlier block valuation without doubling.",
        H("The exact native CM model-thickening test"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("wss-native-cm-model-thickening"),
                DeclarationHandle.Create(Module + "native_cm_model_thickening"),
                H("Admissible CM model equivalence has the exact earlier block depth"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Over the quotient by a prime power, an admissible Weierstrass change takes a later "
                    + "native model to the constant CM model precisely when the power is no greater than the "
                    + "original block valuation. The first three short coefficients force the shift terms to "
                    + "vanish and the sixth coefficient has exactly the original depth. Unlike the coarse "
                    + "j-invariant test, this contact does not double the valuation."))),
                DescribeRole.Theorem))));
}
