using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.DifferentialAlgebra;

internal sealed class FractionFieldDerivationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/DifferentialAlgebra/ax1971schanuel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An integer-linear derivation on an integral domain extends to every realization of its fraction field.",
        H("Derivations on Fraction Fields"),
        Blocks(
            Paragraph(Text("Generality G: the integral domain and its fraction field are arbitrary. Extension and compatibility are classical differential algebra.")),
            Describe.Remark(
                DescribeId.Create("fraction-field-derivation-extension"),
                DeclarationHandle.Create("D5/S1/DifferentialAlgebra/FractionFieldDerivation.extend"),
                H("The extended derivation"),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Let R be an integral domain, F a fraction field of R, and D an integer-linear derivation from R to R. "
                    + "Map r to the dual number whose two coordinates are the images of r and D(r) in F. "
                    + "Every nonzero denominator maps to a unit because its first coordinate is nonzero. "
                    + "The universal property of localization extends this ring homomorphism to F. "
                    + "Its first coordinate is the identity on F, so its second coordinate is an integer-linear derivation. "
                    + "This formalization of the classical extension construction uses Mathlib's localization and trivial square-zero extension APIs.")))),
            Describe.Lean(
                DescribeId.Create("fraction-field-derivation-agreement"),
                DeclarationHandle.Create("D5/S1/DifferentialAlgebra/FractionFieldDerivation.extend_algebraMap"),
                H("Agreement on the original domain"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every r in R, the value of the extended derivation at the image of r in F equals the image of D(r). "
                    + "Consequently, a differential equation proved in the original domain remains valid after embedding into its fraction field."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fraction-field-derivation-commutation"),
                DeclarationHandle.Create("D5/S1/DifferentialAlgebra/FractionFieldDerivation.extend_commutes"),
                H("Compatibility with further field extensions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Let L be a field over F, with compatible embeddings of R, and let d be an integer-linear derivation on L. "
                    + "If d agrees with D on the embedded original domain R, then d commutes with the extended derivation on every element of F. "
                    + "This is a bind-only compatibility helper, consumed by the kAmbientDifferential and hAmbientDifferential instances in ExponentialDifferentialField. The differentiated identity xb=a proves it after embedding into L and cancelling the image of the nonzero denominator b."))),
                DescribeRole.Theorem))));
}
