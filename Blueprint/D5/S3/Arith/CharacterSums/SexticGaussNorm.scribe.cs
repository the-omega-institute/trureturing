using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class SexticGaussNormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Primitive order-six Gauss sums have the finite-field norm required for normalized phase questions.",
        H("Sextic Gauss Sum Norm"),
        Blocks(
            Paragraph(Text(
                "For a finite field F, an order-six multiplicative character chi, and a primitive "
                    + "complex additive character psi, the squared complex modulus of the Gauss sum "
                    + "is the cardinality of F. Consequently the square divided by that cardinality "
                    + "lies on the unit circle. These are pointwise algebraic constraints; the "
                    + "family-level equidistribution conjecture remains open.")),
            Describe.Lean(
                DescribeId.Create("sextic-gauss-normsq"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/SexticGaussNorm.sextic_gauss_normSq"),
                H("Finite-field norm of a sextic Gauss sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The proof combines Mathlib's primitive Gauss product with conjugation of "
                        + "both characters, then identifies the resulting complex product with "
                        + "Complex.normSq."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sextic-gauss-square-unit-circle"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/SexticGaussNorm.sextic_gauss_square_div_card_normSq"),
                H("Normalized square lies on the unit circle"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The pointwise norm identity is transported through Complex.normSq of a "
                        + "square and a quotient, producing the exact unit-circle constraint "
                        + "used by later phase-moment and Weyl-criterion work."))),
                DescribeRole.Theorem))));
}
