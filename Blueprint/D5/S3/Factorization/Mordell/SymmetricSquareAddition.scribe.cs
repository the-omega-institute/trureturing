using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Mordell;

internal sealed class SymmetricSquareAdditionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/tauceti2026canonicalheight");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Homogeneous addition and subtraction.",
        H("Homogeneous addition and subtraction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("symmetric-square-addition"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/SymmetricSquareAddition.sym2x_add_sub_eq_addSubMap_sym2x"),
                H("Homogeneous addition and subtraction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every field F, affine Weierstrass curve W, and nonsingular points P and Q, there is a nonzero scalar t such that t times sym2x(P + Q, P - Q) equals the homogeneous addition-and-subtraction map of W evaluated at sym2x(P, Q). Infinity, inverses and doubling are included in every characteristic.")),
                    Paragraph(Text("The proof treats finite distinct points, inverses, infinity and doubling. Nonsingularity excludes simultaneous vanishing of the duplication numerator and denominator; the remaining coordinate identities follow from the curve and addition equations."))),
                DescribeRole.Theorem))));
}
