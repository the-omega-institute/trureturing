using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Exchange;

internal sealed class OneSquareDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One Square", H("One Square"),
        Blocks(
            Paragraph(Text("Up-then-down and down-then-up theta lifts agree on partner data up to L-values.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Exchange/OneSquare.one_square"),
                H("one_square"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("One square. Let rk A = rk A′ + 2e, q = q(U₁) + q(U₂) = q(A) + q(A′) negative signs, 2q + 2 ≤ n = rk U₁ + rk U₂ ≤ 2μ + 2q, ν tame of weight μ, and the four products of characters equal ν⁻¹υ^⌊n/2⌋ (rankTwist). Send f from U₁ to U₂ along edges, through A (lift, descent) or A′ (descent, lift), with point data at the blocks of x or y. For every functional l the resulting functions of x and y satisfy SquareLaw with constant κ/c (κ may be 0), c ≠ 0, |c|² = C·lValueProd, with C, κ uniform in the family.")))))));
}
