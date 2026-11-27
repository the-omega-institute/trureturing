using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Rows;

internal sealed class LineCoordinatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Line Coordinates", H("Line Coordinates"),
        Blocks(
            Paragraph(Text("Names for index sets, characters, moduli and polynomials of the comparison construction. Column counts of the weight add up to w_j − j − ⌊(t+k−1)/2⌋. Index sets, determinant data and coefficient vectors for the one-line identity. Degree, denominator and size of coordinates of the determinant product in Weyl's lattice.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Rows/LineCoordinates.exists_denom_linePolyCoords"),
                H("exists_denom_linePolyCoords"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For 1 ≤ j ≤ m there are d ≤ 31m·∑_τ |Data.DetIndex j τ| and an integer 0 < H ≤ d^{3d} such that every H·Data.linePolyCoords is homogeneous of degree d, with coefficients in any subring of ℂ containing all τ(Y_ab).")))))));
}
