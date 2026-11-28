using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Exchange;

internal sealed class GridMoveDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Grid Move", H("Grid Move"),
        Blocks(
            Paragraph(Text("Tuples of matrices, tidy data on paths, and the periods of the staircase. Weights, levels, kernels and final period along the definite edges of the grids.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Exchange/GridMove.exists_square_move"),
                H("exists_square_move"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Crossing a square. Let all (L i, M i) satisfy SquareLaw χ ε C, χ⁻¹ the product of the characters of (p, v), (Q, U), opposite edges having equal characters, with conditions hQ, h on admissible families, μ-edges, nodes and w. A tidy Λ of order n on w, (p, v), (Q, U) gives a tidy Φ of order n + 2 on w, (U, R), (v, r), with Λ of M, Fourier transformed in the block T, equal to C·Φ of L.")))))));
}
