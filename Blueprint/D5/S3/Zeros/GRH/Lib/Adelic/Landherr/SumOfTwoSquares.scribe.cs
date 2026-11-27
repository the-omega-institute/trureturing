using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.Landherr;

internal sealed class SumOfTwoSquaresDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sum Of Two Squares", H("Sum Of Two Squares"),
        Blocks(
            Paragraph(Text("A totally positive element is a sum of two squares in a quadratic algebra, via Hasse's norm theorem.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/Landherr/SumOfTwoSquares.exists_sq_add_sq_quadraticAlgebra"),
                H("exists_sq_add_sq_quadraticAlgebra"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let E satisfy StablyUnram, S be a set of finite places of E, and p, q, B ∈ E⁺, p ≠ 0 totally positive, p a unit outside S, q a unit on S ∪ S̄. Then p = x² + y² is solvable in E⁺[X]/(X² − (qp − B²)).")))))));
}
