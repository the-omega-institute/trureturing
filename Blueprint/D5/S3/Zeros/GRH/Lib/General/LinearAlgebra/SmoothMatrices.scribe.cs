using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.LinearAlgebra;

internal sealed class SmoothMatricesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Smooth Matrices", H("Smooth Matrices"),
        Blocks(
            Paragraph(Text("A twisted trace identity between commuting families transfers eigensystems. Double counting of moves between weighted class sums gives proportional traces. Non-stationary phase: uniform rapid Fourier decay with polynomial loss in a parameter. Smoothness of matrix operations and exponential; global smooth extension of an analytic germ.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/SmoothMatrices.exists_contDiff_eventuallyEq"),
                H("exists_contDiff_eventuallyEq"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("A map from a finite-dimensional real normed space to a real normed space that is analytic at x agrees near x with a globally smooth map.")))))));
}
