using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Seesaw;

internal sealed class EdgePairDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Edge Pair", H("Edge Pair"),
        Blocks(
            Paragraph(Text("Finite part of the zero term; its frequency lies in the dual period lattice. Two lifts as one arrow: weight-zero splitting, finite evaluation map and its equivariance.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Seesaw/EdgePair.finEval_inclXFin"),
                H("finEval_inclXFin"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The finite evaluation ArrowPair.finEval commutes with the finite points of U(X) × U(X') × U(X₀).")))))));
}
