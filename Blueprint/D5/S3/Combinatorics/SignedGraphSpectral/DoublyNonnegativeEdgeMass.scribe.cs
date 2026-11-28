using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SignedGraphSpectral;

internal sealed class DoublyNonnegativeEdgeMassDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cut splitting and local edge-mass estimates for doubly nonnegative matrices.",
        H("Doubly nonnegative edge mass"),
        Blocks(Describe.Lean(
            DescribeId.Create("gram-cut-split"),
            DeclarationHandle.Create("D5/S3/Combinatorics/SignedGraphSpectral/DoublyNonnegativeEdgeMass.gram_cut_split"),
            H("Gram splitting at a cut vertex"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/QuadraticForms/huhan2026signedsquareenergy")),
            Blocks(Paragraph(Text(
                "A positive semidefinite entrywise nonnegative matrix supported on a graph "
                + "splits into two such matrices on the sides of a valid cut. Their Gram "
                + "vectors come from orthogonal projection onto the span of the left-side "
                + "vectors and the orthogonal remainder. Both total entry mass and the sum "
                + "of square roots over edges add across the cut."))),
            DescribeRole.Theorem))));
}
