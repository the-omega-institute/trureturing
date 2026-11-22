using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Transportation;
internal sealed class SupportedCycleSupplierDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Boolean tables with equal individual row and column counts have a simple alternating cycle whenever they differ. Rows and columns can have independent universes. The conclusion gives a cycle of length at least two with separately distinct rows and columns, positive diagonal disagreements and negative shifted disagreements, including the closing edge.", H("SupportedCycleSupplier"), Blocks(
        Describe.Lean(DescribeId.Create("simple-cycle"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Transportation/SupportedCycleSupplier.simple_cycle"),
            H("A simple cycle of target disagreements"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Combinatorics/wang2026ktv")),
            Blocks(Paragraph(Text("Finite Boolean tables with equal individual row and column counts have a simple alternating cycle whenever they differ. Rows and columns can have independent universes. The conclusion gives a cycle of length at least two with separately distinct rows and columns, positive diagonal disagreements and negative shifted disagreements, including the closing edge."))), DescribeRole.Theorem),
        Paragraph(Text("Equal row counts pair a positive disagreement with a negative disagreement in the same row; equal column counts then give a positive disagreement in the next row. Iteration on the finite set of positive disagreements repeats a state and yields an alternating closed walk. Opposite Boolean values exclude a one-step loop. A shortest such walk has no repeated row or column, since either repetition would cut out a shorter alternating closed walk. Its length is therefore at least two, with separately distinct rows and columns and the required closing edge.")))));
}
