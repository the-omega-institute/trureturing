using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class CompleteSubdivisionSelectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionSelection.";

    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/farhan2026multiset");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The diagonal-aware selection matrix",
        H("The diagonal-aware selection matrix"),
        Blocks(
            Paragraph(Text("The diagonal records selected original vertices and the off-diagonal records selected midpoints. Both come from the same arbitrary landmark set. Each entry is binary, the matrix is symmetric, and its row sum is the selected incident-midpoint count plus the original selection bit. The diagonal is free; it is not an irreflexive adjacency predicate.")),
            Describe.Lean(DescribeId.Create("complete-subdivision-selection-pair-bit"),
                DeclarationHandle.Create(Prefix + "pairBit"),
                H("pairBit"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The off-diagonal integer bit records the selected midpoint; its diagonal is zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("complete-subdivision-selection-selected-degree-eq-sum-pair-bit"),
                DeclarationHandle.Create(Prefix + "selectedDegree_eq_sum_pairBit"),
                H("selectedDegree eq sum pairBit"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Each selected midpoint incident with u corresponds to exactly one other original index, so the selected degree equals the off-diagonal row sum."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-subdivision-selection-pair-bit-symm"),
                DeclarationHandle.Create(Prefix + "pairBit_symm"),
                H("pairBit symm"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The selected off-diagonal bits are symmetric under exchanging original indices."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-subdivision-selection-pair-bit-binary"),
                DeclarationHandle.Create(Prefix + "pairBit_binary"),
                H("pairBit binary"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Every off-diagonal bit is zero or one."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-subdivision-selection-selection"),
                DeclarationHandle.Create(Prefix + "selection"),
                H("selection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The natural-valued selection matrix uses original bits on its diagonal and midpoint bits off the diagonal."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("complete-subdivision-selection-selection-symm"),
                DeclarationHandle.Create(Prefix + "selection_symm"),
                H("selection symm"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The actual landmark selection matrix is symmetric, including its independent diagonal."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-subdivision-selection-selection-binary"),
                DeclarationHandle.Create(Prefix + "selection_binary"),
                H("selection binary"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Every selection entry is at most one."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-subdivision-selection-selection-diagonal"),
                DeclarationHandle.Create(Prefix + "selection_diagonal"),
                H("selection diagonal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The integer coercion of a diagonal entry is exactly the original selection bit."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-subdivision-selection-selection-off-diagonal"),
                DeclarationHandle.Create(Prefix + "selection_offDiagonal"),
                H("selection offDiagonal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The integer coercion of an off-diagonal entry is exactly the selected midpoint bit."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-subdivision-selection-selection-row"),
                DeclarationHandle.Create(Prefix + "selection_row"),
                H("selection row"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The integer row sum is the selected midpoint degree plus the original selection bit."))), DescribeRole.Theorem))));
}
