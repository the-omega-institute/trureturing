using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Orthogonality;
internal sealed class SevenBitSpreadCompletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unique completion of every original eight-member partial spread.",
        H("SevenBitSpreadCompletion"),
        Blocks(
            Describe.Lean(DescribeId.Create("orthogonal-seven"), DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SevenBitSpreadCompletion.orthogonal_seven"), H("Entire even hyperplane"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuadraticForms/binarysubspace2026complete")), Blocks(Paragraph(Text("All seven-point orthogonal sets in the original full even hyperplane are Lagrangians. The ordinary kernel check covers every compatible extension through the generic include-or-omit soundness theorem. It includes XOR closure and all original hyperplane intersection counts; it does not sample a spread."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("unique-completion"), DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SevenBitSpreadCompletion.result"), H("Unique actual ninth Lagrangian"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuadraticForms/binarysubspace2026complete")), Blocks(Paragraph(Text("For every eight disjoint full Lagrangians, the seven actual holes are the unique disjoint ninth completion. The conclusion returns the entire coordinate Submodule, exact carrier, finrank three and vanishing pairing on all its vectors. It uses the universal point/hyperplane count, rather than an example or transitivity assumption. Exact n7 remains open and the paused nineteen-color case exclusions are not executed."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Orthogonality/SevenBitCapacity")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Orthogonality/PartialSpreadHoles"))]));
}
