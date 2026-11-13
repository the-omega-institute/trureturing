using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Orthogonality.SevenDimensional;
internal sealed class ActualSpreadCompletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The unique ninth completion on arbitrary actual coordinate Submodules.",
        H("ActualSpreadCompletion"),
        Blocks(
            Describe.Lean(DescribeId.Create("carrier"), DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SevenDimensional/ActualSpreadCompletion.carrier"), H("Entire carrier correspondence"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuadraticForms/binarysubspace2026complete")), Blocks(Paragraph(Text("For every actual Submodule, the original finite-point representation, with zero restored, equals its entire coordinate carrier. The representation is injective."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("data"), DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SevenDimensional/ActualSpreadCompletion.actual_data"), H("Geometric input supplies all incidence data"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuadraticForms/binarysubspace2026complete")), Blocks(Paragraph(Text("An arbitrary actual finrank-three totally isotropic Submodule supplies all seven-point Lagrangian data. No hyperplane counts, chosen basis or expected completion are assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SevenDimensional/ActualSpreadCompletion.result"), H("Unique ninth actual Submodule"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuadraticForms/binarysubspace2026complete")), Blocks(Paragraph(Text("Every eight actual three-dimensional totally isotropic Submodules with pairwise zero intersection have exactly one actual ninth completion. Their full nonzero point sets partition the original entire even hyperplane. This is the source universal completion theorem, distinct from the paused nineteen-color exclusions or any chosen spread examples."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Orthogonality/SevenBitSpreadCompletion"))]));
}
