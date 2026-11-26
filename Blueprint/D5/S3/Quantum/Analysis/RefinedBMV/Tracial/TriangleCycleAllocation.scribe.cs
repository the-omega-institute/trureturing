using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.RefinedBMV.Tracial;

internal sealed class TriangleCycleAllocationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed spectral triangles in the four-copy refined BMV comparison",
        H("Signed spectral triangles in the four-copy refined BMV comparison"),
        Blocks(Describe.Lean(
            DescribeId.Create("refined-bmv-signed-spectral-triangle"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Analysis/RefinedBMV/Tracial/TriangleCycleAllocation.diagonal_word_bound_of_triangle_allocation"),
            H("The word mean under a three-edge allocation"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv")),
            Blocks(Paragraph(Text(
                "For a nonnegative spectrum with three labels and a Hermitian second factor, " +
                "a positive semidefinite coefficient block on each edge gives the four-copy word bound. " +
                "The vectors in the edge Grams are products of two spectral blocks through each " +
                "intermediate label. The remaining alternating traces are squared Hilbert–Schmidt norms."))),
            DescribeRole.Theorem))));
}
