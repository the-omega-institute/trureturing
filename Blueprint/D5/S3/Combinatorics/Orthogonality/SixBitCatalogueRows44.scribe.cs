using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Orthogonality;

internal sealed class SixBitCatalogueRows44Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact block of the full received six-dimensional certificate.",
        H("All checks in rows 2762 through 2824"),
        Blocks(Describe.Lean(DescribeId.Create("checked-rows"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitCatalogueRows44.checked_rows_44"),
            H("Kernel checked certificate rows"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                "D5/L/QuadraticForms/binarysubspace2026complete")),
            Blocks(Paragraph(Text("Every row retains the original mask/color bounds, all 64 adjoining-vector witnesses, all orthogonal-complement tests and all 2825 pair-color comparisons. The full verification module combines every block to prove the original Covers and Proper predicates and transfers the resulting chromatic theorem to every actual nonzero Submodule. Historical native_decide provenance belongs to the supplied source; this block uses ordinary kernel reduction."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/Orthogonality/SixBitCatalogueData"))]));
}
