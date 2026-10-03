using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.AbsoluteValues.Heights;

internal sealed class SuccessiveMinimaDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Successive minima yield linearly independent lattice points in dilated convex bodies.",
        H("Successive Minima"),
        Blocks(Describe.Lean(
            DescribeId.Create("successive-minima"),
            DeclarationHandle.Create("D5/S3/Arith/AbsoluteValues/Heights/SuccessiveMinima.exists_linearIndependent_mem_smul_successiveMinimum"),
            H("Successive Minima"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("Successive minima yield linearly independent lattice points in dilated convex bodies."))),
            DescribeRole.Theorem))));
}
