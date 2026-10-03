using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.AbsoluteValues.Heights;

internal sealed class MixedLatticeDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The mixed Gram determinant equals the archimedean Pluecker height factor.",
        H("Mixed Lattice"),
        Blocks(Describe.Lean(
            DescribeId.Create("mixed-lattice"),
            DeclarationHandle.Create("D5/S3/Arith/AbsoluteValues/Heights/MixedLattice.norm_det_gram"),
            H("Mixed Lattice"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("The mixed Gram determinant equals the archimedean Pluecker height factor."))),
            DescribeRole.Theorem))));
}
