using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.AbsoluteValues.Heights;

internal sealed class NumberFieldLatticeDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The covolume of the mixed lattice is expressed through number-field data and height.",
        H("Number Field Lattice"),
        Blocks(Describe.Lean(
            DescribeId.Create("number-field-lattice"),
            DeclarationHandle.Create("D5/S3/Arith/AbsoluteValues/Heights/NumberFieldLattice.covolume_mixedLattice"),
            H("Number Field Lattice"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("The covolume of the mixed lattice is expressed through number-field data and height."))),
            DescribeRole.Theorem))));
}
