using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.AbsoluteValues.Heights;

internal sealed class NumberFieldIntegralLatticeDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral points of a subspace have unit Pluecker ideal in the primitive normalization.",
        H("Number Field Integral Lattice"),
        Blocks(Describe.Lean(
            DescribeId.Create("number-field-integral-lattice"),
            DeclarationHandle.Create("D5/S3/Arith/AbsoluteValues/Heights/NumberFieldIntegralLattice.prod_mul_plucker_eq_one"),
            H("Number Field Integral Lattice"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("Integral points of a subspace have unit Pluecker ideal in the primitive normalization."))),
            DescribeRole.Theorem))));
}
