using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.AbsoluteValues.Heights;

internal sealed class QuotientFubiniDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A quotient-space integration bound controls measure of lattice translates.",
        H("Quotient Fubini"),
        Blocks(Describe.Lean(
            DescribeId.Create("quotient-fubini"),
            DeclarationHandle.Create("D5/S3/Arith/AbsoluteValues/Heights/QuotientFubini.pow_mul_measure_inter_add_le"),
            H("Quotient Fubini"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("A quotient-space integration bound controls measure of lattice translates."))),
            DescribeRole.Theorem))));
}
