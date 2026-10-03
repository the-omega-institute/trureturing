using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.AbsoluteValues.Heights;

internal sealed class GelfondDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A power-of-two estimate controls the sup norm of a product of complex polynomials.",
        H("Gelfond"),
        Blocks(Describe.Lean(
            DescribeId.Create("gelfond"),
            DeclarationHandle.Create("D5/S3/Arith/AbsoluteValues/Heights/Gelfond.supNorm_mul_supNorm_le_two_pow"),
            H("Gelfond"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("A power-of-two estimate controls the sup norm of a product of complex polynomials."))),
            DescribeRole.Theorem))));
}
