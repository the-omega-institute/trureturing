using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.AbsoluteValues.Heights;

internal sealed class MixedBallDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The squared norm in the mixed space splits into real and complex place components.",
        H("Mixed Ball"),
        Blocks(Describe.Lean(
            DescribeId.Create("mixed-ball"),
            DeclarationHandle.Create("D5/S3/Arith/AbsoluteValues/Heights/MixedBall.norm_sq_mixedPi"),
            H("Mixed Ball"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("The squared norm in the mixed space splits into real and complex place components."))),
            DescribeRole.Theorem))));
}
