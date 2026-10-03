using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.DiophantineApproximation;

internal sealed class RothAuxiliaryDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An auxiliary polynomial realizes prescribed derivative vanishing with degree and height bounds.",
        H("Roth Auxiliary"),
        Blocks(Describe.Lean(
            DescribeId.Create("roth-auxiliary"),
            DeclarationHandle.Create("D5/S3/Arith/DiophantineApproximation/RothAuxiliary.exists_auxiliary_deriv"),
            H("Roth Auxiliary"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("An auxiliary polynomial realizes prescribed derivative vanishing with degree and height bounds."))),
            DescribeRole.Theorem))));
}
