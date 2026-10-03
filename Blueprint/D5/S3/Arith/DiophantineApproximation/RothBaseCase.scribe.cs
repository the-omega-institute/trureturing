using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.DiophantineApproximation;

internal sealed class RothBaseCaseDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A one-variable index estimate supplies the base case of the Roth argument.",
        H("Roth Base Case"),
        Blocks(Describe.Lean(
            DescribeId.Create("roth-base-case"),
            DeclarationHandle.Create("D5/S3/Arith/DiophantineApproximation/RothBaseCase.index_le_base"),
            H("Roth Base Case"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("A one-variable index estimate supplies the base case of the Roth argument."))),
            DescribeRole.Theorem))));
}
