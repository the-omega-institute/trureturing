using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.DiophantineApproximation;

internal sealed class RothKeyInequalityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The auxiliary-polynomial estimates imply Roth's key local approximation inequality.",
        H("Roth Key Inequality"),
        Blocks(Describe.Lean(
            DescribeId.Create("roth-key-inequality"),
            DeclarationHandle.Create("D5/S3/Arith/DiophantineApproximation/RothKeyInequality.roth_key_inequality"),
            H("Roth Key Inequality"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("The auxiliary-polynomial estimates imply Roth's key local approximation inequality."))),
            DescribeRole.Theorem))));
}
