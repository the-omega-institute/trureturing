using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.DiophantineApproximation;

internal sealed class RothLemmaDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Degree ratios bound the polynomial index in Roth's lemma.",
        H("Roth Lemma"),
        Blocks(Describe.Lean(
            DescribeId.Create("roth-lemma"),
            DeclarationHandle.Create("D5/S3/Arith/DiophantineApproximation/RothLemma.index_le_of_degree_ratio"),
            H("Roth Lemma"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("Degree ratios bound the polynomial index in Roth's lemma."))),
            DescribeRole.Theorem))));
}
