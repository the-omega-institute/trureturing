using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class SteinerPaschSwitchCountDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/SteinerPaschSwitchCount";
    private static readonly LibraryNoteRef Pasch = LibraryNoteRef.Create(
        "D5/L/FiniteGeometry/falconefigulagalici2025veblenpoints");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pasch configurations detect whether the number of successful starts can vary with the labels.",
        H("Pasch configurations and fixed-pivot switch counts"),
        Blocks(Describe.Lean(
            DescribeId.Create("steiner-opposite-pasch-variable-count"),
            DeclarationHandle.Create(Module + ".variableLabelledSwitchCount_iff"),
            H("An opposite pair in a Pasch gives variable switch counts"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Pasch),
            Blocks(
                Paragraph(Text("Fix two distinct pivots in a finite Steiner loop with trivial centre and fix a finite nontrivial binary fibre. Use the graph given by left multiplication by the pivots. In normalized extensions, the compatible labelled complete triple systems give at least two distinct successful-start counts exactly when four blocks form a Pasch in which the two pivots occur in no common block.")),
                Paragraph(Text("The four other points of such a Pasch form a square in the graph of the two matchings. Uniqueness of the block through two points excludes the special square containing the identity. Conversely, each other square gives four blocks through the two pivots and four distinct corners. The count range gives two distinct values as soon as there is one such square."))),
            DescribeRole.Theorem))));
}
