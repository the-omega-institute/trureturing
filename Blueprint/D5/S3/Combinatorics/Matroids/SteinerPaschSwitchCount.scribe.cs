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
                Paragraph(Text("Fix distinct nonidentity pivots p and q in a finite Steiner loop with trivial centre, and fix a finite nontrivial binary fibre. Across normalized label tables, the compatible labelled extensions attain at least two successful-start counts for the lifted pivots (p,0) and (q,0) exactly when the original Steiner triple system contains a Pasch whose four blocks place p and q opposite one another.")),
                Paragraph(Text("The four other points of such a Pasch form a square in the graph of the two matchings. Uniqueness of the block through two points excludes the special square containing the identity. Conversely, each other square gives four blocks through the two pivots and four distinct corners. The count range gives two distinct values as soon as there is one such square."))),
            DescribeRole.Theorem))));
}
