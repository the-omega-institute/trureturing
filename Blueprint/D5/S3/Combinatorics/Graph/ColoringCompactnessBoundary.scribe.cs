using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class ColoringCompactnessBoundaryDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/ColoringCompactnessBoundary.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/debruijnerdos1951colour");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite palettes support graph-coloring compactness; an infinite palette need not.",
        H("The finite-palette boundary of coloring compactness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-palette-compactness-and-infinite-palette-failure"),
                DeclarationHandle.Create(Prefix
                    + "finite_palette_compactness_and_infinite_palette_failure"),
                H("Finite compactness and its infinite-palette failure"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For every simple graph G and natural number k, G has a proper coloring "
                            + "by Fin(k) exactly when each finite induced subgraph does. The "
                            + "reverse implication adapts induced-subgraph colorings to the "
                            + "finite-subgraph premise of Mathlib's pinned compactness theorem; "
                            + "it does not reproduce the compactness argument.")),
                    Paragraph(Text(
                        "The same local-to-global statement fails when the palette is Nat. Every "
                            + "finite induced subgraph of the complete graph on Set(Nat) can be "
                            + "colored by enumerating its finite vertex subtype and embedding that "
                            + "finite index into Nat. Any global Nat-coloring would be injective, "
                            + "because all distinct vertices are adjacent, contradicting Cantor's "
                            + "theorem that no injection Set(Nat) to Nat exists. The finite and "
                            + "infinite clauses form one boundary statement; the source records the "
                            + "classical finite-palette theorem, while the explicit Cantor witness "
                            + "is repository-derived."))),
                DescribeRole.Theorem)),
        []));
}
