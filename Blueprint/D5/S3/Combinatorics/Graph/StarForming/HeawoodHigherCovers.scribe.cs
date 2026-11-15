using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class HeawoodHigherCoversDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/HeawoodHigherCovers.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual higher-cover density through connected double quotients", H("Actual higher-cover density through connected double quotients"),
        Blocks(Paragraph(Text("An arbitrary neighborhood cover of the actual binary Heawood base with two-element fibers is the intermediate graph. Its actual connectedness gives a dissociation set of size at least fifteen. Exact finite fiber cardinalities and actual cubic bipartite parameter transport prove fifteen times the higher-cover order at most twenty-eight beta and one hundred ninety-six times its SF-minus-beta gap at most nine times its order. Zero higher fibers are included. No deck-group factorization, character injection or rank-four matrix-space extraction is assumed to have been completed.")),
            Node("connected_double_quotient", "connected double quotient", "Exact declaration: theorem connected_double_quotient (p : V → Fin 14) (double : CoverPullback.NeighborhoodCover HeawoodLift.base.Adj Q.Adj p) (two : ∀ v, (Finset.univ.filter (fun x => p x=v)).card=2) (connected : Q.Preconnected) (q : W → V) (higher : CoverPullback.NeighborhoodCover Q.Adj H.Adj q) (k : ℕ) (fibers : ∀ v, (Finset.univ.filter (fun x => q x=v)).card=k) : 15*Fintype.card W ≤ 28*beta H 2 ∧ 196*(SF H 2-beta H 2) ≤ 9*Fintype.card W.", DescribeRole.Theorem)), []));
}
