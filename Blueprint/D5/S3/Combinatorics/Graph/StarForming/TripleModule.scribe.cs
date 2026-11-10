using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class TripleModuleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/TripleModule.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual triple-port core and disjoint block accounting", H("Actual triple-port core and disjoint block accounting"),
        Blocks(Paragraph(Text("The original forty-eight-vertex module consists of its twenty-vertex core and two broken Heawood blocks attached to distinct prescribed ports. The stronger closed-core omission theorem applies after deleting one core edge. Exact disjoint slice counts and the two actual saturated-block omission charges bound every dissociation selection by twenty-six.")),
            Node("neighbors", "neighbors", "Exact declaration: def neighbors : Fin 48 → List (Fin 48).", DescribeRole.Definition),
            Node("graph", "graph", "Exact declaration: def graph : SimpleGraph (Fin 48).", DescribeRole.Definition),
            Node("partition", "partition", "Exact declaration: def partition : Fin 48 ≃ (Fin 20 ⊕ (Fin 2 × Fin 14)).", DescribeRole.Definition),
            Node("core", "core", "Exact declaration: def core (v : Fin 20) : Fin 48.", DescribeRole.Definition),
            Node("block", "block", "Exact declaration: def block (j : Fin 2) (v : Fin 14) : Fin 48.", DescribeRole.Definition),
            Node("coreSlice", "coreSlice", "Exact declaration: def coreSlice (D : Finset (Fin 48)) : Finset (Fin 20).", DescribeRole.Definition),
            Node("blockSlice", "blockSlice", "Exact declaration: def blockSlice (D : Finset (Fin 48)) (j : Fin 2) : Finset (Fin 14).", DescribeRole.Definition),
            Node("card_fibers", "card fibers", "Exact declaration: theorem card_fibers {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (S : Finset (A × B)) : S.card=∑ a : A, (Finset.univ.filter (fun b => (a,b)∈S)).card.", DescribeRole.Theorem),
            Node("card_slices", "card slices", "Exact declaration: theorem card_slices (D : Finset (Fin 48)) : D.card=(coreSlice D).card+∑ j : Fin 2, (blockSlice D j).card.", DescribeRole.Theorem),
            Node("evenPort", "evenPort", "Exact declaration: def evenPort (j : Fin 2) : Fin 20.", DescribeRole.Definition),
            Node("oddPort", "oddPort", "Exact declaration: def oddPort (j : Fin 2) : Fin 20.", DescribeRole.Definition),
            Node("saturated_omission", "saturated omission", "Exact declaration: theorem saturated_omission (D : Finset (Fin 48)) (hD : IsKIndependent graph 2 D) (j : Fin 2) (h8 : (blockSlice D j).card=8) : evenPort j∉coreSlice D ∧ oddPort j∉coreSlice D.", DescribeRole.Theorem),
            Node("beta_cap", "beta cap", "Exact declaration: theorem beta_cap (D : Finset (Fin 48)) (hD : IsKIndependent graph 2 D) : D.card≤26.", DescribeRole.Theorem)), []));
}
