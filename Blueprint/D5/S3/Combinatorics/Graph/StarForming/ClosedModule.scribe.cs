using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class ClosedModuleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/ClosedModule.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual sixty-two-vertex module accounting", H("Actual sixty-two-vertex module accounting"),
        Blocks(Paragraph(Text("The actual disjoint core and three broken-Heawood blocks partition sixty-two vertices. Restricting any actual dissociation selection gives the local omission inequality. Every saturated eight-block omits its own designated pair, and the three distinct omission budgets yield the unconditional module cap thirty-three. No restriction is imposed on either open interface vertex.")),
            Node("neighbors", "neighbors", "Exact declaration: def neighbors : Fin 62 → List (Fin 62).", DescribeRole.Definition),
            Node("graph", "graph", "Exact declaration: def graph : SimpleGraph (Fin 62).", DescribeRole.Definition),
            Node("partition", "partition", "Exact declaration: def partition : Fin 62 ≃ (Fin 20 ⊕ (Fin 3 × Fin 14)).", DescribeRole.Definition),
            Node("core", "core", "Exact declaration: def core (v : Fin 20) : Fin 62.", DescribeRole.Definition),
            Node("block", "block", "Exact declaration: def block (j : Fin 3) (v : Fin 14) : Fin 62.", DescribeRole.Definition),
            Node("coreSlice", "coreSlice", "Exact declaration: def coreSlice (D : Finset (Fin 62)) : Finset (Fin 20).", DescribeRole.Definition),
            Node("blockSlice", "blockSlice", "Exact declaration: def blockSlice (D : Finset (Fin 62)) (j : Fin 3) : Finset (Fin 14).", DescribeRole.Definition),
            Node("card_fibers", "card fibers", "Exact declaration: theorem card_fibers {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (S : Finset (A × B)) : S.card=∑ a : A, (Finset.univ.filter (fun b => (a,b)∈S)).card.", DescribeRole.Theorem),
            Node("card_slices", "card slices", "Exact declaration: theorem card_slices (D : Finset (Fin 62)) : D.card=(coreSlice D).card+∑ j : Fin 3, (blockSlice D j).card.", DescribeRole.Theorem),
            Node("evenPort", "evenPort", "Exact declaration: def evenPort (j : Fin 3) : Fin 20.", DescribeRole.Definition),
            Node("oddPort", "oddPort", "Exact declaration: def oddPort (j : Fin 3) : Fin 20.", DescribeRole.Definition),
            Node("saturated_omission", "saturated omission", "Exact declaration: theorem saturated_omission (D : Finset (Fin 62)) (hD : IsKIndependent graph 2 D) (j : Fin 3) (h8 : (blockSlice D j).card=8) : evenPort j∉coreSlice D ∧ oddPort j∉coreSlice D.", DescribeRole.Theorem),
            Node("beta_cap", "beta cap", "Exact declaration: theorem beta_cap (D : Finset (Fin 62)) (hD : IsKIndependent graph 2 D) : D.card≤33.", DescribeRole.Theorem)), []));
}
