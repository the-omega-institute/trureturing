using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class LongCoreRingsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/LongCoreRings.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual long-core family and exact beta", H("The actual long-core family and exact beta"),
        Blocks(Paragraph(Text("The H and X seams both cross the index permutation. Actual core restriction and three distinct saturated Heawood charges use the exact long-core omission theorem. The original separated word, with compatible seven/eight-block selections, attains beta thirty-three k plus floor(k/2) for every cyclic length. The actual graphs are cubic bipartite and the original thirty-six-per-cell selection is minimal. This module does not yet prove the separate all-k SF upper bound, which is resolved in the written block-compensation source.")),
            Node("localNeighbors", "localNeighbors", "Exact declaration: def localNeighbors (v : Fin 62) : List (Fin 62).", DescribeRole.Definition),
            Node("localGraph", "localGraph", "Exact declaration: def localGraph : SimpleGraph (Fin 62).", DescribeRole.Definition),
            Node("saturated_omission", "saturated omission", "Exact declaration: theorem saturated_omission (D : Finset (Fin 62)) (hD : IsKIndependent localGraph 2 D) (j : Fin 3) (h8 : (blockSlice D j).card=8) : evenPort j∉coreSlice D ∧ oddPort j∉coreSlice D.", DescribeRole.Theorem),
            Node("module_credit", "module credit", "Exact declaration: theorem module_credit (D : Finset (Fin 62)) (hD : IsKIndependent localGraph 2 D) : D.card≤21+(coreSlice D).card+LongCoreOmission.omitted (coreSlice D) false.", DescribeRole.Theorem),
            Node("forward", "forward", "Exact declaration: def forward (v w : Fin 62) : Prop.", DescribeRole.Definition),
            Node("graph", "graph", "Exact declaration: def graph (e : Equiv.Perm I) : SimpleGraph (I × Fin 62).", DescribeRole.Definition),
            Node("slice", "slice", "Exact declaration: def slice (S : Finset (I × Fin 62)) (i : I) : Finset (Fin 62).", DescribeRole.Definition),
            Node("coreSet", "coreSet", "Exact declaration: def coreSet (S : Finset (I × Fin 62)) : Finset (I × Fin 20).", DescribeRole.Definition),
            Node("beta_upper", "beta upper", "Exact declaration: theorem beta_upper (e : Equiv.Perm I) : beta (graph e) 2≤33*Fintype.card I+Fintype.card I/2.", DescribeRole.Theorem),
            Node("pattern", "pattern", "Exact declaration: def pattern (kind : Bool) : Finset (Fin 62).", DescribeRole.Definition),
            Node("selection", "selection", "Exact declaration: def selection (word : I → Bool) : Finset (I × Fin 62).", DescribeRole.Definition),
            Node("selection_independent", "selection independent", "Exact declaration: theorem selection_independent (e : Equiv.Perm I) (word : I → Bool) (hsep : ∀ i, ¬ (word i=true ∧ word (e i)=true)) : IsKIndependent (graph e) 2 (selection word).", DescribeRole.Theorem),
            Node("cyclic_beta", "cyclic beta", "Exact declaration: theorem cyclic_beta (k : ℕ) : beta (graph (finRotate k)) 2=33*k+k/2.", DescribeRole.Theorem),
            Node("neighbors", "neighbors", "Exact declaration: def neighbors (e : Equiv.Perm I) (v : I × Fin 62) : List (I × Fin 62).", DescribeRole.Definition),
            Node("regular", "regular", "Exact declaration: theorem regular (e : Equiv.Perm I) : ∀ v, DegreeCapacity.degree (graph e) v=3.", DescribeRole.Theorem),
            Node("bipartite", "bipartite", "Exact declaration: theorem bipartite (e : Equiv.Perm I) : (graph e).Colorable 2.", DescribeRole.Theorem),
            Node("forming_minimal", "forming minimal", "Exact declaration: theorem forming_minimal (e : Equiv.Perm I) : Regular.Minimal (graph e).Adj (fun v => ClosedRingWitnesses.forming v.2).", DescribeRole.Theorem),
            Node("sf_lower", "sf lower", "Exact declaration: theorem sf_lower (e : Equiv.Perm I) : 36*Fintype.card I≤SF (graph e) 2.", DescribeRole.Theorem)), []));
}
