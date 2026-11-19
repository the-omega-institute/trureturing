using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.SubQuorum;

internal sealed class GridDissociationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/SubQuorum/GridDissociation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All-size rectangular-grid dissociation equality", H("All-size rectangular-grid dissociation equality"),
        Blocks(Paragraph(Text("The actual Cartesian path graph is used throughout. Actual row restrictions give the no-three-selected path cap. Each two-by-two square has capacity two; saturation in an odd two-row band forces full even columns and empty odd columns, and prevents three consecutive positive row deviations. The odd-integer profile theorem and exact even-width pairing give the upper bound for every pair of natural dimensions, including zero. The actual periodic selection and its transpose attain both terms of F, with exact symbolic residue counts. Thus beta equals F without bounded-size grid enumeration. Coloring psiSq, representative Omega, arbitrary matching directions, absorption and strip-transfer claims are separate parameters and remain outside this theorem.")),
            Node("graph", "graph", "Exact declaration: def graph (m n : ℕ) : SimpleGraph (Fin m × Fin n).", DescribeRole.Definition),
            Node("row", "row", "Exact declaration: def row (D : Finset (Fin m × Fin n)) (i : Fin m) : Finset (Fin n).", DescribeRole.Definition),
            Node("rowCount", "rowCount", "Exact declaration: def rowCount (D : Finset (Fin m × Fin n)) (i : Fin m) : ℕ.", DescribeRole.Definition),
            Node("sum_rowCount", "sum rowCount", "Exact declaration: theorem sum_rowCount (D : Finset (Fin m × Fin n)) : ∑ i, rowCount D i=D.card.", DescribeRole.Theorem),
            Node("row_three_free", "row three free", "Exact declaration: theorem row_three_free (D : Finset (Fin m × Fin n)) (hD : IsKIndependent (graph m n) 2 D) (i : Fin m) (j k l : Fin n) (hjk : j.val+1=k.val) (hkl : k.val+1=l.val) : ¬ (j ∈ row D i ∧ k ∈ row D i ∧ l ∈ row D i).", DescribeRole.Theorem),
            Node("row_bound", "row bound", "Exact declaration: theorem row_bound (D : Finset (Fin m × Fin n)) (hD : IsKIndependent (graph m n) 2 D) (i : Fin m) : rowCount D i ≤ n-n/3.", DescribeRole.Theorem),
            Node("bandCount", "bandCount", "Exact declaration: def bandCount (D : Finset (Fin m × Fin n)) (i k : Fin m) (j : Fin n) : ℕ.", DescribeRole.Definition),
            Node("band_pair_bound", "band pair bound", "Exact declaration: theorem band_pair_bound (D : Finset (Fin m × Fin n)) (hD : IsKIndependent (graph m n) 2 D) (i k : Fin m) (hik : (SimpleGraph.pathGraph m).Adj i k) (j l : Fin n) (hjl : (SimpleGraph.pathGraph n).Adj j l) : bandCount D i k j+bandCount D i k l ≤ 2.", DescribeRole.Theorem),
            Node("sum_bandCount", "sum bandCount", "Exact declaration: theorem sum_bandCount (D : Finset (Fin m × Fin n)) (i k : Fin m) : (∑ j, bandCount D i k j)=rowCount D i+rowCount D k.", DescribeRole.Theorem),
            Node("bandCount_cap", "bandCount cap", "Exact declaration: theorem bandCount_cap (D : Finset (Fin m × Fin n)) (i k : Fin m) (j : Fin n) : bandCount D i k j ≤ 2.", DescribeRole.Theorem),
            Node("even_band_bound", "even band bound", "Exact declaration: theorem even_band_bound (hn : n%2=0) (D : Finset (Fin m × Fin n)) (hD : IsKIndependent (graph m n) 2 D) (i k : Fin m) (hik : (SimpleGraph.pathGraph m).Adj i k) : rowCount D i+rowCount D k ≤ n.", DescribeRole.Theorem),
            Node("odd_band_bound", "odd band bound", "Exact declaration: theorem odd_band_bound (hn : n%2=1) (D : Finset (Fin m × Fin n)) (hD : IsKIndependent (graph m n) 2 D) (i k : Fin m) (hik : (SimpleGraph.pathGraph m).Adj i k) : rowCount D i+rowCount D k ≤ n+1.", DescribeRole.Theorem),
            Node("band_rigidity", "band rigidity", "Exact declaration: theorem band_rigidity (hn : n%2=1) (D : Finset (Fin m × Fin n)) (hD : IsKIndependent (graph m n) 2 D) (i k : Fin m) (hik : (SimpleGraph.pathGraph m).Adj i k) (htotal : n+1 ≤ rowCount D i+rowCount D k) : ∀ j, bandCount D i k j=if j.val%2=0 then 2 else 0.", DescribeRole.Theorem),
            Node("odd_row_pair", "odd row pair", "Exact declaration: theorem odd_row_pair (hn : n%2=1) (D : Finset (Fin m × Fin n)) (hD : IsKIndependent (graph m n) 2 D) (i k : Fin m) (hik : (SimpleGraph.pathGraph m).Adj i k) : rowCount D i+rowCount D k ≤ n ∨ (2*rowCount D i=n+1 ∧ 2*rowCount D k=n+1).", DescribeRole.Theorem),
            Node("row_profile_three_free", "row profile three free", "Exact declaration: theorem row_profile_three_free (hn : n%2=1) (D : Finset (Fin m × Fin n)) (hD : IsKIndependent (graph m n) 2 D) (i k l : Fin m) (hik : i.val+1=k.val) (hkl : k.val+1=l.val) : ¬ (0<2*(rowCount D i : ℤ)-n ∧ 0<2*(rowCount D k : ℤ)-n ∧ 0<2*(rowCount D l : ℤ)-n).", DescribeRole.Theorem),
            Node("g", "g", "Exact declaration: def g (p : ℕ) : ℕ.", DescribeRole.Definition),
            Node("rowFormula", "rowFormula", "Exact declaration: def rowFormula (p q : ℕ) : ℕ.", DescribeRole.Definition),
            Node("formula", "formula", "Exact declaration: def formula (p q : ℕ) : ℕ.", DescribeRole.Definition),
            Node("odd_width_bound", "odd width bound", "Exact declaration: theorem odd_width_bound (hn : n%2=1) (D : Finset (Fin m × Fin n)) (hD : IsKIndependent (graph m n) 2 D) : D.card ≤ formula m n.", DescribeRole.Theorem),
            Node("selection_bound", "selection bound", "Exact declaration: theorem selection_bound (D : Finset (Fin m × Fin n)) (hD : IsKIndependent (graph m n) 2 D) : D.card ≤ formula m n.", DescribeRole.Theorem),
            Node("beta_bound", "beta bound", "Exact declaration: theorem beta_bound : beta (graph m n) 2 ≤ formula m n.", DescribeRole.Theorem),
            Node("chosen", "chosen", "Exact declaration: def chosen (p q : ℕ) : Finset (Fin p × Fin q).", DescribeRole.Definition),
            Node("chosen_dissociation", "chosen dissociation", "Exact declaration: theorem chosen_dissociation : IsKIndependent (graph m n) 2 (chosen m n).", DescribeRole.Theorem),
            Node("chosen_card", "chosen card", "Exact declaration: theorem chosen_card : (chosen m n).card=rowFormula m n.", DescribeRole.Theorem),
            Node("transpose", "transpose", "Exact declaration: def transpose : graph m n ≃g graph n m.", DescribeRole.Definition),
            Node("formula_le_beta", "formula le beta", "Exact declaration: theorem formula_le_beta : formula m n ≤ beta (graph m n) 2.", DescribeRole.Theorem),
            Node("beta_exact", "beta exact", "Exact declaration: theorem beta_exact : beta (graph m n) 2=formula m n.", DescribeRole.Theorem)), []));
}
