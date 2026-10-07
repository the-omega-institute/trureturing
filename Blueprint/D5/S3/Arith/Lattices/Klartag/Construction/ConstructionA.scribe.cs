using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Construction;

internal sealed class ConstructionADocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Construction/ConstructionA.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Construction A lattices, covolumes and ellipsoid transfer.",
        H("Construction A"),
        Blocks(
            Paragraph(Text("Construction A lattices, covolumes and ellipsoid transfer. The results below relate construction a to the stochastic ellipsoid construction.")),
            Node("claim-1", "redMod", "red Mod",
                "Coordinatewise reduction ℤⁿ → (ZMod p)ⁿ.", DescribeRole.Definition),
            Node("claim-2", "OnLine", "On Line",
                "Construction A with k = 1: the residue v lies on the line C_g = ⟨g⟩.", DescribeRole.Definition),
            Node("claim-4", "card_filter_onLine", "card filter on Line",
                "The line count. A nonzero residue lies on exactly p - 1 lines ⟨g⟩.", DescribeRole.Theorem),
            Node("claim-5", "sum_card_filter_onLine", "sum card filter on Line",
                "First-moment lemma (exact form). Summing over *all* g, the total number of incidences between a finite set A of p-indivisible integer points and the lines ⟨g⟩ is exactly (p - 1) * |A|. This is the swap of two finite sums.", DescribeRole.Theorem),
            Node("claim-6", "sum_card_filter_onLine_erase", "sum card filter on Line erase",
                "The g = 0 line carries no p-indivisible point, so the sum over g ≠ 0 is the same.", DescribeRole.Theorem),
            Node("claim-8", "sum_card_le", "sum card le",
                "The density bound, division-free. p^{n-1} · Σ_{g≠0} (count) ≤ (pⁿ - 1) · |A|, i.e. the average over the pⁿ - 1 nonzero g is at most |A| · p^{1-n}.", DescribeRole.Theorem),
            Node("claim-9", "exists_mem_not_mem", "exists mem not mem",
                "The union bound / selection step (1/2 + 1/e < 1): if the two bad sets together miss some element of s, a good g exists.", DescribeRole.Theorem),
            Node("claim-10", "le_abs_of_dvd", "le abs of dvd",
                "A nonzero integer point all of whose coordinates are divisible by p has a coordinate of absolute value at least p. This is why the pℤⁿ term of the first-moment lemma vanishes identically once p exceeds the radius of the support.", DescribeRole.Theorem),
            Node("claim-11", "card_erase_univ", "card erase univ",
                "The number of nonzero g is pⁿ - 1.", DescribeRole.Theorem),
            Node("claim-12", "card_bad_one_le", "card bad one le",
                "Use 1's Markov step (eq. 64), discrete counterpart. The number of lines meeting the finite set A at all is at most (pⁿ-1)·|A|/p^{n-1}.", DescribeRole.Theorem),
            Node("claim-13", "discreteTopology_of_le", "discrete Topology of le",
                "Generic sublattice criterion (absent from Mathlib). If M ≤ L with L a ℤ-lattice and M ⊇ k · L for some k ≠ 0, then M is a ℤ-lattice.", DescribeRole.Theorem),
            Node("claim-15", "toReal", "to Real",
                "The ℤ-linear inclusion ℤⁿ ↪ ℝⁿ.", DescribeRole.Definition),
            Node("claim-18", "redLin", "red Lin",
                "Coordinatewise reduction ℤⁿ → (ZMod p)ⁿ, as a ℤ-linear map.", DescribeRole.Definition),
            Node("claim-21", "lineZ", "line Z",
                "The p-ary line C_g = ⟨g⟩, as a ℤ-submodule.", DescribeRole.Definition),
            Node("claim-22", "latZ", "lat Z",
                "Construction A in ℤⁿ: Λ₀(g) = {y ∈ ℤⁿ : y mod p ∈ ⟨g⟩}.", DescribeRole.Definition),
            Node("claim-24", "smul_mem_latZ", "smul mem lat Z",
                "Λ₀(g) contains p·ℤⁿ.", DescribeRole.Theorem),
            Node("claim-25", "intLat", "int Lat",
                "The standard integer lattice in ℝⁿ.", DescribeRole.Definition),
            Node("claim-27", "latR", "lat R",
                "Construction A in ℝⁿ: Λ(g) = {x ∈ ℤⁿ : x mod p ∈ ⟨g⟩} ⊆ ℝⁿ.", DescribeRole.Definition),
            Node("claim-33", "index_latZ", "index lat Z",
                "The index of Construction A in ℤⁿ is p^{n-1}.", DescribeRole.Theorem),
            Node("claim-34", "toRealEquiv", "to Real Equiv",
                "toReal as a ℤ-linear equivalence onto the standard integer lattice of ℝⁿ.", DescribeRole.Definition),
            Node("claim-38", "relIndex_latR", "rel Index lat R",
                "The relative index of Λ(g) in ℤⁿ ⊆ ℝⁿ is p^{n-1}.", DescribeRole.Theorem),
            Node("claim-39", "intLatBasis", "int Lat Basis",
                "A ℤ-basis of the standard integer lattice of ℝⁿ.", DescribeRole.Definition),
            Node("claim-41", "covolume_latR", "covolume lat R",
                "The covolume of Construction A. covol Λ(g) = p^{n-1}.", DescribeRole.Theorem),
            Node("claim-42", "mem_latZ_iff_onLine", "mem lat Z iff on Line",
                "Membership in Construction A is exactly the incidence relation counted above.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
