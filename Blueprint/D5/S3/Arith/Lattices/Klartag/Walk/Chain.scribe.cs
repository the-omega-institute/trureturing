using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Walk;

internal sealed class ChainDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Walk/Chain.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian matrix walk, filtration and stopped increments.",
        H("Chain"),
        Blocks(
            Paragraph(Text("Gaussian matrix walk, filtration and stopped increments. The results below relate chain to the stochastic ellipsoid construction.")),
            Node("claim-1", "kSet", "k Set",
                "kSet q W = {A | ∀ i ∈ W, 1 ≤ ⟪A, q i⟫}. With q x = x ⊗ x this is Klartag's set of L-free matrices (p. 6, eq. 9): E_A = {x | ⟪A x, x⟫ < 1} misses every x with q x a constraint.", DescribeRole.Definition),
            Node("claim-2", "q_ne_zero_of_nonempty", "q ne zero of nonempty",
                "If K_L is nonempty then no constraint vector vanishes (⟪A, 0⟫ = 0 < 1).", DescribeRole.Theorem),
            Node("claim-3", "IsProjOn", "Is Proj On",
                "p is *the* projection of u onto K: p ∈ K and K lies in the half-space through p orthogonal to u - p.", DescribeRole.Definition),
            Node("claim-5", "eq", "eq",
                "The projection onto a convex set is unique.", DescribeRole.Theorem),
            Node("claim-6", "freeSub", "free Sub",
                "The free subspace F(C) = {B | ∀ i ∈ C, ⟪B, q i⟫ = 0} (Klartag eq. 13).", DescribeRole.Definition),
            Node("claim-7", "freeSub_eq_orthogonal", "free Sub eq orthogonal",
                "F(C) is the orthogonal complement of the span of the active constraints.", DescribeRole.Theorem),
            Node("claim-8", "finrank_freeSub_ge", "finrank free Sub ge",
                "dim F(C) ≥ dim E - |q(C)|: Klartag's N_t ≥ n(n+1)/2 - |∂E_t ∩ L|/2 (p. 16). Counting the *image* q '' C rather than C itself is what supplies the paper's factor 1/2, since q x = x ⊗ x = q (-x) identifies the antipodal pairs of contact points.", DescribeRole.Theorem),
            Node("claim-9", "finrank_freeSub_ge_card", "finrank free Sub ge card",
                "The crude form of finrank_freeSub_ge, without the antipodal saving.", DescribeRole.Theorem),
            Node("claim-10", "violated", "violated",
                "The window constraints broken by A'.", DescribeRole.Definition),
            Node("claim-13", "lift", "lift",
                "The one-sided lift back into K_L: move along the broken constraints only, each by exactly the amount that makes it tight.", DescribeRole.Definition),
            Node("claim-15", "lift_mem_kSet", "lift mem k Set",
                "The lift lands in K_L. The only structural input is non-negative correlation of the constraint vectors, 0 ≤ ⟪q i, q j⟫ — true for q x = x ⊗ x, where it is (x ⬝ᵥ y)² ≥ 0.", DescribeRole.Theorem),
            Node("claim-16", "stepTo", "step To",
                "One step of the chain: Gaussian increment inside the free subspace, then the lift, then the newly broken constraints are adjoined to the active set.", DescribeRole.Definition),
            Node("claim-17", "chain", "chain",
                "The chain (A_k, C_k), driven by an arbitrary sequence ξ. Klartag's Proposition 2.3.", DescribeRole.Definition),
            Node("claim-19", "chain_fst_mem_kSet", "chain fst mem k Set",
                "A_k ∈ K_L for every k (Klartag Proposition 2.3(C), the L-free half).", DescribeRole.Theorem),
            Node("claim-20", "chain_snd_subset_succ", "chain snd subset succ",
                "The active set only grows (Klartag Proposition 2.3(D)).", DescribeRole.Theorem),
            Node("claim-23", "freeDim", "free Dim",
                "N_k = dim F(C_k), Klartag's N_t (p. 13, eq. 39).", DescribeRole.Definition),
            Node("claim-24", "newActive", "new Active",
                "V_{k+1}: the constraints newly broken at step k.", DescribeRole.Definition),
            Node("claim-26", "violated_disjoint", "violated disjoint",
                "A step breaks no already-active constraint.", DescribeRole.Theorem),
            Node("claim-28", "card_chain_snd_succ", "card chain snd succ",
                "The active set grows by exactly the size of the new block.", DescribeRole.Theorem),
            Node("claim-29", "sum_card_newActive", "sum card new Active",
                "∑_{k<m} |V_k| = |C_m| — the number of terms in the discretisation-error sum.", DescribeRole.Theorem),
            Node("claim-30", "measurableSet_filter_eq", "measurable Set filter eq",
                "A Finset-valued filter of measurable predicates is measurable.", DescribeRole.Theorem),
            Node("claim-32", "lift_eq_sum_window", "lift eq sum window",
                "The lift, written as a sum over the whole window: this is the form measurability uses.", DescribeRole.Theorem),
            Node("claim-35", "measurable_chain", "measurable chain",
                "Adaptedness. If ξ k is m (k+1)-measurable along a monotone family of σ-algebras, then (A_k, C_k) is m k-measurable — Klartag Proposition 2.3's \"adapted to the filtration\".", DescribeRole.Theorem),
            Node("claim-37", "measurable_chain_fst", "measurable chain fst",
                "A_k is measurable.", DescribeRole.Theorem),
            Node("claim-38", "measurableSet_mem_active", "measurable Set mem active",
                "{ω | i ∈ C_k ω} is measurable — the form the contact-count expectation E |C_N| = ∑_i P(i ∈ C_N) consumes.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
