using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PureState;

internal sealed class BargmannRealRephasingDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/PureState/BargmannRealRephasing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Hermitian matrix with a nonvanishing row is real up to phases iff triples are real.",
        H("Real rephasing and three-point Bargmann products"), Blocks(
            Paragraph(Text(
                "Let G be an N × N complex matrix. Rephasing by real angles θ replaces each entry "
                + "G(i, j) by exp(iθ_i) G(i, j) exp(−iθ_j). When G is the Gram matrix of pure states "
                + "ψ_1, …, ψ_N, the rephased matrix is the Gram matrix of the same states with each "
                + "vector multiplied by a phase, so it describes the same family of rays. The "
                + "three-point cyclic products G(i, j) G(j, k) G(k, i), the third-order Bargmann "
                + "invariants of the family, do not change under rephasing.")),
            Describe.Lean(DescribeId.Create("bargmann-real-rephasing-criterion"),
                DeclarationHandle.Create(Module + "exists_real_rephasing_iff_triple_products_real"),
                H("Real rephasing is detected by triple products"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Quantum/fernandes2024imaginarity"),
                    LibraryNoteRef.Create("D5/L/Quantum/chaturvedi2013nullphase"),
                    LibraryNoteRef.Create("D5/L/HilbertOperators/chien2013projective"),
                    LibraryNoteRef.Create("D5/L/HilbertOperators/oszmaniec2021relational")),
                Blocks(
                    Paragraph(Text(
                        "Let G be a Hermitian N × N complex matrix and i₀ an index with G(i₀, j) ≠ 0 "
                        + "for every j. There are real angles θ such that every entry "
                        + "exp(iθ_i) G(i, j) exp(−iθ_j) has imaginary part zero if and only if "
                        + "G(i, j) G(j, k) G(k, i) has imaginary part zero for all indices i, j and "
                        + "k, repeated indices included.")),
                    Paragraph(Text(
                        "Proof: the phases cancel around a triangle, so each cyclic product of G "
                        + "equals the corresponding product of three rephased entries; a product of "
                        + "three real numbers is real. This direction uses no hypothesis on G. "
                        + "Conversely, take i₀ as a base and θ_j = arg G(i₀, j). Then "
                        + "exp(iθ_i) = G(i₀, i)/|G(i₀, i)| and exp(−iθ_j) = conj G(i₀, j)/|G(i₀, j)| "
                        + "= G(j, i₀)/|G(i₀, j)| by the Hermitian symmetry, so the rephased entry at "
                        + "(i, j) is G(i₀, i) G(i, j) G(j, i₀) divided by the positive number "
                        + "|G(i₀, i)| |G(i₀, j)|, which is real by hypothesis. Entries of G outside "
                        + "row i₀ and column i₀ may vanish; a zero entry stays zero.")),
                    Paragraph(Text(
                        "The Hermitian symmetry cannot be dropped: the 1 × 1 matrix with entry "
                        + "exp(2πi/3) has a real cube but stays non-real under every rephasing, "
                        + "since rephasing does not change diagonal entries. The nonvanishing row "
                        + "cannot be dropped entirely either. Take N = 4 and G equal to the identity "
                        + "plus 1/4 times the adjacency of the 4-cycle 0, 1, 2, 3, with "
                        + "G(0, 1) = G(1, 2) = G(2, 3) = 1/4 and G(3, 0) = i/4, completed "
                        + "Hermitian. Every row of this G contains a zero entry, so no index i₀ "
                        + "satisfies the row hypothesis. Its eigenvalues are 1 ± (1/2)cos(π/8) and 1 ± (1/2)sin(π/8), "
                        + "so it is positive definite. Every triple product is real: on three "
                        + "distinct indices it vanishes, and with a repeated index it is "
                        + "|G(i, j)|² G(i, i) or G(i, i)³. The 4-cycle product "
                        + "G(0, 1) G(1, 2) G(2, 3) G(3, 0) = i/256 is unchanged by rephasing and "
                        + "not real, so no real rephasing exists. Other overlap patterns, "
                        + "including the chordal case, are not treated here.")),
                    Paragraph(Text(
                        "Fernandes, Wagner, Novo and Galvão, and Oszmaniec, Brod and Galvão, use "
                        + "the gauge invariance of Bargmann invariants to witness the imaginarity "
                        + "of a set of states by a non-real invariant; Fernandes et al. also give, "
                        + "for three states with nonzero overlaps, a gauge in which the only "
                        + "remaining phase is the three-state cyclic phase. The base-index gauge is "
                        + "the anchor lift of Chaturvedi et al. for positive three-state invariants, "
                        + "and the gauge used by Chien and Waldron to show that triple products "
                        + "determine a family with all overlaps nonzero up to projective unitary "
                        + "equivalence; their n-cycle example is the analogue, for projective "
                        + "unitary equivalence, of the failure of triple products without a "
                        + "nonvanishing pattern. The N-state statement above was "
                        + "not found verbatim in these four sources; no novelty is claimed."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bargmann-real-gram-realization"),
                DeclarationHandle.Create(
                    Module + "exists_real_gram_rephasing_iff_triple_products_real"),
                H("Real Gram realization up to phases"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Quantum/fernandes2024imaginarity"),
                    LibraryNoteRef.Create("D5/L/Quantum/chaturvedi2013nullphase"),
                    LibraryNoteRef.Create("D5/L/HilbertOperators/chien2013projective"),
                    LibraryNoteRef.Create("D5/L/HilbertOperators/oszmaniec2021relational")),
                Blocks(
                    Paragraph(Text(
                        "Let G be a positive semidefinite N × N complex matrix and i₀ an index with "
                        + "G(i₀, j) ≠ 0 for every j. There are real angles θ and a real N × N matrix B with "
                        + "exp(iθ_i) G(i, j) exp(−iθ_j) = (Bᵀ B)(i, j) for all i and j if and only if "
                        + "every cyclic product G(i, j) G(j, k) G(k, i) is real. Equivalently, the "
                        + "columns b_1, …, b_N of B are vectors in ℝ^N whose real inner products "
                        + "⟨b_i, b_j⟩ reproduce the rephased matrix. When G is the Gram matrix of pure "
                        + "states, passing from this to real amplitudes for the original rays uses "
                        + "the standard fact that a family is determined up to an isometry of its "
                        + "span by its Gram matrix; that step is not formalized here.")),
                    Paragraph(Text(
                        "Proof: a positive semidefinite matrix is Hermitian, so the previous "
                        + "theorem supplies angles θ making the rephased matrix real exactly when "
                        + "the cyclic products are real. The rephased matrix is D G D* with D the "
                        + "unitary diagonal matrix of the phases exp(iθ_i), hence positive "
                        + "semidefinite. Its entries are real, so its real part R is a real "
                        + "symmetric matrix, and for a real vector x the number xᵀ R x is the value "
                        + "of the complex quadratic form at x, hence nonnegative. A positive "
                        + "semidefinite real matrix has the form Bᵀ B with B real. The converse "
                        + "direction holds because the rephased entries (Bᵀ B)(i, j) are real.")),
                    Paragraph(Text(
                        "The real vectors live in ℝ^N; nothing is claimed about realizations in "
                        + "lower dimension, about qubits or Bloch vectors, or about overlap "
                        + "patterns without a nonvanishing row."))),
                DescribeRole.Theorem))));
}
