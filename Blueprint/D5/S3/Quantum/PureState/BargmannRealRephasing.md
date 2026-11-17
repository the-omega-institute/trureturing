# Real rephasing and three-point Bargmann products

## Abstract

Nonvanishing Hermitian matrices are real up to rephasing iff triple products are real.

Let G be an N × N complex matrix. Rephasing by real angles θ replaces each entry G(i, j) by exp(iθ_i) G(i, j) exp(−iθ_j). When G is the Gram matrix of pure states ψ_1, …, ψ_N, the rephased matrix is the Gram matrix of the same states with each vector multiplied by a phase, so it describes the same family of rays. The three-point cyclic products G(i, j) G(j, k) G(k, i), the third-order Bargmann invariants of the family, do not change under rephasing.

**Theorem 1.1 (Real rephasing is detected by triple products).**

Lean statement: `D5/S3/Quantum/PureState/BargmannRealRephasing.exists_real_rephasing_iff_triple_products_real`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/BargmannRealRephasing.exists_real_rephasing_iff_triple_products_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Carlos Fernandes, Rafael Wagner, Leonardo Novo, Ernesto F. Galvão (2024). *Unitary-invariant witnesses of quantum imaginarity*. URL: <https://arxiv.org/abs/2403.15066v1>.

*Commentary.*

Let G be a Hermitian N × N complex matrix with G(i, j) ≠ 0 for all i and j. There are real angles θ such that every entry exp(iθ_i) G(i, j) exp(−iθ_j) has imaginary part zero if and only if G(i, j) G(j, k) G(k, i) has imaginary part zero for all indices i, j and k, repeated indices included.

Proof: the phases cancel around a triangle, so each cyclic product of G equals the corresponding product of three rephased entries; a product of three real numbers is real. Conversely, for N ≥ 1 take index 0 as a base and θ_j = arg G(0, j). Then exp(iθ_i) = G(0, i)/|G(0, i)| and exp(−iθ_j) = conj G(0, j)/|G(0, j)| = G(j, 0)/|G(0, j)| by the Hermitian symmetry, so the rephased entry at (i, j) is G(0, i) G(i, j) G(j, 0) divided by the positive number |G(0, i)| |G(0, j)|, which is real by hypothesis. For N = 0 there is nothing to prove.

Every hypothesis is needed. Without the Hermitian symmetry the 1 × 1 matrix with entry exp(2πi/3) has real cube but stays non-real under every rephasing. The nonvanishing of all entries is what lets a single base index reach every pair; for families with orthogonal pairs, real triangles need not suffice, and longer cycles of nonzero overlaps carry further phase invariants. Such overlap patterns, including the chordal case, are not treated here.

Fernandes, Wagner, Novo and Galvão use the gauge invariance of Bargmann invariants to witness the imaginarity of a set of states by a non-real invariant, and display for three states with nonzero overlaps a gauge in which the only remaining phase is the three-state cyclic phase; that is the forward direction and the three-state case of the converse. A verbatim source for the N-state statement was not found; no novelty is claimed.

**Theorem 1.2 (Real Gram realization up to phases).**

Lean statement: `D5/S3/Quantum/PureState/BargmannRealRephasing.exists_real_gram_rephasing_iff_triple_products_real`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/BargmannRealRephasing.exists_real_gram_rephasing_iff_triple_products_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Carlos Fernandes, Rafael Wagner, Leonardo Novo, Ernesto F. Galvão (2024). *Unitary-invariant witnesses of quantum imaginarity*. URL: <https://arxiv.org/abs/2403.15066v1>.

*Commentary.*

Let G be a positive semidefinite N × N complex matrix with G(i, j) ≠ 0 for all i and j. There are real angles θ and a real N × N matrix B with exp(iθ_i) G(i, j) exp(−iθ_j) = (Bᵀ B)(i, j) for all i and j if and only if every cyclic product G(i, j) G(j, k) G(k, i) is real. Equivalently, the columns b_1, …, b_N of B are vectors in ℝ^N whose real inner products ⟨b_i, b_j⟩ reproduce the rephased matrix; when G is the Gram matrix of pure states, the same rays are then described by real amplitudes.

Proof: a positive semidefinite matrix is Hermitian, so the previous theorem supplies angles θ making the rephased matrix real exactly when the cyclic products are real. The rephased matrix is D G D* with D the unitary diagonal matrix of the phases exp(iθ_i), hence positive semidefinite. Its entries are real, so its real part R is a real symmetric matrix, and for a real vector x the number xᵀ R x is the value of the complex quadratic form at x, hence nonnegative. A positive semidefinite real matrix has the form Bᵀ B with B real. The converse direction holds because the rephased entries (Bᵀ B)(i, j) are real.

The real vectors live in ℝ^N; nothing is claimed about realizations in lower dimension, about qubits or Bloch vectors, or about families with vanishing overlaps.

## References

- Truth anchor: `D5/S3/Quantum/PureState/BargmannRealRephasing.exists_real_gram_rephasing_iff_triple_products_real`
- Truth anchor: `D5/S3/Quantum/PureState/BargmannRealRephasing.exists_real_rephasing_iff_triple_products_real`
