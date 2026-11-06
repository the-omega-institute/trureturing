/- GID: D5/S3/Quantum/Tomography/KanachovaLiuTuPureStateDetection
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/KanachovaLiuTuPureStateDetection
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Entangled qubit-qutrit pure states have negative reconstructed eigenvalues. -/

/-
admission_basis: open-problem-resolution (#22252; Proved)
escape_witness: none
proof_shape: expectation_identity: bind-only; consumer: result.
proof_shape: product_of_minors_zero: bind-only; consumer: delta_pos.
proof_shape: delta_pos: bind-only; consumer: result.
proof_shape: measured_hermitian: bind-only; consumer: result.
proof_shape: negative_eigenpair: bind-only; consumer: result.
proof_shape: result: bind-only; settling result.
Direct frozen dependencies (same-module helpers expanded):
R = D5/S3/Quantum/PureState/PureStateHandshake.rankOneDensity,
    statement_id sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3.
P = D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite.partialTranspose,
    statement_id sha256:a32d36fcfc6230cb476603467a27ba53eff6b9eb11958a19179f2695906e3df1.
H = D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPureBound.pt_rank_hermitian,
    statement_id sha256:02a7f49ee0e696f31804829cb0c0452a9b0f778a33261730f85f14d48f183561.
U: none; localConjugation: none; measured: P; claim: R, P; eta: none; delta: none.
expectation_identity: R, P; product_of_minors_zero: none; delta_pos: none.
measured_hermitian: R, P, H; negative_eigenpair: none; result: R, P, H.
U, localConjugation and measured use Eq. (3) and Eqs. (S18)-(S19).
The qubit index comes first; qutrit indices 0, 1, 2 denote +1, 0, -1.
The normalized non-product hypothesis and explicit real eigenpair are those of #22252.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22682
-/

import D5.S3.Quantum.PureState.PureStateHandshake
import D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite
import D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound

noncomputable section

namespace D5.S3.Quantum.Tomography.KanachovaLiuTuPureStateDetection

open Matrix
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite (partialTranspose)

/-- Eq. (S18): U in the ordered meson basis |+1⟩, |0⟩, |-1⟩. -/
def U : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, -1; 0, 1, 0; -1, 0, 0]

/-- The source's local unitary conjugation 𝒰_B. -/
def localConjugation
    (ρ : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ) :
    Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ :=
  let K := Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) U
  K * ρ * K.conjTranspose

/-- Eq. (3): the measured reconstruction, using the canonical second-factor PT. -/
def measured
    (ρ : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ) :
    Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ :=
  (1 / 2 : ℂ) • (ρ + localConjugation (partialTranspose ρ))

/-- Every normalized non-product pure vector gives a measured reconstruction
with a negative real eigenvalue. The conclusion is an eigenpair, not merely a
negative expectation or the negation of positive semidefiniteness. -/
def claim : Prop :=
  ∀ ψ : Fin 2 × Fin 3 → ℂ,
    star ψ ⬝ᵥ ψ = 1 →
    (¬ ∃ (a : Fin 2 → ℂ) (b : Fin 3 → ℂ),
      ∀ (i : Fin 2) (j : Fin 3), ψ (i, j) = a i * b j) →
    ∃ (eigenvalue : ℝ) (w : Fin 2 × Fin 3 → ℂ),
      eigenvalue < 0 ∧ w ≠ 0 ∧ measured (rankOneDensity ψ) *ᵥ w = (eigenvalue : ℂ) • w

open scoped ComplexOrder
private def eta (ψ : Fin 2 × Fin 3 → ℂ) : Fin 2 × Fin 3 → ℂ :=
  fun p => ![![-star (ψ (1, 2)), star (ψ (1, 1)), -star (ψ (1, 0))],
    ![star (ψ (0, 2)), -star (ψ (0, 1)), star (ψ (0, 0))]] p.1 p.2

private def delta (ψ : Fin 2 × Fin 3 → ℂ) : ℝ :=
  Complex.normSq (ψ (0, 0) * ψ (1, 1) - ψ (0, 1) * ψ (1, 0)) +
    Complex.normSq (ψ (0, 0) * ψ (1, 2) - ψ (0, 2) * ψ (1, 0)) +
    Complex.normSq (ψ (0, 1) * ψ (1, 2) - ψ (0, 2) * ψ (1, 1))

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private theorem expectation_identity (ψ : Fin 2 × Fin 3 → ℂ) :
    star (eta ψ) ⬝ᵥ (measured (rankOneDensity ψ) *ᵥ eta ψ) = -(delta ψ : ℂ) := by
  simp [measured, localConjugation, U, rankOneDensity, partialTranspose,
    Matrix.mulVec, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.vecMulVec_apply, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ,
    eta, delta, Complex.normSq_eq_conj_mul_self, Complex.ofReal_add]
  ring

private theorem product_of_minors_zero (ψ : Fin 2 × Fin 3 → ℂ)
    (hm : ∀ j k, (ψ (0, j) * ψ (1, k) - ψ (0, k) * ψ (1, j)) = 0) :
    ∃ (a : Fin 2 → ℂ) (b : Fin 3 → ℂ), ∀ i j, ψ (i, j) = a i * b j := by
  classical
  by_cases hu : ∀ j, ψ (0, j) = 0
  · refine ⟨![0, 1], fun j => ψ (1, j), ?_⟩
    intro i j
    fin_cases i <;> simp [hu]
  · push Not at hu
    obtain ⟨j, hj⟩ := hu
    refine ⟨![1, ψ (1, j) / ψ (0, j)], fun k => ψ (0, k), ?_⟩
    intro i k
    fin_cases i
    · simp
    · change ψ (1, k) = (ψ (1, j) / ψ (0, j)) * ψ (0, k)
      rw [div_mul_eq_mul_div]
      apply (eq_div_iff hj).2
      simpa [mul_comm] using sub_eq_zero.mp (hm j k)

private theorem delta_pos (ψ : Fin 2 × Fin 3 → ℂ)
    (hent : ¬ ∃ (a : Fin 2 → ℂ) (b : Fin 3 → ℂ),
      ∀ i j, ψ (i, j) = a i * b j) : 0 < delta ψ := by
  have h01 := Complex.normSq_nonneg ((ψ (0, 0) * ψ (1, 1) - ψ (0, 1) * ψ (1, 0)))
  have h02 := Complex.normSq_nonneg ((ψ (0, 0) * ψ (1, 2) - ψ (0, 2) * ψ (1, 0)))
  have h12 := Complex.normSq_nonneg ((ψ (0, 1) * ψ (1, 2) - ψ (0, 2) * ψ (1, 1)))
  have hd : 0 ≤ delta ψ := add_nonneg (add_nonneg h01 h02) h12
  by_contra hn
  have hz : delta ψ = 0 := le_antisymm (le_of_not_gt hn) hd
  have hz01 : (ψ (0, 0) * ψ (1, 1) - ψ (0, 1) * ψ (1, 0)) = 0 :=
    Complex.normSq_eq_zero.mp (by dsimp [delta] at hz; linarith)
  have hz02 : (ψ (0, 0) * ψ (1, 2) - ψ (0, 2) * ψ (1, 0)) = 0 :=
    Complex.normSq_eq_zero.mp (by dsimp [delta] at hz; linarith)
  have hz12 : (ψ (0, 1) * ψ (1, 2) - ψ (0, 2) * ψ (1, 1)) = 0 :=
    Complex.normSq_eq_zero.mp (by dsimp [delta] at hz; linarith)
  apply hent
  apply product_of_minors_zero ψ
  intro j k
  apply sub_eq_zero.mpr
  fin_cases j <;> fin_cases k
  all_goals first | rfl | exact sub_eq_zero.mp hz01 | exact (sub_eq_zero.mp hz01).symm |
    exact sub_eq_zero.mp hz02 | exact (sub_eq_zero.mp hz02).symm |
    exact sub_eq_zero.mp hz12 | exact (sub_eq_zero.mp hz12).symm

private theorem measured_hermitian (ψ : Fin 2 × Fin 3 → ℂ) :
    (measured (rankOneDensity ψ)).IsHermitian := by
  have hr : (rankOneDensity ψ).IsHermitian :=
    (Matrix.posSemidef_vecMulVec_self_star ψ).isHermitian
  have ht : (partialTranspose (rankOneDensity ψ)).IsHermitian := by
    exact (D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound.pt_rank_hermitian ψ).transpose
  exact (hr.add (Matrix.isHermitian_mul_mul_conjTranspose _ ht)).smul (by
    simp [IsSelfAdjoint])

private theorem negative_eigenpair {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (z : n → ℂ)
    (hz : (star z ⬝ᵥ (A *ᵥ z)).re < 0) :
    ∃ (t : ℝ) (w : n → ℂ), t < 0 ∧ w ≠ 0 ∧ A *ᵥ w = (t : ℂ) • w := by
  classical
  have hnpsd : ¬ A.PosSemidef := by
    intro hp
    exact (not_lt_of_ge (hp.re_dotProduct_nonneg z)) hz
  have hi : ∃ i, hA.eigenvalues i < 0 := by
    by_contra h
    push Not at h
    exact hnpsd (hA.posSemidef_iff_eigenvalues_nonneg.mpr h)
  obtain ⟨i, hi⟩ := hi
  refine ⟨hA.eigenvalues i, (hA.eigenvectorBasis i : n → ℂ), hi, ?_, ?_⟩
  · exact (WithLp.ofLp_eq_zero 2).ne.2 (hA.eigenvectorBasis.orthonormal.ne_zero i)
  · exact hA.mulVec_eigenvectorBasis i

theorem result : claim := by
  intro ψ _hnorm hent
  apply negative_eigenpair _ (measured_hermitian ψ) (eta ψ)
  rw [expectation_identity]
  simpa using neg_neg_of_pos (delta_pos ψ hent)

end D5.S3.Quantum.Tomography.KanachovaLiuTuPureStateDetection
