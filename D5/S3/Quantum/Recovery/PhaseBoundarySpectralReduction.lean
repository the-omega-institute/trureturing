/- GID: D5/S3/Quantum/Recovery/PhaseBoundarySpectralReduction
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PhaseBoundarySpectralReduction
   mirror-E: none(waiver:research-interface)
   anchors: []
   utility: none
   digest: Pure-reference recovery error and rank-one spectral inertia. -/
import D5.S3.Quantum.Recovery.PhaseBoundarySourceModel
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Tactic

noncomputable section
namespace D5.S3.Quantum.Recovery.PhaseBoundarySpectralReduction
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Recovery.PhaseBoundarySourceModel
open Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000

private theorem rank_one_sub_hermitian {n : Type*} [Fintype n] [DecidableEq n]
    (v : n → ℂ) {B : Matrix n n ℂ} (hB : B.PosSemidef) :
    (vecMulVec v (star v) - B).IsHermitian :=
  (posSemidef_vecMulVec_self_star v).isHermitian.sub hB.isHermitian

private theorem quadratic_nonpositive_on_perp {n : Type*} [Fintype n]
    (v : n → ℂ) {B : Matrix n n ℂ} (hB : B.PosSemidef)
    (x : n → ℂ) (hx : star v ⬝ᵥ x = 0) :
    (star x ⬝ᵥ ((vecMulVec v (star v) - B) *ᵥ x)).re ≤ 0 := by
  have hp := (Complex.nonneg_iff.mp (hB.dotProduct_mulVec_nonneg x)).1
  rw [Matrix.sub_mulVec, Matrix.vecMulVec_mulVec, hx]
  simpa using neg_nonpos.mpr hp

/-- A rank-one positive update of a negative semidefinite matrix has at most
one strictly positive eigenvalue, counted with multiplicity. -/
theorem positive_eigenvalues_unique {n : Type*} [Fintype n] [DecidableEq n]
    (v : n → ℂ) {B : Matrix n n ℂ} (hB : B.PosSemidef)
    (i j : n)
    (hi : 0 < (rank_one_sub_hermitian v hB).eigenvalues i)
    (hj : 0 < (rank_one_sub_hermitian v hB).eigenvalues j) : i = j := by
  classical
  by_contra hij
  let A := vecMulVec v (star v) - B
  let hA : A.IsHermitian := rank_one_sub_hermitian v hB
  let e : n → n → ℂ := fun k => ⇑(hA.eigenvectorBasis k)
  have he (k l : n) : star (e k) ⬝ᵥ e l = if k = l then 1 else 0 := by
    change star (⇑(hA.eigenvectorBasis k)) ⬝ᵥ ⇑(hA.eigenvectorBasis l) = _
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
    exact orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal k l
  have hAe (k : n) : A *ᵥ e k = (hA.eigenvalues k : ℂ) • e k :=
    hA.mulVec_eigenvectorBasis k
  let a := star v ⬝ᵥ e i
  let b := star v ⬝ᵥ e j
  have ha : a ≠ 0 := by
    intro ha
    have hh := quadratic_nonpositive_on_perp v hB (e i) ha
    change (star (e i) ⬝ᵥ (A *ᵥ e i)).re ≤ 0 at hh
    rw [hAe, dotProduct_smul, he] at hh
    have hh' : hA.eigenvalues i ≤ 0 := by simpa using hh
    exact (not_le_of_gt hi) hh'
  let x := b • e i - a • e j
  have hx : star v ⬝ᵥ x = 0 := by
    simp only [x, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    change b * a - a * b = 0
    ring
  have hnonpos := quadratic_nonpositive_on_perp v hB x hx
  have hquad : star x ⬝ᵥ (A *ᵥ x) =
      (hA.eigenvalues i : ℂ) * (Complex.normSq b : ℂ) +
        (hA.eigenvalues j : ℂ) * (Complex.normSq a : ℂ) := by
    simp only [x, Matrix.mulVec_sub, Matrix.mulVec_smul, hAe,
      star_sub, star_smul, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, he, hij, Ne.symm hij,
      if_true, if_false, mul_one, mul_zero, sub_zero, zero_sub]
    simp only [Complex.normSq_eq_conj_mul_self, Complex.star_def]
    ring
  change (star x ⬝ᵥ (A *ᵥ x)).re ≤ 0 at hnonpos
  rw [hquad] at hnonpos
  have hpos : 0 < hA.eigenvalues i * Complex.normSq b +
      hA.eigenvalues j * Complex.normSq a :=
    add_pos_of_nonneg_of_pos (mul_nonneg hi.le (Complex.normSq_nonneg b))
      (mul_pos hj (Complex.normSq_pos.mpr ha))
  have hr : (hA.eigenvalues i * Complex.normSq b +
      hA.eigenvalues j * Complex.normSq a : ℝ) ≤ 0 := by
    simpa using hnonpos
  exact (not_le_of_gt hpos) hr

/-
Copyright (c) 2026 QuAIR. Authors: QuAIR Team.
Released under Apache 2.0; full license: docs/reports/recordtimebound/Lean-QIT-LICENSE.txt.
The positive-part trace primitive is from QIT/States/TraceNorm/PositivePart.lean,
revision 15a0a5ef13e5824327e0850ea896e472366287af, with its local real-part helper
inlined and the repository's matrix notation. No NOTICE is present at that revision.
This primitive is replaced by direct application when the repository's pinned
Mathlib contains the equivalent positive-part trace theorem.
-/
private theorem positive_part_trace {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    (posPart A).trace.re = ∑ i, if 0 < hA.eigenvalues i then hA.eigenvalues i else 0 := by
  rw [CFC.posPart_def, cfcₙ_eq_cfc, hA.cfc_eq, Matrix.IsHermitian.cfc,
    Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.one_mul]
  have hr (x : ℝ) : posPart x = if 0 < x then x else 0 := by
    by_cases hx : 0 < x
    · simp [posPart_def, hx, max_eq_left hx.le]
    · simp [posPart_def, hx, max_eq_right (le_of_not_gt hx)]
  simp [Matrix.trace, hr]

/-- For a trace-zero rank-one-minus-positive difference, the half trace norm
is its largest eigenvalue. No strict positivity or invertibility is required. -/
theorem rank_one_half_trace_norm {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (v : n → ℂ) {B : Matrix n n ℂ} (hB : B.PosSemidef)
    (htr : (vecMulVec v (star v) - B).trace = 0) :
    IsGreatest (Set.range (rank_one_sub_hermitian v hB).eigenvalues)
      (traceNorm (vecMulVec v (star v) - B) / 2) := by
  classical
  let A := vecMulVec v (star v) - B
  let hA : A.IsHermitian := rank_one_sub_hermitian v hB
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image (Finset.univ : Finset n)
    hA.eigenvalues Finset.univ_nonempty
  have hzero : ∑ i, hA.eigenvalues i = 0 := by
    have hh := congrArg Complex.re hA.trace_eq_sum_eigenvalues
    rw [htr] at hh
    simpa using hh.symm
  have hnonnegative : 0 ≤ hA.eigenvalues k := by
    by_contra hn
    have hneg : ∑ i, hA.eigenvalues i < 0 :=
      Finset.sum_neg (fun i _ => lt_of_le_of_lt (hk i (Finset.mem_univ i))
        (lt_of_not_ge hn)) Finset.univ_nonempty
    rw [hzero] at hneg
    exact lt_irrefl _ hneg
  have hother (i : n) (hik : i ≠ k) : hA.eigenvalues i ≤ 0 := by
    by_contra hn
    have hi := lt_of_not_ge hn
    have hp := hi.trans_le (hk i (Finset.mem_univ i))
    exact hik (positive_eigenvalues_unique v hB i k hi hp)
  have hsum : (∑ i, if 0 < hA.eigenvalues i then hA.eigenvalues i else 0) =
      hA.eigenvalues k := by
    rw [Finset.sum_eq_single k]
    · split_ifs with hp
      · rfl
      · exact (le_antisymm (le_of_not_gt hp) hnonnegative).symm
    · intro i _ hik
      exact if_neg (not_lt.mpr (hother i hik))
    · simp
  have hmass := trace_norm_jordan_mass A hA
  have hbalance : (posPart A).trace.re = (negPart A).trace.re := by
    have hh := congrArg (fun X : Matrix n n ℂ => X.trace.re)
      (CFC.posPart_sub_negPart A hA)
    rw [htr] at hh
    simpa only [Matrix.trace_sub, Complex.sub_re, Complex.zero_re, sub_eq_zero] using hh
  have hnorm : traceNorm A / 2 = hA.eigenvalues k := by
    rw [hmass, ← hbalance, positive_part_trace A hA, hsum]
    ring
  rw [show traceNorm (vecMulVec v (star v) - B) / 2 = hA.eigenvalues k from hnorm]
  exact ⟨⟨k, rfl⟩, fun x ⟨i, hi⟩ => hi ▸ hk i (Finset.mem_univ i)⟩

/-- The coherent target minus the recovered actual source, on a joint input.
Memory belongs to the output index and is untouched by the decoder. -/
def recoveryDifference {F : Type*} [Fintype F] [DecidableEq F]
    (ell beta gamma : ℝ) (w : Qubit → ℝ)
    (hl : 0 ≤ ell) (hu : ell ≤ 1) (hb : 0 < beta)
    (hw : ∀ j, 0 ≤ w j) (hmax : ∀ j, w j ≤ beta / (beta ^ 2 + gamma ^ 2))
    (D : QuantumChannel (Qubit × Qubit) (Qubit × Qubit))
    (rho : DensityState (F × Qubit)) :
    Matrix (F × (Qubit × (Qubit × Qubit))) (F × (Qubit × (Qubit × Qubit))) ℂ :=
  CStarMatrix.ofMatrix.symm (referenceState (targetChannel ell hl hu) rho).1 -
    CStarMatrix.ofMatrix.symm (referenceState ((receiverChannel (M := Qubit) D).comp
      (sourceChannel ell beta gamma w hl hu hb hw hmax)) rho).1

/-- On every normalized pure input and every finite reference, the half error
of the actual recovery problem is the largest eigenvalue of its output
difference. All CPTP receiver decoders and the boundary `ell = 0` are included. -/
theorem pure_reference_error_eq_top_eigenvalue {F : Type*} [Fintype F] [DecidableEq F]
    (ell beta gamma : ℝ) (w : Qubit → ℝ)
    (hl : 0 ≤ ell) (hu : ell ≤ 1) (hb : 0 < beta)
    (hw : ∀ j, 0 ≤ w j) (hmax : ∀ j, w j ≤ beta / (beta ^ 2 + gamma ^ 2))
    (D : QuantumChannel (Qubit × Qubit) (Qubit × Qubit))
    (v : F × Qubit → ℂ) (hv : star v ⬝ᵥ v = 1) :
    let rho := pureState v hv
    let A := recoveryDifference ell beta gamma w hl hu hb hw hmax D rho
    ∃ hA : A.IsHermitian, IsGreatest (Set.range hA.eigenvalues)
      (referenceError (targetChannel ell hl hu)
        ((receiverChannel (M := Qubit) D).comp
          (sourceChannel ell beta gamma w hl hu hb hw hmax)) rho / 2) := by
  classical
  intro rho A
  let target := referenceState (targetChannel ell hl hu) rho
  let actual := referenceState ((receiverChannel (M := Qubit) D).comp
    (sourceChannel ell beta gamma w hl hu hb hw hmax)) rho
  let t : F × (Qubit × (Qubit × Qubit)) → ℂ := fun p =>
    v (p.1, p.2.2.1) * xi ell (p.2.1, p.2.2.2)
  have ht : CStarMatrix.ofMatrix.symm target.1 = vecMulVec t (star t) := by
    ext ⟨f, m, j, a⟩ ⟨g, n, k, b⟩
    change referenceAction (targetChannel ell hl hu) rho.1
      (f, (m, (j, a))) (g, (n, (k, b))) = _
    rw [target_reference]
    simp only [rho, pureState, CStarMatrix.ofMatrix_apply,
      Matrix.vecMulVec_apply, t, Pi.star_apply, star_mul]
    ring
  let B := CStarMatrix.ofMatrix.symm actual.1
  have hB : B.PosSemidef := Matrix.nonneg_iff_posSemidef.mp
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm actual.2.1)
  have hA : A = vecMulVec t (star t) - B := by
    change CStarMatrix.ofMatrix.symm target.1 - B = _
    rw [ht]
  have htr : A.trace = 0 := by
    change (CStarMatrix.ofMatrix.symm target.1 - B).trace = 0
    rw [Matrix.trace_sub]
    change Matrix.trace target.1 - Matrix.trace actual.1 = 0
    rw [target.2.2, actual.2.2, sub_self]
  haveI : Nonempty (F × (Qubit × (Qubit × Qubit))) := by
    by_contra hn
    haveI : IsEmpty (F × (Qubit × (Qubit × Qubit))) := not_nonempty_iff.mp hn
    have hh := target.2.2
    simpa [Matrix.trace] using hh
  have hAH : A.IsHermitian := hA ▸ rank_one_sub_hermitian t hB
  refine ⟨hAH, ?_⟩
  change IsGreatest (Set.range hAH.eigenvalues) (traceNorm A / 2)
  clear_value A
  subst A
  exact rank_one_half_trace_norm t hB htr

end D5.S3.Quantum.Recovery.PhaseBoundarySpectralReduction
