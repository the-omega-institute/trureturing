/- GID: D5/S3/Quantum/Foundation/FiniteKrausPureDirections
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/FiniteKrausPureDirections
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kraus collinearity and normalized pure directions of finite quantum channels. -/

import D5.S3.Quantum.Foundation.FiniteDiamondDistance
import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.LinearAlgebra.Matrix.Dual

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Foundation.FiniteKrausPureDirections

open Matrix
open scoped BigOperators ComplexOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Foundation.FiniteKrausChannel

/-- A rank-one sum of outer products has one common direction. -/
private theorem rank_one_sum_collinear {a κ : Type*} [Fintype a] [DecidableEq a] [Fintype κ]
    (φ : a → ℂ) (v : κ → a → ℂ) (hφ : star φ ⬝ᵥ φ = 1)
    (hv : ∑ u, vecMulVec (v u) (star (v u)) = vecMulVec φ (star φ)) :
    (∀ u, v u = (star φ ⬝ᵥ v u) • φ) ∧
      ∑ u, star (star φ ⬝ᵥ v u) * (star φ ⬝ᵥ v u) = 1 := by
  classical
  let Z : Matrix a κ ℂ := fun i u => v u i
  let P := vecMulVec φ (star φ)
  have hZ : Z * Z.conjTranspose = P := by
    calc
      Z * Z.conjTranspose = ∑ u, vecMulVec (v u) (star (v u)) := by
        ext i j
        change (∑ u, v u i * star (v u j)) = _
        simp only [Matrix.sum_apply, vecMulVec_apply, Pi.star_apply]
      _ = P := hv
  have hproj : (1 - P) * P = 0 := by
    simp [P, Matrix.sub_mul, vecMulVec_mul_vecMulVec, hφ]
  have hz : (1 - P) * Z = 0 := by
    apply Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Z, hZ,
      ← Matrix.mul_assoc, hproj, Matrix.zero_mul]
    simp
  have hfix : Z = P * Z := by
    simpa only [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] using hz
  have hcol (u : κ) : v u = (star φ ⬝ᵥ v u) • φ := by
    funext i
    have hi := congrFun₂ hfix i u
    change v u i = ∑ j, (φ i * star (φ j)) * v u j at hi
    simpa [dotProduct, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] using hi
  refine ⟨hcol, ?_⟩
  have ht := congrArg Matrix.trace hv
  rw [trace_sum, trace_vecMulVec, dotProduct_comm, hφ] at ht
  have hunit : φ ⬝ᵥ star φ = 1 := (dotProduct_comm _ _).trans hφ
  simp_rw [trace_vecMulVec] at ht
  conv at ht => lhs; arg 2; ext u; rw [hcol u]
  simpa only [star_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, hunit, mul_one, one_mul, mul_comm] using ht

private theorem unit_of_state_eq {a : Type*} [Fintype a] [DecidableEq a]
    (ρ : DensityState a) (v : a → ℂ)
    (hv : ρ.1 = CStarMatrix.ofMatrix (vecMulVec v (star v))) :
    star v ⬝ᵥ v = 1 := by
  have ht := ρ.2.2
  rw [hv] at ht
  exact (dotProduct_comm _ _).trans ((trace_vecMulVec _ _).symm.trans ht)

/-- Pure channel output supplies normalized coefficients for the same Kraus table. -/
private theorem kraus_collinear_of_pure_output {d : ℕ}
    (channel : QuantumChannel (Fin d) (Fin d))
    (ψ φ : Fin d → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1)
    (hout : (channel.mapState (pureState ψ hψ)).1 =
      CStarMatrix.ofMatrix (vecMulVec φ (star φ))) :
    ∃ c : Fin d × Fin d → ℂ,
      (∀ u, ((krausRepresentation channel.toCompletelyPositiveMap).1 u) *ᵥ ψ = c u • φ) ∧
      ∑ u, star (c u) * c u = 1 := by
  have hφ := unit_of_state_eq _ φ hout
  let K := (krausRepresentation channel.toCompletelyPositiveMap).1
  have hsum : ∑ u, vecMulVec (K u *ᵥ ψ) (star (K u *ᵥ ψ)) =
      vecMulVec φ (star φ) := by
    have h := (krausRepresentation channel.toCompletelyPositiveMap).2 (vecMulVec ψ (star ψ))
    have ho := congrArg CStarMatrix.ofMatrix.symm hout
    change CStarMatrix.ofMatrix.symm
      (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix (vecMulVec ψ (star ψ)))) =
        vecMulVec φ (star φ) at ho
    rw [h] at ho
    simpa only [mul_vecMulVec, vecMulVec_mul, star_mulVec] using ho
  exact ⟨fun u => star φ ⬝ᵥ (K u *ᵥ ψ), rank_one_sum_collinear φ _ hφ hsum⟩

private theorem mass_cast {a : Type*} [Fintype a] (v : a → ℂ) :
    ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) = star v ⬝ᵥ v := by
  simp only [Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self, dotProduct,
    Pi.star_apply, Complex.star_def]

private theorem mass_pos {a : Type*} [Fintype a] (v : a → ℂ) (hv : v ≠ 0) :
    0 < ∑ i, Complex.normSq (v i) := by
  have h := (dotProduct_star_self_pos_iff (v := v)).mpr hv
  rw [← mass_cast] at h
  exact_mod_cast h

private theorem normalization_weight {a : Type*} [Fintype a] (v : a → ℂ) :
    star ((Real.sqrt (∑ i, Complex.normSq (v i)) : ℂ)⁻¹) *
        ((Real.sqrt (∑ i, Complex.normSq (v i)) : ℂ)⁻¹) =
      ((∑ i, Complex.normSq (v i) : ℝ) : ℂ)⁻¹ := by
  rw [star_inv₀]
  simp only [Complex.star_def, Complex.conj_ofReal]
  rw [← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg (v i)))]

private theorem normalized_unit {a : Type*} [Fintype a] (v : a → ℂ) (hv : v ≠ 0) :
    star (((Real.sqrt (∑ i, Complex.normSq (v i)) : ℂ)⁻¹) • v) ⬝ᵥ
      (((Real.sqrt (∑ i, Complex.normSq (v i)) : ℂ)⁻¹) • v) = 1 := by
  rw [star_smul, smul_dotProduct, dotProduct_smul]
  change star _ * (_ * (star v ⬝ᵥ v)) = 1
  rw [← mul_assoc, normalization_weight, ← mass_cast]
  exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt (mass_pos v hv)))

/-- A nonzero direction normalized by its Euclidean squared mass. -/
def directionState {a : Type*} [Fintype a] [DecidableEq a]
    (v : a → ℂ) (hv : v ≠ 0) : DensityState a :=
  pureState (((Real.sqrt (∑ i, Complex.normSq (v i)) : ℂ)⁻¹) • v)
    (normalized_unit v hv)

private theorem directionState_value {a : Type*} [Fintype a] [DecidableEq a]
    (v : a → ℂ) (hv : v ≠ 0) :
    (directionState v hv).1 =
      ((∑ i, Complex.normSq (v i) : ℝ) : ℂ)⁻¹ •
        CStarMatrix.ofMatrix (vecMulVec v (star v)) := by
  change CStarMatrix.ofMatrix (vecMulVec (_ • v) (star (_ • v))) = _
  rw [star_smul, smul_vecMulVec, vecMulVec_smul, smul_smul, mul_comm,
    normalization_weight]
  rfl

/-- Collinear Kraus images give an exact transition between normalized directions.
Trace preservation supplies the scale; the linear motion need not preserve norms. -/
theorem map_directionState_of_collinear {d : ℕ}
    (channel : QuantumChannel (Fin d) (Fin d))
    (v w : Fin d → ℂ) (hv : v ≠ 0) (hw : w ≠ 0)
    (μ : Fin d × Fin d → ℂ)
    (hcol : ∀ u, (krausRepresentation channel.toCompletelyPositiveMap).1 u *ᵥ v = μ u • w) :
    channel.mapState (directionState v hv) = directionState w hw := by
  let K := (krausRepresentation channel.toCompletelyPositiveMap).1
  let a : ℂ := ∑ u, μ u * star (μ u)
  have hraw : channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix (vecMulVec v (star v))) =
      a • CStarMatrix.ofMatrix (vecMulVec w (star w)) := by
    have h := (krausRepresentation channel.toCompletelyPositiveMap).2 (vecMulVec v (star v))
    apply CStarMatrix.ofMatrix.symm.injective
    change CStarMatrix.ofMatrix.symm
      (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix (vecMulVec v (star v)))) =
        a • vecMulVec w (star w)
    rw [h]
    simp_rw [mul_vecMulVec, vecMulVec_mul, ← star_mulVec, hcol,
      star_smul, smul_vecMulVec, vecMulVec_smul, smul_smul]
    exact (Finset.sum_smul ..).symm
  let b := ((∑ i, Complex.normSq (v i) : ℝ) : ℂ)⁻¹ * a
  have hb : (channel.mapState (directionState v hv)).1 =
      b • CStarMatrix.ofMatrix (vecMulVec w (star w)) := by
    rw [QuantumChannel.mapState_value, directionState_value, map_smul, hraw, smul_smul]
  have ht : b * ((∑ i, Complex.normSq (w i) : ℝ) : ℂ) = 1 := by
    have h := (channel.mapState (directionState v hv)).2.2
    rw [hb] at h
    change Matrix.trace (b • vecMulVec w (star w)) = 1 at h
    simpa only [trace_smul, trace_vecMulVec, dotProduct_comm w,
      ← mass_cast, smul_eq_mul] using h
  have hc : b = ((∑ i, Complex.normSq (w i) : ℝ) : ℂ)⁻¹ := by
    have hn := Complex.ofReal_ne_zero.mpr (ne_of_gt (mass_pos w hw))
    simpa using (eq_div_of_mul_eq hn ht)
  apply Subtype.ext
  rw [hb, hc, directionState_value]

/-- A finite pure history admits one linear orbit with the same Kraus directions.
The coefficients selecting the linear map work simultaneously at every prefix time. -/
theorem linear_lift_of_pure_prefix {d N : ℕ}
    (channel : QuantumChannel (Fin d) (Fin d)) (ρ : ℕ → DensityState (Fin d))
    (hstep : ∀ n < N, ρ (n + 1) = channel.mapState (ρ n))
    (hpure : ∀ n ≤ N, IsPure (ρ n)) :
    ∃ (A : Module.End ℂ (Fin d → ℂ)) (x : Fin d → ℂ),
      (∃ hx : x ≠ 0, directionState x hx = ρ 0) ∧
      (∀ n ≤ N, (A ^ n) x ≠ 0) ∧
      ∀ n < N, ∃ μ : Fin d × Fin d → ℂ,
        ∀ u, (krausRepresentation channel.toCompletelyPositiveMap).1 u *ᵥ ((A ^ n) x) =
          μ u • ((A ^ (n + 1)) x) := by
  classical
  let ψ (n : ℕ) : Fin d → ℂ := if h : n ≤ N then (hpure n h).choose else 0
  have hψ (n : ℕ) (hn : n ≤ N) :
      (ρ n).1 = CStarMatrix.ofMatrix (vecMulVec (ψ n) (star (ψ n))) := by
    simpa only [ψ, dif_pos hn] using (hpure n hn).choose_spec
  have hu (n : ℕ) (hn : n ≤ N) : star (ψ n) ⬝ᵥ ψ n = 1 :=
    unit_of_state_eq _ _ (hψ n hn)
  have hnz (n : ℕ) (hn : n ≤ N) : ψ n ≠ 0 := by
    intro hz
    simpa [hz] using hu n hn
  have hc (n : Fin N) : ∃ c : Fin d × Fin d → ℂ,
      (∀ u, (krausRepresentation channel.toCompletelyPositiveMap).1 u *ᵥ ψ n =
        c u • ψ (n + 1)) ∧ ∑ u, star (c u) * c u = 1 := by
    apply kraus_collinear_of_pure_output channel _ _ (hu n n.isLt.le)
    have heq : pureState (ψ n) (hu n n.isLt.le) = ρ n :=
      Subtype.ext (hψ n n.isLt.le).symm
    rw [heq, ← hstep n n.isLt]
    exact hψ (n + 1) n.isLt
  choose c hcol hweight using hc
  obtain ⟨h, hh⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists
    (fun n : Fin N => dotProductEquiv ℂ (Fin d × Fin d) (c n)) (by
      intro n
      refine ⟨star (c n), ?_⟩
      change c n ⬝ᵥ star (c n) ≠ 0
      rw [dotProduct_comm]
      exact (hweight n).trans_ne one_ne_zero)
  let A : Module.End ℂ (Fin d → ℂ) :=
    ∑ u, h u • ((krausRepresentation channel.toCompletelyPositiveMap).1 u).mulVecLin
  have hact (n : Fin N) : A (ψ n) = (c n ⬝ᵥ h) • ψ (n + 1) := by
    simp only [A, LinearMap.sum_apply, LinearMap.smul_apply, Matrix.mulVecLin_apply, hcol,
      smul_smul]
    rw [← Finset.sum_smul]
    congr 1
    exact dotProduct_comm _ _
  have horbit : ∀ n ≤ N, ∃ a : ℂ, a ≠ 0 ∧ (A ^ n) (ψ 0) = a • ψ n := by
    intro n
    induction n with
    | zero => intro _; exact ⟨1, one_ne_zero, by simp⟩
    | succ n ih =>
      intro hn
      obtain ⟨a, ha, heq⟩ := ih (by omega)
      let i : Fin N := ⟨n, hn⟩
      refine ⟨a * (c i ⬝ᵥ h), mul_ne_zero ha (hh i), ?_⟩
      rw [pow_succ', Module.End.mul_apply, heq, map_smul, hact i, smul_smul]
  refine ⟨A, ψ 0, ?_, ?_, ?_⟩
  · refine ⟨hnz 0 (Nat.zero_le _), ?_⟩
    apply Subtype.ext
    rw [directionState_value, mass_cast, hu 0 (Nat.zero_le _), inv_one, one_smul]
    exact (hψ 0 (Nat.zero_le _)).symm
  · intro n hn
    obtain ⟨a, ha, heq⟩ := horbit n hn
    rw [heq]
    exact smul_ne_zero ha (hnz n hn)
  · intro n hn
    let i : Fin N := ⟨n, hn⟩
    obtain ⟨a, ha, heq⟩ := horbit n hn.le
    refine ⟨fun u => c i u / (c i ⬝ᵥ h), ?_⟩
    intro u
    rw [pow_succ', Module.End.mul_apply, heq, map_smul, hact i,
      Matrix.mulVec_smul, hcol i, smul_smul, smul_smul, smul_smul]
    congr 1
    field_simp [show c i ⬝ᵥ h ≠ 0 from hh i]

#print axioms rank_one_sum_collinear
#print axioms kraus_collinear_of_pure_output
#print axioms map_directionState_of_collinear
#print axioms linear_lift_of_pure_prefix

end D5.S3.Quantum.Foundation.FiniteKrausPureDirections
