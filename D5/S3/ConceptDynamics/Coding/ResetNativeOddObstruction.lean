/- GID: D5/S3/ConceptDynamics/Coding/ResetNativeOddObstruction
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResetNativeOddObstruction
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: A nonzero integral direct-limit class killed by identity plus transition for every positive odd carrier. -/
import D5.S3.ConceptDynamics.Coding.ResetNumberedHistories
import D5.S3.ConceptDynamics.Coding.InertGroupBlockConjugacy
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.ConceptDynamics.Coding.ResetNumberedHistories
open Multiplicative

section NativeOddObstructionContent

open scoped BigOperators Matrix
open D5.S3.ConceptDynamics.Coding.InertGroupBlockConjugacy
  (VertexModule integerMatrix transition stationaryTransition DimensionGroup
   StationaryModule induced)

abbrev oddTau : Sign := ofAdd true

private theorem oddTau_ne_one : oddTau ≠ (1 : Sign) := by decide

def resetLabel : MonoidAlgebra ℤ Sign := MonoidAlgebra.single oddTau 1

private def oddAntiUnit : MonoidAlgebra ℤ Sign :=
  MonoidAlgebra.single 1 1 - MonoidAlgebra.single oddTau 1

private theorem integer_reset_entry (q : ℕ) (i j : Fin q) :
    integerMatrix (resetMatrix q) i j =
      (if j.val = 0 then resetLabel else 0) +
      (if j.val = i.val + 1 then 1 else 0) := by
  classical
  change MonoidAlgebra.mapRingHom Sign (Nat.castRingHom ℤ)
    ((resetMatrix q) i j) = _
  by_cases hzero : j.val = 0 <;> by_cases hsucc : j.val = i.val + 1 <;>
    simp [resetMatrix, resetLabel, oddTau, MonoidAlgebra.one_def, hzero, hsucc]

/- The original integerMatrix and row toLinearMapRight' are used here.
   In particular, the reset label multiplies the input coordinate on the RIGHT. -/
theorem transition_zero (N : ℕ) (v : VertexModule Sign (N + 1)) :
    transition (resetMatrix (N + 1)) v (0 : Fin (N + 1)) =
      (∑ i : Fin (N + 1), v i) * resetLabel := by
  classical
  change (v ᵥ* integerMatrix (resetMatrix (N + 1))) 0 = _
  rw [Matrix.vecMul_apply_eq_sum]
  have hentry (i : Fin (N + 1)) :
      integerMatrix (resetMatrix (N + 1)) i 0 = resetLabel := by
    rw [integer_reset_entry]
    simp
  simp_rw [hentry]
  rw [Finset.sum_mul]

theorem transition_succ (N : ℕ) (v : VertexModule Sign (N + 1))
    (j : Fin N) :
    transition (resetMatrix (N + 1)) v j.succ = v j.castSucc := by
  classical
  change (v ᵥ* integerMatrix (resetMatrix (N + 1))) j.succ = _
  rw [Matrix.vecMul_apply_eq_sum]
  have hentry (i : Fin (N + 1)) :
      integerMatrix (resetMatrix (N + 1)) i j.succ =
        if i = j.castSucc then 1 else 0 := by
    have hzero : j.succ.val ≠ 0 := by simp
    have hindex : j.succ.val = i.val + 1 ↔ i = j.castSucc := by
      constructor
      · intro h
        apply Fin.ext
        change j.val + 1 = i.val + 1 at h
        change i.val = j.val
        omega
      · rintro rfl
        rfl
    simp only [integer_reset_entry, if_neg hzero, zero_add, hindex]
  simp_rw [hentry]
  simp [mul_ite]

private theorem oddAntiUnit_mul_resetLabel :
    oddAntiUnit * resetLabel = -oddAntiUnit := by
  simp only [oddAntiUnit, resetLabel, sub_mul,
    MonoidAlgebra.single_mul_single, mul_one, one_mul]
  abel

/- Pairwise induction, starting at q=1. Appending the next -1,+1 pair
   leaves the sum unchanged; no assumption q≥3 or mixing enters the proof. -/
private theorem alternating_sum_pairs (m : ℕ) :
    (∑ i : Fin (2 * m + 1), (-1 : ℤ) ^ i.val) = 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hn : 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 := by omega
      rw [hn, Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, ih]
      have hodd : (-1 : ℤ) ^ (2 * m + 1) = -1 := by
        rw [pow_add, pow_mul]
        norm_num
      have heven : (-1 : ℤ) ^ (2 * m + 1 + 1) = 1 := by
        rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega, pow_mul]
        norm_num
      rw [hodd, heven]
      norm_num

private theorem alternating_sum_odd (q : ℕ) (ho : Odd q) :
    (∑ i : Fin q, (-1 : ℤ) ^ i.val) = 1 := by
  rcases ho with ⟨m, hm⟩
  have hq : q = 2 * m + 1 := by omega
  rw [hq]
  exact alternating_sum_pairs m

/-- The explicit original integral row w_i=(-1)^i(1-tau).
    Both coefficients are retained in Z[C2]; no sign quotient is taken. -/
def resetOddVector (q : ℕ) : VertexModule Sign q :=
  fun i => ((-1 : ℤ) ^ i.val) •
    (MonoidAlgebra.single (1 : Sign) 1 - MonoidAlgebra.single (ofAdd true) 1)

theorem resetOddVector_coeff_one (q : ℕ) (i : Fin q) :
    (resetOddVector q i).coeff 1 = (-1 : ℤ) ^ i.val := by
  change (((-1 : ℤ) ^ i.val) • oddAntiUnit).coeff 1 = _
  rw [MonoidAlgebra.coeff_smul_apply]
  simp [oddAntiUnit, MonoidAlgebra.coeff_single, Finsupp.single_apply,
    oddTau_ne_one, smul_eq_mul]

/-- Actual row calculation for every positive odd q, including q=1:
    at zero the odd alternating sum is 1 and multiplication by tau negates
    1-tau; at each successor the original row reads the preceding coordinate. -/
theorem reset_odd_transition (q : ℕ) (hq : 0 < q) (ho : Odd q) :
    transition (resetMatrix q) (resetOddVector q) = -resetOddVector q := by
  classical
  cases q with
  | zero => omega
  | succ N =>
      have hsum : (∑ i : Fin (N + 1), resetOddVector (N + 1) i) =
          oddAntiUnit := by
        change (∑ i : Fin (N + 1), ((-1 : ℤ) ^ i.val) • oddAntiUnit) = _
        rw [← Finset.sum_smul, alternating_sum_odd (N + 1) ho, one_smul]
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · change transition (resetMatrix (N + 1)) (resetOddVector (N + 1))
          (0 : Fin (N + 1)) = -(resetOddVector (N + 1) 0)
        rw [transition_zero, hsum, oddAntiUnit_mul_resetLabel]
        change -oddAntiUnit = -(((-1 : ℤ) ^ 0) • oddAntiUnit)
        simp only [pow_zero, one_smul]
      · change transition (resetMatrix (N + 1)) (resetOddVector (N + 1))
          j.succ = -(resetOddVector (N + 1) j.succ)
        rw [transition_succ]
        change ((-1 : ℤ) ^ j.val) • oddAntiUnit =
          -(((-1 : ℤ) ^ (j.val + 1)) • oddAntiUnit)
        simp only [pow_succ, mul_neg, mul_one, neg_smul, neg_neg]

/-- Every future transition iterate is still the explicit integral row,
    multiplied by the integer unit (-1)^k. -/
theorem reset_odd_transition_pow (q : ℕ) (hq : 0 < q) (ho : Odd q) (k : ℕ) :
    ((transition (resetMatrix q)) ^ k) (resetOddVector q) =
      ((-1 : ℤ) ^ k) • resetOddVector q := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul,
        reset_odd_transition q hq ho]
      simp only [pow_succ, mul_neg, mul_one, neg_smul, smul_neg]

/-- A concrete coefficient, rather than injectivity or torsion-freeness,
    certifies the survival of every future iterate. -/
theorem reset_odd_transition_pow_coeff_one
    (q : ℕ) (hq : 0 < q) (ho : Odd q) (k : ℕ) :
    (((transition (resetMatrix q)) ^ k) (resetOddVector q) ⟨0, hq⟩).coeff 1 =
      (-1 : ℤ) ^ k := by
  rw [reset_odd_transition_pow q hq ho k]
  change (((-1 : ℤ) ^ k) • (resetOddVector q ⟨0, hq⟩)).coeff 1 = _
  rw [MonoidAlgebra.coeff_smul_apply, resetOddVector_coeff_one]
  simp [smul_eq_mul]

theorem reset_odd_transition_pow_ne_zero
    (q : ℕ) (hq : 0 < q) (ho : Odd q) (k : ℕ) :
    ((transition (resetMatrix q)) ^ k) (resetOddVector q) ≠ 0 := by
  intro hz
  have hc := congrArg
    (fun v : VertexModule Sign q => (v ⟨0, hq⟩).coeff 1) hz
  have hunit : (-1 : ℤ) ^ k = 0 := by
    simpa only [reset_odd_transition_pow_coeff_one q hq ho k,
      Pi.zero_apply, MonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hc
  exact (pow_ne_zero k (by norm_num : (-1 : ℤ) ≠ 0)) hunit

/-- Stationary transition induced on the ORIGINAL DimensionGroup.
    This definition makes no claim about the standard geometric shift action.
    The native groupAction(resetMatrix q)(ofAdd true) is complement, not Theta. -/
def resetTheta (q : ℕ) : Module.End ℤ (DimensionGroup (resetMatrix q)) :=
  induced (transition (resetMatrix q)) (transition (resetMatrix q))
    (Commute.refl (transition (resetMatrix q)))

theorem resetTheta_apply_of (q n : ℕ) (v : VertexModule Sign q) :
    resetTheta q
      (Module.DirectLimit.of ℤ ℕ (fun _ : ℕ => VertexModule Sign q)
        (stationaryTransition (transition (resetMatrix q))) n v) =
    Module.DirectLimit.of ℤ ℕ (fun _ : ℕ => VertexModule Sign q)
      (stationaryTransition (transition (resetMatrix q))) n
      (transition (resetMatrix q) v) := by
  dsimp only [resetTheta, induced, DimensionGroup, StationaryModule]
  exact Module.DirectLimit.map_apply_of (R := ℤ) (ι := ℕ)
    (G := fun _ : ℕ => VertexModule Sign q)
    (G' := fun _ : ℕ => VertexModule Sign q)
    (f := stationaryTransition (transition (resetMatrix q)))
    (f' := stationaryTransition (transition (resetMatrix q)))
    (fun _ : ℕ => transition (resetMatrix q)) _ (i := n) v

/-- The explicit witness at stage zero of the full original integral colimit.
    This is a single element, not an independently retained anti-lattice map. -/
def resetOddClass (q : ℕ) : DimensionGroup (resetMatrix q) :=
  Module.DirectLimit.of ℤ ℕ (fun _ : ℕ => VertexModule Sign q)
    (stationaryTransition (transition (resetMatrix q))) 0 (resetOddVector q)

/-- Equality with zero would force a future transition iterate to be zero.
    Its suffix-zero identity coefficient is the nonzero unit (-1)^k. -/
theorem resetOddClass_ne_zero (q : ℕ) (hq : 0 < q) (ho : Odd q) :
    resetOddClass q ≠ 0 := by
  intro hz
  have heq :
      Module.DirectLimit.of ℤ ℕ (fun _ : ℕ => VertexModule Sign q)
        (stationaryTransition (transition (resetMatrix q))) 0 (resetOddVector q) =
      Module.DirectLimit.of ℤ ℕ (fun _ : ℕ => VertexModule Sign q)
        (stationaryTransition (transition (resetMatrix q))) 0
        (0 : VertexModule Sign q) := by
    exact hz.trans (map_zero (Module.DirectLimit.of ℤ ℕ
      (fun _ : ℕ => VertexModule Sign q)
      (stationaryTransition (transition (resetMatrix q))) 0)).symm
  obtain ⟨k, h0k, hk⟩ := Module.DirectLimit.exists_eq_of_of_eq heq
  have hkzero : ((transition (resetMatrix q)) ^ k) (resetOddVector q) = 0 := by
    simpa only [stationaryTransition, Nat.sub_zero, map_zero] using hk
  exact reset_odd_transition_pow_ne_zero q hq ho k hkzero

/-- The precise nonzero killed-class proposition in the original dimension group.
    No geometry-to-native representation theorem is assumed or asserted. -/
theorem reset_odd_killed_class (q : ℕ) (hq : 0 < q) (ho : Odd q) :
    resetOddClass q ≠ 0 ∧
      ((LinearMap.id : Module.End ℤ (DimensionGroup (resetMatrix q))) + resetTheta q) (resetOddClass q) = 0 := by
  refine ⟨resetOddClass_ne_zero q hq ho, ?_⟩
  change ((LinearMap.id : Module.End ℤ (DimensionGroup (resetMatrix q))) + resetTheta q)
    (Module.DirectLimit.of ℤ ℕ (fun _ : ℕ => VertexModule Sign q)
      (stationaryTransition (transition (resetMatrix q))) 0 (resetOddVector q)) = 0
  rw [LinearMap.add_apply, LinearMap.id_apply, resetTheta_apply_of,
    reset_odd_transition q hq ho, map_neg, add_neg_cancel]

end NativeOddObstructionContent
end D5.S3.ConceptDynamics.Coding.ResetNumberedHistories
