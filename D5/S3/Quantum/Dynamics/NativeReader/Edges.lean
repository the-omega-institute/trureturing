/- GID: D5/S3/Quantum/Dynamics/NativeReader/Edges
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/NativeReader/Edges
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact two-point restrictions of the native changed-address operators. -/

import D5.S3.Quantum.Dynamics.NativeReader.Pulses

/-! The two changed addresses are restricted only after proving their actual row supports. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Quantum.Dynamics.NativeReader

open Matrix
open D5.S3.Quantum.Algebra.WeightedLegalPathTemperleyLieb
open D5.S3.Quantum.Measurement.OneSidedGoldenHistory (x x_properties)

/-- False selects physical address eleven; true selects physical address thirteen. -/
def changedAddress (a : Bool) : Fin 5 := if a then 3 else 1

def edgePosition (a : Bool) : Fin 7 := if a then 4 else 2

/-- Both ends of the actual legal edge, ordered by the physical center bit. -/
def edgeConfig (i a b : Bool) : Tail i :=
  ⟨if a then ![i, false, true, false, b, false, true]
    else ![i, false, b, false, false, false, true], by
    refine ⟨by cases a <;> simp, by cases a <;> simp, ?_⟩
    intro k
    cases a <;> fin_cases k <;> simp [adjacent]⟩

theorem edge_center (i a b : Bool) : (edgeConfig i a b).1 (edgePosition a) = b := by
  cases a <;> simp [edgeConfig, edgePosition]

theorem edge_away (i a b c : Bool) (k : Fin 7)
    (hk : k.val ≠ (edgePosition a).val) :
    (edgeConfig i a b).1 k = (edgeConfig i a c).1 k := by
  cases a <;> fin_cases k <;> simp_all [edgeConfig, edgePosition]

theorem edge_injective (i a : Bool) : Function.Injective (edgeConfig i a) := by
  intro b c he
  simpa [edge_center] using congrArg (fun z : Tail i => z.1 (edgePosition a)) he

theorem edge_ready (i a : Bool) : edgeConfig i a (!a) = readyTail i := by
  cases a <;> rfl

def sourceQ : Matrix Bool Bool ℂ := fun b c =>
  if b then (if c then (x : ℂ)^2 else (x * Real.sqrt x : ℝ))
  else (if c then (x * Real.sqrt x : ℝ) else x)

/-- No row contribution from any of the other legal configurations is omitted. -/
theorem projection_edge_outside (i a b : Bool) (z : Tail i)
    (hz0 : z ≠ edgeConfig i a false) (hz1 : z ≠ edgeConfig i a true) :
    projection i (changedAddress a) (edgeConfig i a b) z = 0 := by
  have hpos : (changedAddress a).val + 1 = (edgePosition a).val := by
    cases a <;> rfl
  have haway : ¬ ∀ k : Fin 7, k.val ≠ (changedAddress a).val + 1 →
      (edgeConfig i a b).1 k = z.1 k := by
    intro h
    have he : z = edgeConfig i a (z.1 (edgePosition a)) := by
      apply Subtype.ext
      funext k
      by_cases hk : k = edgePosition a
      · subst k
        simp [edge_center]
      · have hv : k.val ≠ (edgePosition a).val := Fin.val_ne_of_ne hk
        exact (h k (by simpa [hpos] using hv)).symm.trans (edge_away i a b _ k hv)
    cases hb : z.1 (edgePosition a)
    · exact hz0 (by simpa [hb] using he)
    · exact hz1 (by simpa [hb] using he)
  simp [projection, pathProjection, haway]

theorem projection_edge_entry (i a b c : Bool) :
    projection i (changedAddress a) (edgeConfig i a b) (edgeConfig i a c) = sourceQ b c := by
  have hpos : (changedAddress a).val + 1 = (edgePosition a).val := by
    cases a <;> rfl
  have haway : ∀ k : Fin 7, k.val ≠ (changedAddress a).val + 1 →
      (edgeConfig i a b).1 k = (edgeConfig i a c).1 k := by
    intro k hk
    exact edge_away i a b c k (by simpa [hpos] using hk)
  have hl : (edgeConfig i a b).1 ⟨(changedAddress a).val + 1 - 1, by omega⟩ = false := by
    cases a <;> rfl
  have hr : (edgeConfig i a b).1 ⟨(changedAddress a).val + 1 + 1, by omega⟩ = false := by
    cases a <;> rfl
  have hm (v : Bool) : (edgeConfig i a v).1 ⟨(changedAddress a).val + 1, by omega⟩ = v := by
    cases a <;> rfl
  unfold projection pathProjection
  rw [if_pos ⟨haway, hl.trans hr.symm⟩, hl, hm, hm]
  simp only [weight, mul_one]
  rw [div_eq_mul_inv, show Real.goldenRatio⁻¹ = x from rfl]
  cases b <;> cases c <;>
    simp [sourceQ, weight, Real.sqrt_mul_self x_properties.1.le, mul_comm, pow_two]

/-- The exact local coordinates are extracted from the full vector, with no state update. -/
def pairVector (i a : Bool) (v : Tail i → ℂ) : Bool → ℂ := fun b => v (edgeConfig i a b)

theorem projection_edge_mulVec (i a : Bool) (v : Tail i → ℂ) (b : Bool) :
    (projection i (changedAddress a) *ᵥ v) (edgeConfig i a b) =
      (sourceQ *ᵥ pairVector i a v) b := by
  classical
  have hne : edgeConfig i a false ≠ edgeConfig i a true := by
    exact fun he => Bool.false_ne_true (edge_injective i a he)
  change (∑ z : Tail i, projection i (changedAddress a) (edgeConfig i a b) z * v z) = _
  calc
    _ = ∑ z ∈ ({edgeConfig i a false, edgeConfig i a true} : Finset (Tail i)),
        projection i (changedAddress a) (edgeConfig i a b) z * v z := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro z _ hz
      have hn := (by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hz :
        z ≠ edgeConfig i a false ∧ z ≠ edgeConfig i a true)
      rw [projection_edge_outside i a b z hn.1 hn.2, zero_mul]
    _ = _ := by
      simp [hne, projection_edge_entry, Matrix.mulVec, dotProduct, pairVector,
        Fintype.sum_bool, add_comm]

def pairPulse (t : ℝ) : Matrix Bool Bool ℂ :=
  unitPhase t • (1 + (unitPhase t - 1) • sourceQ)

theorem pulse_pair (i a : Bool) (v : Tail i → ℂ) (t : ℝ) :
    pairVector i a (pulse i (changedAddress a) t *ᵥ v) = pairPulse t *ᵥ pairVector i a v := by
  ext b
  simp only [pairVector, pulse, pairPulse, Matrix.smul_mulVec, Matrix.add_mulVec,
    Matrix.one_mulVec, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [projection_edge_mulVec]

end D5.S3.Quantum.Dynamics.NativeReader
