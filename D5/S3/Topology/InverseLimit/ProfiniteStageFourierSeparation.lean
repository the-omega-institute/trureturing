/- GID: D5/S3/Topology/InverseLimit/ProfiniteStageFourierSeparation
   generality: I
   mirror-B: D5/B/S3/Topology/InverseLimit/ProfiniteStageFourierSeparation
   mirror-E: none(waiver:finite-stage-character-reflection)
   anchors: []
   utility: none
   digest: Finite additive-character correlations separate compatible profinite residue families. -/

import D5.S1.Dynamics.ProfiniteIntegers
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Topology.Instances.AddCircle.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Topology.InverseLimit.ProfiniteStageFourierSeparation

open D5.S1.Dynamics
open scoped BigOperators

noncomputable section

private instance : Zero ProfiniteIntegers :=
  ⟨⟨0, by intro m n h; simp⟩⟩

private instance : Add ProfiniteIntegers :=
  ⟨fun x y => ⟨x.1 + y.1, by
    intro m n h
    simp only [Pi.add_apply, map_add, x.2 h, y.2 h]⟩⟩

private instance : Neg ProfiniteIntegers :=
  ⟨fun x => ⟨-x.1, by
    intro m n h
    simp only [Pi.neg_apply, map_neg, x.2 h]⟩⟩

private instance : AddCommGroup ProfiniteIntegers where
  add := (· + ·)
  add_assoc _ _ _ := Subtype.ext (add_assoc _ _ _)
  zero := 0
  zero_add _ := Subtype.ext (zero_add _)
  add_zero _ := Subtype.ext (add_zero _)
  neg := Neg.neg
  neg_add_cancel _ := Subtype.ext (neg_add_cancel _)
  add_comm _ _ := Subtype.ext (add_comm _ _)
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- A finite residue character viewed as a continuous character of the profinite integers. -/
noncomputable def coordinateCharacter (m : ℕ) (k : ZMod (m + 1)) :
    ProfiniteIntegers →ₜ+ UnitAddCircle where
  toFun x := ZMod.toAddCircle (k * x.1 m)
  map_zero' := by
    change ZMod.toAddCircle (k * (0 : ZMod (m + 1))) = 0
    simp
  map_add' x y := by
    change ZMod.toAddCircle (k * (x.1 m + y.1 m)) =
      ZMod.toAddCircle (k * x.1 m) + ZMod.toAddCircle (k * y.1 m)
    rw [mul_add, map_add]
  continuous_toFun :=
    (continuous_of_discreteTopology
      (f := fun z : ZMod (m + 1) => ZMod.toAddCircle (k * z))).comp
      ((continuous_apply m).comp continuous_subtype_val)

/-- The complete standard-character correlation at one finite residue stage. -/
theorem stage_correlation (m : ℕ) (x y : ProfiniteIntegers) :
    (∑ k : ZMod (m + 1),
      ZMod.stdAddChar (k * (x.1 m - y.1 m))) =
      if x.1 m = y.1 m then ((m + 1 : ℕ) : ℂ) else 0 := by
  have hs := AddChar.sum_mulShift (R := ZMod (m + 1))
    (R' := ℂ) (ψ := ZMod.stdAddChar) (x.1 m - y.1 m)
    (ZMod.isPrimitive_stdAddChar (m + 1))
  simpa only [ZMod.card, Nat.cast_ite, Nat.cast_zero, sub_eq_zero] using hs

/-- Every distinct profinite pair is detected by one finite-stage character sum. -/
theorem profinite_fourier_separates {x y : ProfiniteIntegers} (hxy : x ≠ y) :
    ∃ m : ℕ,
      (∑ k : ZMod (m + 1),
        ZMod.stdAddChar (k * (x.1 m - y.1 m))) = 0 := by
  have hfun : x.1 ≠ y.1 := by
    intro h
    exact hxy (Subtype.ext h)
  obtain ⟨m, hm⟩ := Function.ne_iff.mp hfun
  refine ⟨m, ?_⟩
  simpa [hm] using stage_correlation m x y

/-- Nonzero complete correlations at every finite stage reflect profinite equality. -/
theorem profinite_fourier_reflects {x y : ProfiniteIntegers} :
    x = y ↔ ∀ m : ℕ,
      (∑ k : ZMod (m + 1),
        ZMod.stdAddChar (k * (x.1 m - y.1 m))) ≠ 0 := by
  constructor
  · rintro rfl m
    have hcard : ((m + 1 : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero m
    simpa [stage_correlation] using hcard
  · intro hsum
    by_contra hxy
    obtain ⟨m, hm⟩ := profinite_fourier_separates hxy
    exact (hsum m) hm

/-- Continuous finite-coordinate characters separate every distinct profinite pair. -/
theorem continuous_character_separates {x y : ProfiniteIntegers} (hxy : x ≠ y) :
    ∃ m : ℕ, ∃ k : ZMod (m + 1),
      coordinateCharacter m k x ≠ coordinateCharacter m k y := by
  have hfun : x.1 ≠ y.1 := by
    intro h
    exact hxy (Subtype.ext h)
  obtain ⟨m, hm⟩ := Function.ne_iff.mp hfun
  refine ⟨m, 1, ?_⟩
  intro heq
  apply hm
  apply ZMod.toAddCircle_injective (m + 1)
  change ZMod.toAddCircle ((1 : ZMod (m + 1)) * x.1 m) =
    ZMod.toAddCircle ((1 : ZMod (m + 1)) * y.1 m) at heq
  simpa using heq

#print axioms coordinateCharacter
#print axioms stage_correlation
#print axioms profinite_fourier_separates
#print axioms profinite_fourier_reflects
#print axioms continuous_character_separates

end
end D5.S3.Topology.InverseLimit.ProfiniteStageFourierSeparation
