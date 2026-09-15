/- GID: D5/S0/History/Spacetime/AllSetNaturalLeafMembers
   generality: G
   mirror-B: D5/B/S0/History/Spacetime/AllSetNaturalLeafMembers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The semantic members of each natural leaf are exactly the natural leaves of the smaller natural numbers. -/

import D5.S0.History.Spacetime.AllSetZeckendorfEncoding

set_option autoImplicit false
universe u
namespace D5.S0.History.Spacetime.AllSetNaturalLeafMembers
open D5.S0.History.Spacetime.AllSetZeckendorfEncoding
noncomputable section
attribute [local instance] Classical.allZFSetDefinable Classical.propDecidable

/-- The semantic members of the encoded finite ordinal are exactly the smaller natural leaves. -/
theorem el_natZ (n : ℕ) :
    El (encode (natOrd n : ZFSet.{u})) =
      ZFSet.range (fun m : Fin n => (NatZ m.val : ZFSet.{u})) := by
  have natOrd_mem_omega : ∀ m : ℕ, (natOrd m : ZFSet.{u}) ∈ ZFSet.omega := by
    intro m
    induction m with
    | zero =>
      simpa only [natOrd, Nat.cast_zero, Ordinal.toZFSet_zero] using ZFSet.omega_zero
    | succ m ih =>
      simpa only [natOrd, Nat.cast_succ, Ordinal.toZFSet_add_one] using ZFSet.omega_succ ih
  have hnat : ∀ m : ℕ, Enc (natOrd m : ZFSet.{u}) = NatZ m := by
    intro m
    rw [show Enc (natOrd m : ZFSet.{u}) = encStep (natOrd m) (fun y _ => Enc y) from
      WellFounded.fix_eq ZFSet.mem_wf encStep (natOrd m)]
    unfold encStep
    rw [if_pos (natOrd_mem_omega m)]
    have hi : Function.Injective (natOrd : ℕ → ZFSet.{u}) := by
      intro a b h
      exact_mod_cast Ordinal.toZFSet_injective h
    congr 1
    exact Function.leftInverse_invFun hi m
  change ZFSet.image Enc (Dec (encode (natOrd n))) = _
  rw [enc_injective_and_left_inverse.2]
  apply ZFSet.ext
  intro c
  simp only [ZFSet.mem_image, ZFSet.mem_range]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, ha, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hx
    obtain ⟨m, rfl⟩ := Ordinal.eq_natCast_of_le_natCast ha.le
    have hm : m < n := by exact_mod_cast ha
    exact ⟨⟨m, hm⟩, (hnat m).symm⟩
  · rintro ⟨m, rfl⟩
    refine ⟨natOrd m.val, ?_, hnat m.val⟩
    exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (by exact_mod_cast m.isLt)

end
end D5.S0.History.Spacetime.AllSetNaturalLeafMembers
