/- GID: D5/S0/History/Spacetime/IntegerEncoding
   generality: G
   mirror-B: D5/B/S0/History/Spacetime/IntegerEncoding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed integers have exactly the tagged natural HF codes with no negative zero. -/

import D5.S0.History.Spacetime.HFEncoding

set_option autoImplicit false

namespace D5.S0.History.Spacetime.IntegerEncoding

open HFEncoding
noncomputable section

/-- The two allowed tags and the strictly positive negative magnitude are structural. -/
def IsIntCode (c : HF) : Prop :=
  ∃ s m, c = pair s m ∧ IsNatCode m ∧
    (s = natCode 0 ∨ s = natCode 1 ∧ m ≠ natCode 0)

def intCode : Int → HF
  | .ofNat n => pair (natCode 0) (natCode n)
  | .negSucc n => pair (natCode 1) (natCode (n + 1))

theorem intCode_valid (z : Int) : IsIntCode (intCode z) := by
  cases z with
  | ofNat n => exact ⟨_, _, rfl, natCode_valid n, Or.inl rfl⟩
  | negSucc n => exact ⟨_, _, rfl, natCode_valid _, Or.inr ⟨rfl, by simp⟩⟩

theorem intCode_injective : Function.Injective intCode := by
  intro a b h
  cases a <;> cases b <;> simp_all [intCode]

theorem intCode_full {c : HF} (h : IsIntCode c) : ∃ z, intCode z = c := by
  obtain ⟨s, m, rfl, hm, hs⟩ := h
  obtain ⟨n, hn⟩ := nat_code_equiv.surjective ⟨m, hm⟩
  have hn' : natCode n = m := congrArg Subtype.val hn
  subst m
  rcases hs with rfl | ⟨rfl, hpos⟩
  · exact ⟨Int.ofNat n, rfl⟩
  · cases n with
    | zero => exact (hpos rfl).elim
    | succ n => exact ⟨Int.negSucc n, rfl⟩

def int_code_equiv : Int ≃ {c : HF // IsIntCode c} :=
  Equiv.ofBijective (fun z => ⟨intCode z, intCode_valid z⟩)
    ⟨fun _ _ h => intCode_injective (congrArg Subtype.val h), by
      rintro ⟨c, hc⟩
      obtain ⟨z, hz⟩ := intCode_full hc
      exact ⟨z, Subtype.ext hz⟩⟩

def decodeInt (c : HF) (h : IsIntCode c) : Int := int_code_equiv.symm ⟨c, h⟩

@[simp] theorem decodeInt_encode (z : Int) : decodeInt (intCode z) (intCode_valid z) = z :=
  int_code_equiv.symm_apply_apply z

@[simp] theorem encode_decodeInt (c : HF) (h : IsIntCode c) : intCode (decodeInt c h) = c :=
  congrArg Subtype.val (int_code_equiv.apply_symm_apply ⟨c, h⟩)

end
end D5.S0.History.Spacetime.IntegerEncoding
