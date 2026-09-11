/- GID: D5/S0/History/Spacetime/SourceTreeEncoding
   generality: G
   mirror-B: D5/B/S0/History/Spacetime/SourceTreeEncoding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Free source trees represent exactly the independently specified tagged HF grammar. -/

import D5.S0.History.Spacetime.HFEncoding
import Mathlib.Algebra.Free

set_option autoImplicit false

namespace D5.S0.History.Spacetime.SourceTreeEncoding

open HFEncoding
noncomputable section

/-- Repeated natural leaves retain the same source identifier. -/
abbrev SourceTree := FreeMagma Nat

/-- The legal source syntax is stated on HF sets, independently of sourceCode. -/
inductive IsSourceCode : HF → Prop
  | leaf (n : HF) : IsNatCode n → IsSourceCode (pair (natCode 0) n)
  | branch (r s : HF) : IsSourceCode r → IsSourceCode s →
      IsSourceCode (pair (natCode 1) (pair r s))

def sourceCode : SourceTree → HF
  | .of n => pair (natCode 0) (natCode n)
  | .mul r s => pair (natCode 1) (pair (sourceCode r) (sourceCode s))

theorem sourceCode_valid (t : SourceTree) : IsSourceCode (sourceCode t) := by
  induction t using FreeMagma.rec with
  | of n => exact .leaf _ (natCode_valid n)
  | mul r s hr hs => exact .branch _ _ hr hs

theorem sourceCode_injective : Function.Injective sourceCode := by
  intro a
  induction a using FreeMagma.rec with
  | of n =>
    intro b h
    cases b with
    | of m => exact congrArg FreeMagma.of (by simpa [sourceCode] using h)
    | mul r s => simp [sourceCode] at h
  | mul r s hr hs =>
    intro b h
    cases b with
    | of n => simp [sourceCode] at h
    | mul u v =>
      have h' : sourceCode r = sourceCode u ∧ sourceCode s = sourceCode v := by
        simpa [sourceCode] using h
      exact congrArg₂ FreeMagma.mul (hr h'.1) (hs h'.2)

/-- Structural grammar induction reconstructs a tree for every legal HF code. -/
theorem sourceCode_full {c : HF} (h : IsSourceCode c) : ∃ t, sourceCode t = c := by
  induction h with
  | leaf n hn =>
    obtain ⟨m, hm⟩ := nat_code_equiv.surjective ⟨n, hn⟩
    exact ⟨.of m, congrArg (pair (natCode 0)) (congrArg Subtype.val hm)⟩
  | branch r s _ _ hr hs =>
    obtain ⟨u, rfl⟩ := hr
    obtain ⟨v, rfl⟩ := hs
    exact ⟨.mul u v, rfl⟩

def source_code_equiv : SourceTree ≃ {c : HF // IsSourceCode c} :=
  Equiv.ofBijective (fun t => ⟨sourceCode t, sourceCode_valid t⟩)
    ⟨fun _ _ h => sourceCode_injective (congrArg Subtype.val h), by
      rintro ⟨c, hc⟩
      obtain ⟨t, ht⟩ := sourceCode_full hc
      exact ⟨t, Subtype.ext ht⟩⟩

def decodeSource (c : HF) (h : IsSourceCode c) : SourceTree :=
  source_code_equiv.symm ⟨c, h⟩

@[simp] theorem decodeSource_encode (t : SourceTree) :
    decodeSource (sourceCode t) (sourceCode_valid t) = t :=
  source_code_equiv.symm_apply_apply t

@[simp] theorem encode_decodeSource (c : HF) (h : IsSourceCode c) :
    sourceCode (decodeSource c h) = c :=
  congrArg Subtype.val (source_code_equiv.apply_symm_apply ⟨c, h⟩)

end
end D5.S0.History.Spacetime.SourceTreeEncoding
