/- GID: D5/S0/History/Spacetime/AllSetZeckendorfEncoding
   generality: G
   mirror-B: D5/B/S0/History/Spacetime/AllSetZeckendorfEncoding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Membership recursion with finite Zeckendorf natural leaves gives an injective encoding of all sets with a decoding left inverse. -/

import Mathlib.SetTheory.ZFC.Ordinal
import Mathlib.Data.Nat.Fib.Zeckendorf

set_option autoImplicit false
universe u
namespace D5.S0.History.Spacetime.AllSetZeckendorfEncoding
noncomputable section
attribute [local instance] Classical.allZFSetDefinable Classical.propDecidable

/-- The finite von Neumann ordinal associated to a natural number. -/
def natOrd (n : ℕ) : ZFSet.{u} := Ordinal.toZFSet (n : Ordinal.{u})

/-- The length of the finite Zeckendorf word, with the empty word representing zero. -/
def wordLength (n : ℕ) : ℕ := (Nat.zeckendorf n).headD 1 - 1

/-- The Zeckendorf digit at the Fibonacci weight with index two greater than the position. -/
def digit (n j : ℕ) : ℕ := if j + 2 ∈ Nat.zeckendorf n then 1 else 0

/-- The set graph of a finite Boolean word on finite ordinal positions. -/
def wordGraph (ell : ℕ) (b : Fin ell → Bool) : ZFSet.{u} :=
  ZFSet.range fun j : Fin ell => ZFSet.pair (natOrd j.val) (natOrd (if b j then 1 else 0))

/-- A finite word has no adjacent ones and ends in one whenever it is nonempty. -/
def CanonicalWord (ell : ℕ) (b : Fin ell → Bool) : Prop :=
  (∀ (j : ℕ) (h : j + 1 < ell),
    ¬ (b ⟨j, Nat.lt_trans (Nat.lt_succ_self j) h⟩ = true ∧ b ⟨j + 1, h⟩ = true)) ∧
  (∀ h : 0 < ell, b ⟨ell - 1, Nat.sub_lt h (by decide)⟩ = true)

/-- The set of graphs of canonical finite Zeckendorf words. -/
def WZ : ZFSet.{u} :=
  ZFSet.range fun w : {w : (ell : ℕ) × (Fin ell → Bool) // CanonicalWord w.1 w.2} =>
    wordGraph w.val.1 w.val.2

/-- The finite graph of the canonical Zeckendorf digits of a natural number. -/
def zeta (n : ℕ) : ZFSet.{u} :=
  ZFSet.range fun j : Fin (wordLength n) =>
    ZFSet.pair (natOrd j.val) (natOrd (digit n j.val))

/-- A natural leaf consists of tag zero and its finite Zeckendorf word graph. -/
def NatZ (n : ℕ) : ZFSet.{u} := ZFSet.pair (natOrd 0) (zeta n)

/-- The set of all natural leaves. -/
def NZ : ZFSet.{u} := ZFSet.range (NatZ : ℕ → ZFSet.{u})

/-- The natural index of a finite ordinal, with an arbitrary value outside that range. -/
def natIndex (x : ZFSet.{u}) : ℕ := Function.invFun natOrd x

/-- The recursive encoding step uses natural leaves or tag one with encoded members. -/
def encStep (x : ZFSet.{u}) (rec : ∀ y : ZFSet.{u}, y ∈ x → ZFSet.{u}) : ZFSet.{u} :=
  if x ∈ ZFSet.omega then NatZ (natIndex x)
  else ZFSet.pair (natOrd 1) (ZFSet.image (fun y => if h : y ∈ x then rec y h else ∅) x)

/-- The set encoding defined by well-founded recursion on membership. -/
def Enc : ZFSet.{u} → ZFSet.{u} := ZFSet.mem_wf.fix encStep

/-- A set is a valid code when it is the encoding of some set. -/
def Valid (c : ZFSet.{u}) : Prop := ∃ x, Enc x = c

/-- The type of valid set codes. -/
abbrev Code := {c : ZFSet.{u} // Valid c}

/-- The encoding of a set as a valid code. -/
def encode (x : ZFSet.{u}) : Code := ⟨Enc x, x, rfl⟩

/-- A selected preimage of a valid code, with empty-set fallback on other inputs. -/
def decodeRaw (c : ZFSet.{u}) : ZFSet.{u} :=
  if h : Valid c then h.choose else ∅

/-- Decoding on the type of valid codes. -/
def Dec (c : Code.{u}) : ZFSet.{u} := decodeRaw c.val

/-- Semantic membership is membership between decoded sets. -/
def MemZ (d c : Code.{u}) : Prop := Dec d ∈ Dec c

/-- The image of the decoded members under the set encoding. -/
def elRaw (c : ZFSet.{u}) : ZFSet.{u} := ZFSet.image Enc (decodeRaw c)

/-- The set of encoded members of the decoded set. -/
def El (c : Code.{u}) : ZFSet.{u} := elRaw c.val

/-- Every member of a given set is a valid code. -/
def AllValid (B : ZFSet.{u}) : Prop := ∀ d ∈ B, Valid d

/-- Packing decodes a set of codes and encodes the resulting set. -/
def packRaw (B : ZFSet.{u}) : ZFSet.{u} := Enc (ZFSet.image decodeRaw B)

/-- Packing a set of valid codes produces a valid code. -/
def Pack (B : ZFSet.{u}) (_ : AllValid B) : Code.{u} :=
  encode (ZFSet.image decodeRaw B)

/-- The semantic unordered pair obtained by packing two valid codes. -/
def unorderedPairZ (c d : Code.{u}) : Code.{u} :=
  Pack {c.val, d.val} (by
    intro e he
    rcases ZFSet.mem_pair.mp he with rfl | rfl
    · exact c.property
    · exact d.property)

/-- The semantic Kuratowski ordered pair of two valid codes. -/
def orderedPairZ (c d : Code.{u}) : Code.{u} :=
  unorderedPairZ (unorderedPairZ c c) (unorderedPairZ c d)

/-- The raw semantic union obtained by packing encoded members of encoded members. -/
def unionRawZ (c : ZFSet.{u}) : ZFSet.{u} :=
  packRaw (ZFSet.sUnion (ZFSet.image elRaw (elRaw c)))

/-- The raw semantic power set obtained by packing the packs of all subsets. -/
def powerRawZ (c : ZFSet.{u}) : ZFSet.{u} :=
  packRaw (ZFSet.image packRaw (elRaw c).powerset)

/-- Equal encodings characterize equal sets, and decoding an encoded set recovers it. -/
theorem enc_injective_and_left_inverse :
    (∀ x y : ZFSet.{u}, Enc x = Enc y ↔ x = y) ∧
      (∀ x : ZFSet.{u}, Dec (encode x) = x) := by
  sorry

end
end D5.S0.History.Spacetime.AllSetZeckendorfEncoding
