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

/-- Equal encodings characterize equal sets, and decoding an encoded set recovers it. -/
theorem enc_injective_and_left_inverse :
    (∀ x y : ZFSet.{u}, Enc x = Enc y ↔ x = y) ∧
      (∀ x : ZFSet.{u}, Dec (encode x) = x) := by
  have natOrd_inj : Function.Injective (natOrd : ℕ → ZFSet.{u}) := by
    intro a b h
    exact_mod_cast Ordinal.toZFSet_injective h
  have nat_branch : ∀ x : ZFSet.{u}, x ∈ ZFSet.omega ↔ ∃ n : ℕ, natOrd n = x := by
    have hn : ∀ n : ℕ, (natOrd n : ZFSet.{u}) = ZFSet.mk (PSet.ofNat n) := by
      intro n
      induction n with
      | zero =>
        simp only [natOrd, Nat.cast_zero, Ordinal.toZFSet_zero, PSet.ofNat]
        rfl
      | succ n ih =>
        simp only [natOrd, Nat.cast_succ, Ordinal.toZFSet_add_one]
        change insert (natOrd n) (natOrd n) =
          insert (ZFSet.mk (PSet.ofNat n)) (ZFSet.mk (PSet.ofNat n))
        rw [ih]
    intro x
    induction x using Quotient.inductionOn with
    | _ px =>
      change (∃ i : ULift ℕ, PSet.Equiv px (PSet.ofNat i.down)) ↔
        ∃ n : ℕ, natOrd n = ZFSet.mk px
      constructor
      · rintro ⟨⟨n⟩, he⟩
        exact ⟨n, (hn n).trans (ZFSet.sound he).symm⟩
      · rintro ⟨n, he⟩
        exact ⟨⟨n⟩, ZFSet.exact (he.symm.trans (hn n))⟩
  have nat_index : ∀ n : ℕ, natIndex (natOrd n : ZFSet.{u}) = n :=
    Function.leftInverse_invFun natOrd_inj
  have enc_eq : ∀ x : ZFSet.{u},
      Enc x = if x ∈ ZFSet.omega then NatZ (natIndex x)
        else ZFSet.pair (natOrd 1) (ZFSet.image Enc x) := by
    intro x
    rw [show Enc x = encStep x (fun y _ => Enc y) from
      WellFounded.fix_eq ZFSet.mem_wf encStep x]
    unfold encStep
    split
    · rfl
    · congr 1
      apply ZFSet.ext
      intro z
      simp only [ZFSet.mem_image]
      constructor
      · rintro ⟨y, hy, he⟩
        exact ⟨y, hy, by simpa only [dif_pos hy] using he⟩
      · rintro ⟨y, hy, he⟩
        exact ⟨y, hy, by simpa only [dif_pos hy] using he⟩
  have natZ_inj : Function.Injective (NatZ : ℕ → ZFSet.{u}) := by
    have list_facts : ∀ n : ℕ,
        (Nat.zeckendorf n).Pairwise (fun a b => b + 2 ≤ a) ∧
          (∀ k ∈ Nat.zeckendorf n, 2 ≤ k) := by
      intro n
      let : IsTrans ℕ (fun a b => b + 2 ≤ a) := ⟨by intros; omega⟩
      have hp : (Nat.zeckendorf n ++ [0]).Pairwise (fun a b => b + 2 ≤ a) :=
        List.isChain_iff_pairwise.mp (Nat.isZeckendorfRep_zeckendorf n)
      obtain ⟨hs, _, hmin⟩ := List.pairwise_append.mp hp
      exact ⟨hs, fun k hk => by simpa using hmin k hk 0 (by simp)⟩
    have index_bounds : ∀ n k : ℕ, k ∈ Nat.zeckendorf n →
        2 ≤ k ∧ k - 2 < wordLength n := by
      intro n k hk
      have hlow := (list_facts n).2 k hk
      have hhigh : k ≤ (Nat.zeckendorf n).headD 1 := by
        have hs := (list_facts n).1
        cases hl : Nat.zeckendorf n with
        | nil => simp [hl] at hk
        | cons a l =>
          rw [hl, List.pairwise_cons] at hs
          rw [hl] at hk
          simp only [List.headD_cons]
          rcases List.mem_cons.mp hk with rfl | hk
          · exact le_rfl
          · have := hs.1 k hk
            omega
      exact ⟨hlow, by unfold wordLength; omega⟩
    have transfer : ∀ m n : ℕ, (zeta m : ZFSet.{u}) = zeta n →
        ∀ k ∈ Nat.zeckendorf m, k ∈ Nat.zeckendorf n := by
      intro m n he k hk
      obtain ⟨hmin, hlen⟩ := index_bounds m k hk
      have hdigit : digit m (k - 2) = 1 := by
        simp only [digit, Nat.sub_add_cancel hmin, if_pos hk]
      have hedge : ZFSet.pair (natOrd (k - 2)) (natOrd 1) ∈ (zeta m : ZFSet.{u}) := by
        have hg := ZFSet.mem_range_self (f := fun j : Fin (wordLength m) =>
          (ZFSet.pair (natOrd j.val) (natOrd (digit m j.val)) : ZFSet.{u})) ⟨k - 2, hlen⟩
        simpa only [zeta, hdigit] using hg
      rw [he] at hedge
      obtain ⟨j, hj⟩ := ZFSet.mem_range.mp hedge
      have hpos := natOrd_inj (ZFSet.pair_inj.mp hj).1
      have hval := natOrd_inj (ZFSet.pair_inj.mp hj).2
      have hmem : j.val + 2 ∈ Nat.zeckendorf n := by
        by_contra hnot
        simp only [digit, if_neg hnot] at hval
        exact Nat.zero_ne_one hval
      simpa only [hpos, Nat.sub_add_cancel hmin] using hmem
    intro m n he
    have hz : (zeta m : ZFSet.{u}) = zeta n := (ZFSet.pair_inj.mp he).2
    apply Nat.zeckendorfEquiv.injective
    apply Subtype.ext
    change Nat.zeckendorf m = Nat.zeckendorf n
    have sorted : ∀ k : ℕ, (Nat.zeckendorf k).Pairwise (· > ·) := by
      intro k
      exact (list_facts k).1.imp (by intros; omega)
    exact (sorted m).eq_of_mem_iff (sorted n)
      (fun k => ⟨transfer m n hz k, transfer n m hz.symm k⟩)
  have tag_ne : (natOrd 0 : ZFSet.{u}) ≠ natOrd 1 := by
    intro h
    exact Nat.zero_ne_one (natOrd_inj h)
  have enc_inj : Function.Injective (Enc : ZFSet.{u} → ZFSet.{u}) := by
    intro x
    induction x using ZFSet.mem_wf.induction with
    | h x ih =>
      intro y he
      rw [enc_eq x, enc_eq y] at he
      by_cases hx : x ∈ ZFSet.omega <;> by_cases hy : y ∈ ZFSet.omega
      · rw [if_pos hx, if_pos hy] at he
        obtain ⟨m, rfl⟩ := (nat_branch x).mp hx
        obtain ⟨n, rfl⟩ := (nat_branch y).mp hy
        rw [nat_index m, nat_index n] at he
        exact congrArg natOrd (natZ_inj he)
      · rw [if_pos hx, if_neg hy] at he
        exact False.elim (tag_ne (ZFSet.pair_inj.mp he).1)
      · rw [if_neg hx, if_pos hy] at he
        exact False.elim (tag_ne (ZFSet.pair_inj.mp he).1.symm)
      · rw [if_neg hx, if_neg hy] at he
        have himage := (ZFSet.pair_inj.mp he).2
        apply ZFSet.ext
        intro z
        constructor
        · intro hz
          have hcode : Enc z ∈ ZFSet.image Enc y := by
            rw [← himage]
            exact ZFSet.mem_image.mpr ⟨z, hz, rfl⟩
          obtain ⟨w, hw, hew⟩ := ZFSet.mem_image.mp hcode
          exact (ih z hz hew.symm).symm ▸ hw
        · intro hz
          have hcode : Enc z ∈ ZFSet.image Enc x := by
            rw [himage]
            exact ZFSet.mem_image.mpr ⟨z, hz, rfl⟩
          obtain ⟨w, hw, hew⟩ := ZFSet.mem_image.mp hcode
          exact (ih w hw hew) ▸ hw
  constructor
  · intro x y
    exact ⟨fun h => enc_inj h, congrArg Enc⟩
  · intro x
    apply enc_inj
    have hc : Valid (Enc x) := ⟨x, rfl⟩
    change Enc (decodeRaw (Enc x)) = Enc x
    rw [decodeRaw, dif_pos hc]
    exact hc.choose_spec

end
end D5.S0.History.Spacetime.AllSetZeckendorfEncoding
