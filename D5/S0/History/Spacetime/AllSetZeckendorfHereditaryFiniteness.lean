/- GID: D5/S0/History/Spacetime/AllSetZeckendorfHereditaryFiniteness
   generality: G
   mirror-B: D5/B/S0/History/Spacetime/AllSetZeckendorfHereditaryFiniteness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Recursive Zeckendorf encoding preserves and reflects hereditary finiteness in every universe. -/

import D5.S0.History.Spacetime.AllSetZeckendorfEncoding
import Mathlib.SetTheory.ZFC.VonNeumann
import Mathlib.Data.Set.Finite.Powerset
import Mathlib.Data.Set.Finite.Lattice

set_option autoImplicit false
universe u
namespace D5.S0.History.Spacetime.AllSetZeckendorfHereditaryFiniteness
noncomputable section
open D5.S0.History.Spacetime.AllSetZeckendorfEncoding
attribute [local instance] Classical.allZFSetDefinable Classical.propDecidable

/-- A set is hereditarily finite when its ordinal rank is less than omega. -/
def IsHF (x : ZFSet.{u}) : Prop := ZFSet.rank x < Ordinal.omega0

/-- A recursive Zeckendorf code is hereditarily finite exactly when its original set is. -/
theorem enc_isHF_iff (x : ZFSet.{u}) : IsHF (Enc x) ↔ IsHF x := by
  have finite_level : ∀ n : ℕ,
      Set.Finite (ZFSet.vonNeumann (n : Ordinal.{u}) : Set ZFSet.{u}) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ, ZFSet.vonNeumann_add_one]
      have : Finite (𝒫 (ZFSet.vonNeumann (n : Ordinal.{u}) : Set ZFSet.{u})) :=
        ih.powerset.to_subtype
      have : Finite ((ZFSet.vonNeumann (n : Ordinal.{u})).powerset) :=
        Finite.of_equiv _ (ZFSet.powersetEquiv _).symm
      exact Set.toFinite _
  have finite_of_hf : ∀ a : ZFSet.{u}, IsHF a → Set.Finite (a : Set ZFSet.{u}) := by
    intro a ha
    obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp ha
    exact (finite_level n).subset (ZFSet.subset_vonNeumann.mpr hn.le)
  have hf_of_finite : ∀ a : ZFSet.{u}, Set.Finite (a : Set ZFSet.{u}) →
      (∀ b ∈ a, IsHF b) → IsHF a := by
    intro a ha hm
    let : Finite a := ha.to_subtype
    let n : a → ℕ := fun b => (Ordinal.lt_omega0.mp (hm b b.property)).choose
    have hn : ∀ b : a, ZFSet.rank b.val = (n b : Ordinal.{u}) :=
      fun b => (Ordinal.lt_omega0.mp (hm b b.property)).choose_spec
    obtain ⟨N, hN⟩ := (Set.finite_range n).bddAbove
    have hb : ZFSet.rank a ≤ ((N + 1 : ℕ) : Ordinal.{u}) := by
      apply ZFSet.rank_le_iff.mpr
      intro b hb
      rw [hn ⟨b, hb⟩]
      exact_mod_cast Nat.lt_succ_of_le (hN (Set.mem_range_self ⟨b, hb⟩))
    exact hb.trans_lt (Ordinal.natCast_lt_omega0 _)
  have hf_pair : ∀ a b : ZFSet.{u}, IsHF (ZFSet.pair a b) ↔ IsHF a ∧ IsHF b := by
    intro a b
    simp only [ZFSet.pair, IsHF, ZFSet.rank_pair, ZFSet.rank_singleton,
      max_lt_iff, Ordinal.isSuccLimit_omega0.succ_lt_iff, and_self_left]
  have hf_nat : ∀ n : ℕ, IsHF (natOrd n : ZFSet.{u}) := by
    intro n
    simp [IsHF, natOrd]
  have hf_leaf : ∀ n : ℕ, IsHF (NatZ n : ZFSet.{u}) := by
    intro n
    apply (hf_pair _ _).mpr
    refine ⟨hf_nat 0, hf_of_finite _ ?_ ?_⟩
    · simpa only [zeta, ZFSet.coe_range] using
        (Set.finite_range (fun j : Fin (wordLength n) =>
          (ZFSet.pair (natOrd j.val) (natOrd (digit n j.val)) : ZFSet.{u})))
    · intro b hb
      obtain ⟨j, rfl⟩ := ZFSet.mem_range.mp hb
      exact (hf_pair _ _).mpr ⟨hf_nat _, hf_nat _⟩
  have nat_branch : ∀ a : ZFSet.{u}, a ∈ ZFSet.omega → IsHF a := by
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
    intro a
    induction a using Quotient.inductionOn with
    | _ pa =>
      change (∃ i : ULift ℕ, PSet.Equiv pa (PSet.ofNat i.down)) → _
      rintro ⟨⟨n⟩, he⟩
      change IsHF (ZFSet.mk pa)
      rw [ZFSet.sound he, ← hn n]
      exact hf_nat n
  have enc_eq : ∀ a : ZFSet.{u},
      Enc a = if a ∈ ZFSet.omega then NatZ (natIndex a)
        else ZFSet.pair (natOrd 1) (ZFSet.image Enc a) := by
    intro a
    rw [show Enc a = encStep a (fun b _ => Enc b) from
      WellFounded.fix_eq ZFSet.mem_wf encStep a]
    unfold encStep
    split
    · rfl
    · congr 1
      apply ZFSet.ext
      intro b
      simp only [ZFSet.mem_image]
      constructor
      · rintro ⟨c, hc, he⟩
        exact ⟨c, hc, by simpa only [dif_pos hc] using he⟩
      · rintro ⟨c, hc, he⟩
        exact ⟨c, hc, by simpa only [dif_pos hc] using he⟩
  have enc_inj : Function.Injective (Enc : ZFSet.{u} → ZFSet.{u}) :=
    fun a b h => (enc_injective_and_left_inverse.1 a b).mp h
  induction x using ZFSet.mem_wf.induction with
  | h x ih =>
    by_cases hx : x ∈ ZFSet.omega
    · exact iff_of_true (by rw [enc_eq x, if_pos hx]; exact hf_leaf _) (nat_branch x hx)
    · rw [enc_eq x, if_neg hx, hf_pair]
      constructor
      · rintro ⟨_, hi⟩
        apply hf_of_finite x
        · have hf := finite_of_hf _ hi
          rw [ZFSet.coe_image] at hf
          exact hf.of_finite_image enc_inj.injOn
        · intro y hy
          apply (ih y hy).mp
          exact (ZFSet.rank_lt_of_mem (ZFSet.mem_image.mpr ⟨y, hy, rfl⟩)).trans hi
      · intro h
        refine ⟨hf_nat 1, hf_of_finite _ ?_ ?_⟩
        · rw [ZFSet.coe_image]
          exact (finite_of_hf x h).image Enc
        · intro b hb
          obtain ⟨y, hy, rfl⟩ := ZFSet.mem_image.mp hb
          exact (ih y hy).mpr ((ZFSet.rank_lt_of_mem hy).trans h)

end
end D5.S0.History.Spacetime.AllSetZeckendorfHereditaryFiniteness
