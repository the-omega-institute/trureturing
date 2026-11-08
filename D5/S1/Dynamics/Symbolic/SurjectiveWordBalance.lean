/- GID: D5/S1/Dynamics/Symbolic/SurjectiveWordBalance
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/SurjectiveWordBalance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact finite-word balance for arbitrary surjective integer block codes. -/

import D5.S1.Dynamics.Symbolic.GardenOfEden
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.Archimedean.Basic

/-! Finite-word balance for surjective cellular automata. -/

set_option autoImplicit false
noncomputable section

namespace D5.S1.Dynamics.Symbolic.SurjectiveWordBalance

open Function Set
open PermutativeLifts.BipermutativeLift
open PermutativeLifts.BipermutativePreinjectivity
open GardenOfEden

variable {A : Type*} {k : ℕ} {h : (Fin (k + 2) → A) → A}

/-- Apply the local rule at every complete window of a finite word. -/
def wordMap (h : (Fin (k + 2) → A) → A) {n : ℕ}
    (p : Fin (n + k + 1) → A) : Fin n → A :=
  fun i => h (fun j => p ⟨i.val + j.val, by omega⟩)

private abbrev Fiber (h : (Fin (k + 2) → A) → A) {n : ℕ} (w : Fin n → A) :=
  {p : Fin (n + k + 1) → A // wordMap h p = w}

private theorem fiber_power_bound [Finite A] [Nonempty A]
    (hpre : Preinjective h) {n : ℕ} (w : Fin n → A) (m : ℕ) :
    Nat.card (Fiber h w) ^ m ≤ (Nat.card A) ^ ((k + 1) * (m + 1)) := by
  classical
  let r := k + 1
  let L := n + k + 1
  have hL : 0 < L := by dsimp [L]; omega
  have hrL : r ≤ L := by dsimp [r, L]; omega
  let c : ℤ → A := fun _ => Classical.choice ‹Nonempty A›
  let cat (v : Fin m → Fiber h w) : Fin (m * L) → A := fun i =>
    (v ⟨i.val / L, (Nat.div_lt_iff_lt_mul hL).mpr i.isLt⟩).val
      ⟨i.val % L, Nat.mod_lt _ hL⟩
  have hcat (v : Fin m → Fiber h w) (b : Fin m) (s : Fin L) :
      cat v ⟨b.val * L + s.val, by nlinarith [b.isLt, s.isLt]⟩ = (v b).val s := by
    simp [cat, Nat.add_div, Nat.div_eq_of_lt s.isLt, Nat.mul_div_cancel _ hL,
      Nat.add_mod, Nat.mod_eq_of_lt s.isLt]
  let lift (v : Fin m → Fiber h w) : ℤ → A := writeWord (cat v) (r : ℕ) c
  have hlift (v : Fin m → Fiber h w) (b : Fin m) (s : Fin L) :
      lift v ((r : ℕ) + (b.val * L + s.val : ℕ)) = (v b).val s := by
    exact (writeWord_at (cat v) (r : ℕ) c
      ⟨b.val * L + s.val, by nlinarith [b.isLt, s.isLt]⟩).trans (hcat v b s)
  have hknown (v : Fin m → Fiber h w) (b : Fin m) (i : Fin n) :
      code h (lift v) ((r + b.val * L + i.val : ℕ)) = w i := by
    have he := congrFun (v b).property i
    change h (fun j => (v b).val ⟨i.val + j.val, by omega⟩) = w i at he
    rw [← he]
    apply congrArg h
    funext j
    change lift v (((r + b.val * L + i.val : ℕ) : ℤ) + (j.val : ℕ)) = _
    have hs : i.val + j.val < L := by dsimp [L]; have hi := i.isLt; have hj := j.isLt; omega
    have heq : (((r + b.val * L + i.val : ℕ) : ℤ) + (j.val : ℕ)) =
        (r : ℕ) + (b.val * L + (i.val + j.val) : ℕ) := by push_cast; ring
    rw [heq]
    exact hlift v b ⟨i.val + j.val, hs⟩
  let key (v : Fin m → Fiber h w) : Fin (m + 1) → Fin r → A :=
    fun b s => code h (lift v) ((b.val * L + s.val : ℕ))
  have hkey : Injective key := by
    intro v z he
    have hfin : FiniteDifference (lift v) (lift z) := by
      apply (finite_Ico (r : ℤ) ((r : ℤ) + m * L)).subset
      intro i hi
      by_contra hout
      apply hi
      dsimp [lift, writeWord]
      rw [dite_eq_right (by simpa only [mem_Ico, Nat.cast_mul] using hout),
        dite_eq_right (by simpa only [mem_Ico, Nat.cast_mul] using hout)]
    have hcode : code h (lift v) = code h (lift z) := by
      funext i
      by_cases hi : 0 ≤ i ∧ i < m * L + r
      · let a := i.toNat
        have ha : (a : ℤ) = i := Int.natCast_toNat_eq_self.mpr hi.1
        have hab : a < m * L + r := by omega
        have hrem := Nat.mod_lt a hL
        have hdiv := Nat.div_add_mod' a L
        by_cases hs : a % L < r
        · have hb : a / L < m + 1 := by
            apply (Nat.div_lt_iff_lt_mul hL).mpr
            nlinarith
          have hk := congrFun (congrFun he ⟨a / L, hb⟩) ⟨a % L, hs⟩
          change code h (lift v) ((a / L * L + a % L : ℕ)) =
            code h (lift z) ((a / L * L + a % L : ℕ)) at hk
          simpa only [hdiv, ha] using hk
        · have hb : a / L < m := by nlinarith
          have ht : a % L - r < n := by dsimp [L, r] at *; omega
          have hp : r + a / L * L + (a % L - r) = a := by omega
          have hv := hknown v ⟨a / L, hb⟩ ⟨a % L - r, ht⟩
          have hz := hknown z ⟨a / L, hb⟩ ⟨a % L - r, ht⟩
          rw [hp, ha] at hv hz
          exact hv.trans hz.symm
      · apply congrArg h
        funext j
        have hj := j.isLt
        change writeWord (cat v) (r : ℕ) c (i + (j : ℕ)) =
          writeWord (cat z) (r : ℕ) c (i + (j : ℕ))
        dsimp only [writeWord]
        rw [dite_eq_right (by dsimp [r] at *; push_cast at *; omega),
          dite_eq_right (by dsimp [r] at *; push_cast at *; omega)]
    have heq := hpre hfin hcode
    funext b
    apply Subtype.ext
    funext s
    have hx := congrFun heq ((r : ℕ) + (b.val * L + s.val : ℕ))
    exact (hlift v b s).symm.trans (hx.trans (hlift z b s))
  have hc := Nat.card_le_card_of_injective key hkey
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin,
    ← pow_mul, r, Nat.mul_comm] using hc

private theorem fiber_card_le [Finite A] (hpre : Preinjective h)
    {n : ℕ} (w : Fin n → A) : Nat.card (Fiber h w) ≤ (Nat.card A) ^ (k + 1) := by
  classical
  cases isEmpty_or_nonempty A with
  | inl hA =>
    let := hA
    have : IsEmpty (Fiber h w) := ⟨fun p => isEmptyElim (p.val ⟨0, by omega⟩)⟩
    simp
  | inr hA =>
    let := hA
    let B := (Nat.card A) ^ (k + 1)
    have hB : 0 < B := pow_pos (Nat.card_pos (α := A)) _
    by_contra hnot
    have hlt : (B : ℝ) < Nat.card (Fiber h w) := by exact_mod_cast (show B < _ from Nat.lt_of_not_ge hnot)
    have hratio : 1 < (Nat.card (Fiber h w) : ℝ) / B :=
      (one_lt_div (by exact_mod_cast hB)).mpr hlt
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (B : ℝ) hratio
    have hc := fiber_power_bound hpre w m
    have hp : (Nat.card (Fiber h w) : ℝ) ^ m ≤ (B : ℝ) ^ m * B := by
      exact_mod_cast (show Nat.card (Fiber h w) ^ m ≤ B ^ m * B by
        simpa only [B, pow_succ, pow_mul] using hc)
    rw [div_pow] at hm
    have hm' := (lt_div_iff₀ (pow_pos (by exact_mod_cast hB : (0 : ℝ) < B) m)).mp hm
    nlinarith

/-- Every finite output word of a surjective finite-alphabet integer block
code has exactly `card(A)^(k+1)` source words of the required length. -/
theorem surjective_word_balance [Finite A] (k : ℕ)
    (h : (Fin (k + 2) → A) → A) (hsurj : Surjective (code h))
    (n : ℕ) (w : Fin n → A) :
    Nat.card {p : Fin (n + k + 1) → A //
      ∀ i : Fin n, h (fun j : Fin (k + 2) => p ⟨i.val + j.val, by omega⟩) = w i} =
        (Nat.card A) ^ (k + 1) := by
  classical
  let := Fintype.ofFinite A
  have hpre := (garden_of_eden k h).mp hsurj
  have hle (v : Fin n → A) : Nat.card (Fiber h v) ≤ (Nat.card A) ^ (k + 1) :=
    fiber_card_le hpre v
  have hsum : (∑ v : Fin n → A, Nat.card (Fiber h v)) =
      Fintype.card (Fin (n + k + 1) → A) := by
    simpa only [Fintype.card_sigma, Nat.card_eq_fintype_card] using
      Fintype.card_congr (Equiv.sigmaFiberEquiv (wordMap h (n := n)))
  have htotal : (∑ v : Fin n → A, Nat.card (Fiber h v)) =
      ∑ _v : Fin n → A, (Nat.card A) ^ (k + 1) := by
    rw [hsum]
    simp only [Fintype.card_fun, Fintype.card_fin, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]
    rw [← pow_add]
  have heq := (Finset.sum_eq_sum_iff_of_le (fun v _ => hle v)).mp htotal w (Finset.mem_univ w)
  convert heq using 1
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun p => by simp only [wordMap, funext_iff])

end D5.S1.Dynamics.Symbolic.SurjectiveWordBalance
