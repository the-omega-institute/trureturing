/- GID: D5/S3/Arith/Covering/PrimeRootCapacity
   generality: G
   mirror-B: D5/B/S3/Arith/Covering/PrimeRootCapacity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A fixed ordinary-prime root contains at most two originals at every ternary height. -/

import D5.S3.Arith.Covering.FixedCollisionExceptions
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Sum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos7.OddDistinctCoveringSystem

open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {L : ℕ}

/-- Three originals at one literal prime root admit a cheaper cover of the same size. -/
theorem top_ordinary_prime_root_card_le_two
    (F : OddDistinctCoveringSystem L)
    (hsumMin : ∀ H : OddDistinctCoveringSystem L,
      (∑ i, F.modulus i) ≤ ∑ i, H.modulus i)
    (h : ℕ) (hnoNext : ∀ i, ¬ 3 ^ (h + 1) ∣ F.modulus i)
    (u omega p b : ℕ) (hp : Nat.Prime p) (hp3 : p ≠ 3) (hp5 : p ≠ 5) :
    (Finset.univ.filter fun i =>
      5 * 3 ^ h ∣ F.modulus i ∧ F.residue i ≡ u [MOD 3 ^ h] ∧
      F.residue i ≡ omega [MOD 5] ∧ p ∣ F.modulus i ∧
      F.residue i ≡ b [MOD p]).card ≤ 2 := by
  classical
  let K := Finset.univ.filter fun i =>
    5 * 3 ^ h ∣ F.modulus i ∧ F.residue i ≡ u [MOD 3 ^ h] ∧
    F.residue i ≡ omega [MOD 5] ∧ p ∣ F.modulus i ∧ F.residue i ≡ b [MOD p]
  change K.card ≤ 2
  by_contra hcard
  have hthree : 3 ≤ K.card := by omega
  let selected : Fin 3 ↪ K := (Fin.castLEEmb hthree).trans K.equivFin.symm.toEmbedding
  let slot : Fin 3 ↪ Fin L := selected.trans (Function.Embedding.subtype _)
  have hslot (t : Fin 3) :
      5 * 3 ^ h ∣ F.modulus (slot t) ∧ F.residue (slot t) ≡ u [MOD 3 ^ h] ∧
      F.residue (slot t) ≡ omega [MOD 5] ∧ p ∣ F.modulus (slot t) ∧
      F.residue (slot t) ≡ b [MOD p] :=
    (Finset.mem_filter.mp (selected t).property).2
  obtain ⟨hpo, hpge, hp27, _, hpFive⟩ :=
    collision_prime_arithmetic F (slot 0) p hp hp3 hp5 (hslot 0).2.2.2.1
  let D := 3 ^ h
  let N := 3 ^ (h + 1)
  have hDpos : 0 < D := pow_pos (by decide) h
  have hN : N = 3 * D := by simp [N, D, pow_succ, Nat.mul_comm]
  have hNpos : 0 < N := pow_pos (by decide) (h + 1)
  have hNodd : Odd N := (by decide : Odd 3).pow
  have hpThree : Nat.Coprime 3 p := hp27.of_dvd_left (by decide : 3 ∣ 27)
  have hpD : Nat.Coprime D p := hpThree.pow_left h
  have hpN : Nat.Coprime N p := hpThree.pow_left (h + 1)
  have hNfive : Nat.Coprime N 5 := (by decide : Nat.Coprime 3 5).pow_left (h + 1)
  have hbasep : Nat.Coprime (5 * D) p := hpFive.mul_left hpD
  have hold (t : Fin 3) : 5 * D * p ≤ F.modulus (slot t) :=
    Nat.le_of_dvd (Nat.zero_lt_of_lt (F.modulus_one_lt (slot t)))
      (hbasep.mul_dvd_of_dvd_of_dvd (hslot t).1 (hslot t).2.2.2.1)
  let a5 := (Nat.chineseRemainder hNfive (u % D + D) omega).val
  let ap := (Nat.chineseRemainder hpN (u % D + D * 2) b).val
  let m : Fin 3 → ℕ := ![N, 5 * N, N * p]
  let a : Fin 3 → ℕ := ![u % D, a5, ap]
  have hm : ∀ t, 1 < m t := by
    intro t
    fin_cases t <;> dsimp [m]
    · omega
    · omega
    · nlinarith
  have ho : ∀ t, Odd (m t) := by
    intro t
    fin_cases t
    · exact hNodd
    · exact (by decide : Odd 5).mul hNodd
    · exact hNodd.mul hpo
  have hfirst : N < 5 * N := by omega
  have hsecond : 5 * N < N * p := by
    have hpgt : 5 < p := by omega
    simpa only [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_left hpgt hNpos
  have hinj : Function.Injective m := by
    intro s t hst
    fin_cases s <;> fin_cases t
    all_goals first
      | rfl
      | (exfalso
         dsimp [m] at hst
         omega)
  have hfresh : ∀ t i, m t ≠ F.modulus i := by
    intro t i hi
    apply hnoNext i
    rw [← hi]
    change N ∣ m t
    fin_cases t
    · exact dvd_refl N
    · exact ⟨5, by simp [m, Nat.mul_comm]⟩
    · exact ⟨p, rfl⟩
  have hcover : ∀ x t, x ≡ F.residue (slot t) [MOD F.modulus (slot t)] →
      ∃ s, x ≡ a s [MOD m s] := by
    intro x t hx
    have hxD : x ≡ u [MOD D] :=
      (hx.of_dvd ((dvd_mul_left D 5).trans (hslot t).1)).trans (hslot t).2.1
    have hx5 : x ≡ omega [MOD 5] :=
      (hx.of_dvd ((dvd_mul_right 5 D).trans (hslot t).1)).trans (hslot t).2.2.1
    have hxp : x ≡ b [MOD p] := (hx.of_dvd (hslot t).2.2.2.1).trans (hslot t).2.2.2.2
    let digit : Fin 3 := ⟨x / D % 3, Nat.mod_lt _ (by decide)⟩
    have hrem : x % D = u % D := hxD
    have heq : x % N = u % D + D * digit.val := by
      dsimp only [N, digit]
      rw [Nat.mod_pow_succ]
      change x % D + D * (x / D % 3) = u % D + D * (x / D % 3)
      rw [hrem]
    have hbranch : x ≡ u % D + D * digit.val [MOD N] := by
      change x % N = (u % D + D * digit.val) % N
      rw [← heq, Nat.mod_mod]
    have hdigit : digit.val = 0 ∨ digit.val = 1 ∨ digit.val = 2 := by
      have := digit.isLt
      omega
    rcases hdigit with hdigit | hdigit | hdigit
    · exact ⟨0, by simpa [a, m, hdigit] using hbranch⟩
    · refine ⟨1, ?_⟩
      have hbranch1 : x ≡ u % D + D [MOD N] := by simpa [hdigit] using hbranch
      simpa [a, m, a5, Nat.mul_comm] using
        Nat.chineseRemainder_modEq_unique hNfive hbranch1 hx5
    · refine ⟨2, ?_⟩
      have hbranch2 : x ≡ u % D + D * 2 [MOD N] := by simpa [hdigit] using hbranch
      simpa [a, m, ap] using Nat.chineseRemainder_modEq_unique hpN hbranch2 hxp
  have hthird : N * p < 5 * D * p :=
    Nat.mul_lt_mul_of_pos_right (by omega : N < 5 * D) hp.pos
  have hbound (t : Fin 3) : m t ≤ N * p := by
    fin_cases t
    · exact le_of_lt (hfirst.trans hsecond)
    · exact le_of_lt hsecond
    · exact le_rfl
  have hless (t : Fin 3) : m t < F.modulus (slot t) :=
    (hbound t).trans_lt (hthird.trans_le (hold t))
  let Remaining := {i : Fin L // i ∉ Set.range (slot : Fin 3 → Fin L)}
  let e : Fin 3 ⊕ Remaining ≃ Fin L :=
    (Equiv.sumCongr (Equiv.ofInjective slot slot.injective) (Equiv.refl Remaining)).trans
      (Equiv.sumCompl (fun i => i ∈ Set.range (slot : Fin 3 → Fin L)))
  have heLeft (t : Fin 3) : e (Sum.inl t) = slot t := rfl
  have heRight (i : Remaining) : e (Sum.inr i) = i.val := rfl
  let newMod : Fin 3 ⊕ Remaining → ℕ := Sum.elim m (fun i => F.modulus i.val)
  let newRes : Fin 3 ⊕ Remaining → ℕ := Sum.elim a (fun i => F.residue i.val)
  have hnewInj : Function.Injective newMod := by
    rintro (t | i) (s | j) heq
    · exact congrArg Sum.inl (hinj heq)
    · exact False.elim (hfresh t j.val heq)
    · exact False.elim (hfresh s i.val heq.symm)
    · exact congrArg Sum.inr (Subtype.ext (F.modulus_injective heq))
  let H : OddDistinctCoveringSystem L :=
    { modulus := fun i => newMod (e.symm i)
      residue := fun i => newRes (e.symm i)
      covers := by
        intro x
        obtain ⟨i, hxi⟩ := F.covers x
        by_cases hi : i ∈ Set.range (slot : Fin 3 → Fin L)
        · obtain ⟨t, rfl⟩ := hi
          obtain ⟨s, hs⟩ := hcover x t hxi
          exact ⟨e (Sum.inl s), by simpa [newMod, newRes] using hs⟩
        · exact ⟨e (Sum.inr ⟨i, hi⟩), by simpa [newMod, newRes] using hxi⟩
      modulus_one_lt := by
        intro i
        cases e.symm i with
        | inl t => exact hm t
        | inr j => exact F.modulus_one_lt j.val
      modulus_odd := by
        intro i
        cases e.symm i with
        | inl t => exact ho t
        | inr j => exact F.modulus_odd j.val
      modulus_injective := hnewInj.comp e.symm.injective }
  have hcost : (∑ t, m t) < ∑ t, F.modulus (slot t) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun t _ => hless t)
  have htotal : (∑ z, newMod z) < ∑ z, F.modulus (e z) := by
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simpa only [newMod, Sum.elim_inl, Sum.elim_inr, heLeft, heRight] using
      Nat.add_lt_add_right hcost (∑ i : Remaining, F.modulus i.val)
  rw [e.sum_comp F.modulus] at htotal
  have hnewSum : (∑ i, H.modulus i) = ∑ z, newMod z := e.symm.sum_comp newMod
  have hmin := hsumMin H
  rw [hnewSum] at hmin
  exact (Nat.not_lt_of_ge hmin) htotal

end Erdos7.OddDistinctCoveringSystem
