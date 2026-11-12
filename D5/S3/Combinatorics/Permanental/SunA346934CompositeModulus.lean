/- GID: D5/S3/Combinatorics/Permanental/SunA346934CompositeModulus
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Permanental/SunA346934CompositeModulus
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Odd composite moduli divide Sun's signed-difference permanent. -/

/- Mathematical classification:
   a: proof_shape: bind-only (definition); consumer: claim, result; escape_witness: none
   claim: proof_shape: bind-only (definition); consumer: result; escape_witness: none
   two_positions: proof_shape: bind-only; consumer: factorial_split; escape_witness: none
   factorial_split: proof_shape: bind-only; consumer: result; escape_witness: none
   blocks_card: proof_shape: bind-only; consumer: additive_permanent_dvd; escape_witness: none
   image_eq_iff_blocks: proof_shape: bind-only; consumer: additive_permanent_dvd;
     escape_witness: none
   additive_permanent_dvd: proof_shape: bind-only; consumer: result; escape_witness: none
   result: proof_shape: bind-only; consumer: none; escape_witness: none
   admission_basis: open-problem-resolution (#22031; Proved)
   Direct frozen dependencies: none for every declaration.
   Proof shapes include all helpers: finite-product expansion, subtype equivalences,
   cardinality identities, prime-factor bounds and divisibility normalization.
   The permanent and primality operations use Mathlib's owners; a and claim retain
   the source expressions. Only the composite-modulus sentence is asserted.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22540 -/

import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.GroupTheory.Perm.DomMulAct

set_option autoImplicit false

namespace D5.S3.Combinatorics.Permanental.SunA346934CompositeModulus

/-- OEIS A346934: the permanent of `[i-j]` indexed by `1,...,2n`.
`Fin (2*n)` represents that index set by sending `i` to `i.val + 1`.
The permanent is Mathlib's existing `Matrix.permanent`, not a new notion. -/
noncomputable def a (n : ℕ) : ℤ :=
  Matrix.permanent (fun i j : Fin (2 * n) =>
    ((i.val : ℤ) + 1) - ((j.val : ℤ) + 1))

/-- Only Conjecture 1's composite-modulus sentence.
Since `n ≥ 1`, `2*n+1 > 1`, so nonprime is exactly composite.
The sign sentence and Conjecture 2 are excluded. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → ¬ Nat.Prime (2 * n + 1) →
    (((2 * n + 1 : ℕ) : ℤ) ∣ a n)

end D5.S3.Combinatorics.Permanental.SunA346934CompositeModulus

set_option maxRecDepth 2000
set_option maxHeartbeats 1000000

open Finset Equiv
open scoped Classical
namespace D5.S3.Combinatorics.Permanental.SunA346934CompositeModulus

private theorem two_positions {a b L : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hne : a ≠ b) (haL : a ≤ L) (hbL : b ≤ L) : a * b ∣ L.factorial := by
  have hne' : a - 1 ≠ b - 1 := by omega
  have hs : ({a - 1, b - 1} : Finset ℕ) ⊆ range L := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp only [mem_range] <;> omega
  have h := Finset.prod_dvd_prod_of_subset ({a - 1, b - 1} : Finset ℕ)
    (range L) (fun x => x + 1) hs
  simpa only [Finset.prod_insert (show a - 1 ∉ ({b - 1} : Finset ℕ) by simpa using hne'), Finset.prod_singleton,
    Nat.sub_add_cancel ha, Nat.sub_add_cancel hb, ← Nat.factorial_eq_prod_range_add_one] using h

private theorem factorial_split {q r : ℕ} (hq : 3 ≤ q) (ho : Odd q)
    (hc : ¬Nat.Prime q) (hr : r ≤ q - 1) :
    q ∣ r.factorial * (q - 1 - r).factorial := by
  let p := q.minFac
  let b := q / p
  have hp : Nat.Prime p := Nat.minFac_prime (by omega)
  have hp2 : 2 ≤ p := hp.two_le
  have hpb : p * b = q := Nat.mul_div_cancel' (Nat.minFac_dvd q)
  have hpleb : p ≤ b := Nat.minFac_le_div (by omega) hc
  have hpodd : Odd p := Nat.Odd.of_mul_left (show Odd (p * b) by rwa [hpb])
  have hp3 : 3 ≤ p := (Nat.Prime.odd_iff hp).mp hpodd
  let L := max r (q - 1 - r)
  have hhalf : q - 1 ≤ 2 * L := by dsimp [L]; omega
  have hlift : L.factorial ∣ r.factorial * (q - 1 - r).factorial := by
    rcases le_total r (q - 1 - r) with h | h
    · simp only [L, max_eq_right h]
      exact dvd_mul_left _ _
    · simp only [L, max_eq_left h]
      exact dvd_mul_right _ _
  by_cases hbeq : b = p
  · by_cases hp5 : 5 ≤ p
    · have hL : 2 * p ≤ L := by nlinarith [Nat.sub_add_cancel (show 1 ≤ q by omega)]
      apply dvd_trans (b := L.factorial) _ hlift
      have hd := two_positions (a := p) (b := 2 * p) (by omega) (by omega)
        (by omega) (by omega) hL
      have hqdiv : q ∣ p * (2 * p) := ⟨2, by rw [← hpb, hbeq]; ring⟩
      exact hqdiv.trans hd
    · have hpval : p = 3 := by
        obtain ⟨k, hk⟩ := hpodd
        omega
      have hq9 : q = 9 := by nlinarith [hbeq]
      by_cases hL : 6 ≤ L
      · have hd := two_positions (a := 3) (b := 6) (L := L) (by decide) (by decide)
          (by decide) (by omega) hL
        simpa only [hq9] using (dvd_trans (by norm_num : 9 ∣ 3 * 6) hd).trans hlift
      · have hr35 : 3 ≤ r ∧ r ≤ 5 := by dsimp [L] at hL; omega
        obtain ⟨hr3, hr5⟩ := hr35
        rw [hq9]
        interval_cases r <;> norm_num [Nat.factorial]
  · have hbgt : p < b := by exact Nat.lt_of_le_of_ne hpleb (Ne.symm hbeq)
    have hbL : b ≤ L := by nlinarith [Nat.sub_add_cancel (show 1 ≤ q by omega)]
    apply dvd_trans (b := L.factorial) _ hlift
    rw [← hpb]
    exact two_positions (by omega) (by omega) (Ne.symm hbeq) (by omega) hbL


variable {α : Type*} [Fintype α] [DecidableEq α]

private theorem blocks_card (s t : Finset α) (w : Perm α) (hw : (∀ i, w i ∈ t ↔ i ∈ s)) :
    Fintype.card {v : Perm α // (∀ i, v i ∈ t ↔ i ∈ s)} =
      s.card.factorial * (Fintype.card α - s.card).factorial := by
  classical
  have hcard : Fintype.card {v : Perm α // (∀ i, v i ∈ t ↔ i ∈ s)} =
      Fintype.card {v : Perm α // (∀ i, v i ∈ s ↔ i ∈ s)} := by
    apply Fintype.card_congr
    apply Equiv.subtypeEquiv (Equiv.mulLeft w.symm)
    intro v
    apply forall_congr'
    intro i
    change (v i ∈ t ↔ i ∈ s) ↔ (w.symm (v i) ∈ s ↔ i ∈ s)
    rw [← hw (w.symm (v i)), w.apply_symm_apply]
  rw [hcard]
  let f : α → Bool := fun i => decide (i ∈ s)
  have hbool : Fintype.card {v : Perm α // (∀ i, v i ∈ s ↔ i ∈ s)} =
      Fintype.card {v : Perm α // f ∘ v = f} := by
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun v => by simp [f, funext_iff, Function.comp_def])
  rw [hbool, DomMulAct.stabilizer_card]
  simp [f, Fintype.card_subtype_compl]


omit [Fintype α] in
private theorem image_eq_iff_blocks (s t : Finset α) (w : Perm α) :
    s.image w = t ↔ (∀ i, w i ∈ t ↔ i ∈ s) := by
  rw [eq_comm (a := s.image w)]
  simpa only [← Finset.coe_inj, Finset.coe_image, Set.ext_iff,
    Set.mem_preimage, Finset.mem_coe] using
    (Set.preimage_eq_iff_eq_image w.bijective (s := (t : Set α))
      (t := (s : Set α))).symm

private theorem additive_permanent_dvd (q : ℕ)
    (hfac : ∀ r : ℕ, r ≤ Fintype.card α →
      q ∣ r.factorial * (Fintype.card α - r).factorial)
    (x y : α → ℤ) :
    (q : ℤ) ∣ Matrix.permanent (fun i j => x i + y j) := by
  classical
  unfold Matrix.permanent
  simp_rw [Fintype.prod_add]
  rw [Finset.sum_comm]
  apply Finset.dvd_sum
  intro s _
  rw [← Finset.sum_mul]
  apply dvd_mul_of_dvd_left
  rw [← Finset.sum_fiberwise (univ : Finset (Perm α)) (fun w => s.image w)]
  apply Finset.dvd_sum
  intro t _
  have hprod (w : Perm α) (hw : s.image w = t) :
      (∏ i ∈ s, x (w i)) = ∏ j ∈ t, x j := by
    rw [← hw, Finset.prod_image w.injective.injOn]
  have hsum : (∑ w ∈ univ.filter (fun w : Perm α => s.image w = t), ∏ i ∈ s, x (w i)) =
      ((univ.filter (fun w : Perm α => s.image w = t)).card : ℤ) * (∏ j ∈ t, x j) := by
    calc
      _ = ∑ _w ∈ univ.filter (fun w : Perm α => s.image w = t), ∏ j ∈ t, x j := by
        apply Finset.sum_congr rfl
        intro w hw
        exact hprod w (Finset.mem_filter.mp hw).2
      _ = _ := by simp
  rw [hsum]
  apply dvd_mul_of_dvd_left
  by_cases ht : ∃ w : Perm α, s.image w = t
  · obtain ⟨w, hw⟩ := ht
    have hc : (univ.filter (fun w : Perm α => s.image w = t)).card =
        s.card.factorial * (Fintype.card α - s.card).factorial := by
      let e := Equiv.subtypeEquivRight (fun v : Perm α => image_eq_iff_blocks s t v)
      calc
        _ = Fintype.card {v : Perm α // s.image v = t} := by simp [Fintype.card_subtype]
        _ = Fintype.card {v : Perm α // (∀ i, v i ∈ t ↔ i ∈ s)} := Fintype.card_congr e
        _ = _ := blocks_card s t w ((image_eq_iff_blocks s t w).mp hw)
    rw [hc]
    exact_mod_cast hfac s.card (Finset.card_le_univ s)
  · have hzero : univ.filter (fun w : Perm α => s.image w = t) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      exact ht ⟨w, (Finset.mem_filter.mp hw).2⟩
    simp [hzero]


theorem result : claim := by
  intro n hn hc
  have hfac : ∀ r : ℕ, r ≤ Fintype.card (Fin (2 * n)) →
      (2 * n + 1) ∣ r.factorial * (Fintype.card (Fin (2 * n)) - r).factorial := by
    intro r hr
    simpa only [Fintype.card_fin, Nat.add_sub_cancel] using
      factorial_split (q := 2 * n + 1) (r := r) (by omega)
        (show Odd (2 * n + 1) from ⟨n, by omega⟩) hc
        (by simpa only [Fintype.card_fin, Nat.add_sub_cancel] using hr)
  have h := additive_permanent_dvd (2 * n + 1) hfac
    (fun i : Fin (2 * n) => (i.val : ℤ) + 1)
    (fun j : Fin (2 * n) => -((j.val : ℤ) + 1))
  simpa only [a, sub_eq_add_neg] using h

end D5.S3.Combinatorics.Permanental.SunA346934CompositeModulus
