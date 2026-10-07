/- GID: D5/S3/Quantum/Entanglement/SynchronousDoilyClassicalValue
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/SynchronousDoilyClassicalValue
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The one-tenth synchronous doily game has classical value exactly 22/25. -/

/-
proof_shape: result: content; few_disagreements: content; grid_bound: content
escape_witness: grid_bound (ten-grid directed-loss bound); few_disagreements
  (minority-event counting and parity-valid local flips force twelve losses).
admission_basis: open-problem-resolution (#12753; Proved)
Direct frozen dependencies: none (pinned Mathlib only).
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
set_option Elab.async false
set_option simprocs false

namespace SynchronousDoilyClassicalValue
open Finset

def vars : (Fin 15) → Fin 3 → Fin 15 := ![
  ![0,3,6], ![1,3,7], ![2,3,8], ![0,4,9], ![1,4,10],
  ![2,4,11], ![0,5,12], ![1,5,13], ![2,5,14], ![6,11,13],
  ![10,12,8], ![14,7,9], ![6,10,14], ![11,12,7], ![13,8,9]]

def odd (e : (Fin 15)) : Bool := decide (12 ≤ e.val)

def sat (e : (Fin 15)) (a : (Fin 3 → Bool)) : Prop := (∑ i, (a i).toNat) % 2 = (odd e).toNat

private instance decidableSat (e : (Fin 15)) (a : (Fin 3 → Bool)) : Decidable (sat e a) := inferInstanceAs (Decidable (_ = _))

def meet (e f : (Fin 15)) : Prop := e ≠ f ∧
  ((univ.image (vars e)) ∩ (univ.image (vars f))).card = 1

private instance decidableMeet (e f : (Fin 15)) : Decidable (meet e f) := inferInstanceAs (Decidable (_ ∧ _))

def R (e f : (Fin 15)) (a b : (Fin 3 → Bool)) : Prop :=
  sat e a ∧ sat f b ∧ ∀ i j, vars e i = vars f j → a i = b j

private instance decidableR (e f : (Fin 15)) (a b : (Fin 3 → Bool)) : Decidable (R e f a b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

private def intersecting : Finset ((Fin 15) × (Fin 15)) := univ.filter fun q => meet q.1 q.2

noncomputable def winProb (p : ℝ) (A B : (Fin 15 → Fin 3 → Bool)) : ℝ :=
  (1-p) * (((intersecting.filter fun q => R q.1 q.2 (A q.1) (B q.2)).card : ℝ) /
    intersecting.card) + p * (((univ.filter fun e => R e e (A e) (B e)).card : ℝ) / 15)

noncomputable def classicalValue (p : ℝ) : ℝ :=
  letI := Fintype.ofFinite ((Fin 15 → Fin 3 → Bool) × (Fin 15 → Fin 3 → Bool))
  (univ : Finset ((Fin 15 → Fin 3 → Bool) × (Fin 15 → Fin 3 → Bool))).sup' univ_nonempty (fun S => winProb p S.1 S.2)

def claim : Prop := classicalValue (1/10) = 22/25

private def explicitStrategy (e : (Fin 15)) : (Fin 3 → Bool) := ![odd e, false, false]

private def inc : Fin 15 → Fin 3 → (Fin 15 × Fin 3) := ![
 ![(0,0),(3,0),(6,0)], ![(1,0),(4,0),(7,0)], ![(2,0),(5,0),(8,0)],
 ![(0,1),(1,1),(2,1)], ![(3,1),(4,1),(5,1)], ![(6,1),(7,1),(8,1)],
 ![(0,2),(9,0),(12,0)], ![(1,2),(11,1),(13,2)], ![(2,2),(10,2),(14,1)],
 ![(3,2),(11,2),(14,2)], ![(4,2),(10,0),(12,1)], ![(5,2),(9,1),(13,0)],
 ![(6,2),(10,1),(13,1)], ![(7,2),(9,2),(14,0)], ![(8,2),(11,0),(12,2)]]

private def grid : Fin 10 → Fin 6 → (Fin 15) := ![
 ![4,8,9,5,7,12], ![0,8,10,2,6,12], ![0,4,11,1,3,12],
 ![0,7,13,1,6,9], ![1,5,10,2,4,13], ![3,8,13,5,6,11],
 ![0,5,14,2,3,9], ![3,7,10,4,6,14], ![1,8,14,2,7,11], ![9,10,11,12,13,14]]

private def gridSet : Fin 10 → Finset (Fin 15) := ![
 {4,8,9,5,7,12}, {0,8,10,2,6,12}, {0,4,11,1,3,12},
 {0,7,13,1,6,9}, {1,5,10,2,4,13}, {3,8,13,5,6,11},
 {0,5,14,2,3,9}, {3,7,10,4,6,14}, {1,8,14,2,7,11}, {9,10,11,12,13,14}]

private def majority (A : (Fin 15 → Fin 3 → Bool)) (v : Fin 15) : Bool :=
  Bool.carry (A (inc v 0).1 (inc v 0).2) (A (inc v 1).1 (inc v 1).2)
    (A (inc v 2).1 (inc v 2).2)

private def minority (A : (Fin 15 → Fin 3 → Bool)) (e : (Fin 15)) (i : Fin 3) : Bool :=
  A e i != majority A (vars e i)

private def q (A : (Fin 15 → Fin 3 → Bool)) (e : (Fin 15)) : ℕ := ∑ i, (minority A e i).toNat

private def m (A : (Fin 15 → Fin 3 → Bool)) : ℕ := ∑ e, q A e

private def gridCount (A : (Fin 15 → Fin 3 → Bool)) (g : Fin 10) : ℕ := ∑ e ∈ gridSet g, q A e

private def idx : (Fin 15) → Fin 3 → Fin 3 := ![![0,0,0], ![0,1,0], ![0,2,0], ![1,0,0], ![1,1,0], ![1,2,0], ![2,0,0], ![2,1,0], ![2,2,0], ![1,1,1], ![1,1,1], ![1,1,1], ![2,2,2], ![2,2,2], ![2,2,2]]

private def bits (A : (Fin 15 → Fin 3 → Bool)) (v : Fin 15) : (Fin 3 → Bool) := fun j => A (inc v j).1 (inc v j).2

private def isConst (a : (Fin 3 → Bool)) : Bool := decide (a 0 = a 1 ∧ a 0 = a 2)

private def edgeCost (a : (Fin 3 → Bool)) (j : Fin 3) (b : Bool) : ℕ :=
  ∑ i, if i = j then 0 else (a i != b).toNat

private def localLoss (a b : (Fin 3 → Bool)) : ℕ := ∑ j, edgeCost a j (b j)

private def L (A B : (Fin 15 → Fin 3 → Bool)) : ℕ := ∑ v, localLoss (bits A v) (bits B v)

private def cost (A B : (Fin 15 → Fin 3 → Bool)) (e : (Fin 15)) : ℕ :=
  ∑ i, edgeCost (bits A (vars e i)) (idx e i) (B e i)

private def disag (A B : (Fin 15 → Fin 3 → Bool)) (e : (Fin 15)) : ℕ := if A e = B e then 0 else 1

private def flip (A B : (Fin 15 → Fin 3 → Bool)) (e : (Fin 15)) (i : Fin 3) : Bool := A e i != B e i

private def rowpos : Fin 10 → Fin 3 → Fin 3 → Fin 3 := ![![![1, 0, 2], ![0, 1, 2], ![1, 2, 0]], ![![1, 0, 2], ![0, 1, 2], ![2, 1, 0]], ![![1, 0, 2], ![0, 1, 2], ![1, 2, 0]], ![![1, 0, 2], ![0, 1, 2], ![2, 1, 0]], ![![1, 0, 2], ![0, 1, 2], ![2, 0, 1]], ![![1, 0, 2], ![0, 1, 2], ![0, 1, 2]], ![![1, 0, 2], ![0, 1, 2], ![1, 2, 0]], ![![1, 0, 2], ![0, 1, 2], ![0, 1, 2]], ![![1, 0, 2], ![0, 1, 2], ![1, 0, 2]], ![![0, 1, 2], ![0, 1, 2], ![0, 1, 2]]]

private def colpos : Fin 10 → Fin 3 → Fin 3 → Fin 3 := ![![![1, 0, 1], ![0, 1, 2], ![2, 2, 0]], ![![1, 0, 0], ![0, 1, 2], ![2, 2, 1]], ![![1, 0, 0], ![0, 1, 1], ![2, 2, 2]], ![![1, 0, 0], ![0, 1, 2], ![2, 2, 1]], ![![1, 0, 2], ![0, 1, 0], ![2, 2, 1]], ![![1, 0, 2], ![0, 1, 0], ![2, 2, 1]], ![![1, 0, 0], ![0, 1, 1], ![2, 2, 2]], ![![1, 0, 2], ![0, 1, 0], ![2, 2, 1]], ![![1, 0, 1], ![0, 1, 0], ![2, 2, 2]], ![![0, 0, 0], ![1, 1, 1], ![2, 2, 2]]]

private def row (g : Fin 10) (i : Fin 3) : (Fin 15) := grid g (Fin.castLE (by decide) i)

private def col (g : Fin 10) (j : Fin 3) : (Fin 15) := grid g ⟨j.val+3, by omega⟩

private def dirGridLoss (A B : (Fin 15 → Fin 3 → Bool)) (g : Fin 10) : ℕ :=
  ∑ i, ∑ j, (A (row g i) (rowpos g i j) != B (col g j) (colpos g i j)).toNat

private def edges : Finset (Fin 15 × (Fin 3 × Fin 3)) := univ.filter fun x => x.2.1 ≠ x.2.2

private def edgeQ (x : (Fin 15 × (Fin 3 × Fin 3))) : (Fin 15) × (Fin 15) := ((inc x.1 x.2.1).1, (inc x.1 x.2.2).1)

private def crossQ (x : (Fin 10 × (Fin 3 × (Fin 3 × Bool)))) : (Fin 15) × (Fin 15) :=
  if x.2.2.2 then (row x.1 x.2.1, col x.1 x.2.2.1) else (col x.1 x.2.2.1, row x.1 x.2.1)

private def questionLoss (A B : (Fin 15 → Fin 3 → Bool)) (x : (Fin 15) × (Fin 15)) : ℕ :=
  if R x.1 x.2 (A x.1) (B x.2) then 0 else 1

private def repair (A : (Fin 15 → Fin 3 → Bool)) (e : (Fin 15)) : (Fin 3 → Bool) :=
  if sat e (A e) then A e else explicitStrategy e

private theorem few_disagreements (A B : (Fin 15 → Fin 3 → Bool)) (hA : ∀ e, sat e (A e))
    (hB : ∀ e, sat e (B e)) (hr : hammingDist A B ≤ 2) : 12 ≤ L A B := by
  have inc_bij : Function.Bijective (fun p : (Fin 15 × Fin 3) => inc p.1 p.2) := by decide +kernel

  have inc_vars : ∀ v j, vars (inc v j).1 (inc v j).2 = v := by decide +kernel

  have sum_inc (w : (Fin 15 × Fin 3) → ℕ) :
      ∑ v, ∑ j, w (inc v j) = ∑ e, ∑ i, w (e,i) := by
    let E : (Fin 15 × Fin 3) ≃ (Fin 15 × Fin 3) := Equiv.ofBijective _ inc_bij
    simpa only [Fintype.sum_prod_type, E, Equiv.ofBijective_apply] using (Equiv.sum_comp E w)

  have xor_cast : ∀ a b : Bool,
      (((a != b).toNat : ℕ) : ZMod 2) = (a.toNat : ZMod 2) + (b.toNat : ZMod 2) := by decide +kernel

  have sat_cast (e : (Fin 15)) (a : (Fin 3 → Bool)) (h : sat e a) :
      (∑ i, (a i).toNat : ZMod 2) = ((odd e).toNat : ZMod 2) := by
    have h' := congrArg (fun n : ℕ => (n : ZMod 2)) h
    simpa only [sat, Nat.cast_sum, ZMod.natCast_mod] using h'

  have grid_majorities (X : Fin 15 → ZMod 2) (g : Fin 10) :
      ∑ e ∈ gridSet g, ∑ i, X (vars e i) = 0 := by
    have hz : (2 : ZMod 2) = 0 := by decide +kernel
    fin_cases g
    · change ((X 1 + (X 4 + (X 10 + 0))) + ((X 2 + (X 5 + (X 14 + 0))) + ((X 6 + (X 11 + (X 13 + 0))) + ((X 2 + (X 4 + (X 11 + 0))) + ((X 1 + (X 5 + (X 13 + 0))) + ((X 6 + (X 10 + (X 14 + 0))) + 0)))))) = 0
      (ring_nf; simp only [hz, mul_zero, add_zero])
    · change ((X 0 + (X 3 + (X 6 + 0))) + ((X 2 + (X 5 + (X 14 + 0))) + ((X 10 + (X 12 + (X 8 + 0))) + ((X 2 + (X 3 + (X 8 + 0))) + ((X 0 + (X 5 + (X 12 + 0))) + ((X 6 + (X 10 + (X 14 + 0))) + 0)))))) = 0
      (ring_nf; simp only [hz, mul_zero, add_zero])
    · change ((X 0 + (X 3 + (X 6 + 0))) + ((X 1 + (X 4 + (X 10 + 0))) + ((X 14 + (X 7 + (X 9 + 0))) + ((X 1 + (X 3 + (X 7 + 0))) + ((X 0 + (X 4 + (X 9 + 0))) + ((X 6 + (X 10 + (X 14 + 0))) + 0)))))) = 0
      (ring_nf; simp only [hz, mul_zero, add_zero])
    · change ((X 0 + (X 3 + (X 6 + 0))) + ((X 1 + (X 5 + (X 13 + 0))) + ((X 11 + (X 12 + (X 7 + 0))) + ((X 1 + (X 3 + (X 7 + 0))) + ((X 0 + (X 5 + (X 12 + 0))) + ((X 6 + (X 11 + (X 13 + 0))) + 0)))))) = 0
      (ring_nf; simp only [hz, mul_zero, add_zero])
    · change ((X 1 + (X 3 + (X 7 + 0))) + ((X 2 + (X 4 + (X 11 + 0))) + ((X 10 + (X 12 + (X 8 + 0))) + ((X 2 + (X 3 + (X 8 + 0))) + ((X 1 + (X 4 + (X 10 + 0))) + ((X 11 + (X 12 + (X 7 + 0))) + 0)))))) = 0
      (ring_nf; simp only [hz, mul_zero, add_zero])
    · change ((X 0 + (X 4 + (X 9 + 0))) + ((X 2 + (X 5 + (X 14 + 0))) + ((X 11 + (X 12 + (X 7 + 0))) + ((X 2 + (X 4 + (X 11 + 0))) + ((X 0 + (X 5 + (X 12 + 0))) + ((X 14 + (X 7 + (X 9 + 0))) + 0)))))) = 0
      (ring_nf; simp only [hz, mul_zero, add_zero])
    · change ((X 0 + (X 3 + (X 6 + 0))) + ((X 2 + (X 4 + (X 11 + 0))) + ((X 13 + (X 8 + (X 9 + 0))) + ((X 2 + (X 3 + (X 8 + 0))) + ((X 0 + (X 4 + (X 9 + 0))) + ((X 6 + (X 11 + (X 13 + 0))) + 0)))))) = 0
      (ring_nf; simp only [hz, mul_zero, add_zero])
    · change ((X 0 + (X 4 + (X 9 + 0))) + ((X 1 + (X 5 + (X 13 + 0))) + ((X 10 + (X 12 + (X 8 + 0))) + ((X 1 + (X 4 + (X 10 + 0))) + ((X 0 + (X 5 + (X 12 + 0))) + ((X 13 + (X 8 + (X 9 + 0))) + 0)))))) = 0
      (ring_nf; simp only [hz, mul_zero, add_zero])
    · change ((X 1 + (X 3 + (X 7 + 0))) + ((X 2 + (X 5 + (X 14 + 0))) + ((X 13 + (X 8 + (X 9 + 0))) + ((X 2 + (X 3 + (X 8 + 0))) + ((X 1 + (X 5 + (X 13 + 0))) + ((X 14 + (X 7 + (X 9 + 0))) + 0)))))) = 0
      (ring_nf; simp only [hz, mul_zero, add_zero])
    · change ((X 6 + (X 11 + (X 13 + 0))) + ((X 10 + (X 12 + (X 8 + 0))) + ((X 14 + (X 7 + (X 9 + 0))) + ((X 6 + (X 10 + (X 14 + 0))) + ((X 11 + (X 12 + (X 7 + 0))) + ((X 13 + (X 8 + (X 9 + 0))) + 0)))))) = 0
      (ring_nf; simp only [hz, mul_zero, add_zero])

  have grid_odd (g : Fin 10) :
      (∑ e ∈ gridSet g, (odd e).toNat : ZMod 2) = 1 := by
    fin_cases g <;> decide

  have minority_grid_parity (A : (Fin 15 → Fin 3 → Bool)) (hA : ∀ e, sat e (A e)) (g : Fin 10) :
      gridCount A g % 2 = 1 := by
    have h : (gridCount A g : ZMod 2) = 1 := by
      simp only [gridCount, q, minority, Nat.cast_sum]
      simp_rw [xor_cast, Finset.sum_add_distrib]
      have hs : (∑ e ∈ gridSet g, ∑ i, ((A e i).toNat : ZMod 2)) = 1 := by
        simp_rw [sat_cast _ _ (hA _)]
        exact grid_odd g
      rw [hs, grid_majorities (fun v => ((majority A v).toNat : ZMod 2)) g, add_zero]
    have hv := congrArg ZMod.val h
    simpa only [ZMod.val_natCast, ZMod.val_one] using hv

  have grid_membership_count : ∀ e : (Fin 15),
      ((univ : Finset (Fin 10)).filter fun g => e ∈ gridSet g).card = 4 := by decide +kernel

  have grid_pair_count : ∀ e f : (Fin 15), meet e f →
      ((univ : Finset (Fin 10)).filter fun g => e ∈ gridSet g ∧ f ∈ gridSet g).card = 2 := by decide +kernel

  have gridCount_total (A : (Fin 15 → Fin 3 → Bool)) : ∑ g, gridCount A g = 4 * m A := by
    have ht (e : (Fin 15)) : (∑ g : Fin 10, if e ∈ gridSet g then q A e else 0) = 4 * q A e := by
      rw [← Finset.sum_filter]
      simp only [sum_const, smul_eq_mul, grid_membership_count]
    calc
      ∑ g, gridCount A g = ∑ g : Fin 10, ∑ e : (Fin 15), if e ∈ gridSet g then q A e else 0 := by
        apply sum_congr rfl
        intro g _
        simp [gridCount, Finset.sum_ite_mem]
      _ = ∑ e : (Fin 15), ∑ g : Fin 10, if e ∈ gridSet g then q A e else 0 := Finset.sum_comm
      _ = ∑ e, 4 * q A e := by simp_rw [ht]
      _ = 4 * m A := by simp only [m, Finset.mul_sum]

  have at_least_three (A : (Fin 15 → Fin 3 → Bool)) (hA : ∀ e, sat e (A e)) : 3 ≤ m A := by
    have h : 10 ≤ ∑ g, gridCount A g := by
      calc
        10 = ∑ _g : Fin 10, (1 : ℕ) := by simp
        _ ≤ _ := sum_le_sum fun g _ => by have := minority_grid_parity A hA g; omega
    rw [gridCount_total] at h
    omega

  have double_minority_large (A : (Fin 15 → Fin 3 → Bool)) (hA : ∀ e, sat e (A e))
      (e : (Fin 15)) (he : 2 ≤ q A e) : 5 ≤ m A := by
    have hl (g : Fin 10) : 1 + 2 * (if e ∈ gridSet g then 1 else 0) ≤ gridCount A g := by
      have hp := minority_grid_parity A hA g
      by_cases hg : e ∈ gridSet g
      · have hc : q A e ≤ gridCount A g := single_le_sum (fun _ _ => Nat.zero_le _) hg
        simp [hg]; omega
      · simp [hg]; omega
    have hs := sum_le_sum (s := (univ : Finset (Fin 10))) fun g _ => hl g
    have hc : (∑ g : Fin 10, if e ∈ gridSet g then 1 else 0) = 4 := by
      rw [← sum_filter]; simp only [sum_const, smul_eq_mul, grid_membership_count, mul_one]
    simp only [sum_add_distrib, ← mul_sum, hc, sum_const, card_univ, Fintype.card_fin,
      smul_eq_mul] at hs
    rw [gridCount_total] at hs
    omega

  have meeting_minority_large (A : (Fin 15 → Fin 3 → Bool)) (hA : ∀ e, sat e (A e))
      (e f : (Fin 15)) (hm : meet e f) (he : 1 ≤ q A e) (hf : 1 ≤ q A f) : 4 ≤ m A := by
    have hl (g : Fin 10) :
        1 + 2 * (if e ∈ gridSet g ∧ f ∈ gridSet g then 1 else 0) ≤ gridCount A g := by
      have hp := minority_grid_parity A hA g
      by_cases hg : e ∈ gridSet g ∧ f ∈ gridSet g
      · have hc : q A e + q A f ≤ gridCount A g := by
          have hsub : ({e,f} : Finset (Fin 15)) ⊆ gridSet g := by simp only [insert_subset_iff, singleton_subset_iff]; exact hg
          have hle := sum_le_sum_of_subset hsub (f := q A)
          simpa [gridCount, hm.1] using hle
        simp [hg]; omega
      · simp [hg]; omega
    have hs := sum_le_sum (s := (univ : Finset (Fin 10))) fun g _ => hl g
    have hc : (∑ g : Fin 10, if e ∈ gridSet g ∧ f ∈ gridSet g then 1 else 0) = 2 := by
      rw [← sum_filter]; simp only [sum_const, smul_eq_mul, grid_pair_count e f hm, mul_one]
    simp only [sum_add_distrib, ← mul_sum, hc, sum_const, card_univ, Fintype.card_fin,
      smul_eq_mul] at hs
    rw [gridCount_total] at hs
    omega

  have inc_idx : ∀ e i, inc (vars e i) (idx e i) = (e,i) := by decide +kernel

  have idx_inc : ∀ v j, idx (inc v j).1 (inc v j).2 = j := by decide +kernel

  have vars_injective : ∀ e, Function.Injective (vars e) := by decide +kernel

  have contains_meet : ∀ e f i j, e ≠ f → vars e i = vars f j → meet e f := by decide +kernel

  have bits_idx (A : (Fin 15 → Fin 3 → Bool)) (e : (Fin 15)) (i : Fin 3) :
      bits A (vars e i) (idx e i) = A e i := by simp [bits, inc_idx]

  have loss_eq_cost (A B : (Fin 15 → Fin 3 → Bool)) : L A B = ∑ e, cost A B e := by
    unfold L localLoss cost
    calc
      (∑ v, ∑ j, edgeCost (bits A v) j (bits B v j)) =
        ∑ v, ∑ j, edgeCost (bits A (vars (inc v j).1 (inc v j).2))
          (idx (inc v j).1 (inc v j).2) (B (inc v j).1 (inc v j).2) := by
            simp only [inc_vars, idx_inc, bits]
      _ = _ := sum_inc (fun p => edgeCost (bits A (vars p.1 p.2)) (idx p.1 p.2) (B p.1 p.2))

  have local_baseline : ∀ a : (Fin 3 → Bool),
      localLoss a a = 4 * ∑ j, (a j != Bool.carry (a 0) (a 1) (a 2)).toNat := by decide +kernel

  have loss_baseline (A : (Fin 15 → Fin 3 → Bool)) : L A A = 4 * m A := by
    unfold L
    have hs : (∑ v, localLoss (bits A v) (bits A v)) =
        ∑ v, 4 * ∑ j, (bits A v j != Bool.carry (bits A v 0) (bits A v 1) (bits A v 2)).toNat :=
      sum_congr rfl fun v _ => local_baseline (bits A v)
    rw [hs]
    rw [← mul_sum]
    have hi := sum_inc (fun p => (minority A p.1 p.2).toNat)
    exact congrArg (fun n : ℕ => 4 * n) (by
      simpa only [minority, inc_vars, majority, bits, m, q] using hi)

  have local_shift : ∀ (a : (Fin 3 → Bool)) (j : Fin 3) (b : Bool),
      edgeCost a j b + 2 * ((a j != Bool.carry (a 0) (a 1) (a 2)) && (a j != b)).toNat =
      edgeCost a j (a j) + 2 * (isConst a && (a j != b)).toNat := by decide +kernel

  have bit_flip_bound : ∀ (a : (Fin 3 → Bool)) (j : Fin 3) (b : Bool),
      edgeCost a j (a j) ≤ edgeCost a j b + 2 * (a j != b).toNat := by decide +kernel

  have valid_flip_count : ∀ (a b : (Fin 3 → Bool)),
      (∑ i, (a i).toNat) % 2 = (∑ i, (b i).toNat) % 2 →
      (∑ i, (a i != b i).toNat) = 2 * (if a = b then 0 else 1) := by decide +kernel

  have general_cost_bound (A B : (Fin 15 → Fin 3 → Bool)) (hA : ∀ e, sat e (A e))
      (hB : ∀ e, sat e (B e)) (e : (Fin 15)) : cost A A e ≤ cost A B e + 4 * disag A B e := by
    have hf : (∑ i, (flip A B e i).toNat) = 2 * disag A B e := by
      exact valid_flip_count (A e) (B e) ((hA e).trans (hB e).symm)
    have hs := sum_le_sum (s := (univ : Finset (Fin 3))) fun i _ =>
      bit_flip_bound (bits A (vars e i)) (idx e i) (B e i)
    simp only [bits_idx, sum_add_distrib, ← mul_sum] at hs
    change cost A A e ≤ cost A B e + 2 * (∑ i, (flip A B e i).toNat) at hs
    rw [hf] at hs
    omega

  have general_loss_bound (A B : (Fin 15 → Fin 3 → Bool)) (hA : ∀ e, sat e (A e))
      (hB : ∀ e, sat e (B e)) : 4 * m A ≤ L A B + 4 * hammingDist A B := by
    have hs := sum_le_sum (s := (univ : Finset (Fin 15))) fun e _ => general_cost_bound A B hA hB e
    have hd : (∑ e, disag A B e) = hammingDist A B := by
      unfold hammingDist
      change (∑ e, (if A e = B e then 0 else 1)) =
        (univ.filter (fun i => A i ≠ B i)).card
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      simp [ne_eq]
    simpa only [sum_add_distrib, ← mul_sum, ← loss_eq_cost, loss_baseline, hd] using hs

  have bit_minority_bound : ∀ (a : (Fin 3 → Bool)) (j : Fin 3) (b : Bool),
      edgeCost a j (a j) ≤ edgeCost a j b + 2 * (a j != Bool.carry (a 0) (a 1) (a 2)).toNat := by decide +kernel

  have minority_cost_bound (A B : (Fin 15 → Fin 3 → Bool)) (e : (Fin 15)) :
      cost A A e ≤ cost A B e + 2 * q A e := by
    have hs := sum_le_sum (s := (univ : Finset (Fin 3))) fun i _ =>
      bit_minority_bound (bits A (vars e i)) (idx e i) (B e i)
    simp only [bits_idx, sum_add_distrib, ← mul_sum] at hs
    exact hs

  have small_cost_bound (A B : (Fin 15 → Fin 3 → Bool)) (hA : ∀ e, sat e (A e))
      (hm : m A ≤ 4) (e : (Fin 15)) : cost A A e ≤ cost A B e + 2 * disag A B e := by
    have hq : q A e ≤ 1 := by
      by_contra hn
      have := double_minority_large A hA e (by omega)
      omega
    by_cases he : A e = B e
    · have hc : cost A B e = cost A A e := by unfold cost; rw [he]
      simp [hc, disag, he]
    · have hc := minority_cost_bound A B e
      simp only [disag, if_neg he]
      omega

  have nonconstant_minor : ∀ a : (Fin 3 → Bool), isConst a ≠ true →
      ∃ j, (a j != Bool.carry (a 0) (a 1) (a 2)) = true := by decide +kernel

  have two_minor : ∀ (u : (Fin 3 → Bool)) (i j : Fin 3), i ≠ j → u i = true → u j = true →
      2 ≤ ∑ k, (u k).toNat := by decide +kernel

  have isolated_flip_bound : ∀ (u c d : (Fin 3 → Bool)),
      (∀ i j, u i = true → i ≠ j → c j = true) →
      (∑ i, (d i).toNat) % 2 = 0 →
      (∑ i, (u i && d i).toNat) ≤ ∑ i, (c i && d i).toNat := by decide +kernel

  have three_isolated (A : (Fin 15 → Fin 3 → Bool)) (hA : ∀ e, sat e (A e)) (hm : m A = 3)
      (e : (Fin 15)) (i j : Fin 3) (hi : minority A e i = true) (hij : i ≠ j) :
      isConst (bits A (vars e j)) = true := by
    by_contra hn
    obtain ⟨k,hk⟩ := nonconstant_minor (bits A (vars e j)) hn
    let f := (inc (vars e j) k).1
    let t := (inc (vars e j) k).2
    have ht : minority A f t = true := by
      simpa only [minority, f, t, inc_vars, bits, majority] using hk
    have hq : q A e ≤ 1 := by
      by_contra h
      have := double_minority_large A hA e (by omega)
      omega
    have hfe : e ≠ f := by
      intro hef
      have hp : t = j := vars_injective e (by simpa only [f, t, ← hef] using inc_vars (vars e j) k)
      have ht' : minority A e j = true := by simpa only [← hef, hp] using ht
      have hc := two_minor (minority A e) i j hij hi ht'
      change 2 ≤ q A e at hc
      omega
    have hmeet : meet e f := contains_meet e f j t hfe (by
      exact (inc_vars (vars e j) k).symm)
    have heq : 1 ≤ q A e := by
      have hc := single_le_sum (fun (k : Fin 3) _ => Nat.zero_le (minority A e k).toNat)
        (mem_univ i)
      simpa only [hi, Bool.toNat_true, q] using hc
    have hfq : 1 ≤ q A f := by
      have hc := single_le_sum (fun (k : Fin 3) _ => Nat.zero_le (minority A f k).toNat)
        (mem_univ t)
      simpa only [ht, Bool.toNat_true, q] using hc
    have := meeting_minority_large A hA e f hmeet heq hfq
    omega

  have equation_shift (A B : (Fin 15 → Fin 3 → Bool)) (e : (Fin 15)) :
      cost A B e + 2 * (∑ i, (minority A e i && flip A B e i).toNat) =
      cost A A e + 2 * (∑ i, (isConst (bits A (vars e i)) && flip A B e i).toNat) := by
    have hs := sum_congr (s₁ := (univ : Finset (Fin 3))) rfl fun i _ =>
      local_shift (bits A (vars e i)) (idx e i) (B e i)
    simp only [bits_idx, sum_add_distrib, ← mul_sum] at hs
    exact hs

  have three_cost_bound (A B : (Fin 15 → Fin 3 → Bool)) (hA : ∀ e, sat e (A e))
      (hB : ∀ e, sat e (B e)) (hm : m A = 3) (e : (Fin 15)) : cost A A e ≤ cost A B e := by
    have hf : (∑ i, (flip A B e i).toNat) = 2 * disag A B e := by
      exact valid_flip_count (A e) (B e) ((hA e).trans (hB e).symm)
    have hi := isolated_flip_bound (minority A e) (fun i => isConst (bits A (vars e i)))
      (flip A B e) (three_isolated A hA hm e) (by omega)
    have hs := equation_shift A B e
    omega
  have hm := at_least_three A hA
  by_cases h3 : m A = 3
  · have hs := sum_le_sum (s := (univ : Finset (Fin 15))) fun e _ => three_cost_bound A B hA hB h3 e
    simp only [← loss_eq_cost, loss_baseline, h3] at hs
    omega
  · by_cases h4 : m A = 4
    · have hs := sum_le_sum (s := (univ : Finset (Fin 15))) fun e _ => small_cost_bound A B hA (by omega) e
      simp only [sum_add_distrib, ← mul_sum, ← loss_eq_cost, loss_baseline] at hs
      have hd : (∑ e, disag A B e) = hammingDist A B := by
        unfold hammingDist
        change (∑ e, (if A e = B e then 0 else 1)) =
          (univ.filter (fun i => A i ≠ B i)).card
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
        simp [ne_eq]
      rw [hd] at hs
      omega
    · have := general_loss_bound A B hA hB
      omega

private theorem grid_bound (A B : (Fin 15 → Fin 3 → Bool)) (hA : ∀ e, sat e (A e))
    (hB : ∀ e, sat e (B e)) : 10 ≤ L A B := by
  have inc_vars : ∀ v j, vars (inc v j).1 (inc v j).2 = v := by decide +kernel

  have sat_cast (e : (Fin 15)) (a : (Fin 3 → Bool)) (h : sat e a) :
      (∑ i, (a i).toNat : ZMod 2) = ((odd e).toNat : ZMod 2) := by
    have h' := congrArg (fun n : ℕ => (n : ZMod 2)) h
    simpa only [sat, Nat.cast_sum, ZMod.natCast_mod] using h'

  have rowpos_bij : ∀ g i, Function.Bijective (rowpos g i) := by decide +kernel

  have colpos_bij : ∀ g j, Function.Bijective (fun i => colpos g i j) := by decide +kernel

  have grid_shared : ∀ g i j,
      vars (row g i) (rowpos g i j) = vars (col g j) (colpos g i j) := by decide +kernel

  have parts_odd : ∀ g,
      (∑ i, (odd (row g i)).toNat : ZMod 2) + (∑ j, (odd (col g j)).toNat : ZMod 2) = 1 := by decide +kernel

  have mismatch_zero : ∀ a b : Bool, (a != b).toNat = 0 → a = b := by decide +kernel

  have grid_loss_positive (A B : (Fin 15 → Fin 3 → Bool)) (hA : ∀ e, sat e (A e))
      (hB : ∀ e, sat e (B e)) (g : Fin 10) : 1 ≤ dirGridLoss A B g := by
    by_contra hn
    have hz : dirGridLoss A B g = 0 := by omega
    have hbits (i j : Fin 3) : A (row g i) (rowpos g i j) = B (col g j) (colpos g i j) := by
      have h1 := single_le_sum (fun (j' : Fin 3) _ => Nat.zero_le
        (A (row g i) (rowpos g i j') != B (col g j') (colpos g i j')).toNat) (mem_univ j)
      have h2 := single_le_sum (fun (i' : Fin 3) _ => Nat.zero_le
        (∑ j', (A (row g i') (rowpos g i' j') != B (col g j') (colpos g i' j')).toNat)) (mem_univ i)
      have hh : (A (row g i) (rowpos g i j) != B (col g j) (colpos g i j)).toNat = 0 := by
        change _ ≤ dirGridLoss A B g at h2
        omega
      exact mismatch_zero _ _ hh
    have hsum : (∑ i, ∑ k, ((A (row g i) k).toNat : ZMod 2)) =
        ∑ j, ∑ k, ((B (col g j) k).toNat : ZMod 2) := by
      calc
        _ = ∑ i, ∑ j, ((A (row g i) (rowpos g i j)).toNat : ZMod 2) := by
          apply sum_congr rfl; intro i _
          symm
          simpa only [Equiv.ofBijective_apply] using
            Equiv.sum_comp (Equiv.ofBijective _ (rowpos_bij g i))
              (fun k : Fin 3 => ((A (row g i) k).toNat : ZMod 2))
        _ = ∑ i, ∑ j, ((B (col g j) (colpos g i j)).toNat : ZMod 2) := by simp_rw [hbits]
        _ = ∑ j, ∑ i, ((B (col g j) (colpos g i j)).toNat : ZMod 2) := sum_comm
        _ = _ := by
          apply sum_congr rfl; intro j _
          simpa only [Equiv.ofBijective_apply] using
            Equiv.sum_comp (Equiv.ofBijective _ (colpos_bij g j))
              (fun k : Fin 3 => ((B (col g j) k).toNat : ZMod 2))
    simp_rw [sat_cast _ _ (hA _), sat_cast _ _ (hB _)] at hsum
    have hp := parts_odd g
    rw [hsum] at hp
    have ht (z : ZMod 2) : z+z = 0 := by
      calc z+z = z*(2:ZMod 2) := by ring
           _ = 0 := by rw [show (2:ZMod 2)=0 by decide +kernel, mul_zero]
    rw [ht] at hp
    exact (by decide : (0 : ZMod 2) ≠ 1) hp

  have edge_multiplicity : ∀ z : (Fin 15) × (Fin 15),
      (edges.filter fun x => edgeQ x = z).card = if meet z.1 z.2 then 1 else 0 := by decide +kernel

  have cross_multiplicity : ∀ z : (Fin 15) × (Fin 15),
      ((univ : Finset (Fin 10 × (Fin 3 × (Fin 3 × Bool)))).filter fun x => crossQ x = z).card =
        if meet z.1 z.2 then 2 else 0 := by decide +kernel

  have shared_positions : ∀ v (i j k l : Fin 3), i ≠ j →
      (vars (inc v i).1 k = vars (inc v j).1 l ↔ k = (inc v i).2 ∧ l = (inc v j).2) := by decide +kernel

  have grid_positions : ∀ g (i j k l : Fin 3),
      (vars (row g i) k = vars (col g j) l ↔ k = rowpos g i j ∧ l = colpos g i j) := by decide +kernel

  have indicator_mismatch : ∀ a b : Bool,
      (if a = b then 0 else 1) = (a != b).toNat := by decide +kernel

  have R_inc (A B : (Fin 15 → Fin 3 → Bool)) (hA : ∀ e, sat e (A e)) (hB : ∀ e, sat e (B e))
      (v : Fin 15) (i j : Fin 3) (hij : i ≠ j) :
      R (inc v i).1 (inc v j).1 (A (inc v i).1) (B (inc v j).1) ↔
        bits A v i = bits B v j := by
    constructor
    · intro h
      exact h.2.2 _ _ ((inc_vars v i).trans (inc_vars v j).symm)
    · intro h
      refine ⟨hA _, hB _, ?_⟩
      intro k l hkl
      obtain ⟨hk,hl⟩ := (shared_positions v i j k l hij).mp hkl
      simpa only [hk, hl, bits] using h

  have edge_loss_sum (A B : (Fin 15 → Fin 3 → Bool)) (hA : ∀ e, sat e (A e))
      (hB : ∀ e, sat e (B e)) : ∑ z ∈ intersecting, questionLoss A B z = L A B := by
    have hs := Finset.sum_fiberwise' edges edgeQ (questionLoss A B)
    simp only [sum_const, smul_eq_mul, edge_multiplicity] at hs
    have ht (x : (Fin 15 × (Fin 3 × Fin 3))) (hx : x ∈ edges) :
        questionLoss A B (edgeQ x) = (bits A x.1 x.2.1 != bits B x.1 x.2.2).toNat := by
      have hij : x.2.1 ≠ x.2.2 := (mem_filter.mp hx).2
      unfold questionLoss edgeQ
      simp only [R_inc A B hA hB _ _ _ hij]
      exact indicator_mismatch _ _
    have hR : (∑ x ∈ edges, questionLoss A B (edgeQ x)) = L A B := by
      rw [Finset.sum_congr rfl ht]
      calc
        (∑ x ∈ edges, (bits A x.1 x.2.1 != bits B x.1 x.2.2).toNat) =
          ∑ v, ∑ i, ∑ j, if i = j then 0 else (bits A v i != bits B v j).toNat := by
            simp only [edges, sum_filter, Fintype.sum_prod_type, ite_not]
        _ = ∑ v, ∑ j, ∑ i, if i = j then 0 else (bits A v i != bits B v j).toNat := by
          apply sum_congr rfl; intro v _; exact sum_comm
        _ = L A B := rfl
    have hL : (∑ z : (Fin 15) × (Fin 15), (if meet z.1 z.2 then 1 else 0) * questionLoss A B z) =
        ∑ z ∈ intersecting, questionLoss A B z := by
      simp [intersecting, sum_filter, ite_mul]
    rw [hL, hR] at hs
    exact hs

  have R_grid (A B : (Fin 15 → Fin 3 → Bool)) (hA : ∀ e, sat e (A e)) (hB : ∀ e, sat e (B e))
      (g : Fin 10) (i j : Fin 3) : R (row g i) (col g j) (A (row g i)) (B (col g j)) ↔
        A (row g i) (rowpos g i j) = B (col g j) (colpos g i j) := by
    constructor
    · intro h; exact h.2.2 _ _ (grid_shared g i j)
    · intro h
      refine ⟨hA _, hB _, ?_⟩
      intro k l hkl
      obtain ⟨hk,hl⟩ := (grid_positions g i j k l).mp hkl
      simpa only [hk, hl] using h

  have R_symm (e f : (Fin 15)) (a b : (Fin 3 → Bool)) : R e f a b ↔ R f e b a := by
    constructor <;> intro h
    · refine ⟨h.2.1, h.1, ?_⟩; intro i j hij; exact (h.2.2 j i hij.symm).symm
    · refine ⟨h.2.1, h.1, ?_⟩; intro i j hij; exact (h.2.2 j i hij.symm).symm

  have cross_loss_sum (A B : (Fin 15 → Fin 3 → Bool)) (hA : ∀ e, sat e (A e))
      (hB : ∀ e, sat e (B e)) :
      (∑ g, (dirGridLoss A B g + dirGridLoss B A g)) = 2 * L A B := by
    have hs := Finset.sum_fiberwise' (univ : Finset (Fin 10 × (Fin 3 × (Fin 3 × Bool)))) crossQ (questionLoss A B)
    simp only [sum_const, smul_eq_mul, cross_multiplicity] at hs
    have hL : (∑ z : (Fin 15) × (Fin 15), (if meet z.1 z.2 then 2 else 0) * questionLoss A B z) =
        2 * L A B := by
      rw [← edge_loss_sum A B hA hB]
      simp [intersecting, sum_filter, ite_mul, mul_ite, mul_sum]
    have ht (g : Fin 10) (i j : Fin 3) (d : Bool) :
        questionLoss A B (crossQ (g,i,j,d)) =
        if d then (A (row g i) (rowpos g i j) != B (col g j) (colpos g i j)).toNat
        else (B (row g i) (rowpos g i j) != A (col g j) (colpos g i j)).toNat := by
      cases d
      · have hp : R (col g j) (row g i) (A (col g j)) (B (row g i)) ↔
            B (row g i) (rowpos g i j) = A (col g j) (colpos g i j) :=
          (R_symm _ _ _ _).trans (R_grid B A hB hA g i j)
        simp only [crossQ, Bool.false_eq_true, if_false, questionLoss, hp]
        exact indicator_mismatch _ _
      · simp only [crossQ, if_true, questionLoss, R_grid A B hA hB g i j]
        exact indicator_mismatch _ _
    have hR : (∑ x : (Fin 10 × (Fin 3 × (Fin 3 × Bool))), questionLoss A B (crossQ x)) =
        ∑ g, (dirGridLoss A B g + dirGridLoss B A g) := by
      simp only [Fintype.sum_prod_type]
      simp_rw [ht]
      simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true,
        sum_add_distrib, dirGridLoss]
    rw [hL, hR] at hs
    exact hs.symm
  have hs := sum_le_sum (s := (univ : Finset (Fin 10))) fun g _ =>
    Nat.add_le_add (grid_loss_positive A B hA hB g) (grid_loss_positive B A hB hA g)
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, cross_loss_sum A B hA hB] at hs
  omega

theorem result : claim := by
  have explicit_probability : winProb (1/10) explicitStrategy explicitStrategy = 22/25 := by
    have h0 : intersecting.card = 90 := by decide +kernel
    have h1 : (intersecting.filter fun q => R q.1 q.2
      (explicitStrategy q.1) (explicitStrategy q.2)).card = 78 := by decide +kernel
    have h2 : (univ.filter fun e => R e e (explicitStrategy e) (explicitStrategy e)).card = 15 := by decide +kernel
    norm_num [winProb, h0, h1, h2]

  have inc_vars : ∀ v j, vars (inc v j).1 (inc v j).2 = v := by decide +kernel

  have vars_injective : ∀ e, Function.Injective (vars e) := by decide +kernel

  have edge_multiplicity : ∀ z : (Fin 15) × (Fin 15),
      (edges.filter fun x => edgeQ x = z).card = if meet z.1 z.2 then 1 else 0 := by decide +kernel

  have shared_positions : ∀ v (i j k l : Fin 3), i ≠ j →
      (vars (inc v i).1 k = vars (inc v j).1 l ↔ k = (inc v i).2 ∧ l = (inc v j).2) := by decide +kernel

  have indicator_mismatch : ∀ a b : Bool,
      (if a = b then 0 else 1) = (a != b).toNat := by decide +kernel

  have R_inc (A B : (Fin 15 → Fin 3 → Bool)) (hA : ∀ e, sat e (A e)) (hB : ∀ e, sat e (B e))
      (v : Fin 15) (i j : Fin 3) (hij : i ≠ j) :
      R (inc v i).1 (inc v j).1 (A (inc v i).1) (B (inc v j).1) ↔
        bits A v i = bits B v j := by
    constructor
    · intro h
      exact h.2.2 _ _ ((inc_vars v i).trans (inc_vars v j).symm)
    · intro h
      refine ⟨hA _, hB _, ?_⟩
      intro k l hkl
      obtain ⟨hk,hl⟩ := (shared_positions v i j k l hij).mp hkl
      simpa only [hk, hl, bits] using h

  have edge_loss_sum (A B : (Fin 15 → Fin 3 → Bool)) (hA : ∀ e, sat e (A e))
      (hB : ∀ e, sat e (B e)) : ∑ z ∈ intersecting, questionLoss A B z = L A B := by
    have hs := Finset.sum_fiberwise' edges edgeQ (questionLoss A B)
    simp only [sum_const, smul_eq_mul, edge_multiplicity] at hs
    have ht (x : (Fin 15 × (Fin 3 × Fin 3))) (hx : x ∈ edges) :
        questionLoss A B (edgeQ x) = (bits A x.1 x.2.1 != bits B x.1 x.2.2).toNat := by
      have hij : x.2.1 ≠ x.2.2 := (mem_filter.mp hx).2
      unfold questionLoss edgeQ
      simp only [R_inc A B hA hB _ _ _ hij]
      exact indicator_mismatch _ _
    have hR : (∑ x ∈ edges, questionLoss A B (edgeQ x)) = L A B := by
      rw [Finset.sum_congr rfl ht]
      calc
        (∑ x ∈ edges, (bits A x.1 x.2.1 != bits B x.1 x.2.2).toNat) =
          ∑ v, ∑ i, ∑ j, if i = j then 0 else (bits A v i != bits B v j).toNat := by
            simp only [edges, sum_filter, Fintype.sum_prod_type, ite_not]
        _ = ∑ v, ∑ j, ∑ i, if i = j then 0 else (bits A v i != bits B v j).toNat := by
          apply sum_congr rfl; intro v _; exact sum_comm
        _ = L A B := rfl
    have hL : (∑ z : (Fin 15) × (Fin 15), (if meet z.1 z.2 then 1 else 0) * questionLoss A B z) =
        ∑ z ∈ intersecting, questionLoss A B z := by
      simp [intersecting, sum_filter, ite_mul]
    rw [hL, hR] at hs
    exact hs

  have weighted_loss_bound (A B : (Fin 15 → Fin 3 → Bool)) (hA : ∀ e, sat e (A e))
      (hB : ∀ e, sat e (B e)) : 36 ≤ 3 * L A B + 2 * hammingDist A B := by
    by_cases hr : hammingDist A B ≤ 2
    · have := few_disagreements A B hA hB hr; omega
    · have := grid_bound A B hA hB; omega

  have nonsync_account (A B : (Fin 15 → Fin 3 → Bool)) (hA : ∀ e, sat e (A e))
      (hB : ∀ e, sat e (B e)) :
      (intersecting.filter fun z => R z.1 z.2 (A z.1) (B z.2)).card + L A B = 90 := by
    have hL : (intersecting.filter fun z => ¬ R z.1 z.2 (A z.1) (B z.2)).card = L A B := by
      rw [← edge_loss_sum A B hA hB]
      symm
      simpa only [questionLoss, ite_not, Nat.cast_id] using
        (Finset.sum_boole (R := ℕ) (fun z => ¬ R z.1 z.2 (A z.1) (B z.2)) intersecting)
    have hs := card_filter_add_card_filter_not (s := intersecting) (fun z => R z.1 z.2 (A z.1) (B z.2))
    rw [hL] at hs
    exact hs.trans (by decide +kernel)

  have R_sync (A B : (Fin 15 → Fin 3 → Bool)) (hA : ∀ e, sat e (A e))
      (hB : ∀ e, sat e (B e)) (e : (Fin 15)) : R e e (A e) (B e) ↔ A e = B e := by
    constructor
    · intro h; funext i; exact h.2.2 i i rfl
    · intro h; refine ⟨hA e, hB e, ?_⟩
      intro i j hij
      have hij' : i = j := vars_injective e hij
      subst j
      exact congrFun h i

  have sync_account (A B : (Fin 15 → Fin 3 → Bool)) (hA : ∀ e, sat e (A e))
      (hB : ∀ e, sat e (B e)) :
      (univ.filter fun e => R e e (A e) (B e)).card + hammingDist A B = 15 := by
    have hr : (univ.filter fun e => ¬ R e e (A e) (B e)).card = hammingDist A B := by
      simp only [hammingDist, Finset.card_eq_sum_ones, Finset.sum_filter, R_sync A B hA hB,
        ite_not, Nat.cast_id]
    have hs := card_filter_add_card_filter_not (s := (univ : Finset (Fin 15))) (fun e => R e e (A e) (B e))
    rw [hr] at hs
    simpa using hs

  have probability_account (A B : (Fin 15 → Fin 3 → Bool)) (hA : ∀ e, sat e (A e))
      (hB : ∀ e, sat e (B e)) :
      300 * (1 - winProb (1/10) A B) = 3 * (L A B : ℝ) + 2 * (hammingDist A B : ℝ) := by
    have hL := congrArg (fun n : ℕ => (n : ℝ)) (nonsync_account A B hA hB)
    have hr := congrArg (fun n : ℕ => (n : ℝ)) (sync_account A B hA hB)
    simp only [Nat.cast_add, Nat.cast_ofNat] at hL hr
    have hc : intersecting.card = 90 := by decide +kernel
    unfold winProb
    rw [hc]
    push_cast
    nlinarith

  have valid_probability_bound (A B : (Fin 15 → Fin 3 → Bool)) (hA : ∀ e, sat e (A e))
      (hB : ∀ e, sat e (B e)) : winProb (1/10) A B ≤ 22/25 := by
    have hw := weighted_loss_bound A B hA hB
    have hw' : (36 : ℝ) ≤ 3 * (L A B : ℝ) + 2 * (hammingDist A B : ℝ) := by exact_mod_cast hw
    have ha := probability_account A B hA hB
    linarith

  have repair_valid (A : (Fin 15 → Fin 3 → Bool)) : ∀ e, sat e (repair A e) := by
    have hs : ∀ e, sat e (explicitStrategy e) := by decide +kernel
    intro e
    by_cases h : sat e (A e)
    · simpa only [repair, if_pos h] using h
    · simpa only [repair, if_neg h] using hs e

  have repair_preserves_win (A B : (Fin 15 → Fin 3 → Bool)) (e f : (Fin 15))
      (h : R e f (A e) (B f)) : R e f (repair A e) (repair B f) := by
    simpa only [repair, if_pos h.1, if_pos h.2.1] using h

  have repair_probability (A B : (Fin 15 → Fin 3 → Bool)) :
      winProb (1/10) A B ≤ winProb (1/10) (repair A) (repair B) := by
    have h1 : (intersecting.filter fun z => R z.1 z.2 (A z.1) (B z.2)).card ≤
        (intersecting.filter fun z => R z.1 z.2 (repair A z.1) (repair B z.2)).card := by
      apply card_le_card
      intro z hz
      obtain ⟨hz,hR⟩ := mem_filter.mp hz
      exact mem_filter.mpr ⟨hz, repair_preserves_win A B _ _ hR⟩
    have h2 : (univ.filter fun e => R e e (A e) (B e)).card ≤
        (univ.filter fun e => R e e (repair A e) (repair B e)).card := by
      apply card_le_card
      intro e he
      obtain ⟨he,hR⟩ := mem_filter.mp he
      exact mem_filter.mpr ⟨he, repair_preserves_win A B _ _ hR⟩
    have h1' : ((intersecting.filter fun z => R z.1 z.2 (A z.1) (B z.2)).card : ℝ) ≤
        ((intersecting.filter fun z => R z.1 z.2 (repair A z.1) (repair B z.2)).card : ℝ) := by exact_mod_cast h1
    have h2' : ((univ.filter fun e => R e e (A e) (B e)).card : ℝ) ≤
        ((univ.filter fun e => R e e (repair A e) (repair B e)).card : ℝ) := by exact_mod_cast h2
    unfold winProb
    have hc : intersecting.card = 90 := by decide +kernel
    rw [hc]
    push_cast
    nlinarith

  have probability_bound (A B : (Fin 15 → Fin 3 → Bool)) : winProb (1/10) A B ≤ 22/25 :=
    (repair_probability A B).trans (valid_probability_bound (repair A) (repair B)
      (repair_valid A) (repair_valid B))
  unfold claim classicalValue
  let _ := Fintype.ofFinite ((Fin 15 → Fin 3 → Bool) × (Fin 15 → Fin 3 → Bool))
  apply le_antisymm
  · apply Finset.sup'_le
    intro S _
    exact probability_bound S.1 S.2
  · calc
      (22/25 : ℝ) = winProb (1/10) explicitStrategy explicitStrategy := explicit_probability.symm
      _ ≤ _ := Finset.le_sup' (f := fun S : (Fin 15 → Fin 3 → Bool) × (Fin 15 → Fin 3 → Bool) => winProb (1/10) S.1 S.2)
        (mem_univ (explicitStrategy, explicitStrategy))

end SynchronousDoilyClassicalValue
