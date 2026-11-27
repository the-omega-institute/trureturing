/- GID: D5/S3/Combinatorics/Turnpike/PrunedSingletonProjectionObstruction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Turnpike/PrunedSingletonProjectionObstruction
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Turnpike/PrunedSingletonProjectionObstruction.claim; result=D5/S3/Combinatorics/Turnpike/PrunedSingletonProjectionObstruction.result; claim=D5/S3/Combinatorics/Turnpike/PrunedSingletonProjectionObstruction.claim
   digest: A realizable nine-point assignment passes every singleton cut but has no full lift. -/
module
public import OmegaMath.Combinatorics.Turnpike.PrunedTriangleLP
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin

/-! The numerical relation and marginal system are from Elder, Marçais and
Kingsford, WABI 2026, Proposition 10 and System 11 (CC BY 4.0).
The rank-pruned singleton-cut comparison and this certificate are repository-derived.
-/
@[expose] public section
namespace D5.S3.Combinatorics.Turnpike.PrunedSingletonProjectionObstruction
open Omega.Turnpike
open scoped BigOperators
noncomputable section

def claim : Prop :=
  ∀ (n d : ℕ) (y : Fin d → ℝ) (μ : Fin d → ℕ), Admissible n d y μ →
    (∃ x : Fin n → ℝ, Realizes y μ x) →
    PrunedProjection (n := n) y μ full =
      {P | P ∈ PrunedProjection y μ spine ∧ SingletonCuts y μ P}

private def values : Fin 20 → ℕ := ![22, 21, 20, 19, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 6, 5, 4, 3, 2, 1]
private def y : Fin 20 → ℝ := fun q => values q
private def μ : Fin 20 → ℕ := ![1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 1, 2, 2, 1, 2, 3, 4]
private def xNat : Fin 9 → ℕ := ![0, 5, 6, 9, 11, 19, 20, 21, 22]
private def ruler : Fin 9 → ℝ := fun i => xNat i
private def numerator (e : Interval 9) (q : Fin 20) : ℕ :=
  match e.1.1.val, e.1.2.val with
  | 0, 1 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 10, 20] q
  | 0, 2 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 38, 12, 0, 0, 12, 0] q
  | 0, 3 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 19, 22, 8, 0, 0, 12, 0, 0] q
  | 0, 4 => ![0, 0, 0, 0, 0, 0, 0, 2, 8, 4, 10, 31, 7, 0, 0, 0, 0, 0, 0, 0] q
  | 0, 5 => ![0, 0, 0, 32, 0, 8, 0, 10, 10, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0] q
  | 0, 6 => ![0, 0, 32, 0, 10, 16, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] q
  | 0, 7 => ![0, 42, 8, 0, 8, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] q
  | 0, 8 => ![62, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] q
  | 1, 2 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 6, 8, 0, 44] q
  | 1, 3 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 8, 9, 0, 11, 13, 11, 9] q
  | 1, 4 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 10, 11, 0, 0, 23, 7, 0, 0, 0] q
  | 1, 5 => ![0, 0, 0, 0, 0, 0, 8, 32, 10, 0, 10, 2, 0, 0, 0, 0, 0, 0, 0, 0] q
  | 1, 6 => ![0, 0, 0, 0, 0, 4, 50, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] q
  | 1, 7 => ![0, 0, 0, 18, 0, 40, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] q
  | 1, 8 => ![0, 20, 10, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] q
  | 2, 3 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 22, 19, 20] q
  | 2, 4 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 6, 0, 9, 6, 26, 7, 0, 0] q
  | 2, 5 => ![0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 12, 6, 12, 0, 0, 0, 0, 0, 0, 0] q
  | 2, 6 => ![0, 0, 0, 0, 0, 0, 4, 36, 0, 4, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0] q
  | 2, 7 => ![0, 0, 0, 0, 0, 6, 50, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] q
  | 2, 8 => ![0, 0, 12, 0, 12, 38, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] q
  | 3, 4 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 6, 4, 11, 0, 2, 17, 18] q
  | 3, 5 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 27, 0, 0, 0, 7, 0, 0, 3, 0] q
  | 3, 6 => ![0, 0, 0, 0, 0, 0, 0, 0, 8, 12, 23, 8, 11, 0, 0, 0, 0, 0, 0, 0] q
  | 3, 7 => ![0, 0, 0, 0, 0, 0, 8, 8, 26, 11, 8, 1, 0, 0, 0, 0, 0, 0, 0, 0] q
  | 3, 8 => ![0, 0, 0, 12, 0, 8, 0, 22, 19, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] q
  | 4, 5 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 31, 0, 1, 5, 0, 6, 18, 1] q
  | 4, 6 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 25, 0, 0, 16, 0, 0, 8, 6, 0] q
  | 4, 7 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 38, 7, 5, 0, 2, 0, 6, 2, 2, 0] q
  | 4, 8 => ![0, 0, 0, 0, 0, 0, 0, 0, 7, 31, 10, 4, 8, 2, 0, 0, 0, 0, 0, 0] q
  | 5, 6 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 6, 10, 44] q
  | 5, 7 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 10, 6, 0, 0, 0, 34, 10] q
  | 5, 8 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 10, 10, 8, 0, 0, 32, 0, 0] q
  | 6, 7 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 6, 6, 4, 40] q
  | 6, 8 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 16, 10, 0, 0, 32, 0] q
  | 7, 8 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 8, 0, 0, 8, 42] q
  | _, _ => 0
private def assignment : Assignment 9 20 := fun e q => (numerator e q : ℝ) / 62
private def raw (τ : Triangle 9) (s : Fin 12) : (Fin 20 × Fin 20 × Fin 20) × ℕ :=
  match τ.1.2.1.val, τ.1.2.2.val with
  | 1, 2 => ![((15,19,14),32), ((18,16,14),2), ((18,17,15),8), ((19,15,14),4), ((19,16,15),4), ((19,19,18),12), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0)] s
  | 1, 3 => ![((15,16,12),11), ((15,17,13),13), ((15,19,14),8), ((18,14,13),9), ((18,19,17),1), ((19,11,10),1), ((19,13,12),8), ((19,18,17),11), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0)] s
  | 1, 4 => ![((15,12,7),2), ((15,15,11),23), ((15,16,12),7), ((18,10,8),8), ((18,11,9),1), ((18,12,10),1), ((19,10,9),3), ((19,11,10),9), ((19,12,11),8), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0)] s
  | 1, 5 => ![((15,7,3),32), ((18,10,8),10), ((19,6,5),8), ((19,8,7),10), ((19,11,10),2), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0)] s
  | 1, 6 => ![((15,6,2),32), ((18,6,4),6), ((18,7,5),4), ((19,5,4),4), ((19,6,5),12), ((19,8,7),4), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0)] s
  | 1, 7 => ![((15,5,1),32), ((18,3,1),10), ((19,3,2),8), ((19,5,4),8), ((19,6,5),4), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0)] s
  | 1, 8 => ![((15,4,0),32), ((18,2,0),10), ((19,1,0),20), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0)] s
  | 2, 3 => ![((14,17,12),19), ((14,18,13),19), ((15,14,10),1), ((15,17,13),3), ((15,19,14),8), ((18,19,17),12), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0)] s
  | 2, 4 => ![((14,14,9),4), ((14,15,10),1), ((14,16,11),26), ((14,17,12),7), ((15,12,7),2), ((15,14,10),5), ((15,15,11),5), ((18,10,8),8), ((18,12,10),4), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0)] s
  | 2, 5 => ![((14,8,3),32), ((14,11,5),6), ((15,10,5),2), ((15,12,7),10), ((18,10,8),10), ((18,12,10),2), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0)] s
  | 2, 6 => ![((14,7,2),32), ((14,10,4),6), ((15,10,5),12), ((18,6,4),4), ((18,7,5),4), ((18,9,7),4), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0)] s
  | 2, 7 => ![((14,6,1),36), ((14,7,2),2), ((15,5,1),6), ((15,6,2),6), ((18,6,4),8), ((18,7,5),4), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0)] s
  | 2, 8 => ![((14,5,0),38), ((15,4,0),12), ((18,2,0),12), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0)] s
  | 3, 4 => ![((10,18,8),1), ((12,18,10),2), ((12,19,11),17), ((13,15,8),7), ((13,18,11),14), ((13,19,12),1), ((14,13,7),2), ((14,15,10),4), ((14,17,12),2), ((17,12,9),4), ((17,13,10),4), ((17,14,12),4)] s
  | 3, 5 => ![((10,18,8),1), ((12,11,3),17), ((12,18,10),2), ((13,10,3),15), ((13,15,8),7), ((14,11,5),8), ((17,10,7),10), ((17,11,8),2), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0)] s
  | 3, 6 => ![((10,12,2),1), ((12,10,2),19), ((13,9,2),12), ((13,12,4),10), ((14,11,5),8), ((17,8,5),8), ((17,10,7),4), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0)] s
  | 3, 7 => ![((10,11,1),1), ((12,9,1),11), ((12,10,2),8), ((13,8,1),22), ((14,6,1),8), ((17,7,4),8), ((17,8,5),4), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0)] s
  | 3, 8 => ![((10,10,0),1), ((12,8,0),19), ((13,7,0),22), ((14,5,0),8), ((17,3,0),12), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0)] s
  | 4, 5 => ![((7,18,5),2), ((8,14,3),1), ((8,17,5),6), ((8,19,7),1), ((9,18,7),4), ((10,18,8),10), ((11,12,3),31), ((12,15,7),5), ((12,18,10),2), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0)] s
  | 4, 6 => ![((7,18,5),2), ((8,17,5),8), ((9,18,7),4), ((10,14,4),10), ((11,11,2),25), ((11,14,5),6), ((12,10,2),7), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0)] s
  | 4, 7 => ![((7,18,5),2), ((8,16,4),6), ((8,17,5),2), ((9,12,1),4), ((10,11,1),7), ((10,12,2),1), ((10,14,4),2), ((11,10,1),31), ((12,10,2),7), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0)] s
  | 4, 8 => ![((7,13,0),2), ((8,12,0),8), ((9,11,0),4), ((10,10,0),10), ((11,9,0),31), ((12,8,0),7), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0)] s
  | 5, 6 => ![((3,19,2),32), ((5,19,4),8), ((7,18,5),10), ((8,17,5),6), ((8,19,7),4), ((10,14,4),2), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0)] s
  | 5, 7 => ![((3,18,1),30), ((3,19,2),2), ((5,19,4),8), ((7,14,2),6), ((7,18,5),4), ((8,13,1),10), ((10,11,1),2), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0)] s
  | 5, 8 => ![((3,17,0),32), ((5,14,0),8), ((7,13,0),10), ((8,12,0),10), ((10,10,0),2), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0)] s
  | 6, 7 => ![((2,19,1),32), ((4,16,1),4), ((4,17,2),6), ((5,15,1),6), ((5,16,2),2), ((5,19,4),8), ((7,18,5),4), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0)] s
  | 6, 8 => ![((2,18,0),32), ((4,15,0),10), ((5,14,0),16), ((7,13,0),4), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0)] s
  | 7, 8 => ![((1,19,0),42), ((2,18,0),8), ((4,15,0),8), ((5,14,0),4), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0), ((15,19,14),0)] s
  | _, _ => ((15,19,14),0)
private def occurrence (e : Interval 9) : Fin 20 :=
  match e.1.1.val, e.1.2.val with
  | 0, 1 => 15
  | 0, 2 => 14
  | 0, 3 => 12
  | 0, 4 => 10
  | 0, 5 => 3
  | 0, 6 => 2
  | 0, 7 => 1
  | 0, 8 => 0
  | 1, 2 => 19
  | 1, 3 => 16
  | 1, 4 => 14
  | 1, 5 => 7
  | 1, 6 => 6
  | 1, 7 => 5
  | 1, 8 => 4
  | 2, 3 => 17
  | 2, 4 => 15
  | 2, 5 => 8
  | 2, 6 => 7
  | 2, 7 => 6
  | 2, 8 => 5
  | 3, 4 => 18
  | 3, 5 => 11
  | 3, 6 => 10
  | 3, 7 => 9
  | 3, 8 => 8
  | 4, 5 => 13
  | 4, 6 => 12
  | 4, 7 => 11
  | 4, 8 => 10
  | 5, 6 => 19
  | 5, 7 => 18
  | 5, 8 => 17
  | 6, 7 => 19
  | 6, 8 => 18
  | 7, 8 => 19
  | _, _ => 0

private theorem admissible : Admissible 9 20 y μ := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · have h : StrictAnti values := by decide +kernel
    intro a b hab
    change (values b : ℝ) < (values a : ℝ)
    exact_mod_cast h hab
  · have h : ∀ q, 0 < values q := by decide +kernel
    intro q
    change (0 : ℝ) < (values q : ℝ)
    exact_mod_cast h q
  · decide +kernel
  · decide +kernel

private theorem realizes : Realizes y μ ruler := by
  have hm : StrictMono xNat := by decide +kernel
  have hd : ∀ e : Interval 9, xNat e.1.2 = xNat e.1.1 + values (occurrence e) := by
    decide +kernel
  have hc : ∀ q : Fin 20,
      (Finset.univ.filter fun e : Interval 9 => occurrence e = q).card = μ q := by
    decide +kernel
  have hr : ∀ e : Interval 9, ruler e.1.2 - ruler e.1.1 = y (occurrence e) := by
    intro e
    have h := congrArg (fun k : ℕ => (k : ℝ)) (hd e)
    push_cast at h
    change (xNat e.1.2 : ℝ) - xNat e.1.1 = values (occurrence e)
    linarith
  refine ⟨?_, fun e => ⟨occurrence e, hr e⟩, ?_⟩
  · intro i j hij
    change (xNat i : ℝ) < (xNat j : ℝ)
    exact_mod_cast hm hij
  · intro q
    have heq : (Finset.univ.filter fun e : Interval 9 =>
        ruler e.1.2 - ruler e.1.1 = y q) =
        (Finset.univ.filter fun e : Interval 9 => occurrence e = q) := by
      apply Finset.filter_congr
      intro e _
      rw [hr e]
      exact admissible.2.2.1.injective.eq_iff
    rw [heq]
    exact hc q

private theorem p_bounds : ∀ e : Interval 9, ∀ q : Fin 20,
    numerator e q ≤ 62 ∧ (numerator e q ≠ 0 → RankAllowed μ e q) := by
  unfold RankAllowed
  decide +kernel
private theorem p_rows : ∀ e : Interval 9, ∑ q, numerator e q = 62 := by
  decide +kernel
private theorem p_columns : ∀ q : Fin 20,
    ∑ e : Interval 9, numerator e q = 62 * μ q := by
  decide +kernel

private theorem domain : PrunedDomain μ assignment := by
  classical
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro e q
    have hb : (numerator e q : ℝ) ≤ 62 := by exact_mod_cast (p_bounds e q).1
    dsimp [assignment]
    constructor
    · positivity
    · linarith
  · intro e
    have h := congrArg (fun z : ℕ => (z : ℝ) / 62) (p_rows e)
    simpa [assignment, Nat.cast_sum, Finset.sum_div] using h
  · intro q
    have h := congrArg (fun z : ℕ => (z : ℝ) / 62) (p_columns q)
    simpa [assignment, Nat.cast_sum, Nat.cast_mul, Finset.sum_div] using h
  · intro e q
    by_cases hn : numerator e q = 0
    · simp [assignment,hn,rankMask]; split_ifs <;> norm_num
    · rw [rankMask, if_pos ((p_bounds e q).2 hn)]
      exact (show assignment e q ≤ 1 from by
        have hb : (numerator e q : ℝ) ≤ 62 := by exact_mod_cast (p_bounds e q).1
        dsimp [assignment]; linarith)

private theorem raw_valid : ∀ τ : Triangle 9, spine τ → ∀ s : Fin 12,
    values (raw τ s).1.1 + values (raw τ s).1.2.1 = values (raw τ s).1.2.2 ∧
    ((raw τ s).1.1 ≠ (raw τ s).1.2.1 ∨ 2 ≤ μ (raw τ s).1.1) := by
  unfold spine
  decide +kernel
private def support (τ : {τ : Triangle 9 // spine τ}) (s : Fin 12) : Relation y μ :=
  ⟨(raw τ.1 s).1, by
    refine ⟨?_, (raw_valid τ.1 τ.2 s).2⟩
    change (values _ : ℝ) + values _ = values _
    exact_mod_cast (raw_valid τ.1 τ.2 s).1⟩
private theorem raw_masks : ∀ τ : Triangle 9, spine τ → ∀ s : Fin 12,
    (raw τ s).2 ≠ 0 → ProductAllowed μ τ (raw τ s).1 := by
  unfold spine ProductAllowed RankAllowed
  decide +kernel
private theorem raw_total : ∀ τ : Triangle 9, spine τ →
    ∑ s : Fin 12, (raw τ s).2 = 62 := by
  unfold spine
  decide +kernel
private theorem raw_marginals : ∀ τ : Triangle 9, spine τ → ∀ u : Fin 3, ∀ q : Fin 20,
    (∑ s : Fin 12, if coordinate u (raw τ s).1 = q then (raw τ s).2 else 0) =
      numerator (edge τ u) q := by
  unfold spine
  decide +kernel

private def weight (τ : {τ : Triangle 9 // spine τ}) (s : Fin 12) : ℝ :=
  ((raw τ.1 s).2 : ℝ) / 62
private def coupling (τ : {τ : Triangle 9 // spine τ}) : Relation y μ → ℝ :=
  by
    classical
    exact weightedAtoms (support τ) (weight τ)

private theorem coupling_nonneg (τ : {τ : Triangle 9 // spine τ}) (r : Relation y μ) :
    0 ≤ coupling τ r := by
  classical
  unfold coupling weightedAtoms
  apply Finset.sum_nonneg
  intro s _
  unfold weight atom
  positivity
private theorem coupling_total (τ : {τ : Triangle 9 // spine τ}) :
    ∑ r, coupling τ r = 1 := by
  classical
  rw [coupling, weightedAtoms_sum]
  have h := congrArg (fun z : ℕ => (z : ℝ) / 62) (raw_total τ.1 τ.2)
  simpa [weight, Nat.cast_sum, Finset.sum_div] using h
private theorem coupling_marginal (τ : {τ : Triangle 9 // spine τ}) (u : Fin 3)
    (q : Fin 20) :
    (∑ r, if coordinate u r.1 = q then coupling τ r else 0) =
      assignment (edge τ.1 u) q := by
  classical
  rw [coupling, weightedAtoms_marginal]
  change (∑ s, if coordinate u (raw τ.1 s).1 = q then
    ((raw τ.1 s).2 : ℝ) / 62 else 0) = (numerator (edge τ.1 u) q : ℝ) / 62
  have h := congrArg (fun z : ℕ => (z : ℝ) / 62) (raw_marginals τ.1 τ.2 u q)
  simpa only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Finset.sum_div,
    ite_div, zero_div] using h

private theorem spine_feasible : assignment ∈ PrunedProjection y μ spine := by
  classical
  refine ⟨domain, coupling, ?_⟩
  intro τ
  have hb : ∀ r, coupling τ r ≤ 1 := by
    intro r
    calc
      coupling τ r ≤ ∑ r, coupling τ r :=
        Finset.single_le_sum (fun r _ => coupling_nonneg τ r) (Finset.mem_univ r)
      _ = 1 := coupling_total τ
  refine ⟨⟨fun r => ⟨coupling_nonneg τ r, hb r⟩, coupling_total τ, ?_, ?_, ?_⟩, ?_⟩
  · exact coupling_marginal τ 0
  · exact coupling_marginal τ 1
  · exact coupling_marginal τ 2
  · intro r
    by_cases hr : ProductAllowed μ τ.1 r.1
    · simp only [ProductAllowed] at hr
      simp [rankMask,hr.1,hr.2.1,hr.2.2]
      exact hb r
    · have hz : coupling τ r = 0 := by
        unfold coupling weightedAtoms
        apply Finset.sum_eq_zero
        intro s _
        by_cases hn : (raw τ.1 s).2 = 0
        · simp [weight,hn]
        · have hne : r ≠ support τ s := by
            intro he
            apply hr
            rw [he]
            exact raw_masks τ.1 τ.2 s hn
          simp [atom,hne]
      rw [hz]
      unfold rankMask
      split_ifs <;> norm_num

private def inverse (z : ℤ) : Fin 20 :=
  match z with
  | 22 => 0 | 21 => 1 | 20 => 2 | 19 => 3 | 17 => 4 | 16 => 5
  | 15 => 6 | 14 => 7 | 13 => 8 | 12 => 9 | 11 => 10 | 10 => 11
  | 9 => 12 | 8 => 13 | 6 => 14 | 5 => 15 | 4 => 16 | 3 => 17
  | 2 => 18 | 1 => 19 | _ => 0
private def candidate (u v : Fin 3) (a b : Fin 20) : Fin 20 × Fin 20 × Fin 20 :=
  if u = 0 then
    if v = 1 then (a,b,inverse ((values a : ℤ) + values b))
    else (a,inverse ((values b : ℤ) - values a),b)
  else (inverse ((values b : ℤ) - values a),a,b)
private def CutCheck (τ : Triangle 9) (u v w : Fin 3) (a b : Fin 20) : Prop :=
  numerator (edge τ u) a + numerator (edge τ v) b ≤ 62 ∨
  let r := candidate u v a b
  values r.1 + values r.2.1 = values r.2.2 ∧
  (r.1 ≠ r.2.1 ∨ 2 ≤ μ r.1) ∧ ProductAllowed μ τ r ∧
  coordinate u r = a ∧ coordinate v r = b ∧
  numerator (edge τ u) a + numerator (edge τ v) b ≤
    62 + numerator (edge τ w) (coordinate w r)
private theorem cut_012_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,2),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_012_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,2),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_012_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,2),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_013_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,3),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_013_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,3),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_013_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,3),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_014_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,4),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_014_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,4),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_014_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,4),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_015_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,5),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_015_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,5),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_015_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,5),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_016_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_016_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_016_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_017_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_017_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_017_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_018_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_018_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_018_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_023_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,3),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_023_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,3),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_023_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,3),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_024_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,4),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_024_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,4),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_024_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,4),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_025_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,5),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_025_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,5),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_025_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,5),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_026_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_026_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_026_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_027_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_027_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_027_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_028_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_028_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_028_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_034_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,4),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_034_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,4),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_034_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,4),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_035_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,5),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_035_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,5),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_035_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,5),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_036_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_036_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_036_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_037_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_037_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_037_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_038_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_038_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_038_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_045_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,4,5),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_045_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,4,5),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_045_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,4,5),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_046_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,4,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_046_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,4,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_046_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,4,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_047_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,4,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_047_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,4,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_047_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,4,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_048_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,4,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_048_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,4,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_048_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,4,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_056_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,5,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_056_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,5,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_056_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,5,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_057_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,5,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_057_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,5,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_057_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,5,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_058_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,5,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_058_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,5,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_058_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,5,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_067_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,6,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_067_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,6,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_067_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,6,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_068_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,6,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_068_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,6,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_068_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,6,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_078_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,7,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_078_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,7,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_078_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,7,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_123_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,3),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_123_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,3),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_123_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,3),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_124_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,4),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_124_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,4),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_124_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,4),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_125_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,5),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_125_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,5),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_125_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,5),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_126_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_126_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_126_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_127_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_127_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_127_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_128_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_128_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_128_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_134_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,4),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_134_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,4),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_134_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,4),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_135_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,5),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_135_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,5),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_135_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,5),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_136_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_136_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_136_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_137_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_137_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_137_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_138_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_138_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_138_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_145_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,4,5),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_145_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,4,5),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_145_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,4,5),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_146_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,4,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_146_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,4,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_146_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,4,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_147_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,4,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_147_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,4,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_147_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,4,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_148_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,4,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_148_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,4,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_148_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,4,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_156_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,5,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_156_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,5,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_156_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,5,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_157_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,5,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_157_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,5,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_157_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,5,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_158_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,5,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_158_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,5,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_158_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,5,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_167_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,6,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_167_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,6,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_167_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,6,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_168_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,6,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_168_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,6,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_168_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,6,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_178_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,7,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_178_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,7,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_178_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,7,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_234_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,4),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_234_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,4),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_234_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,4),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_235_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,5),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_235_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,5),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_235_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,5),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_236_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_236_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_236_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_237_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_237_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_237_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_238_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_238_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_238_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_245_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,4,5),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_245_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,4,5),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_245_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,4,5),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_246_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,4,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_246_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,4,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_246_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,4,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_247_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,4,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_247_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,4,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_247_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,4,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_248_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,4,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_248_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,4,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_248_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,4,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_256_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,5,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_256_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,5,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_256_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,5,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_257_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,5,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_257_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,5,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_257_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,5,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_258_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,5,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_258_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,5,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_258_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,5,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_267_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,6,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_267_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,6,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_267_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,6,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_268_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,6,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_268_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,6,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_268_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,6,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_278_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,7,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_278_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,7,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_278_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,7,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_345_01 : ∀ a b : Fin 20,
    CutCheck ⟨(3,4,5),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_345_02 : ∀ a b : Fin 20,
    CutCheck ⟨(3,4,5),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_345_12 : ∀ a b : Fin 20,
    CutCheck ⟨(3,4,5),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_346_01 : ∀ a b : Fin 20,
    CutCheck ⟨(3,4,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_346_02 : ∀ a b : Fin 20,
    CutCheck ⟨(3,4,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_346_12 : ∀ a b : Fin 20,
    CutCheck ⟨(3,4,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_347_01 : ∀ a b : Fin 20,
    CutCheck ⟨(3,4,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_347_02 : ∀ a b : Fin 20,
    CutCheck ⟨(3,4,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_347_12 : ∀ a b : Fin 20,
    CutCheck ⟨(3,4,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_348_01 : ∀ a b : Fin 20,
    CutCheck ⟨(3,4,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_348_02 : ∀ a b : Fin 20,
    CutCheck ⟨(3,4,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_348_12 : ∀ a b : Fin 20,
    CutCheck ⟨(3,4,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_356_01 : ∀ a b : Fin 20,
    CutCheck ⟨(3,5,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_356_02 : ∀ a b : Fin 20,
    CutCheck ⟨(3,5,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_356_12 : ∀ a b : Fin 20,
    CutCheck ⟨(3,5,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_357_01 : ∀ a b : Fin 20,
    CutCheck ⟨(3,5,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_357_02 : ∀ a b : Fin 20,
    CutCheck ⟨(3,5,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_357_12 : ∀ a b : Fin 20,
    CutCheck ⟨(3,5,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_358_01 : ∀ a b : Fin 20,
    CutCheck ⟨(3,5,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_358_02 : ∀ a b : Fin 20,
    CutCheck ⟨(3,5,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_358_12 : ∀ a b : Fin 20,
    CutCheck ⟨(3,5,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_367_01 : ∀ a b : Fin 20,
    CutCheck ⟨(3,6,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_367_02 : ∀ a b : Fin 20,
    CutCheck ⟨(3,6,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_367_12 : ∀ a b : Fin 20,
    CutCheck ⟨(3,6,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_368_01 : ∀ a b : Fin 20,
    CutCheck ⟨(3,6,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_368_02 : ∀ a b : Fin 20,
    CutCheck ⟨(3,6,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_368_12 : ∀ a b : Fin 20,
    CutCheck ⟨(3,6,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_378_01 : ∀ a b : Fin 20,
    CutCheck ⟨(3,7,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_378_02 : ∀ a b : Fin 20,
    CutCheck ⟨(3,7,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_378_12 : ∀ a b : Fin 20,
    CutCheck ⟨(3,7,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_456_01 : ∀ a b : Fin 20,
    CutCheck ⟨(4,5,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_456_02 : ∀ a b : Fin 20,
    CutCheck ⟨(4,5,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_456_12 : ∀ a b : Fin 20,
    CutCheck ⟨(4,5,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_457_01 : ∀ a b : Fin 20,
    CutCheck ⟨(4,5,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_457_02 : ∀ a b : Fin 20,
    CutCheck ⟨(4,5,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_457_12 : ∀ a b : Fin 20,
    CutCheck ⟨(4,5,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_458_01 : ∀ a b : Fin 20,
    CutCheck ⟨(4,5,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_458_02 : ∀ a b : Fin 20,
    CutCheck ⟨(4,5,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_458_12 : ∀ a b : Fin 20,
    CutCheck ⟨(4,5,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_467_01 : ∀ a b : Fin 20,
    CutCheck ⟨(4,6,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_467_02 : ∀ a b : Fin 20,
    CutCheck ⟨(4,6,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_467_12 : ∀ a b : Fin 20,
    CutCheck ⟨(4,6,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_468_01 : ∀ a b : Fin 20,
    CutCheck ⟨(4,6,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_468_02 : ∀ a b : Fin 20,
    CutCheck ⟨(4,6,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_468_12 : ∀ a b : Fin 20,
    CutCheck ⟨(4,6,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_478_01 : ∀ a b : Fin 20,
    CutCheck ⟨(4,7,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_478_02 : ∀ a b : Fin 20,
    CutCheck ⟨(4,7,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_478_12 : ∀ a b : Fin 20,
    CutCheck ⟨(4,7,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_567_01 : ∀ a b : Fin 20,
    CutCheck ⟨(5,6,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_567_02 : ∀ a b : Fin 20,
    CutCheck ⟨(5,6,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_567_12 : ∀ a b : Fin 20,
    CutCheck ⟨(5,6,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_568_01 : ∀ a b : Fin 20,
    CutCheck ⟨(5,6,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_568_02 : ∀ a b : Fin 20,
    CutCheck ⟨(5,6,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_568_12 : ∀ a b : Fin 20,
    CutCheck ⟨(5,6,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_578_01 : ∀ a b : Fin 20,
    CutCheck ⟨(5,7,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_578_02 : ∀ a b : Fin 20,
    CutCheck ⟨(5,7,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_578_12 : ∀ a b : Fin 20,
    CutCheck ⟨(5,7,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_678_01 : ∀ a b : Fin 20,
    CutCheck ⟨(6,7,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_678_02 : ∀ a b : Fin 20,
    CutCheck ⟨(6,7,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_678_12 : ∀ a b : Fin 20,
    CutCheck ⟨(6,7,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel

private def triangleCover : List (Triangle 9) :=
  [⟨(0,1,2),by decide⟩,
   ⟨(0,1,3),by decide⟩,
   ⟨(0,1,4),by decide⟩,
   ⟨(0,1,5),by decide⟩,
   ⟨(0,1,6),by decide⟩,
   ⟨(0,1,7),by decide⟩,
   ⟨(0,1,8),by decide⟩,
   ⟨(0,2,3),by decide⟩,
   ⟨(0,2,4),by decide⟩,
   ⟨(0,2,5),by decide⟩,
   ⟨(0,2,6),by decide⟩,
   ⟨(0,2,7),by decide⟩,
   ⟨(0,2,8),by decide⟩,
   ⟨(0,3,4),by decide⟩,
   ⟨(0,3,5),by decide⟩,
   ⟨(0,3,6),by decide⟩,
   ⟨(0,3,7),by decide⟩,
   ⟨(0,3,8),by decide⟩,
   ⟨(0,4,5),by decide⟩,
   ⟨(0,4,6),by decide⟩,
   ⟨(0,4,7),by decide⟩,
   ⟨(0,4,8),by decide⟩,
   ⟨(0,5,6),by decide⟩,
   ⟨(0,5,7),by decide⟩,
   ⟨(0,5,8),by decide⟩,
   ⟨(0,6,7),by decide⟩,
   ⟨(0,6,8),by decide⟩,
   ⟨(0,7,8),by decide⟩,
   ⟨(1,2,3),by decide⟩,
   ⟨(1,2,4),by decide⟩,
   ⟨(1,2,5),by decide⟩,
   ⟨(1,2,6),by decide⟩,
   ⟨(1,2,7),by decide⟩,
   ⟨(1,2,8),by decide⟩,
   ⟨(1,3,4),by decide⟩,
   ⟨(1,3,5),by decide⟩,
   ⟨(1,3,6),by decide⟩,
   ⟨(1,3,7),by decide⟩,
   ⟨(1,3,8),by decide⟩,
   ⟨(1,4,5),by decide⟩,
   ⟨(1,4,6),by decide⟩,
   ⟨(1,4,7),by decide⟩,
   ⟨(1,4,8),by decide⟩,
   ⟨(1,5,6),by decide⟩,
   ⟨(1,5,7),by decide⟩,
   ⟨(1,5,8),by decide⟩,
   ⟨(1,6,7),by decide⟩,
   ⟨(1,6,8),by decide⟩,
   ⟨(1,7,8),by decide⟩,
   ⟨(2,3,4),by decide⟩,
   ⟨(2,3,5),by decide⟩,
   ⟨(2,3,6),by decide⟩,
   ⟨(2,3,7),by decide⟩,
   ⟨(2,3,8),by decide⟩,
   ⟨(2,4,5),by decide⟩,
   ⟨(2,4,6),by decide⟩,
   ⟨(2,4,7),by decide⟩,
   ⟨(2,4,8),by decide⟩,
   ⟨(2,5,6),by decide⟩,
   ⟨(2,5,7),by decide⟩,
   ⟨(2,5,8),by decide⟩,
   ⟨(2,6,7),by decide⟩,
   ⟨(2,6,8),by decide⟩,
   ⟨(2,7,8),by decide⟩,
   ⟨(3,4,5),by decide⟩,
   ⟨(3,4,6),by decide⟩,
   ⟨(3,4,7),by decide⟩,
   ⟨(3,4,8),by decide⟩,
   ⟨(3,5,6),by decide⟩,
   ⟨(3,5,7),by decide⟩,
   ⟨(3,5,8),by decide⟩,
   ⟨(3,6,7),by decide⟩,
   ⟨(3,6,8),by decide⟩,
   ⟨(3,7,8),by decide⟩,
   ⟨(4,5,6),by decide⟩,
   ⟨(4,5,7),by decide⟩,
   ⟨(4,5,8),by decide⟩,
   ⟨(4,6,7),by decide⟩,
   ⟨(4,6,8),by decide⟩,
   ⟨(4,7,8),by decide⟩,
   ⟨(5,6,7),by decide⟩,
   ⟨(5,6,8),by decide⟩,
   ⟨(5,7,8),by decide⟩,
   ⟨(6,7,8),by decide⟩]

private theorem triangleCovered (τ : Triangle 9) : τ ∈ triangleCover := by
  decide +kernel

private theorem cuts_01 : ∀ τ ∈ triangleCover, ∀ a b : Fin 20,
    CutCheck τ 0 1 2 a b := by
  simp only [triangleCover, List.forall_mem_cons]
  exact ⟨cut_012_01,
    cut_013_01,
    cut_014_01,
    cut_015_01,
    cut_016_01,
    cut_017_01,
    cut_018_01,
    cut_023_01,
    cut_024_01,
    cut_025_01,
    cut_026_01,
    cut_027_01,
    cut_028_01,
    cut_034_01,
    cut_035_01,
    cut_036_01,
    cut_037_01,
    cut_038_01,
    cut_045_01,
    cut_046_01,
    cut_047_01,
    cut_048_01,
    cut_056_01,
    cut_057_01,
    cut_058_01,
    cut_067_01,
    cut_068_01,
    cut_078_01,
    cut_123_01,
    cut_124_01,
    cut_125_01,
    cut_126_01,
    cut_127_01,
    cut_128_01,
    cut_134_01,
    cut_135_01,
    cut_136_01,
    cut_137_01,
    cut_138_01,
    cut_145_01,
    cut_146_01,
    cut_147_01,
    cut_148_01,
    cut_156_01,
    cut_157_01,
    cut_158_01,
    cut_167_01,
    cut_168_01,
    cut_178_01,
    cut_234_01,
    cut_235_01,
    cut_236_01,
    cut_237_01,
    cut_238_01,
    cut_245_01,
    cut_246_01,
    cut_247_01,
    cut_248_01,
    cut_256_01,
    cut_257_01,
    cut_258_01,
    cut_267_01,
    cut_268_01,
    cut_278_01,
    cut_345_01,
    cut_346_01,
    cut_347_01,
    cut_348_01,
    cut_356_01,
    cut_357_01,
    cut_358_01,
    cut_367_01,
    cut_368_01,
    cut_378_01,
    cut_456_01,
    cut_457_01,
    cut_458_01,
    cut_467_01,
    cut_468_01,
    cut_478_01,
    cut_567_01,
    cut_568_01,
    cut_578_01,
    cut_678_01, List.forall_mem_nil _⟩

private theorem cuts_02 : ∀ τ ∈ triangleCover, ∀ a b : Fin 20,
    CutCheck τ 0 2 1 a b := by
  simp only [triangleCover, List.forall_mem_cons]
  exact ⟨cut_012_02,
    cut_013_02,
    cut_014_02,
    cut_015_02,
    cut_016_02,
    cut_017_02,
    cut_018_02,
    cut_023_02,
    cut_024_02,
    cut_025_02,
    cut_026_02,
    cut_027_02,
    cut_028_02,
    cut_034_02,
    cut_035_02,
    cut_036_02,
    cut_037_02,
    cut_038_02,
    cut_045_02,
    cut_046_02,
    cut_047_02,
    cut_048_02,
    cut_056_02,
    cut_057_02,
    cut_058_02,
    cut_067_02,
    cut_068_02,
    cut_078_02,
    cut_123_02,
    cut_124_02,
    cut_125_02,
    cut_126_02,
    cut_127_02,
    cut_128_02,
    cut_134_02,
    cut_135_02,
    cut_136_02,
    cut_137_02,
    cut_138_02,
    cut_145_02,
    cut_146_02,
    cut_147_02,
    cut_148_02,
    cut_156_02,
    cut_157_02,
    cut_158_02,
    cut_167_02,
    cut_168_02,
    cut_178_02,
    cut_234_02,
    cut_235_02,
    cut_236_02,
    cut_237_02,
    cut_238_02,
    cut_245_02,
    cut_246_02,
    cut_247_02,
    cut_248_02,
    cut_256_02,
    cut_257_02,
    cut_258_02,
    cut_267_02,
    cut_268_02,
    cut_278_02,
    cut_345_02,
    cut_346_02,
    cut_347_02,
    cut_348_02,
    cut_356_02,
    cut_357_02,
    cut_358_02,
    cut_367_02,
    cut_368_02,
    cut_378_02,
    cut_456_02,
    cut_457_02,
    cut_458_02,
    cut_467_02,
    cut_468_02,
    cut_478_02,
    cut_567_02,
    cut_568_02,
    cut_578_02,
    cut_678_02, List.forall_mem_nil _⟩

private theorem cuts_12 : ∀ τ ∈ triangleCover, ∀ a b : Fin 20,
    CutCheck τ 1 2 0 a b := by
  simp only [triangleCover, List.forall_mem_cons]
  exact ⟨cut_012_12,
    cut_013_12,
    cut_014_12,
    cut_015_12,
    cut_016_12,
    cut_017_12,
    cut_018_12,
    cut_023_12,
    cut_024_12,
    cut_025_12,
    cut_026_12,
    cut_027_12,
    cut_028_12,
    cut_034_12,
    cut_035_12,
    cut_036_12,
    cut_037_12,
    cut_038_12,
    cut_045_12,
    cut_046_12,
    cut_047_12,
    cut_048_12,
    cut_056_12,
    cut_057_12,
    cut_058_12,
    cut_067_12,
    cut_068_12,
    cut_078_12,
    cut_123_12,
    cut_124_12,
    cut_125_12,
    cut_126_12,
    cut_127_12,
    cut_128_12,
    cut_134_12,
    cut_135_12,
    cut_136_12,
    cut_137_12,
    cut_138_12,
    cut_145_12,
    cut_146_12,
    cut_147_12,
    cut_148_12,
    cut_156_12,
    cut_157_12,
    cut_158_12,
    cut_167_12,
    cut_168_12,
    cut_178_12,
    cut_234_12,
    cut_235_12,
    cut_236_12,
    cut_237_12,
    cut_238_12,
    cut_245_12,
    cut_246_12,
    cut_247_12,
    cut_248_12,
    cut_256_12,
    cut_257_12,
    cut_258_12,
    cut_267_12,
    cut_268_12,
    cut_278_12,
    cut_345_12,
    cut_346_12,
    cut_347_12,
    cut_348_12,
    cut_356_12,
    cut_357_12,
    cut_358_12,
    cut_367_12,
    cut_368_12,
    cut_378_12,
    cut_456_12,
    cut_457_12,
    cut_458_12,
    cut_467_12,
    cut_468_12,
    cut_478_12,
    cut_567_12,
    cut_568_12,
    cut_578_12,
    cut_678_12, List.forall_mem_nil _⟩

private theorem cut_checks (τ : Triangle 9) (u v w : Fin 3)
    (huv : u < v) (hwu : w ≠ u) (hwv : w ≠ v) (a b : Fin 20) :
    CutCheck τ u v w a b := by
  have hp : (u = 0 ∧ v = 1 ∧ w = 2) ∨
      (u = 0 ∧ v = 2 ∧ w = 1) ∨ (u = 1 ∧ v = 2 ∧ w = 0) := by
    fin_cases u <;> fin_cases v <;> fin_cases w <;> simp_all
  rcases hp with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · exact cuts_01 τ (triangleCovered τ) a b
  · exact cuts_02 τ (triangleCovered τ) a b
  · exact cuts_12 τ (triangleCovered τ) a b

private theorem singleton_cuts : SingletonCuts y μ assignment := by
  classical
  intro τ u v w huv hwu hwv a b
  have hn : 0 ≤ ∑ c ∈ Completion y μ τ u v w a b, assignment (edge τ w) c :=
    Finset.sum_nonneg fun c _ => (domain.1.1 _ _).1
  rcases cut_checks τ u v w huv hwu hwv a b with h | h
  · have hh : assignment (edge τ u) a + assignment (edge τ v) b ≤ 1 := by
      dsimp [assignment]
      have hh : (numerator (edge τ u) a : ℝ) + numerator (edge τ v) b ≤ 62 := by
        exact_mod_cast h
      linarith
    linarith
  · dsimp only at h
    let r := candidate u v a b
    let rr : Relation y μ := ⟨r, by
      refine ⟨?_, h.2.1⟩
      change (values r.1 : ℝ) + values r.2.1 = values r.2.2
      exact_mod_cast h.1⟩
    have hc : coordinate w r ∈ Completion y μ τ u v w a b := by
      simp only [Completion,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨rr,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,rfl⟩
    have hs : assignment (edge τ w) (coordinate w r) ≤
        ∑ c ∈ Completion y μ τ u v w a b, assignment (edge τ w) c :=
      Finset.single_le_sum (fun c _ => (domain.1.1 (edge τ w) c).1) hc
    have hh : assignment (edge τ u) a + assignment (edge τ v) b ≤
        1 + assignment (edge τ w) (coordinate w r) := by
      dsimp [assignment]
      have ht : (numerator (edge τ u) a : ℝ) + numerator (edge τ v) b ≤
          62 + numerator (edge τ w) (coordinate w r) := by
        exact_mod_cast h.2.2.2.2.2
      linarith
    linarith

private def obsA (q : Fin 20) : Bool := decide (q = 16 ∨ q = 17 ∨ q = 19)
private def obsB (q : Fin 20) : Bool := decide (q = 14 ∨ q = 17 ∨ q = 18 ∨ q = 19)
private def obsC (q : Fin 20) : Bool :=
  decide (q = 11 ∨ q = 12 ∨ q = 14 ∨ q = 15 ∨ q = 16 ∨ q = 17 ∨ q = 18)

private theorem observation_marginal {α : Type*} [Fintype α]
    (f : α → Fin 20) (o : Fin 20 → Bool) (T : α → ℝ) (p : Fin 20 → ℝ)
    (hm : ∀ q, (∑ r, if f r = q then T r else 0) = p q) :
    (∑ r, if o (f r) = true then T r else 0) =
      ∑ q, if o q = true then p q else 0 := by
  classical
  have one : ∀ r, (if o (f r) = true then T r else 0) =
      ∑ q, if o q = true then if f r = q then T r else 0 else 0 := by
    intro r
    symm
    rw [Finset.sum_eq_single (f r)]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  simp_rw [one]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  by_cases h : o q = true
  · simp only [h,if_true]
    exact hm q
  · simp [h]

private theorem not_full : assignment ∉ PrunedProjection y μ full := by
  classical
  rintro ⟨_,T,hT⟩
  let τ : Triangle 9 := ⟨(1,2,3),by decide⟩
  obtain ⟨⟨hb,hn,ha,hb',hc⟩,_⟩ := hT ⟨τ,trivial⟩
  have hf : ∀ a b c : Fin 20, values a + values b = values c →
      obsA a = true → obsB b = true → obsC c = true := by
    decide +kernel
  have forced : ∀ r : Relation y μ, obsA r.1.1 = true →
      obsB r.1.2.1 = true → obsC r.1.2.2 = true := by
    intro r ha hb
    apply hf r.1.1 r.1.2.1 r.1.2.2 _ ha hb
    have hr := r.2.1
    change (values r.1.1 : ℝ) + values r.1.2.1 = values r.1.2.2 at hr
    exact_mod_cast hr
  have h := coupling_separator (fun r : Relation y μ => obsC r.1.2.2)
    (fun r => obsA r.1.1) (fun r => obsB r.1.2.1) true true true
    (T ⟨τ,trivial⟩) (fun r => (hb r).1) hn forced
  rw [observation_marginal _ _ _ _ ha, observation_marginal _ _ _ _ hb',
    observation_marginal _ _ _ _ hc] at h
  norm_num [assignment,τ,first,second,outer,obsA,obsB,obsC,numerator,
    Fin.sum_univ_succ] at h

/-- The original universal claim, including all singleton cuts, is false. -/
theorem result : ¬ claim := by
  intro h
  have he := h 9 20 y μ admissible ⟨ruler,realizes⟩
  have hs : assignment ∈ {P | P ∈ PrunedProjection y μ spine ∧ SingletonCuts y μ P} :=
    ⟨spine_feasible,singleton_cuts⟩
  exact not_full (he.symm ▸ hs)

#print axioms result
end
end D5.S3.Combinatorics.Turnpike.PrunedSingletonProjectionObstruction
