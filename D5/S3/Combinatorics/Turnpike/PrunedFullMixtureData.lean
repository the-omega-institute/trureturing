/- GID: D5/S3/Combinatorics/Turnpike/PrunedFullMixtureData
   generality: G
   mirror-B: none(waiver:covered-by-pruned-full-mixture-obstruction-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed full triangle certificate -/

module
public import D5.S3.Combinatorics.Turnpike.PrunedTriangleLP
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.IntervalCases

/-! Omega original.
# Fixed full triangle certificate

The entries are integer numerators with common denominator four.
-/
@[expose] public section
namespace Omega.Turnpike.PrunedFullMixture
open Omega.Turnpike
open scoped BigOperators
noncomputable section

def values : Fin 9 → ℕ := ![9,8,7,6,5,4,3,2,1]
def y : Fin 9 → ℝ := fun q => values q
def μ : Fin 9 → ℕ := ![1,1,2,1,3,3,3,4,3]
def xNat : Fin 7 → ℕ := ![0,1,2,4,5,7,9]
def ruler : Fin 7 → ℝ := fun i => xNat i
def numerator (e : Interval 7) (q : Fin 9) : ℕ :=
  match e.1.1.val, e.1.2.val with
  | 0, 1 => ![0, 0, 0, 0, 0, 0, 0, 2, 2] q
  | 0, 2 => ![0, 0, 0, 0, 0, 1, 2, 1, 0] q
  | 0, 3 => ![0, 0, 0, 0, 2, 2, 0, 0, 0] q
  | 0, 4 => ![0, 0, 1, 2, 1, 0, 0, 0, 0] q
  | 0, 5 => ![0, 2, 2, 0, 0, 0, 0, 0, 0] q
  | 0, 6 => ![4, 0, 0, 0, 0, 0, 0, 0, 0] q
  | 1, 2 => ![0, 0, 0, 0, 0, 0, 0, 2, 2] q
  | 1, 3 => ![0, 0, 0, 0, 0, 0, 4, 0, 0] q
  | 1, 4 => ![0, 0, 0, 0, 2, 2, 0, 0, 0] q
  | 1, 5 => ![0, 0, 2, 0, 2, 0, 0, 0, 0] q
  | 1, 6 => ![0, 2, 2, 0, 0, 0, 0, 0, 0] q
  | 2, 3 => ![0, 0, 0, 0, 0, 0, 0, 2, 2] q
  | 2, 4 => ![0, 0, 0, 0, 0, 0, 4, 0, 0] q
  | 2, 5 => ![0, 0, 0, 0, 2, 2, 0, 0, 0] q
  | 2, 6 => ![0, 0, 1, 2, 1, 0, 0, 0, 0] q
  | 3, 4 => ![0, 0, 0, 0, 0, 0, 0, 2, 2] q
  | 3, 5 => ![0, 0, 0, 0, 0, 2, 0, 2, 0] q
  | 3, 6 => ![0, 0, 0, 0, 2, 2, 0, 0, 0] q
  | 4, 5 => ![0, 0, 0, 0, 0, 0, 0, 2, 2] q
  | 4, 6 => ![0, 0, 0, 0, 0, 1, 2, 1, 0] q
  | 5, 6 => ![0, 0, 0, 0, 0, 0, 0, 2, 2] q
  | _, _ => 0
def assignment : Assignment 7 9 := fun e q => (numerator e q : ℝ) / 4
def raw (τ : Triangle 7) (s : Fin 4) : (Fin 9 × Fin 9 × Fin 9) × ℕ :=
  match τ.1.1.val, τ.1.2.1.val, τ.1.2.2.val with
  | 0, 1, 2 => ![((7,7,5),1), ((7,8,6),1), ((8,7,6),1), ((8,8,7),1)] s
  | 0, 1, 3 => ![((7,6,4),2), ((8,6,5),2), ((7,6,4),0), ((7,6,4),0)] s
  | 0, 1, 4 => ![((7,4,2),1), ((7,5,3),1), ((8,4,3),1), ((8,5,4),1)] s
  | 0, 1, 5 => ![((7,4,2),2), ((8,2,1),2), ((7,4,2),0), ((7,4,2),0)] s
  | 0, 1, 6 => ![((7,2,0),2), ((8,1,0),2), ((7,2,0),0), ((7,2,0),0)] s
  | 0, 2, 3 => ![((5,8,4),1), ((6,7,4),1), ((6,8,5),1), ((7,7,5),1)] s
  | 0, 2, 4 => ![((5,6,2),1), ((6,6,3),2), ((7,6,4),1), ((5,6,2),0)] s
  | 0, 2, 5 => ![((5,5,1),1), ((6,4,1),1), ((6,5,2),1), ((7,4,2),1)] s
  | 0, 2, 6 => ![((5,4,0),1), ((6,3,0),2), ((7,2,0),1), ((5,4,0),0)] s
  | 0, 3, 4 => ![((4,7,2),1), ((4,8,3),1), ((5,7,3),1), ((5,8,4),1)] s
  | 0, 3, 5 => ![((4,7,2),2), ((5,5,1),2), ((4,7,2),0), ((4,7,2),0)] s
  | 0, 3, 6 => ![((4,5,0),2), ((5,4,0),2), ((4,5,0),0), ((4,5,0),0)] s
  | 0, 4, 5 => ![((2,8,1),1), ((3,7,1),1), ((3,8,2),1), ((4,7,2),1)] s
  | 0, 4, 6 => ![((2,7,0),1), ((3,6,0),2), ((4,5,0),1), ((2,7,0),0)] s
  | 0, 5, 6 => ![((1,8,0),2), ((2,7,0),2), ((1,8,0),0), ((1,8,0),0)] s
  | 1, 2, 3 => ![((7,8,6),2), ((8,7,6),2), ((7,8,6),0), ((7,8,6),0)] s
  | 1, 2, 4 => ![((7,6,4),2), ((8,6,5),2), ((7,6,4),0), ((7,6,4),0)] s
  | 1, 2, 5 => ![((7,4,2),2), ((8,5,4),2), ((7,4,2),0), ((7,4,2),0)] s
  | 1, 2, 6 => ![((7,3,1),1), ((7,4,2),1), ((8,2,1),1), ((8,3,2),1)] s
  | 1, 3, 4 => ![((6,7,4),2), ((6,8,5),2), ((6,7,4),0), ((6,7,4),0)] s
  | 1, 3, 5 => ![((6,5,2),2), ((6,7,4),2), ((6,5,2),0), ((6,5,2),0)] s
  | 1, 3, 6 => ![((6,4,1),2), ((6,5,2),2), ((6,4,1),0), ((6,4,1),0)] s
  | 1, 4, 5 => ![((4,7,2),2), ((5,8,4),2), ((4,7,2),0), ((4,7,2),0)] s
  | 1, 4, 6 => ![((4,6,1),1), ((4,7,2),1), ((5,5,1),1), ((5,6,2),1)] s
  | 1, 5, 6 => ![((2,8,1),2), ((4,7,2),2), ((2,8,1),0), ((2,8,1),0)] s
  | 2, 3, 4 => ![((7,8,6),2), ((8,7,6),2), ((7,8,6),0), ((7,8,6),0)] s
  | 2, 3, 5 => ![((7,7,5),2), ((8,5,4),2), ((7,7,5),0), ((7,7,5),0)] s
  | 2, 3, 6 => ![((7,4,2),1), ((7,5,3),1), ((8,4,3),1), ((8,5,4),1)] s
  | 2, 4, 5 => ![((6,7,4),2), ((6,8,5),2), ((6,7,4),0), ((6,7,4),0)] s
  | 2, 4, 6 => ![((6,5,2),1), ((6,6,3),2), ((6,7,4),1), ((6,5,2),0)] s
  | 2, 5, 6 => ![((4,7,2),1), ((4,8,3),1), ((5,7,3),1), ((5,8,4),1)] s
  | 3, 4, 5 => ![((7,7,5),2), ((8,8,7),2), ((7,7,5),0), ((7,7,5),0)] s
  | 3, 4, 6 => ![((7,6,4),1), ((7,7,5),1), ((8,5,4),1), ((8,6,5),1)] s
  | 3, 5, 6 => ![((5,8,4),2), ((7,7,5),2), ((5,8,4),0), ((5,8,4),0)] s
  | 4, 5, 6 => ![((7,7,5),1), ((7,8,6),1), ((8,7,6),1), ((8,8,7),1)] s
  | _, _, _ => ((7,7,5),0)
def occurrence (e : Interval 7) : Fin 9 :=
  match e.1.1.val, e.1.2.val with
  | 0, 1 => 8
  | 0, 2 => 7
  | 0, 3 => 5
  | 0, 4 => 4
  | 0, 5 => 2
  | 0, 6 => 0
  | 1, 2 => 8
  | 1, 3 => 6
  | 1, 4 => 5
  | 1, 5 => 3
  | 1, 6 => 1
  | 2, 3 => 7
  | 2, 4 => 6
  | 2, 5 => 4
  | 2, 6 => 2
  | 3, 4 => 8
  | 3, 5 => 6
  | 3, 6 => 4
  | 4, 5 => 7
  | 4, 6 => 5
  | 5, 6 => 7
  | _, _ => 0
theorem admissible : Admissible 7 9 y μ := by
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

theorem realizes : Realizes y μ ruler := by
  have hm : StrictMono xNat := by decide +kernel
  have hd : ∀ e : Interval 7, xNat e.1.2 = xNat e.1.1 + values (occurrence e) := by
    decide +kernel
  have hc : ∀ q : Fin 9,
      (Finset.univ.filter fun e : Interval 7 => occurrence e = q).card = μ q := by
    decide +kernel
  have hr : ∀ e : Interval 7, ruler e.1.2 - ruler e.1.1 = y (occurrence e) := by
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
    have heq : (Finset.univ.filter fun e : Interval 7 =>
        ruler e.1.2 - ruler e.1.1 = y q) =
        (Finset.univ.filter fun e : Interval 7 => occurrence e = q) := by
      apply Finset.filter_congr
      intro e _
      rw [hr e]
      exact admissible.2.2.1.injective.eq_iff
    rw [heq]
    exact hc q

theorem p_bounds : ∀ e : Interval 7, ∀ q : Fin 9,
    numerator e q ≤ 4 ∧ (numerator e q ≠ 0 → RankAllowed μ e q) := by
  unfold RankAllowed
  decide +kernel
theorem p_rows : ∀ e : Interval 7, ∑ q, numerator e q = 4 := by
  decide +kernel
theorem p_columns : ∀ q : Fin 9,
    ∑ e : Interval 7, numerator e q = 4 * μ q := by
  decide +kernel

theorem domain : PrunedDomain μ assignment := by
  classical
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro e q
    have hb : (numerator e q : ℝ) ≤ 4 := by exact_mod_cast (p_bounds e q).1
    dsimp [assignment]
    constructor
    · positivity
    · linarith
  · intro e
    have h := congrArg (fun z : ℕ => (z : ℝ) / 4) (p_rows e)
    simpa [assignment, Nat.cast_sum, Finset.sum_div] using h
  · intro q
    have h := congrArg (fun z : ℕ => (z : ℝ) / 4) (p_columns q)
    simpa [assignment, Nat.cast_sum, Nat.cast_mul, Finset.sum_div] using h
  · intro e q
    by_cases hn : numerator e q = 0
    · simp [assignment,hn,rankMask]; split_ifs <;> norm_num
    · rw [rankMask, if_pos ((p_bounds e q).2 hn)]
      exact (show assignment e q ≤ 1 from by
        have hb : (numerator e q : ℝ) ≤ 4 := by exact_mod_cast (p_bounds e q).1
        dsimp [assignment]; linarith)

theorem raw_valid : ∀ τ : Triangle 7, ∀ s : Fin 4,
    values (raw τ s).1.1 + values (raw τ s).1.2.1 = values (raw τ s).1.2.2 ∧
    ((raw τ s).1.1 ≠ (raw τ s).1.2.1 ∨ 2 ≤ μ (raw τ s).1.1) := by
  decide +kernel
def support (τ : {τ : Triangle 7 // full τ}) (s : Fin 4) : Relation y μ :=
  ⟨(raw τ.1 s).1, by
    refine ⟨?_, (raw_valid τ.1 s).2⟩
    change (values _ : ℝ) + values _ = values _
    exact_mod_cast (raw_valid τ.1 s).1⟩
theorem raw_masks : ∀ τ : Triangle 7, ∀ s : Fin 4,
    (raw τ s).2 ≠ 0 → ProductAllowed μ τ (raw τ s).1 := by
  unfold ProductAllowed RankAllowed
  decide +kernel
theorem raw_total : ∀ τ : Triangle 7,
    ∑ s : Fin 4, (raw τ s).2 = 4 := by
  decide +kernel
theorem raw_marginals : ∀ τ : Triangle 7, ∀ u : Fin 3, ∀ q : Fin 9,
    (∑ s : Fin 4, if coordinate u (raw τ s).1 = q then (raw τ s).2 else 0) =
      numerator (edge τ u) q := by
  decide +kernel

def weight (τ : {τ : Triangle 7 // full τ}) (s : Fin 4) : ℝ :=
  ((raw τ.1 s).2 : ℝ) / 4
def coupling (τ : {τ : Triangle 7 // full τ}) : Relation y μ → ℝ :=
  by
    classical
    exact weightedAtoms (support τ) (weight τ)

theorem coupling_nonneg (τ : {τ : Triangle 7 // full τ}) (r : Relation y μ) :
    0 ≤ coupling τ r := by
  classical
  unfold coupling weightedAtoms
  apply Finset.sum_nonneg
  intro s _
  unfold weight atom
  positivity
theorem coupling_total (τ : {τ : Triangle 7 // full τ}) :
    ∑ r, coupling τ r = 1 := by
  classical
  rw [coupling, weightedAtoms_sum]
  have h := congrArg (fun z : ℕ => (z : ℝ) / 4) (raw_total τ.1)
  simpa [weight, Nat.cast_sum, Finset.sum_div] using h
theorem coupling_marginal (τ : {τ : Triangle 7 // full τ}) (u : Fin 3)
    (q : Fin 9) :
    (∑ r, if coordinate u r.1 = q then coupling τ r else 0) =
      assignment (edge τ.1 u) q := by
  classical
  rw [coupling, weightedAtoms_marginal]
  change (∑ s, if coordinate u (raw τ.1 s).1 = q then
    ((raw τ.1 s).2 : ℝ) / 4 else 0) = (numerator (edge τ.1 u) q : ℝ) / 4
  have h := congrArg (fun z : ℕ => (z : ℝ) / 4) (raw_marginals τ.1 u q)
  simpa only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Finset.sum_div,
    ite_div, zero_div] using h

theorem full_feasible : assignment ∈ PrunedProjection y μ full := by
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
            exact raw_masks τ.1 s hn
          simp [atom,hne]
      rw [hz]
      unfold rankMask
      split_ifs <;> norm_num


end
end Omega.Turnpike.PrunedFullMixture
