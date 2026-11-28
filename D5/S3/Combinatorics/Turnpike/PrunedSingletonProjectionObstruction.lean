/- GID: D5/S3/Combinatorics/Turnpike/PrunedSingletonProjectionObstruction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Turnpike/PrunedSingletonProjectionObstruction
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Turnpike/PrunedSingletonProjectionObstruction.claim; result=D5/S3/Combinatorics/Turnpike/PrunedSingletonProjectionObstruction.result; claim=D5/S3/Combinatorics/Turnpike/PrunedSingletonProjectionObstruction.claim
   digest: A realizable nine-point assignment passes every singleton cut but has no full lift. -/
module
public import D5.S3.Combinatorics.Turnpike.PrunedSingletonCutCertificate
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin

/-! The numerical relation and marginal system are from Elder, Marçais and
Kingsford, WABI 2026, Proposition 10 and System 11 (CC BY 4.0).
The rank-pruned singleton-cut comparison and this certificate are repository-derived.
-/
@[expose] public section
namespace D5.S3.Combinatorics.Turnpike.PrunedSingletonProjectionObstruction
open Omega.Turnpike
open Omega.Turnpike.PrunedSingletonCutCertificate
open scoped BigOperators
noncomputable section

def claim : Prop :=
  ∀ (n d : ℕ) (y : Fin d → ℝ) (μ : Fin d → ℕ), Admissible n d y μ →
    (∃ x : Fin n → ℝ, Realizes y μ x) →
    PrunedProjection (n := n) y μ full =
      {P | P ∈ PrunedProjection y μ spine ∧ SingletonCuts y μ P}

private def xNat : Fin 9 → ℕ := ![0, 5, 6, 9, 11, 19, 20, 21, 22]
private def ruler : Fin 9 → ℝ := fun i => xNat i
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
