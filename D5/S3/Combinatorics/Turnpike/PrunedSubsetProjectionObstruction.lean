/- GID: D5/S3/Combinatorics/Turnpike/PrunedSubsetProjectionObstruction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Turnpike/PrunedSubsetProjectionObstruction
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Turnpike/PrunedSubsetProjectionObstruction.claim; result=D5/S3/Combinatorics/Turnpike/PrunedSubsetProjectionObstruction.result; claim=D5/S3/Combinatorics/Turnpike/PrunedSubsetProjectionObstruction.claim
   digest: An assignment for a realizable seven-point input passes every subset cut but has no full lift. -/
module
public import D5.S3.Combinatorics.Turnpike.SubsetCertificateChecks
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin

/-! The numerical relation and marginal system are from Elder, Marçais and
Kingsford, WABI 2026, Proposition 10 and System 11 (CC BY 4.0).
The rank-pruned subset-cut comparison and this certificate are repository-derived.
-/
@[expose] public section
namespace D5.S3.Combinatorics.Turnpike.PrunedSubsetProjectionObstruction
open Omega.Turnpike
open Omega.Turnpike.SubsetCertificate
open scoped BigOperators
noncomputable section

def claim : Prop :=
  ∀ (n d : ℕ) (y : Fin d → ℝ) (μ : Fin d → ℕ), Admissible n d y μ →
    (∃ x : Fin n → ℝ, Realizes y μ x) →
    PrunedProjection (n := n) y μ full =
      {P | P ∈ PrunedProjection y μ spine ∧ SubsetCuts y μ P}

private def xNat : Fin 7 → ℕ := ![0, 4, 6, 9, 10, 11, 12]
private def ruler : Fin 7 → ℝ := fun i => xNat i
private def raw (τ : Triangle 7) (s : Fin 10) : (Fin 12 × Fin 12 × Fin 12) × ℕ :=
  match τ.1.2.1.val, τ.1.2.2.val with
  | 1, 2 =>
    ![((6,10,4),4),
      ((6,11,5),4),
      ((7,11,6),2),
      ((8,11,7),4),
      ((9,9,6),6),
      ((10,8,6),3),
      ((10,9,7),1),
      ((10,11,9),6),
      ((11,8,7),6),
      ((11,11,10),14)] s
  | 1, 3 =>
    ![((6,9,3),8),
      ((7,8,3),2),
      ((8,7,3),3),
      ((8,10,6),1),
      ((9,6,3),6),
      ((10,10,8),10),
      ((11,7,6),13),
      ((11,9,8),4),
      ((11,10,9),3),
      ((6,10,4),0)] s
  | 1, 4 =>
    ![((6,8,2),8),
      ((7,7,2),2),
      ((8,6,2),4),
      ((9,5,2),6),
      ((10,6,4),10),
      ((11,5,4),3),
      ((11,7,6),14),
      ((11,8,7),3),
      ((6,10,4),0),
      ((6,10,4),0)] s
  | 1, 5 =>
    ![((6,7,1),8),
      ((7,6,1),2),
      ((8,5,1),4),
      ((9,4,1),6),
      ((10,3,1),10),
      ((11,3,2),6),
      ((11,5,4),9),
      ((11,6,5),2),
      ((11,7,6),3),
      ((6,10,4),0)] s
  | 1, 6 =>
    ![((6,6,0),8),
      ((7,5,0),2),
      ((8,4,0),4),
      ((9,3,0),6),
      ((10,2,0),10),
      ((11,1,0),20),
      ((6,10,4),0),
      ((6,10,4),0),
      ((6,10,4),0),
      ((6,10,4),0)] s
  | 2, 3 =>
    ![((4,11,3),4),
      ((5,10,3),4),
      ((6,9,3),11),
      ((7,11,6),11),
      ((9,9,6),1),
      ((9,11,8),5),
      ((10,8,6),2),
      ((10,10,8),9),
      ((10,11,9),3),
      ((6,10,4),0)] s
  | 2, 4 =>
    ![((4,10,2),4),
      ((5,9,2),4),
      ((6,8,2),4),
      ((6,10,4),7),
      ((7,7,2),8),
      ((7,9,4),3),
      ((9,9,6),6),
      ((10,6,4),3),
      ((10,8,6),8),
      ((10,9,7),3)] s
  | 2, 5 =>
    ![((4,9,1),4),
      ((5,8,1),4),
      ((6,7,1),11),
      ((7,6,1),11),
      ((9,5,2),6),
      ((10,6,4),9),
      ((10,7,5),2),
      ((10,8,6),3),
      ((6,10,4),0),
      ((6,10,4),0)] s
  | 2, 6 =>
    ![((4,8,0),4),
      ((5,7,0),4),
      ((6,6,0),11),
      ((7,5,0),11),
      ((9,3,0),6),
      ((10,2,0),14),
      ((6,10,4),0),
      ((6,10,4),0),
      ((6,10,4),0),
      ((6,10,4),0)] s
  | 3, 4 =>
    ![((3,11,2),19),
      ((6,8,2),1),
      ((6,10,4),13),
      ((8,10,6),11),
      ((8,11,7),3),
      ((9,9,6),3),
      ((6,10,4),0),
      ((6,10,4),0),
      ((6,10,4),0),
      ((6,10,4),0)] s
  | 3, 5 =>
    ![((3,10,1),19),
      ((6,7,1),11),
      ((6,8,2),3),
      ((8,6,2),3),
      ((8,8,4),9),
      ((8,9,5),2),
      ((9,9,6),3),
      ((6,10,4),0),
      ((6,10,4),0),
      ((6,10,4),0)] s
  | 3, 6 =>
    ![((3,9,0),19),
      ((6,6,0),14),
      ((8,4,0),14),
      ((9,3,0),3),
      ((6,10,4),0),
      ((6,10,4),0),
      ((6,10,4),0),
      ((6,10,4),0),
      ((6,10,4),0),
      ((6,10,4),0)] s
  | 4, 5 =>
    ![((2,11,1),20),
      ((4,9,1),7),
      ((4,10,2),6),
      ((6,7,1),3),
      ((6,10,4),9),
      ((6,11,5),2),
      ((7,11,6),3),
      ((6,10,4),0),
      ((6,10,4),0),
      ((6,10,4),0)] s
  | 4, 6 =>
    ![((2,10,0),20),
      ((4,8,0),13),
      ((6,6,0),14),
      ((7,5,0),3),
      ((6,10,4),0),
      ((6,10,4),0),
      ((6,10,4),0),
      ((6,10,4),0),
      ((6,10,4),0),
      ((6,10,4),0)] s
  | 5, 6 =>
    ![((1,11,0),30),
      ((2,10,0),6),
      ((4,8,0),9),
      ((5,7,0),2),
      ((6,6,0),3),
      ((6,10,4),0),
      ((6,10,4),0),
      ((6,10,4),0),
      ((6,10,4),0),
      ((6,10,4),0)] s
  | _, _ => ((6,10,4),0)
private def occurrence (e : Interval 7) : Fin 12 :=
  match e.1.1.val, e.1.2.val with
  | 0, 1 => 8
  | 0, 2 => 6
  | 0, 3 => 3
  | 0, 4 => 2
  | 0, 5 => 1
  | 0, 6 => 0
  | 1, 2 => 10
  | 1, 3 => 7
  | 1, 4 => 6
  | 1, 5 => 5
  | 1, 6 => 4
  | 2, 3 => 9
  | 2, 4 => 8
  | 2, 5 => 7
  | 2, 6 => 6
  | 3, 4 => 11
  | 3, 5 => 10
  | 3, 6 => 9
  | 4, 5 => 11
  | 4, 6 => 10
  | 5, 6 => 11
  | _, _ => 0

private theorem admissible : Admissible 7 12 y μ := by
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
  have hd : ∀ e : Interval 7, xNat e.1.2 = xNat e.1.1 + values (occurrence e) := by
    decide +kernel
  have hc : ∀ q : Fin 12,
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

private theorem p_bounds : ∀ e : Interval 7, ∀ q : Fin 12,
    numerator e q ≤ 50 ∧ (numerator e q ≠ 0 → RankAllowed μ e q) := by
  unfold RankAllowed
  decide +kernel
private theorem p_columns : ∀ q : Fin 12,
    ∑ e : Interval 7, numerator e q = 50 * μ q := by
  decide +kernel

private theorem domain : PrunedDomain μ assignment := by
  classical
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro e q
    have hb : (numerator e q : ℝ) ≤ 50 := by exact_mod_cast (p_bounds e q).1
    dsimp [assignment]
    constructor
    · positivity
    · linarith
  · intro e
    have h := congrArg (fun z : ℕ => (z : ℝ) / 50) (numerator_rows e)
    simpa [assignment, Nat.cast_sum, Finset.sum_div] using h
  · intro q
    have h := congrArg (fun z : ℕ => (z : ℝ) / 50) (p_columns q)
    simpa [assignment, Nat.cast_sum, Nat.cast_mul, Finset.sum_div] using h
  · intro e q
    by_cases hn : numerator e q = 0
    · simp [assignment,hn,rankMask]; split_ifs <;> norm_num
    · rw [rankMask, if_pos ((p_bounds e q).2 hn)]
      exact (show assignment e q ≤ 1 from by
        have hb : (numerator e q : ℝ) ≤ 50 := by exact_mod_cast (p_bounds e q).1
        dsimp [assignment]; linarith)

private theorem raw_valid : ∀ τ : Triangle 7, spine τ → ∀ s : Fin 10,
    values (raw τ s).1.1 + values (raw τ s).1.2.1 = values (raw τ s).1.2.2 ∧
    ((raw τ s).1.1 ≠ (raw τ s).1.2.1 ∨ 2 ≤ μ (raw τ s).1.1) := by
  unfold spine
  decide +kernel
private def support (τ : {τ : Triangle 7 // spine τ}) (s : Fin 10) : Relation y μ :=
  ⟨(raw τ.1 s).1, by
    refine ⟨?_, (raw_valid τ.1 τ.2 s).2⟩
    change (values _ : ℝ) + values _ = values _
    exact_mod_cast (raw_valid τ.1 τ.2 s).1⟩
private theorem raw_masks : ∀ τ : Triangle 7, spine τ → ∀ s : Fin 10,
    (raw τ s).2 ≠ 0 → ProductAllowed μ τ (raw τ s).1 := by
  unfold spine ProductAllowed RankAllowed
  decide +kernel
private theorem raw_total : ∀ τ : Triangle 7, spine τ →
    ∑ s : Fin 10, (raw τ s).2 = 50 := by
  unfold spine
  decide +kernel
private theorem raw_marginals : ∀ τ : Triangle 7, spine τ → ∀ u : Fin 3, ∀ q : Fin 12,
    (∑ s : Fin 10, if coordinate u (raw τ s).1 = q then (raw τ s).2 else 0) =
      numerator (edge τ u) q := by
  unfold spine
  decide +kernel

private def weight (τ : {τ : Triangle 7 // spine τ}) (s : Fin 10) : ℝ :=
  ((raw τ.1 s).2 : ℝ) / 50
private def coupling (τ : {τ : Triangle 7 // spine τ}) : Relation y μ → ℝ :=
  by
    classical
    exact weightedAtoms (support τ) (weight τ)

private theorem coupling_nonneg (τ : {τ : Triangle 7 // spine τ}) (r : Relation y μ) :
    0 ≤ coupling τ r := by
  classical
  unfold coupling weightedAtoms
  apply Finset.sum_nonneg
  intro s _
  unfold weight atom
  positivity
private theorem coupling_total (τ : {τ : Triangle 7 // spine τ}) :
    ∑ r, coupling τ r = 1 := by
  classical
  rw [coupling, weightedAtoms_sum]
  have h := congrArg (fun z : ℕ => (z : ℝ) / 50) (raw_total τ.1 τ.2)
  simpa [weight, Nat.cast_sum, Finset.sum_div] using h
private theorem coupling_marginal (τ : {τ : Triangle 7 // spine τ}) (u : Fin 3)
    (q : Fin 12) :
    (∑ r, if coordinate u r.1 = q then coupling τ r else 0) =
      assignment (edge τ.1 u) q := by
  classical
  rw [coupling, weightedAtoms_marginal]
  change (∑ s, if coordinate u (raw τ.1 s).1 = q then
    ((raw τ.1 s).2 : ℝ) / 50 else 0) = (numerator (edge τ.1 u) q : ℝ) / 50
  have h := congrArg (fun z : ℕ => (z : ℝ) / 50) (raw_marginals τ.1 τ.2 u q)
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

private def fInt (q : Fin 12) : ℤ :=
  if values q % 3 = 0 then 1 else if values q % 3 = 1 then 4 else -2
private def gInt (q : Fin 12) : ℤ :=
  if values q % 3 = 0 then -2 else if values q % 3 = 1 then 4 else 1
private def f (q : Fin 12) : ℝ := fInt q
private def g (q : Fin 12) : ℝ := gInt q

private theorem not_full : assignment ∉ PrunedProjection y μ full := by
  classical
  rintro ⟨_,T,hT⟩
  let τ : Triangle 7 := ⟨(1,3,5),by decide⟩
  obtain ⟨⟨hb,_,ha,hb',hc⟩,_⟩ := hT ⟨τ,trivial⟩
  have hi : ∀ a b c : Fin 12, values a + values b = values c →
      0 ≤ fInt a + fInt b + gInt c := by decide +kernel
  have hp : ∀ r : Relation y μ, 0 ≤ f r.1.1 + f r.1.2.1 + g r.1.2.2 := by
    intro r
    have hr : values r.1.1 + values r.1.2.1 = values r.1.2.2 := by
      have he := r.2.1
      change (values _ : ℝ) + values _ = values _ at he
      exact_mod_cast he
    dsimp only [f,g]
    exact_mod_cast hi r.1.1 r.1.2.1 r.1.2.2 hr
  have hs : 0 ≤ ∑ r : Relation y μ,
      (f r.1.1 + f r.1.2.1 + g r.1.2.2) * T ⟨τ,trivial⟩ r :=
    Finset.sum_nonneg fun r _ => mul_nonneg (hp r) (hb r).1
  simp_rw [add_mul] at hs
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,
    weighted_marginal _ _ _ f ha, weighted_marginal _ _ _ f hb',
    weighted_marginal _ _ _ g hc] at hs
  norm_num [assignment,τ,first,second,outer,f,g,fInt,gInt,values,numerator,
    Fin.sum_univ_succ] at hs

/-- All subset-pair transport cuts fail to complete the original pruned projection. -/
theorem result : ¬ claim := by
  intro h
  have he := h 7 12 y μ admissible ⟨ruler,realizes⟩
  have hs : assignment ∈ {P | P ∈ PrunedProjection y μ spine ∧ SubsetCuts y μ P} :=
    ⟨spine_feasible,all_subset_cuts⟩
  exact not_full (he.symm ▸ hs)

#print axioms result
end
end D5.S3.Combinatorics.Turnpike.PrunedSubsetProjectionObstruction
