/- GID: D5/S3/Combinatorics/Turnpike/SpineProjectionObstruction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Turnpike/SpineProjectionObstruction
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Turnpike/SpineProjectionObstruction.claim; result=D5/S3/Combinatorics/Turnpike/SpineProjectionObstruction.result; claim=D5/S3/Combinatorics/Turnpike/SpineProjectionObstruction.claim
   digest: A realizable seven-point input separates the full and spine assignment projections. -/

module

public import D5.S3.Combinatorics.Turnpike.TriangleLP
public import Mathlib.Data.Fin.VecNotation

/-! # A fixed-assignment obstruction to the endpoint-spine relaxation

Model source: C. S. Elder, Guillaume Marçais and Carl Kingsford,
Turnpike with Uncertain Measurements, DOI 10.4230/LIPIcs.WABI.2026.20,
Proposition 10 and System 11 (CC BY 4.0).
The projection comparison is the exact internal interpretation studied here;
it is distinct from the scalar statement of Lemma 13.
-/

@[expose] public section
namespace D5.S3.Combinatorics.Turnpike.SpineProjectionObstruction
open Omega.Turnpike
open scoped BigOperators
noncomputable section

/-- Equality of the entire interval-label projections for every admissible input. -/
def claim : Prop :=
  ∀ (n d : ℕ) (y : Fin d → ℝ) (μ : Fin d → ℕ), Admissible n d y μ →
    Projection (n := n) y μ full = Projection (n := n) y μ spine

def values : Fin 16 → ℕ := ![18, 16, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1]
def y : Fin 16 → ℝ := fun q => values q
def μ : Fin 16 → ℕ := ![1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1]
def ruler : Fin 7 → ℝ := ![0,4,7,8,13,16,18]
def leftLabel (e : Interval 7) : Fin 16 :=
  match e.1.1.val, e.1.2.val with
  | 0, 1 => 12
  | 0, 2 => 9
  | 0, 3 => 8
  | 0, 4 => 3
  | 0, 5 => 1
  | 0, 6 => 0
  | 1, 2 => 15
  | 1, 3 => 12
  | 1, 4 => 7
  | 1, 5 => 4
  | 1, 6 => 2
  | 2, 3 => 13
  | 2, 4 => 10
  | 2, 5 => 7
  | 2, 6 => 5
  | 3, 4 => 11
  | 3, 5 => 8
  | 3, 6 => 6
  | 4, 5 => 13
  | 4, 6 => 11
  | 5, 6 => 14
  | _, _ => 0
def rightLabel (e : Interval 7) : Fin 16 :=
  match e.1.1.val, e.1.2.val with
  | 0, 1 => 14
  | 0, 2 => 11
  | 0, 3 => 6
  | 0, 4 => 5
  | 0, 5 => 2
  | 0, 6 => 0
  | 1, 2 => 11
  | 1, 3 => 8
  | 1, 4 => 7
  | 1, 5 => 4
  | 1, 6 => 1
  | 2, 3 => 13
  | 2, 4 => 10
  | 2, 5 => 7
  | 2, 6 => 3
  | 3, 4 => 15
  | 3, 5 => 12
  | 3, 6 => 8
  | 4, 5 => 13
  | 4, 6 => 9
  | 5, 6 => 12
  | _, _ => 0

def assignment : Assignment 7 16 := fun e => mixture (leftLabel e) (rightLabel e)
private def rawLeft (τ : Triangle 7) : Fin 16 × Fin 16 × Fin 16 :=
  match τ.1.2.1.val, τ.1.2.2.val with
  | 1, 2 => (12, 15, 11)
  | 1, 3 => (12, 12, 8)
  | 1, 4 => (12, 7, 3)
  | 1, 5 => (12, 4, 1)
  | 1, 6 => (12, 2, 0)
  | 2, 3 => (9, 13, 6)
  | 2, 4 => (9, 10, 3)
  | 2, 5 => (9, 7, 1)
  | 2, 6 => (9, 5, 0)
  | 3, 4 => (8, 11, 3)
  | 3, 5 => (8, 8, 1)
  | 3, 6 => (8, 6, 0)
  | 4, 5 => (3, 13, 1)
  | 4, 6 => (3, 11, 0)
  | 5, 6 => (1, 14, 0)
  | _, _ => (12, 15, 11)
private def rawRight (τ : Triangle 7) : Fin 16 × Fin 16 × Fin 16 :=
  match τ.1.2.1.val, τ.1.2.2.val with
  | 1, 2 => (14, 11, 9)
  | 1, 3 => (14, 8, 6)
  | 1, 4 => (14, 7, 5)
  | 1, 5 => (14, 4, 2)
  | 1, 6 => (14, 1, 0)
  | 2, 3 => (11, 13, 8)
  | 2, 4 => (11, 10, 5)
  | 2, 5 => (11, 7, 2)
  | 2, 6 => (11, 3, 0)
  | 3, 4 => (6, 15, 5)
  | 3, 5 => (6, 12, 2)
  | 3, 6 => (6, 8, 0)
  | 4, 5 => (5, 13, 2)
  | 4, 6 => (5, 9, 0)
  | 5, 6 => (2, 12, 0)
  | _, _ => (12, 15, 11)

private theorem admissible : Admissible 7 16 y μ := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · have hv : StrictAnti values := by decide +kernel
    intro a b hab
    change (values b : ℝ) < (values a : ℝ)
    exact_mod_cast hv hab
  · have hv : ∀ q, 0 < values q := by decide +kernel
    intro q
    change (0 : ℝ) < (values q : ℝ)
    exact_mod_cast hv q
  · decide +kernel
  · decide +kernel

private theorem counts : ∀ q : Fin 16,
    (∑ e : Interval 7, ((if q = leftLabel e then 1 else 0) +
      (if q = rightLabel e then 1 else 0) : ℕ)) = 2 * μ q := by
  decide +kernel

private theorem domain : AssignmentDomain μ assignment := by
  refine ⟨?_, ?_, ?_⟩
  · intro e q; exact mixture_bounds _ _ _
  · intro e; exact mixture_sum _ _
  · intro q
    have h := congrArg (fun k : ℕ => (k : ℝ) / 2) (counts q)
    simpa [assignment, mixture, atom, ← Finset.sum_div, Finset.sum_add_distrib,
      Nat.cast_sum, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h

private theorem rawLeft_valid (τ : Triangle 7) (hs : spine τ) :
    y (rawLeft τ).1 + y (rawLeft τ).2.1 = y (rawLeft τ).2.2 ∧
      ((rawLeft τ).1 ≠ (rawLeft τ).2.1 ∨ 2 ≤ μ (rawLeft τ).1) := by
  have h : ∀ τ : Triangle 7, spine τ →
      values (rawLeft τ).1 + values (rawLeft τ).2.1 = values (rawLeft τ).2.2 ∧
      ((rawLeft τ).1 ≠ (rawLeft τ).2.1 ∨ 2 ≤ μ (rawLeft τ).1) := by
        unfold spine
        decide +kernel
  refine ⟨?_, (h τ hs).2⟩
  unfold y
  exact_mod_cast (h τ hs).1

private theorem rawRight_valid (τ : Triangle 7) (hs : spine τ) :
    y (rawRight τ).1 + y (rawRight τ).2.1 = y (rawRight τ).2.2 ∧
      ((rawRight τ).1 ≠ (rawRight τ).2.1 ∨ 2 ≤ μ (rawRight τ).1) := by
  have h : ∀ τ : Triangle 7, spine τ →
      values (rawRight τ).1 + values (rawRight τ).2.1 = values (rawRight τ).2.2 ∧
      ((rawRight τ).1 ≠ (rawRight τ).2.1 ∨ 2 ≤ μ (rawRight τ).1) := by
        unfold spine
        decide +kernel
  refine ⟨?_, (h τ hs).2⟩
  unfold y
  exact_mod_cast (h τ hs).1

private theorem spine_marginals (τ : Triangle 7) (hs : spine τ) :
    (∀ q, mixture (rawLeft τ).1 (rawRight τ).1 q = assignment (first τ) q) ∧
    (∀ q, mixture (rawLeft τ).2.1 (rawRight τ).2.1 q = assignment (second τ) q) ∧
    (∀ q, mixture (rawLeft τ).2.2 (rawRight τ).2.2 q = assignment (outer τ) q) := by
  let agrees (a b : Fin 16) (e : Interval 7) :=
    (a = leftLabel e ∧ b = rightLabel e) ∨ (a = rightLabel e ∧ b = leftLabel e)
  have h : ∀ τ : Triangle 7, spine τ →
      agrees (rawLeft τ).1 (rawRight τ).1 (first τ) ∧
      agrees (rawLeft τ).2.1 (rawRight τ).2.1 (second τ) ∧
      agrees (rawLeft τ).2.2 (rawRight τ).2.2 (outer τ) := by
        dsimp only [agrees,spine]
        decide +kernel
  have use_agrees : ∀ a b e, agrees a b e →
      ∀ q, mixture a b q = assignment e q := by
    intro a b e he q
    rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rfl
    · simp only [assignment,mixture,add_comm]
  exact ⟨use_agrees _ _ _ (h τ hs).1,
    use_agrees _ _ _ (h τ hs).2.1,use_agrees _ _ _ (h τ hs).2.2⟩

private theorem spine_feasible : assignment ∈ Projection y μ spine := by
  classical
  refine ⟨domain, ?_⟩
  let a : {τ : Triangle 7 // spine τ} → Relation y μ :=
    fun τ => ⟨rawLeft τ.1, rawLeft_valid τ.1 τ.2⟩
  let b : {τ : Triangle 7 // spine τ} → Relation y μ :=
    fun τ => ⟨rawRight τ.1, rawRight_valid τ.1 τ.2⟩
  refine ⟨fun τ => mixture (a τ) (b τ), ?_⟩
  intro τ
  refine ⟨fun r => mixture_bounds _ _ _, mixture_sum _ _, ?_, ?_, ?_⟩
  · intro q
    rw [mixture_marginal (fun r : Relation y μ => r.1.1)]
    exact (spine_marginals τ.1 τ.2).1 q
  · intro q
    rw [mixture_marginal (fun r : Relation y μ => r.1.2.1)]
    exact (spine_marginals τ.1 τ.2).2.1 q
  · intro q
    rw [mixture_marginal (fun r : Relation y μ => r.1.2.2)]
    exact (spine_marginals τ.1 τ.2).2.2 q

private theorem not_full : assignment ∉ Projection y μ full := by
  rintro ⟨_, T, hT⟩
  let τ : Triangle 7 := ⟨(1,2,4),by norm_num⟩
  obtain ⟨hb,hn,ha,hb',hc⟩ := hT ⟨τ, trivial⟩
  have forced : ∀ r : Relation y μ, r.1.2.1 = 10 → r.1.2.2 = 7 → r.1.1 = 13 := by
    intro r h₁ h₂
    have hr := r.2.1
    rw [h₁,h₂] at hr
    have he : y r.1.1 = y 13 := by norm_num [y,values] at hr ⊢; linarith
    exact admissible.2.2.1.injective he
  have h := coupling_separator (fun r : Relation y μ => r.1.1)
    (fun r => r.1.2.1) (fun r => r.1.2.2) 13 10 7 (T ⟨τ,trivial⟩)
    (fun r => (hb r).1) hn forced
  rw [ha 13,hb' 10,hc 7] at h
  norm_num [τ,first,second,outer,assignment,mixture,atom,leftLabel,rightLabel] at h

private theorem realizable_counterexample :
    ∃ (n d : ℕ) (y : Fin d → ℝ) (μ : Fin d → ℕ)
      (x : Fin n → ℝ) (P : Assignment n d),
      Admissible n d y μ ∧ Realizes y μ x ∧
      P ∈ Projection y μ spine ∧ P ∉ Projection y μ full := by
  let x : Fin 7 → ℕ := ![0,4,7,8,13,16,18]
  let label : Interval 7 → Fin 16 := fun e =>
    if e.1 = (1,2) then 13 else if e.1 = (2,3) then 15 else leftLabel e
  have hx : ∀ i, ruler i = (x i : ℝ) := by
    intro i
    fin_cases i <;> norm_num [ruler,x]
  have hmono : StrictMono x := by decide +kernel
  have hd : ∀ e : Interval 7, x e.1.2 = x e.1.1 + values (label e) := by
    decide +kernel
  have hc : ∀ q : Fin 16,
      (Finset.univ.filter fun e : Interval 7 => label e = q).card = μ q := by
    decide +kernel
  have hr : ∀ e : Interval 7, ruler e.1.2 - ruler e.1.1 = y (label e) := by
    intro e
    rw [hx,hx]
    unfold y
    have h := congrArg (fun k : ℕ => (k : ℝ)) (hd e)
    push_cast at h
    linarith
  refine ⟨7,16,y,μ,ruler,assignment,admissible,?_,spine_feasible,not_full⟩
  refine ⟨?_,?_,?_⟩
  · intro i j hij
    rw [hx,hx]
    exact_mod_cast hmono hij
  · intro e
    exact ⟨label e,hr e⟩
  · intro q
    have heq : (Finset.univ.filter fun e : Interval 7 =>
        ruler e.1.2 - ruler e.1.1 = y q) =
        (Finset.univ.filter fun e : Interval 7 => label e = q) := by
      apply Finset.filter_congr
      intro e _
      rw [hr e]
      exact admissible.2.2.1.injective.eq_iff
    rw [heq]
    exact hc q

/-- The universal fixed-assignment projection equality is false. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨n,d,y,μ,x,P,hadm,_,hs,hf⟩ := realizable_counterexample
  exact hf ((h n d y μ hadm).symm ▸ hs)
end
end D5.S3.Combinatorics.Turnpike.SpineProjectionObstruction
