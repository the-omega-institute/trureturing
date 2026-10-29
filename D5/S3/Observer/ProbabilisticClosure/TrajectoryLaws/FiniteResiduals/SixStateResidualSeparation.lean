/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteResiduals/SixStateResidualSeparation
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteResiduals/SixStateResidualSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteResiduals/SixStateResidualSeparation.claim; result=D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteResiduals/SixStateResidualSeparation.result; claim=D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteResiduals/SixStateResidualSeparation.claim
   digest: One six-state kernel separates every stopping archive from the stable residual and defeats almost-sure label updates. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteResiduals.FiniteResidualStopping
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
open D5.S3.Estimation.DecisionRisk.DescentDefectBounds
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteResiduals.FiniteResidualStopping
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteResiduals.SixStateResidualSeparation

/-- Indices 0,1,2,3,4,5 denote s,t,u,v,w,z, respectively. -/
def row (x : Fin 6) (e : Bool × Fin 6) : ℝ :=
  match x.val, e.1, e.2.val with
  | 0, false, 2 => 1/2
  | 0, false, 3 => 1/2
  | 1, false, 4 => 1
  | 2, false, 5 => 1
  | 3, true, 5 => 1
  | 4, false, 5 => 1/2
  | 4, true, 5 => 1/2
  | 5, false, 5 => 1
  | _, _, _ => 0

private theorem row_stochastic : IsRowStochastic row := by
  constructor
  · intro x e
    rcases e with ⟨y,r⟩
    fin_cases x <;> cases y <;> fin_cases r <;> norm_num [row]
  · intro x
    fin_cases x <;> norm_num [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ, row]

def kernel : FiniteMarkovKernel (Fin 6) (Bool × Fin 6) := ⟨row,row_stochastic⟩

/-- The first three classes are {s,t,u,z}, {v}, {w}. -/
def firstClass (x : Fin 6) : Fin 3 :=
  if x = 3 then 1 else if x = 4 then 2 else 0

/-- The stable five classes are {s}, {t}, {u,z}, {v}, {w}. -/
def stableClass (x : Fin 6) : Fin 5 :=
  match x.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | _ => 2

private theorem first_partition (x x' : Fin 6) :
    residual kernel 1 x x' ↔ firstClass x = firstClass x' := by
  fin_cases x <;> fin_cases x' <;>
    norm_num [FiniteResidualStopping.residual, classMass, kernel, row, firstClass, Fin.sum_univ_succ,
      Fin.forall_fin_succ, Bool.forall_bool]

private theorem second_partition (x x' : Fin 6) :
    residual kernel 2 x x' ↔ stableClass x = stableClass x' := by
  change (residual kernel 1 x x' ∧ ∀ y c,
    classMass kernel (residual kernel 1) x y c =
    classMass kernel (residual kernel 1) x' y c) ↔ _
  simp only [first_partition, classMass]
  fin_cases x <;> fin_cases x' <;>
    norm_num [kernel, row, firstClass, stableClass, Fin.sum_univ_succ,
      Fin.forall_fin_succ, Bool.forall_bool]

private theorem third_partition : residual kernel 3 = residual kernel 2 := by
  funext x x'
  apply propext
  change (residual kernel 2 x x' ∧ ∀ y c,
    classMass kernel (residual kernel 2) x y c =
    classMass kernel (residual kernel 2) x' y c) ↔ _
  simp only [second_partition, classMass]
  fin_cases x <;> fin_cases x' <;>
    norm_num [kernel, row, stableClass, Fin.sum_univ_succ,
      Fin.forall_fin_succ, Bool.forall_bool]

private theorem plateau (n : ℕ) : residual kernel (n+2) = residual kernel 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (fun x x' => residual kernel (n+2) x x' ∧ ∀ y c,
      classMass kernel (residual kernel (n+2)) x y c =
      classMass kernel (residual kernel (n+2)) x' y c) = _
    rw [ih]
    exact third_partition

private theorem limit_partition (x x' : Fin 6) :
    (∀ n, residual kernel n x x') ↔ stableClass x = stableClass x' := by
  constructor
  · intro h
    exact (second_partition x x').mp (h 2)
  · intro h n
    have h2 := (second_partition x x').mpr h
    rcases n with _ | n
    · trivial
    rcases n with _ | n
    · exact h2.1
    · rw [plateau n]
      exact h2

/-- z is an ordinary absorbing state, so precisely all-zero words have mass one. -/
private theorem absorbing_word (w : List Bool) :
    wordProb kernel 5 w = if w.all (fun b => !b) then 1 else 0 := by
  induction w with
  | nil => simp [wordProb]
  | cons y w ih =>
    have hz : wordProb ⟨row,row_stochastic⟩ 5 w =
        (if w.all (fun b => !b) then 1 else 0) := ih
    cases y <;> simp [wordProb,kernel,row,Fin.sum_univ_succ,hz]

/-- The common law has first bit zero, a fair second bit and zero thereafter. -/
def profile : List Bool → ℝ
  | [] => 1
  | [false] => 1
  | false :: _ :: w => (1/2) * (if w.all (fun b => !b) then 1 else 0)
  | _ => 0

private theorem common_word (w : List Bool) :
    wordProb kernel 0 w = profile w ∧ wordProb kernel 1 w = profile w := by
  cases w with
  | nil => simp [wordProb,profile]
  | cons y w =>
    cases w with
    | nil => cases y <;> norm_num [wordProb,kernel,row,Fin.sum_univ_succ,profile]
    | cons b w =>
      have hz : wordProb ⟨row,row_stochastic⟩ 5 w =
          (if w.all (fun b => !b) then 1 else 0) := absorbing_word w
      cases y <;> cases b <;>
        simp [wordProb,kernel,row,Fin.sum_univ_succ,profile,hz]

/-- Canonical representatives of precisely the five stable classes. -/
def representative (q : Fin 5) : Fin 6 := ⟨q.val, by omega⟩

def quotientRow (q : Fin 5) (e : Bool × Fin 5) : ℝ :=
  ∑ r : Fin 6, if stableClass r = e.2 then row (representative q) (e.1,r) else 0

private theorem quotient_reproduces (x : Fin 6) (y : Bool) (q : Fin 5) :
    quotientRow (stableClass x) (y,q) =
      ∑ r : Fin 6, if stableClass r = q then row x (y,r) else 0 := by
  fin_cases x <;> cases y <;> fin_cases q <;>
    norm_num [quotientRow,stableClass,representative,row,Fin.sum_univ_succ]

private theorem quotient_stochastic : IsRowStochastic quotientRow := by
  constructor
  · intro q e
    change 0 ≤ ∑ r : Fin 6, if stableClass r = e.2 then row (representative q) (e.1,r) else 0
    apply Finset.sum_nonneg
    intro r _
    split_ifs <;> first | exact row_stochastic.1 _ _ | exact le_rfl
  · intro q
    simp only [Fintype.sum_prod_type,quotientRow]
    have regroup (y : Bool) :
        (∑ d : Fin 5, ∑ r : Fin 6, if stableClass r = d then row (representative q) (y,r) else 0) =
        ∑ r : Fin 6, row (representative q) (y,r) := by
      rw [Finset.sum_comm]
      simp
    simp_rw [regroup]
    simpa only [Fintype.sum_prod_type] using row_stochastic.2 (representative q)

/-- The quotient is exactly A-infinity and carries the representative-independent
normalized joint label/successor-class kernel of this same six-state process. -/
def StochasticQuotient : Prop :=
  (∀ x x', stableClass x = stableClass x' ↔ ∀ n, residual kernel n x x') ∧
  ∃ Q : FiniteMarkovKernel (Fin 5) (Bool × Fin 5), ∀ x y q,
    Q.1 (stableClass x) (y,q) =
      ∑ r : Fin 6, if stableClass r = q then row x (y,r) else 0

private theorem stochastic_quotient : StochasticQuotient :=
  ⟨fun x x' => (limit_partition x x').symm,
    ⟨⟨quotientRow,quotient_stochastic⟩,quotient_reproduces⟩⟩

/-- Actual one-step failure probability, without discarding any successful branch. -/
def updateFailure (update : Fin 5 → Bool → Fin 5) (x : Fin 6) : ℝ :=
  ∑ e : Bool × Fin 6,
    if stableClass e.2 = update (stableClass x) e.1 then 0 else row x e

private theorem positive_update_failure (update : Fin 5 → Bool → Fin 5) :
    1/2 ≤ updateFailure update 0 := by
  have hne : ¬ (stableClass 2 = update (stableClass 0) false ∧
      stableClass 3 = update (stableClass 0) false) := by
    rintro ⟨h,h'⟩
    have hh := h.trans h'.symm
    norm_num [stableClass] at hh
  simp only [updateFailure,Fintype.sum_prod_type,Fintype.sum_bool,Fin.sum_univ_succ]
  norm_num [row,stableClass] at hne ⊢
  split_ifs <;> simp_all <;> norm_num

/-- Complete classifications, permanent plateau, actual archive equality and the
stochastic quotient and positive update obstruction of one and the same kernel. -/
theorem counterkernel_facts :
    (∀ x x', residual kernel 1 x x' ↔ firstClass x = firstClass x') ∧
    (∀ x x', residual kernel 2 x x' ↔ stableClass x = stableClass x') ∧
    (∀ n, residual kernel (n+2) = residual kernel 2) ∧
    (∀ x x', (∀ n, residual kernel n x x') ↔ stableClass x = stableClass x') ∧
    (∀ w, wordProb kernel 0 w = profile w ∧ wordProb kernel 1 w = profile w) ∧
    (∀ n, StoppingEq kernel n 0 1) ∧
    residual kernel 1 0 1 ∧ ¬ residual kernel 2 0 1 ∧
    ¬ (∀ n, residual kernel n 0 1) ∧ StochasticQuotient ∧
    (∀ update, 1/2 ≤ updateFailure update 0) := by
  refine ⟨first_partition,second_partition,plateau,limit_partition,common_word,?_,?_,?_,?_,
    stochastic_quotient,positive_update_failure⟩
  · intro n
    apply (trace_iff_stopping kernel n 0 1).mp
    intro w _
    exact (common_word w).1.trans (common_word w).2.symm
  · exact (first_partition 0 1).mpr (by decide)
  · intro h
    have hh := (second_partition 0 1).mp h
    norm_num [stableClass] at hh
  · intro h
    have hh := (second_partition 0 1).mp (h 2)
    norm_num [stableClass] at hh

/-- The two withdrawn assertions, restricted to this very process: all-depth
stopping equality implies residual equality; and a stochastic residual quotient
admits a label-determined update with zero actual failure probability. -/
def claim : Prop :=
  (∀ x x' : Fin 6, (∀ n, StoppingEq kernel n x x') → ∀ n, residual kernel n x x') ∨
  (StochasticQuotient → ∃ update : Fin 5 → Bool → Fin 5,
    ∀ x, updateFailure update x = 0)

/-- Each disjunct fails for the same normalized kernel. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨_,_,_,_,_,hs,_,hsecond,_,hq,hfailure⟩ := counterkernel_facts
  rcases h with h | h
  · exact hsecond (h 0 1 hs 2)
  · obtain ⟨update,hu⟩ := h hq
    have hf := hfailure update
    rw [hu 0] at hf
    norm_num at hf

#print axioms counterkernel_facts
#print axioms result
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteResiduals.SixStateResidualSeparation
