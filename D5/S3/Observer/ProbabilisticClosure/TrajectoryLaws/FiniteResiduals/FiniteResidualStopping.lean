/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteResiduals/FiniteResidualStopping
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteResiduals/FiniteResidualStopping
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Recursive joint residuals imply word laws, which exactly characterize finite stopping archives. -/

import D5.S3.Estimation.DecisionRisk.DescentDefectBounds
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Union

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
open D5.S3.Estimation.DecisionRisk.DescentDefectBounds
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteResiduals.FiniteResidualStopping

variable {S Y : Type*} [Fintype S] [Fintype Y]

/-- The joint mass of a label and the equivalence class of a representative. -/
def classMass (K : FiniteMarkovKernel S (Y × S)) (R : S → S → Prop)
    (x : S) (y : Y) (c : S) : ℝ := by
  classical
  exact ∑ r, if R r c then K.1 x (y,r) else 0

/-- Constant current observation gives the universal zeroth relation. The previous
relation is explicitly retained at each successor stage. -/
def residual (K : FiniteMarkovKernel S (Y × S)) : ℕ → S → S → Prop
  | 0, _, _ => True
  | n+1, x, x' => residual K n x x' ∧
      ∀ y c, classMass K (residual K n) x y c = classMass K (residual K n) x' y c

/-- Actual emitted-word probabilities, with no hidden class in the archive. -/
def wordProb (K : FiniteMarkovKernel S (Y × S)) (x : S) : List Y → ℝ
  | [] => 1
  | y :: w => ∑ r, K.1 x (y,r) * wordProb K r w

def TraceEq (K : FiniteMarkovKernel S (Y × S)) (n : ℕ) (x x' : S) : Prop :=
  ∀ w : List Y, w.length ≤ n → wordProb K x w = wordProb K x' w

/-- The only control is stopping or taking the unique legal action; branches are
indexed only by the label actually emitted. -/
inductive Experiment (Y : Type*) : ℕ → Type _
  | stop {n : ℕ} : Experiment Y n
  | step {n : ℕ} : (Y → Experiment Y n) → Experiment Y (n+1)

/-- Chronological execution sums over actual hidden successors, independently of
word probabilities or residual equivalence. -/
def archiveProb (K : FiniteMarkovKernel S (Y × S)) :
    {n : ℕ} → Experiment Y n → S → List Y → ℝ
  | _, .stop, _, w => if w = [] then 1 else 0
  | _, .step _, _, [] => 0
  | _, .step f, x, y::w => ∑ r, K.1 x (y,r) * archiveProb K (f y) r w

/-- Whether the tree stops for the first time at precisely this recorded word. -/
def accepts : {n : ℕ} → Experiment Y n → List Y → Prop
  | _, .stop, w => w = []
  | _, .step _, [] => False
  | _, .step f, y::w => accepts (f y) w

/-- All possible archives form a finite prefix-free leaf set. -/
def leaves [DecidableEq Y] : {n : ℕ} → Experiment Y n → Finset (List Y)
  | _, .stop => {[]}
  | _, .step f => Finset.univ.biUnion fun y => (leaves (f y)).image (List.cons y)

/-- Equality of every permitted finite-depth stopped archive law. -/
def StoppingEq (K : FiniteMarkovKernel S (Y × S)) (n : ℕ) (x x' : S) : Prop :=
  ∀ k, k ≤ n → ∀ E : Experiment Y k, ∀ w, archiveProb K E x w = archiveProb K E x' w

private theorem residual_equivalence (K : FiniteMarkovKernel S (Y × S)) (n : ℕ) :
    Equivalence (residual K n) := by
  induction n with
  | zero => exact ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩
  | succ n ih =>
    refine ⟨fun x => ⟨ih.refl x, fun _ _ => rfl⟩, ?_, ?_⟩
    · intro x x' h
      exact ⟨ih.symm h.1, fun y c => (h.2 y c).symm⟩
    · intro x x' x'' h h'
      exact ⟨ih.trans h.1 h'.1, fun y c => (h.2 y c).trans (h'.2 y c)⟩

/-- A class-constant continuation can be integrated using only class masses. -/
private theorem integrate_classes (K : FiniteMarkovKernel S (Y × S))
    (R : S → S → Prop) (hR : Equivalence R) (x x' : S) (y : Y)
    (h : ∀ c, classMass K R x y c = classMass K R x' y c)
    (g : S → ℝ) (hg : ∀ a b, R a b → g a = g b) :
    (∑ r, K.1 x (y,r) * g r) = ∑ r, K.1 x' (y,r) * g r := by
  classical
  let setoid : Setoid S := ⟨R,hR⟩
  letI := setoid
  conv_lhs => rw [Finset.sum_partition setoid]
  conv_rhs => rw [Finset.sum_partition setoid]
  apply Finset.sum_congr rfl
  intro q _
  obtain ⟨c,rfl⟩ := Quotient.exists_rep q
  have group (a : S) :
      (∑ r ∈ Finset.univ.filter (fun r => (Quotient.mk setoid r) = Quotient.mk setoid c),
        K.1 a (y,r) * g r) = classMass K R a y c * g c := by
    rw [classMass, Finset.sum_mul]
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _
    by_cases hr : R r c
    · rw [if_pos (Quotient.sound hr), if_pos hr, hg r c hr]
    · rw [if_neg (fun he => hr (Quotient.exact he)), if_neg hr, zero_mul]
  rw [group,group,h c]

/-- Every recursive residual preserves all actual words through its horizon. -/
theorem residual_sound (K : FiniteMarkovKernel S (Y × S)) (n : ℕ) (x x' : S)
    (h : residual K n x x') : TraceEq K n x x' := by
  induction n generalizing x x' with
  | zero =>
    intro w hw
    have : w = [] := List.length_eq_zero.mp (Nat.eq_zero_of_le_zero hw)
    subst w
    rfl
  | succ n ih =>
    intro w hw
    cases w with
    | nil => rfl
    | cons y w =>
      exact integrate_classes K (residual K n) (residual_equivalence K n) x x' y
        (h.2 y) (fun r => wordProb K r w)
        (fun a b hab => ih a b hab w (by simpa using hw))

private theorem archive_word (K : FiniteMarkovKernel S (Y × S))
    {n : ℕ} (E : Experiment Y n) (x : S) (w : List Y) :
    archiveProb K E x w = if accepts E w then wordProb K x w else 0 := by
  classical
  induction E generalizing x w with
  | stop => cases w <;> simp [archiveProb, accepts, wordProb]
  | step f ih =>
    cases w with
    | nil => simp [archiveProb, accepts]
    | cons y w =>
      simp only [archiveProb, accepts, ih]
      by_cases h : accepts (f y) w <;> simp [h, wordProb]

private theorem accepts_length {n : ℕ} (E : Experiment Y n) (w : List Y)
    (h : accepts E w) : w.length ≤ n := by
  induction E generalizing w with
  | stop =>
    have hw : w = [] := h
    subst w
    exact Nat.zero_le _
  | step f ih =>
    cases w with
    | nil => exact False.elim h
    | cons y w => exact Nat.succ_le_succ (ih y w h)

private def full : (k : ℕ) → Experiment Y k
  | 0 => .stop
  | k+1 => .step (fun _ => full k)

private theorem full_accepts (w : List Y) : accepts (full w.length) w := by
  induction w with
  | nil => rfl
  | cons y w ih => exact ih

/-- Equality of actual bounded word laws is exactly equality of the independently
executed stopping trees. Immediate stopping, empty words and null branches are included. -/
theorem trace_iff_stopping (K : FiniteMarkovKernel S (Y × S)) (n : ℕ) (x x' : S) :
    TraceEq K n x x' ↔ StoppingEq K n x x' := by
  classical
  constructor
  · intro h k hk E w
    rw [archive_word, archive_word]
    by_cases ha : accepts E w
    · rw [if_pos ha, if_pos ha, h w ((accepts_length E w ha).trans hk)]
    · rw [if_neg ha, if_neg ha]
  · intro h w hw
    have hh := h w.length hw (full w.length) w
    simpa only [archive_word, if_pos (full_accepts w)] using hh

private theorem leaf_sum_step [DecidableEq Y] {n : ℕ} (f : Y → Experiment Y n)
    (g : List Y → ℝ) :
    (∑ w ∈ leaves (.step f), g w) = ∑ y, ∑ w ∈ leaves (f y), g (y::w) := by
  rw [leaves, Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro y _
    exact Finset.sum_image (fun _ _ _ _ h => (List.cons.inj h).2)
  · intro y _ y' _ hne
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    obtain ⟨v,_,hv⟩ := Finset.mem_image.mp hw
    obtain ⟨v',_,hv'⟩ := Finset.mem_image.mp hw'
    exact hne (List.cons.inj (hv.trans hv'.symm)).1

private theorem archive_nonneg (K : FiniteMarkovKernel S (Y × S))
    {n : ℕ} (E : Experiment Y n) (x : S) (w : List Y) : 0 ≤ archiveProb K E x w := by
  induction E generalizing x w with
  | stop => dsimp [archiveProb]; split_ifs <;> norm_num
  | step f ih =>
    cases w with
    | nil => exact le_rfl
    | cons y w => exact Finset.sum_nonneg (fun r _ => mul_nonneg (K.2.1 _ _) (ih y r w))

private theorem archive_total [DecidableEq Y] (K : FiniteMarkovKernel S (Y × S))
    {n : ℕ} (E : Experiment Y n) (x : S) :
    (∑ w ∈ leaves E, archiveProb K E x w) = 1 := by
  induction E generalizing x with
  | stop => simp [leaves,archiveProb]
  | step f ih =>
    rw [leaf_sum_step]
    simp only [archiveProb]
    have regroup (y : Y) :
        (∑ w ∈ leaves (f y), ∑ r, K.1 x (y,r) * archiveProb K (f y) r w) =
          ∑ r, K.1 x (y,r) := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, ih, mul_one]
    simp_rw [regroup]
    simpa only [Fintype.sum_prod_type] using K.2.2 x

/-- Chronological execution is a nonnegative probability law supported on finite
archives of length at most the declared depth. -/
theorem archive_probability_law (K : FiniteMarkovKernel S (Y × S))
    {n : ℕ} (E : Experiment Y n) (x : S) :
    (∀ w, 0 ≤ archiveProb K E x w) ∧
    (∀ w, n < w.length → archiveProb K E x w = 0) ∧
    (letI := Classical.decEq Y; ∑ w ∈ leaves E, archiveProb K E x w) = 1 := by
  classical
  refine ⟨archive_nonneg K E x, ?_, archive_total K E x⟩
  intro w hw
  rw [archive_word, if_neg]
  intro ha
  exact (Nat.not_le_of_lt hw) (accepts_length E w ha)

#print axioms residual_sound
#print axioms trace_iff_stopping
#print axioms archive_probability_law

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteResiduals.FiniteResidualStopping
