/- GID: D5/S3/Quantum/Algebra/MultivariateQSPCollapseRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/MultivariateQSPCollapseRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Algebra/MultivariateQSPCollapseRefutation.claim; result=D5/S3/Quantum/Algebra/MultivariateQSPCollapseRefutation.result; claim=D5/S3/Quantum/Algebra/MultivariateQSPCollapseRefutation.claim
   digest: A two-step three-level signal protocol refutes Laneve--Wolf Conjecture 8. -/

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Algebra.MultivariateQSPCollapseRefutation

open MvPolynomial Matrix
open scoped BigOperators

/-- Polynomial vectors of unit Euclidean norm on the two-dimensional torus. -/
def PolyState := {g : Fin 3 → MvPolynomial (Fin 2) ℂ //
  ∀ a b : ℂ, ‖a‖ = 1 → ‖b‖ = 1 →
    ∑ i, ‖eval ![a, b] (g i)‖ ^ 2 = 1}

/-- Dimension of the span of all coefficient vectors. -/
def effDim (g : Fin 3 → MvPolynomial (Fin 2) ℂ) : ℕ :=
  Module.finrank ℂ (Submodule.span ℂ (Set.range fun s => fun i => (g i).coeff s))

/-- The polynomial signal operator diag(1,a,b). -/
def signalStep (g : Fin 3 → MvPolynomial (Fin 2) ℂ) :
    Fin 3 → MvPolynomial (Fin 2) ℂ := ![g 0, X 0 * g 1, X 1 * g 2]

/-- The first j processing steps, numbered from A_1; stages past m are constant. -/
def stage {m : ℕ} (A : Fin m → specialUnitaryGroup (Fin 3) ℂ)
    (g : Fin 3 → MvPolynomial (Fin 2) ℂ) : ℕ → Fin 3 → MvPolynomial (Fin 2) ℂ :=
  Nat.rec (motive := fun _ => Fin 3 → MvPolynomial (Fin 2) ℂ) g
    (fun j previous => if hj : j < m then
      fun i => ∑ l, C ((A ⟨j, hj⟩).val i l) * signalStep previous l
    else previous)

private def transferPrefix {m : ℕ} (A : Fin m → specialUnitaryGroup (Fin 3) ℂ)
    (a b : ℂ) : ℕ → Matrix (Fin 3) (Fin 3) ℂ :=
  Nat.rec (motive := fun _ => Matrix (Fin 3) (Fin 3) ℂ) 1
    (fun j previous => if hj : j < m then
      (A ⟨j, hj⟩).val * diagonal ![1, a, b] * previous
    else previous)

/-- The evaluated product A_m W ... A_1 W. -/
def transfer {m : ℕ} (A : Fin m → specialUnitaryGroup (Fin 3) ℂ)
    (a b : ℂ) : Matrix (Fin 3) (Fin 3) ℂ := transferPrefix A a b m

/-- The permissive subspace-isometry reading of Laneve--Wolf Conjecture 8. -/
def claim : Prop := ∀ (m : ℕ) (A : Fin m → specialUnitaryGroup (Fin 3) ℂ)
    (g : PolyState),
  effDim g.val ≤ 2 → effDim (stage A g.val m) ≤ 2 →
  (∀ j, 0 < j → j < m → 2 < effDim (stage A g.val j)) →
  ∃ (H H' : Submodule ℂ (EuclideanSpace ℂ (Fin 3))) (U : H ≃ₗᵢ[ℂ] H') (k h : ℕ),
    2 ≤ Module.finrank ℂ H ∧
    ∀ a b : ℂ, ‖a‖ = 1 → ‖b‖ = 1 → ∀ x : H,
      Matrix.toEuclideanLin (transfer A a b) (x : EuclideanSpace ℂ (Fin 3)) =
        (a ^ k * b ^ h) • (U x : EuclideanSpace ℂ (Fin 3))

private def cycleOne : specialUnitaryGroup (Fin 3) ℂ :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by
    rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_eq_conjTranspose]
    · norm_num [Matrix.det_fin_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two]⟩

private def cycleTwo : specialUnitaryGroup (Fin 3) ℂ :=
  ⟨!![0, 1, 0; 0, 0, 1; 1, 0, 0], by
    rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_eq_conjTranspose]
    · norm_num [Matrix.det_fin_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two]⟩

private def protocol : Fin 2 → specialUnitaryGroup (Fin 3) ℂ := ![cycleOne, cycleTwo]

private def initial : Fin 3 → MvPolynomial (Fin 2) ℂ :=
  ![C (3 / 13), C (4 / 13), C (12 / 13) * X 0]

private def middle : Fin 3 → MvPolynomial (Fin 2) ℂ :=
  ![C (12 / 13) * (X 0 * X 1), C (3 / 13), C (4 / 13) * X 0]

private def finalState : Fin 3 → MvPolynomial (Fin 2) ℂ :=
  ![C (3 / 13) * X 0, C (4 / 13) * (X 0 * X 1), C (12 / 13) * (X 0 * X 1)]

private theorem initial_normalized (a b : ℂ) (ha : ‖a‖ = 1) (_hb : ‖b‖ = 1) :
    ∑ i, ‖eval ![a, b] (initial i)‖ ^ 2 = 1 := by
  norm_num [initial, Fin.sum_univ_succ, norm_mul, norm_div, ha]

private theorem stages : stage protocol initial 1 = middle ∧
    stage protocol initial 2 = finalState := by
  have hfirst : stage protocol initial 1 = middle := by
    change (fun i => ∑ l, C ((protocol 0).val i l) * signalStep initial l) = middle
    funext i
    fin_cases i <;>
      simp [protocol, cycleOne, cycleTwo, signalStep, initial, middle,
        Fin.sum_univ_succ] <;> ring
  refine ⟨hfirst, ?_⟩
  change (fun i => ∑ l, C ((protocol 1).val i l) *
    signalStep (stage protocol initial 1) l) = finalState
  rw [hfirst]
  funext i
  fin_cases i <;>
    simp [protocol, cycleOne, cycleTwo, signalStep, middle, finalState,
      Fin.sum_univ_succ] <;> ring

private theorem transfer_diagonal (a b : ℂ) :
    transfer protocol a b = diagonal ![a, a * b, b] := by
  change (protocol 1).val * diagonal ![1, a, b] *
    ((protocol 0).val * diagonal ![1, a, b] * 1) = diagonal ![a, a * b, b]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [protocol, cycleOne, cycleTwo, Matrix.mul_apply,
      Fin.sum_univ_succ, diagonal_apply, Matrix.vecMul, dotProduct] <;> ring

private theorem coefficient_span {n : ℕ} (d : Fin n → (Fin 2 →₀ ℕ))
    (hd : Function.Injective d) (v : Fin n → (Fin 3 → ℂ)) :
    Submodule.span ℂ (Set.range fun s => fun i =>
      coeff s (∑ r, monomial (d r) (v r i))) = Submodule.span ℂ (Set.range v) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨s, rfl⟩
    have hc : (fun i => coeff s (∑ r, monomial (d r) (v r i))) =
        ∑ r, if d r = s then v r else 0 := by
      funext i
      simp only [coeff_sum, coeff_monomial, Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro r _
      by_cases h : d r = s <;> simp [h, eq_comm]
    change (fun i => coeff s (∑ r, monomial (d r) (v r i))) ∈ _
    rw [hc]
    apply Submodule.sum_mem
    intro r _
    by_cases h : d r = s
    · simpa [h] using Submodule.subset_span (Set.mem_range_self r)
    · simp [h]
  · apply Submodule.span_le.mpr
    rintro _ ⟨r, rfl⟩
    have hc : (fun i => coeff (d r) (∑ t, monomial (d t) (v t i))) = v r := by
      funext i
      simp [coeff_sum, coeff_monomial, hd.eq_iff]
    rw [← hc]
    exact Submodule.subset_span (Set.mem_range_self (d r))

private theorem initial_dimension : effDim initial = 2 := by
  let d : Fin 2 → (Fin 2 →₀ ℕ) := ![0, Finsupp.single 0 1]
  let v : Fin 2 → (Fin 3 → ℂ) := ![![3 / 13, 4 / 13, 0], ![0, 0, 12 / 13]]
  have hp : initial = fun i => ∑ r, monomial (d r) (v r i) := by
    funext i
    fin_cases i <;> simp [initial, d, v, Fin.sum_univ_succ, C_mul_X_eq_monomial]
  have hv : LinearIndependent ℂ v := by
    apply linearIndependent_fin2.mpr
    constructor
    · intro h
      have hc := congrFun h 2
      norm_num [v, Matrix.cons_val_two] at hc
    · intro c h
      have hc := congrFun h 0
      norm_num [v, Matrix.cons_val_two] at hc
  have hd : Function.Injective d := by
    intro i j h
    have hzero := congrArg (fun s => s 0) h
    have hone := congrArg (fun s => s 1) h
    fin_cases i <;> fin_cases j
    all_goals try rfl
    all_goals try norm_num [d, Matrix.cons_val_two, Finsupp.single_apply] at hzero
    all_goals norm_num [d, Matrix.cons_val_two, Finsupp.single_apply] at hone
  unfold effDim
  rw [hp, coefficient_span d hd v, finrank_span_eq_card hv]
  rfl

private theorem middle_dimension : effDim middle = 3 := by
  let d : Fin 3 → (Fin 2 →₀ ℕ) :=
    ![Finsupp.single 0 1 + Finsupp.single 1 1, 0, Finsupp.single 0 1]
  let v : Fin 3 → (Fin 3 → ℂ) :=
    ![![12 / 13, 0, 0], ![0, 3 / 13, 0], ![0, 0, 4 / 13]]
  have hp : middle = fun i => ∑ r, monomial (d r) (v r i) := by
    funext i
    fin_cases i <;>
      simp [middle, d, v, Fin.sum_univ_succ, C_mul_X_eq_monomial,
        X, monomial_mul, C_mul_monomial]
  have hv : LinearIndependent ℂ v := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc
    intro r
    have hr := congrFun hc r
    fin_cases r <;>
      simpa [v, Fin.sum_univ_succ, Pi.smul_apply, smul_eq_mul, mul_eq_zero, Matrix.cons_val_two] using hr
  have hd : Function.Injective d := by
    intro i j h
    have hzero := congrArg (fun s => s 0) h
    have hone := congrArg (fun s => s 1) h
    fin_cases i <;> fin_cases j
    all_goals try rfl
    all_goals try norm_num [d, Matrix.cons_val_two, Finsupp.single_apply] at hzero
    all_goals norm_num [d, Matrix.cons_val_two, Finsupp.single_apply] at hone
  unfold effDim
  rw [hp, coefficient_span d hd v, finrank_span_eq_card hv]
  rfl

private theorem final_dimension : effDim finalState = 2 := by
  let d : Fin 2 → (Fin 2 →₀ ℕ) :=
    ![Finsupp.single 0 1, Finsupp.single 0 1 + Finsupp.single 1 1]
  let v : Fin 2 → (Fin 3 → ℂ) := ![![3 / 13, 0, 0], ![0, 4 / 13, 12 / 13]]
  have hp : finalState = fun i => ∑ r, monomial (d r) (v r i) := by
    funext i
    fin_cases i <;>
      simp [finalState, d, v, Fin.sum_univ_succ, C_mul_X_eq_monomial,
        X, monomial_mul, C_mul_monomial]
  have hv : LinearIndependent ℂ v := by
    apply linearIndependent_fin2.mpr
    constructor
    · intro h
      have hc := congrFun h 1
      norm_num [v, Matrix.cons_val_two] at hc
    · intro c h
      have hc := congrFun h 0
      norm_num [v, Matrix.cons_val_two] at hc
  have hd : Function.Injective d := by
    intro i j h
    have hzero := congrArg (fun s => s 0) h
    have hone := congrArg (fun s => s 1) h
    fin_cases i <;> fin_cases j
    all_goals try rfl
    all_goals try norm_num [d, Matrix.cons_val_two, Finsupp.single_apply] at hzero
    all_goals norm_num [d, Matrix.cons_val_two, Finsupp.single_apply] at hone
  unfold effDim
  rw [hp, coefficient_span d hd v, finrank_span_eq_card hv]
  rfl

private theorem scalar_subspace_dimension (d : Fin 3 → ℂ) (hd : Function.Injective d)
    (H : Submodule ℂ (EuclideanSpace ℂ (Fin 3))) (c : ℂ)
    (hc : ∀ x : H, Matrix.toEuclideanLin (diagonal d) (x : EuclideanSpace ℂ (Fin 3)) =
      c • (x : EuclideanSpace ℂ (Fin 3))) :
    Module.finrank ℂ H ≤ 1 := by
  classical
  by_cases hH : H = ⊥
  · rw [hH, finrank_bot]
    decide
  obtain ⟨x, hx, hxzero⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hH
  have he : Module.End.HasEigenvalue (diagonal d).toEuclideanLin c :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (hc ⟨x, hx⟩), hxzero⟩
  obtain ⟨i, hi⟩ := (hasEigenvalue_toLin_diagonal_iff d
    (PiLp.basisFun 2 ℂ (Fin 3))).mp (by
      simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_eq_toLin] using he)
  have hz (y : H) (j : Fin 3) (hj : j ≠ i) :
      (y : EuclideanSpace ℂ (Fin 3)) j = 0 := by
    have heq := congrArg (fun v : EuclideanSpace ℂ (Fin 3) => v j) (hc y)
    simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, PiLp.toLp_apply,
      Matrix.mulVec_diagonal, PiLp.smul_apply, smul_eq_mul] at heq
    apply (mul_eq_mul_right_iff.mp heq).resolve_left
    intro hjc
    exact hj (hd (hjc.trans hi.symm))
  let f : H →ₗ[ℂ] ℂ := (EuclideanSpace.projₗ i).comp H.subtype
  have hf : Function.Injective f := by
    intro y z hyz
    apply Subtype.ext
    apply PiLp.ext
    intro j
    by_cases hj : j = i
    · subst j
      exact hyz
    · rw [hz y j hj, hz z j hj]
  simpa using f.finrank_le_finrank_of_injective hf

private theorem distinct_diagonal : Function.Injective (![Complex.I, -Complex.I, -1] :
    Fin 3 → ℂ) := by
  intro i j hij
  have hreal := congrArg Complex.re hij
  have himag := congrArg Complex.im hij
  fin_cases i <;> fin_cases j
  all_goals try rfl
  all_goals try norm_num [Matrix.cons_val_two] at hreal
  all_goals norm_num [Matrix.cons_val_two] at himag

/-- No two-dimensional subspace carries a common monomial times a fixed isometry. -/
theorem result : ¬ claim := by
  intro hclaim
  let g : PolyState := ⟨initial, initial_normalized⟩
  obtain ⟨H, H', U, k, h, hdim, haction⟩ := hclaim 2 protocol g
    (by simpa [g, initial_dimension])
    (by rw [stages.2, final_dimension])
    (by
      intro j hj hjm
      have hjone : j = 1 := by omega
      rw [hjone, stages.1, middle_dimension]
      norm_num)
  have hid (x : H) :
      (U x : EuclideanSpace ℂ (Fin 3)) = (x : EuclideanSpace ℂ (Fin 3)) := by
    have hx := haction 1 1 (by simp) (by simp) x
    have ht : transfer protocol 1 1 = (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
      rw [transfer_diagonal]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [diagonal_apply]
    simpa [ht, Matrix.toEuclideanLin] using hx.symm
  have hscalar (x : H) :
      Matrix.toEuclideanLin (diagonal ![Complex.I, -Complex.I, -1])
        (x : EuclideanSpace ℂ (Fin 3)) =
        (Complex.I ^ k * (-1 : ℂ) ^ h) • (x : EuclideanSpace ℂ (Fin 3)) := by
    have hx := haction Complex.I (-1) (by simp) (by simp) x
    simpa [transfer_diagonal, hid x] using hx
  have hsmall := scalar_subspace_dimension _ distinct_diagonal H _ hscalar
  omega

#print axioms result

end D5.S3.Quantum.Algebra.MultivariateQSPCollapseRefutation
