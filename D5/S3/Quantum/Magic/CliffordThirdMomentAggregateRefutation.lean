/- GID: D5/S3/Quantum/Magic/CliffordThirdMomentAggregateRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Magic/CliffordThirdMomentAggregateRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Magic/CliffordThirdMomentAggregateRefutation.claim; result=D5/S3/Quantum/Magic/CliffordThirdMomentAggregateRefutation.result; claim=D5/S3/Quantum/Magic/CliffordThirdMomentAggregateRefutation.claim
   digest: An isotropic aggregate of a two-qudit state in dimension five is below six. -/

import D5.S3.Quantum.Magic.CliffordThirdMomentNegativity
import Mathlib.Logic.Equiv.Fin.Basic

namespace D5.S3.Quantum.Magic.CliffordThirdMomentAggregateRefutation

open Matrix
open D5.S3.Quantum.Magic.CliffordThirdMomentNegativity
open scoped ComplexOrder

/-- The graph with the source orientation `(Oy,y)`. -/
def graphSubspace {d : ℕ} (O : Matrix (Fin 3) (Fin 3) (ZMod d)) :
    Submodule (ZMod d) ((Fin 3 → ZMod d) × (Fin 3 → ZMod d)) :=
  LinearMap.range ((Matrix.mulVecLin O).prod LinearMap.id)

/-- The stochastic orthogonal matrices indexing the isotropic graphs. -/
noncomputable def stochasticOrthogonal (d : ℕ) [NeZero d] :
    Finset (Matrix (Fin 3) (Fin 3) (ZMod d)) := by
  classical
  exact Finset.univ.filter (fun O => Oᵀ * O = 1 ∧ O *ᵥ (fun _ => 1) = (fun _ => 1))

/-- The aggregate over all isotropic graph subspaces. -/
noncomputable def kappaIso (d n : ℕ) [NeZero d] (Psi : (Fin n → ZMod d) → ℂ) : ℂ :=
  ∑ O ∈ stochasticOrthogonal d, kappa d n Psi (graphSubspace O)

/-- The aggregate isotropic lower bound of Zhu--Mao--Yi Conjecture 2. -/
def claim : Prop :=
  ∀ (d : ℕ) [Fact d.Prime], d ≠ 2 →
    ∀ (n : ℕ) (Psi : (Fin n → ZMod d) → ℂ),
      ∑ x, ‖Psi x‖ ^ 2 = 1 → (6 : ℂ) ≤ kappaIso d n Psi

private def action {d n : ℕ} (O : Matrix (Fin 3) (Fin 3) (ZMod d))
    (Y : Fin 3 → Fin n → ZMod d) : Fin 3 → Fin n → ZMod d :=
  fun k j => (O *ᵥ (fun i => Y i j)) k

private theorem kappa_graph {d n : ℕ} [NeZero d]
    (O : Matrix (Fin 3) (Fin 3) (ZMod d)) (Psi : (Fin n → ZMod d) → ℂ) :
    kappa d n Psi (graphSubspace O) =
      ∑ Y : Fin 3 → Fin n → ZMod d, ∏ k, Psi (Y k) * star (Psi (action O Y k)) := by
  classical
  have mem_graph (x y : Fin 3 → ZMod d) :
      (x, y) ∈ graphSubspace O ↔ x = O *ᵥ y := by
    change (∃ z, (O *ᵥ z, z) = (x, y)) ↔ _
    simp only [Prod.mk.injEq]
    constructor
    · rintro ⟨z, hx, rfl⟩
      exact hx.symm
    · intro hx
      exact ⟨y, hx.symm, rfl⟩
  unfold kappa
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Y _
  have indicator (X : Fin 3 → Fin n → ZMod d) :
      R d n (graphSubspace O) X Y = if X = action O Y then 1 else 0 := by
    simp only [R, mem_graph]
    by_cases h : X = action O Y
    · subst X
      simp only [action, if_true, Finset.prod_const_one]
    · have hn : ∃ j, (fun k => X k j) ≠ O *ᵥ (fun k => Y k j) := by
        by_contra hh
        push Not at hh
        apply h
        funext k j
        exact congrFun (hh j) k
      obtain ⟨j, hj⟩ := hn
      rw [if_neg h]
      exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)
  simp only [indicator, stateCube, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem kappa_rows {d n : ℕ} [NeZero d]
    (O : Matrix (Fin 3) (Fin 3) (ZMod d)) (Psi : (Fin n → ZMod d) → ℂ)
    (e : Equiv.Perm (Fin 3)) :
    kappa d n Psi (graphSubspace (O.submatrix e id)) =
      kappa d n Psi (graphSubspace O) := by
  classical
  rw [kappa_graph, kappa_graph]
  apply Finset.sum_congr rfl
  intro Y _
  simp only [Finset.prod_mul_distrib]
  congr 1
  exact Fintype.prod_equiv e _ _ (fun k => rfl)

private def base : Matrix (Fin 3) (Fin 3) (ZMod 5) := !![3,4,4;4,3,4;4,4,3]

private def orbit (O : Matrix (Fin 3) (Fin 3) (ZMod 5)) :
    Finset (Matrix (Fin 3) (Fin 3) (ZMod 5)) :=
  Finset.univ.image (fun e : Equiv.Perm (Fin 3) => O.submatrix e id)

private def rows : Fin 6 → Fin 3 → ZMod 5 :=
  ![![1,0,0], ![0,1,0], ![0,0,1], ![3,4,4], ![4,3,4], ![4,4,3]]

private def rowMatrix (r : Fin 3 → Fin 6) : Matrix (Fin 3) (Fin 3) (ZMod 5) :=
  fun i => rows (r i)

private theorem group_five : stochasticOrthogonal 5 = orbit 1 ∪ orbit base := by
  classical
  have row_options : ∀ y : Fin 3 → ZMod 5,
      (∑ k, y k * y k) = 1 → (∑ k, y k) = 1 → ∃ i : Fin 6, y = rows i := by
    decide +kernel
  have row_test : ∀ r : Fin 3 → Fin 6,
      rowMatrix r * (rowMatrix r)ᵀ = 1 → rowMatrix r ∈ orbit 1 ∪ orbit base := by
    decide +kernel
  have valid : ∀ e : Equiv.Perm (Fin 3),
      let P := (1 : Matrix (Fin 3) (Fin 3) (ZMod 5)).submatrix e id
      let Q := base.submatrix e id
      (Pᵀ * P = 1 ∧ P *ᵥ (fun _ => 1) = (fun _ => 1)) ∧
      (Qᵀ * Q = 1 ∧ Q *ᵥ (fun _ => 1) = (fun _ => 1)) := by
    decide +kernel
  ext O
  unfold stochasticOrthogonal
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hO, hOne⟩
    have hOO : O * Oᵀ = 1 := mul_eq_one_comm.mp hO
    have hr (i : Fin 3) : ∃ a : Fin 6, O i = rows a := by
      apply row_options (O i)
      · simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] using
          congrFun (congrFun hOO i) i
      · simpa only [Matrix.mulVec, dotProduct, mul_one] using congrFun hOne i
    choose r hr using hr
    have hmatrix : O = rowMatrix r := funext hr
    rw [hmatrix] at hOO ⊢
    exact row_test r hOO
  · intro hO
    rcases Finset.mem_union.mp hO with hO | hO
    · obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hO
      exact (valid e).1
    · obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hO
      exact (valid e).2

private theorem kappa_identity {d n : ℕ} [NeZero d]
    (Psi : (Fin n → ZMod d) → ℂ) (hn : ∑ x, ‖Psi x‖ ^ 2 = 1) :
    kappa d n Psi (graphSubspace 1) = 1 := by
  classical
  rw [kappa_graph]
  have hid (Y : Fin 3 → Fin n → ZMod d) : action (1 : Matrix _ _ (ZMod d)) Y = Y := by
    funext k j
    exact congrFun (Matrix.one_mulVec (fun i => Y i j)) k
  simp only [hid]
  rw [← Fintype.prod_sum (fun _ : Fin 3 =>
    fun x : Fin n → ZMod d => Psi x * star (Psi x))]
  have hs : (∑ x, Psi x * star (Psi x)) = 1 := by
    simp_rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [← Complex.ofReal_sum, hn]
    rfl
  simp only [hs, Finset.prod_const_one]

private def v (a b : ZMod 5) : ℤ :=
  !![8,-5,0,4,5;0,3,6,4,-4;-2,-5,-3,0,3;-3,0,5,-8,-6;5,-4,2,-5,0]
    ⟨a.val, ZMod.val_lt a⟩ ⟨b.val, ZMod.val_lt b⟩

private noncomputable def psi (x : Fin 2 → ZMod 5) : ℂ :=
  (v (x 0) (x 1) : ℂ) / (Real.sqrt 458 : ℂ)

private theorem normalized_psi : ∑ x, ‖psi x‖ ^ 2 = 1 := by
  classical
  have norm_v : (∑ x : Fin 2 → ZMod 5, v (x 0) (x 1) ^ 2) = 458 := by decide +kernel
  simp_rw [psi, norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 458), Complex.sq_norm, Complex.normSq_intCast,
    ← sq, ← Int.cast_pow]
  rw [← Finset.sum_div, ← Int.cast_sum, norm_v]
  norm_num

private def partialValues (a : Fin 3 → ZMod 5) : ℤ :=
  ![
    ![
      ![808690, -213484, -303836, -120628, -82740],
      ![-213484, -53548, 95997, -66231, 190248],
      ![-303836, 95997, -12492, -5950, 80635],
      ![-120628, -66231, -5950, -277202, -111406],
      ![-82740, 190248, 80635, -111406, -134442]],
    ![
      ![-213484, -53548, 95997, -66231, 190248],
      ![-53548, 166169, -82740, 14755, -277202],
      ![95997, -82740, -72653, 72353, 2165],
      ![-66231, 14755, 72353, -303836, 124689],
      ![190248, -277202, 2165, 124689, -12492]],
    ![
      ![-303836, 95997, -12492, -5950, 80635],
      ![95997, -82740, -72653, 72353, 2165],
      ![-12492, -72653, 41501, -53548, -120628],
      ![-5950, 72353, -53548, -134442, 128535],
      ![80635, 2165, -120628, 128535, 14755]],
    ![
      ![-120628, -66231, -5950, -277202, -111406],
      ![-66231, 14755, 72353, -303836, 124689],
      ![-5950, 72353, -53548, -134442, 128535],
      ![-277202, -303836, -134442, 787610, -72653],
      ![-111406, 124689, 128535, -72653, -213484]],
    ![
      ![-82740, 190248, 80635, -111406, -134442],
      ![190248, -277202, 2165, 124689, -12492],
      ![80635, 2165, -120628, 128535, 14755],
      ![-111406, 124689, 128535, -72653, -213484],
      ![-134442, -12492, 14755, -213484, 90010]]]
    ⟨(a 0).val, ZMod.val_lt (a 0)⟩
    ⟨(a 1).val, ZMod.val_lt (a 1)⟩
    ⟨(a 2).val, ZMod.val_lt (a 2)⟩

set_option maxRecDepth 100000 in
private theorem integer_slice_00 : ∀ c : Fin 5,
    (∑ b : Fin 3 → ZMod 5, ∏ k,
      v (![0,0,c] k) (b k) * v ((base *ᵥ ![0,0,c]) k) ((base *ᵥ b) k)) =
      partialValues ![0,0,c] := by
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 100000 in
private theorem integer_slice_01 : ∀ c : Fin 5,
    (∑ b : Fin 3 → ZMod 5, ∏ k,
      v (![0,1,c] k) (b k) * v ((base *ᵥ ![0,1,c]) k) ((base *ᵥ b) k)) =
      partialValues ![0,1,c] := by
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 100000 in
private theorem integer_slice_02 : ∀ c : Fin 5,
    (∑ b : Fin 3 → ZMod 5, ∏ k,
      v (![0,2,c] k) (b k) * v ((base *ᵥ ![0,2,c]) k) ((base *ᵥ b) k)) =
      partialValues ![0,2,c] := by
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 100000 in
private theorem integer_slice_03 : ∀ c : Fin 5,
    (∑ b : Fin 3 → ZMod 5, ∏ k,
      v (![0,3,c] k) (b k) * v ((base *ᵥ ![0,3,c]) k) ((base *ᵥ b) k)) =
      partialValues ![0,3,c] := by
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 100000 in
private theorem integer_slice_04 : ∀ c : Fin 5,
    (∑ b : Fin 3 → ZMod 5, ∏ k,
      v (![0,4,c] k) (b k) * v ((base *ᵥ ![0,4,c]) k) ((base *ᵥ b) k)) =
      partialValues ![0,4,c] := by
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 100000 in
private theorem integer_slice_10 : ∀ c : Fin 5,
    (∑ b : Fin 3 → ZMod 5, ∏ k,
      v (![1,0,c] k) (b k) * v ((base *ᵥ ![1,0,c]) k) ((base *ᵥ b) k)) =
      partialValues ![1,0,c] := by
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 100000 in
private theorem integer_slice_11 : ∀ c : Fin 5,
    (∑ b : Fin 3 → ZMod 5, ∏ k,
      v (![1,1,c] k) (b k) * v ((base *ᵥ ![1,1,c]) k) ((base *ᵥ b) k)) =
      partialValues ![1,1,c] := by
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 100000 in
private theorem integer_slice_12 : ∀ c : Fin 5,
    (∑ b : Fin 3 → ZMod 5, ∏ k,
      v (![1,2,c] k) (b k) * v ((base *ᵥ ![1,2,c]) k) ((base *ᵥ b) k)) =
      partialValues ![1,2,c] := by
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 100000 in
private theorem integer_slice_13 : ∀ c : Fin 5,
    (∑ b : Fin 3 → ZMod 5, ∏ k,
      v (![1,3,c] k) (b k) * v ((base *ᵥ ![1,3,c]) k) ((base *ᵥ b) k)) =
      partialValues ![1,3,c] := by
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 100000 in
private theorem integer_slice_14 : ∀ c : Fin 5,
    (∑ b : Fin 3 → ZMod 5, ∏ k,
      v (![1,4,c] k) (b k) * v ((base *ᵥ ![1,4,c]) k) ((base *ᵥ b) k)) =
      partialValues ![1,4,c] := by
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 100000 in
private theorem integer_slice_20 : ∀ c : Fin 5,
    (∑ b : Fin 3 → ZMod 5, ∏ k,
      v (![2,0,c] k) (b k) * v ((base *ᵥ ![2,0,c]) k) ((base *ᵥ b) k)) =
      partialValues ![2,0,c] := by
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 100000 in
private theorem integer_slice_21 : ∀ c : Fin 5,
    (∑ b : Fin 3 → ZMod 5, ∏ k,
      v (![2,1,c] k) (b k) * v ((base *ᵥ ![2,1,c]) k) ((base *ᵥ b) k)) =
      partialValues ![2,1,c] := by
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 100000 in
private theorem integer_slice_22 : ∀ c : Fin 5,
    (∑ b : Fin 3 → ZMod 5, ∏ k,
      v (![2,2,c] k) (b k) * v ((base *ᵥ ![2,2,c]) k) ((base *ᵥ b) k)) =
      partialValues ![2,2,c] := by
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 100000 in
private theorem integer_slice_23 : ∀ c : Fin 5,
    (∑ b : Fin 3 → ZMod 5, ∏ k,
      v (![2,3,c] k) (b k) * v ((base *ᵥ ![2,3,c]) k) ((base *ᵥ b) k)) =
      partialValues ![2,3,c] := by
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 100000 in
private theorem integer_slice_24 : ∀ c : Fin 5,
    (∑ b : Fin 3 → ZMod 5, ∏ k,
      v (![2,4,c] k) (b k) * v ((base *ᵥ ![2,4,c]) k) ((base *ᵥ b) k)) =
      partialValues ![2,4,c] := by
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 100000 in
private theorem integer_slice_30 : ∀ c : Fin 5,
    (∑ b : Fin 3 → ZMod 5, ∏ k,
      v (![3,0,c] k) (b k) * v ((base *ᵥ ![3,0,c]) k) ((base *ᵥ b) k)) =
      partialValues ![3,0,c] := by
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 100000 in
private theorem integer_slice_31 : ∀ c : Fin 5,
    (∑ b : Fin 3 → ZMod 5, ∏ k,
      v (![3,1,c] k) (b k) * v ((base *ᵥ ![3,1,c]) k) ((base *ᵥ b) k)) =
      partialValues ![3,1,c] := by
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 100000 in
private theorem integer_slice_32 : ∀ c : Fin 5,
    (∑ b : Fin 3 → ZMod 5, ∏ k,
      v (![3,2,c] k) (b k) * v ((base *ᵥ ![3,2,c]) k) ((base *ᵥ b) k)) =
      partialValues ![3,2,c] := by
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 100000 in
private theorem integer_slice_33 : ∀ c : Fin 5,
    (∑ b : Fin 3 → ZMod 5, ∏ k,
      v (![3,3,c] k) (b k) * v ((base *ᵥ ![3,3,c]) k) ((base *ᵥ b) k)) =
      partialValues ![3,3,c] := by
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 100000 in
private theorem integer_slice_34 : ∀ c : Fin 5,
    (∑ b : Fin 3 → ZMod 5, ∏ k,
      v (![3,4,c] k) (b k) * v ((base *ᵥ ![3,4,c]) k) ((base *ᵥ b) k)) =
      partialValues ![3,4,c] := by
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 100000 in
private theorem integer_slice_40 : ∀ c : Fin 5,
    (∑ b : Fin 3 → ZMod 5, ∏ k,
      v (![4,0,c] k) (b k) * v ((base *ᵥ ![4,0,c]) k) ((base *ᵥ b) k)) =
      partialValues ![4,0,c] := by
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 100000 in
private theorem integer_slice_41 : ∀ c : Fin 5,
    (∑ b : Fin 3 → ZMod 5, ∏ k,
      v (![4,1,c] k) (b k) * v ((base *ᵥ ![4,1,c]) k) ((base *ᵥ b) k)) =
      partialValues ![4,1,c] := by
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 100000 in
private theorem integer_slice_42 : ∀ c : Fin 5,
    (∑ b : Fin 3 → ZMod 5, ∏ k,
      v (![4,2,c] k) (b k) * v ((base *ᵥ ![4,2,c]) k) ((base *ᵥ b) k)) =
      partialValues ![4,2,c] := by
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 100000 in
private theorem integer_slice_43 : ∀ c : Fin 5,
    (∑ b : Fin 3 → ZMod 5, ∏ k,
      v (![4,3,c] k) (b k) * v ((base *ᵥ ![4,3,c]) k) ((base *ᵥ b) k)) =
      partialValues ![4,3,c] := by
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 100000 in
private theorem integer_slice_44 : ∀ c : Fin 5,
    (∑ b : Fin 3 → ZMod 5, ∏ k,
      v (![4,4,c] k) (b k) * v ((base *ᵥ ![4,4,c]) k) ((base *ᵥ b) k)) =
      partialValues ![4,4,c] := by
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 100000 in
private theorem integer_sum :
    (∑ a : Fin 3 → ZMod 5, ∑ b : Fin 3 → ZMod 5,
      ∏ k, v (a k) (b k) * v ((base *ᵥ a) k) ((base *ᵥ b) k)) = -2577430 := by
  have inner : ∀ a : Fin 3 → ZMod 5,
      (∑ b : Fin 3 → ZMod 5,
        ∏ k, v (a k) (b k) * v ((base *ᵥ a) k) ((base *ᵥ b) k)) = partialValues a := by
    simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
    change ∀ i j l : Fin 5,
      (∑ b : Fin 3 → ZMod 5, ∏ k,
        v (![i,j,l] k) (b k) * v ((base *ᵥ ![i,j,l]) k) ((base *ᵥ b) k)) =
        partialValues ![i,j,l]
    intro i j
    fin_cases i <;> fin_cases j
    · exact integer_slice_00
    · exact integer_slice_01
    · exact integer_slice_02
    · exact integer_slice_03
    · exact integer_slice_04
    · exact integer_slice_10
    · exact integer_slice_11
    · exact integer_slice_12
    · exact integer_slice_13
    · exact integer_slice_14
    · exact integer_slice_20
    · exact integer_slice_21
    · exact integer_slice_22
    · exact integer_slice_23
    · exact integer_slice_24
    · exact integer_slice_30
    · exact integer_slice_31
    · exact integer_slice_32
    · exact integer_slice_33
    · exact integer_slice_34
    · exact integer_slice_40
    · exact integer_slice_41
    · exact integer_slice_42
    · exact integer_slice_43
    · exact integer_slice_44
  rw [show (∑ a : Fin 3 → ZMod 5, ∑ b : Fin 3 → ZMod 5,
      ∏ k, v (a k) (b k) * v ((base *ᵥ a) k) ((base *ᵥ b) k)) =
      ∑ a, partialValues a from Finset.sum_congr rfl (fun a _ => inner a)]
  decide +kernel

private theorem kappa_base : kappa 5 2 psi (graphSubspace base) = -2577430 / 458 ^ 3 := by
  classical
  rw [kappa_graph]
  simp only [psi, star_div₀, Complex.star_def, Complex.conj_ofReal,
    map_intCast, div_mul_div_comm]
  simp_rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 458)]
  simp_rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Finset.sum_div]
  simp only [← Int.cast_mul, ← Int.cast_prod, ← Int.cast_sum]
  have compute : (∑ Y : Fin 3 → Fin 2 → ZMod 5,
      ∏ k, v (Y k 0) (Y k 1) * v (action base Y k 0) (action base Y k 1)) =
      (-2577430 : ℤ) := by
    let e := (Equiv.piComm (fun _ : Fin 3 => fun _ : Fin 2 => ZMod 5)).trans
      (finTwoArrowEquiv (Fin 3 → ZMod 5))
    rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
    exact integer_sum
  rw [compute]
  norm_num

private theorem kappa_iso : kappaIso 5 2 psi = 140241723 / 24017978 := by
  classical
  have disjoint : Disjoint (orbit 1) (orbit base) := by decide +kernel
  have orbit_value (O : Matrix (Fin 3) (Fin 3) (ZMod 5)) (hi : Function.Injective O) :
      (∑ Q ∈ orbit O, kappa 5 2 psi (graphSubspace Q)) =
        6 * kappa 5 2 psi (graphSubspace O) := by
    rw [orbit, Finset.sum_image]
    · simp_rw [kappa_rows]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
      norm_num
    · intro e _ f _ heq
      apply Equiv.ext
      intro i
      exact hi (congrFun heq i)
  have hi : Function.Injective (1 : Matrix (Fin 3) (Fin 3) (ZMod 5)) := by
    have h : ∀ i j : Fin 3,
        (1 : Matrix (Fin 3) (Fin 3) (ZMod 5)) i i =
          (1 : Matrix (Fin 3) (Fin 3) (ZMod 5)) j i → i = j := by decide +kernel
    intro i j he
    exact h i j (congrFun he i)
  have hb : Function.Injective base := by
    have h : ∀ i j : Fin 3, base i i = base j i → i = j := by decide +kernel
    intro i j he
    exact h i j (congrFun he i)
  rw [kappaIso, group_five, Finset.sum_union disjoint, orbit_value 1 hi,
    orbit_value base hb, kappa_identity psi normalized_psi, kappa_base]
  norm_num

/-- The aggregate isotropic lower bound fails for a normalized two-qudit state at `d = 5`. -/
theorem result : ¬ claim := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  intro h
  have hbound := h 5 (by decide) 2 psi normalized_psi
  rw [kappa_iso, Complex.le_def] at hbound
  norm_num at hbound

#print axioms result

end D5.S3.Quantum.Magic.CliffordThirdMomentAggregateRefutation
