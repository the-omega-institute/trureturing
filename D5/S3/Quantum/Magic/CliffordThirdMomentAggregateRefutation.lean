/- GID: D5/S3/Quantum/Magic/CliffordThirdMomentAggregateRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Magic/CliffordThirdMomentAggregateRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Magic/CliffordThirdMomentAggregateRefutation.claim; result=D5/S3/Quantum/Magic/CliffordThirdMomentAggregateRefutation.result; claim=D5/S3/Quantum/Magic/CliffordThirdMomentAggregateRefutation.claim
   digest: A normalized two-qudit state in dimension five has aggregate isotropic third moment below six. -/

import D5.S3.Quantum.Magic.CliffordThirdMomentNegativity

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
  simp only [kappa, Matrix.trace, Matrix.diag, Matrix.mul_apply]
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
  simp only [stochasticOrthogonal, Finset.mem_filter, Finset.mem_univ, true_and]
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

end D5.S3.Quantum.Magic.CliffordThirdMomentAggregateRefutation
