/- GID: D5/S3/QuadraticForms/EvolutionAlgebras/NilpotencySpectrumRefutation
   generality: I
   mirror-B: D5/B/S3/QuadraticForms/EvolutionAlgebras/NilpotencySpectrumRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuadraticForms/EvolutionAlgebras/NilpotencySpectrumRefutation.claim; result=D5/S3/QuadraticForms/EvolutionAlgebras/NilpotencySpectrumRefutation.result; claim=D5/S3/QuadraticForms/EvolutionAlgebras/NilpotencySpectrumRefutation.claim
   digest: A fifteen-dimensional evolution algebra has ordinary nilpotency index 256. -/

import D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction

/-! The ordinary lower series of the explicit rational evolution algebra refutes
the proposed binary spectrum in Conjecture 9 of arXiv:2610.22248v1. -/

set_option autoImplicit false

namespace D5.S3.QuadraticForms.EvolutionAlgebras.NilpotencySpectrumRefutation
open scoped BigOperators
open DerivationAnnihilatorObstruction

/-- Linear span of all products of elements of two subspaces. -/
def productSpace {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (μ : V →ₗ[K] V →ₗ[K] V) (U W : Submodule K V) : Submodule K V :=
  Submodule.span K {z | ∃ x ∈ U, ∃ y ∈ W, μ x y = z}

/-- The ordinary lower powers: every positive split is included. The unused zeroth
power is set to zero. -/
def ordinaryPower {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (μ : V →ₗ[K] V →ₗ[K] V) : ℕ → Submodule K V
  | 0 => ⊥
  | 1 => ⊤
  | n + 2 => ⨆ i : Fin (n + 1), productSpace μ
      (ordinaryPower μ (i.val + 1)) (ordinaryPower μ (n + 1 - i.val))
termination_by n => n

/-- Existence in the original category of finite-dimensional bilinear evolution algebras.
The index is k+1, so the preceding nonzero power is k. -/
def indexExists (K : Type) [Field K] (n k : ℕ) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module K V) (_ : FiniteDimensional K V)
    (μ : V →ₗ[K] V →ₗ[K] V),
    Module.finrank K V = n ∧ IsEvolutionAlgebra μ ∧
      ordinaryPower μ (k + 1) = ⊥ ∧ ordinaryPower μ k ≠ ⊥

/-- Both alternatives of the conjectured binary spectrum. Bounds use integer n-1. -/
def predicted (n k : ℤ) : Prop :=
  (∃ a : ℕ, k = 2 ^ a ∧ (a : ℤ) ≤ n - 1) ∨
  (2 ≤ ((Nat.digits 2 k.toNat).count 1) ∧
    (Nat.log 2 k.toNat : ℤ) + ((Nat.digits 2 k.toNat).count 1 : ℤ) ≤ n - 1)

/-- KMV, arXiv:2610.22248v1, section 2.3, Conjecture 9, with its entire universal
field/dimension/positive-k domain and both directions of the equivalence. -/
def claim : Prop :=
  ∀ (K : Type) [Field K] [Infinite K] (n k : ℤ), 0 ≤ n → 1 ≤ k →
    (indexExists K n.toNat k.toNat ↔ predicted n k)

private abbrev A := Fin 15 → ℚ
private def rows : Fin 15 → A := ![
  ![0,1,1,0,1,0,0,0,0,0,0,0,0,0,0],
  ![0,0,0,-1,-1,0,0,0,0,0,0,0,0,0,0],
  ![0,0,0,1,1,0,0,0,0,0,0,0,0,0,0],
  ![0,0,0,0,0,-1,0,-1,0,0,0,0,0,0,0],
  ![0,0,0,0,0,1,0,1,0,0,0,0,0,0,0],
  ![0,0,0,0,0,0,1,1,0,0,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,-1,0,0,0,0,-1,0],
  ![0,0,0,0,0,0,0,0,1,0,0,0,0,1,0],
  ![0,0,0,0,0,0,0,0,0,1,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,1,0,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0,1,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0,0,1,1,0],
  ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,-1],
  ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,1],
  ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]

/-- The actual multiplication on Q^15, specified by natural squares and zero mixed products. -/
def product : (Fin 15 → ℚ) →ₗ[ℚ] (Fin 15 → ℚ) →ₗ[ℚ] (Fin 15 → ℚ) :=
  LinearMap.mk₂ ℚ (fun x y => ∑ i : Fin 15, (x i * y i) • rows i)
    (by intro x y z; simp [add_mul, add_smul, Finset.sum_add_distrib])
    (by intro c x y; simp [mul_assoc, smul_smul, Finset.smul_sum])
    (by intro x y z; simp [mul_add, add_smul, Finset.sum_add_distrib])
    (by intro c x y; simp [mul_left_comm, smul_smul, Finset.smul_sum])


private theorem power_le_filtration {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (μ : V →ₗ[K] V →ₗ[K] V) (F : ℕ → Submodule K V)
    (hfirst : ⊤ ≤ F 1)
    (hmul : ∀ r s x y, x ∈ F r → y ∈ F s → μ x y ∈ F (r + s)) :
    ∀ m, ordinaryPower μ m ≤ F m := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rcases m with _ | (_ | n)
    · simp [ordinaryPower]
    · simpa [ordinaryPower] using hfirst
    · rw [ordinaryPower]
      apply iSup_le
      intro i
      apply Submodule.span_le.mpr
      rintro z ⟨x, hx, y, hy, rfl⟩
      change μ x y ∈ F (n + 1 + 1)
      have hh := hmul (i.val + 1) (n + 1 - i.val) x y
        (ih _ (by omega) hx) (ih _ (by omega) hy)
      have hi := i.isLt
      have hs : (i.val + 1) + (n + 1 - i.val) = n + 1 + 1 := by omega
      rw [← hs]
      exact hh

private theorem mul_mem_power {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (μ : V →ₗ[K] V →ₗ[K] V) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    {x y : V} (hx : x ∈ ordinaryPower μ a) (hy : y ∈ ordinaryPower μ b) :
    μ x y ∈ ordinaryPower μ (a + b) := by
  have hab : a + b = (a + b - 2) + 2 := by omega
  rw [hab, ordinaryPower]
  let i : Fin (a + b - 2 + 1) := ⟨a - 1, by omega⟩
  apply (le_iSup (fun j : Fin (a + b - 2 + 1) => productSpace μ
    (ordinaryPower μ (j.val + 1)) (ordinaryPower μ (a + b - 2 + 1 - j.val))) i)
  apply Submodule.subset_span
  refine ⟨x, ?_, y, ?_, rfl⟩
  · simpa only [show i.val + 1 = a by dsimp [i]; omega] using hx
  · simpa only [show a + b - 2 + 1 - i.val = b by dsimp [i]; omega] using hy

private theorem product_evolution : IsEvolutionAlgebra product := by
  classical
  constructor
  · intro x y
    simp only [product, LinearMap.mk₂_apply]
    congr 1
    funext i
    rw [mul_comm]
  · refine ⟨Fin 15, Pi.basisFun ℚ (Fin 15), ?_⟩
    intro i j hij
    change (∑ l : Fin 15,
      ((Pi.basisFun ℚ (Fin 15) i) l * (Pi.basisFun ℚ (Fin 15) j) l) • rows l) = 0
    apply Finset.sum_eq_zero
    intro l _
    have h : (Pi.basisFun ℚ (Fin 15) i) l * (Pi.basisFun ℚ (Fin 15) j) l = 0 := by
      by_cases hi : i = l
      · subst l; simp [Pi.basisFun_apply, Ne.symm hij]
      · simp [Pi.basisFun_apply, Pi.single_apply, hi]
    rw [h, zero_smul]

private def v : Fin 15 → A := ![
  ![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  ![0,1,1,0,1,0,0,0,0,0,0,0,0,0,0],
  ![0,0,1,0,0,0,0,0,0,0,0,0,0,0,0],
  ![0,0,0,1,1,0,0,0,0,0,0,0,0,0,0],
  ![0,0,0,0,1,0,0,0,0,0,0,0,0,0,0],
  ![0,0,0,0,0,1,0,1,0,0,0,0,0,0,0],
  ![0,0,0,0,0,0,1,1,1,0,0,0,0,1,0],
  ![0,0,0,0,0,0,0,1,0,0,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,1,0,0,0,0,1,0],
  ![0,0,0,0,0,0,0,0,0,1,0,0,0,0,1],
  ![0,0,0,0,0,0,0,0,0,0,1,0,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0,1,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0,0,1,1,0],
  ![0,0,0,0,0,0,0,0,0,0,0,0,0,1,0],
  ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]]

private def weight : Fin 15 → ℕ := ![1,2,1,3,1,5,10,1,15,30,60,120,240,1,255]

private def coordinates (x : A) : Fin 15 → ℚ :=
  ![x 0, x 1, -x 1 + x 2, x 3, -x 1 - x 3 + x 4, x 5, x 6,
    -x 5 - x 6 + x 7, -x 6 + x 8, x 9, x 10, x 11, x 12,
    -x 8 - x 12 + x 13, -x 9 + x 14]

set_option maxHeartbeats 2000000 in
-- Expand the fifteen coordinate identities of the triangular reconstruction.
private theorem reconstruction (x : A) : (∑ i : Fin 15, coordinates x i • v i) = x := by
  ext j
  fin_cases j <;> norm_num [coordinates, v, Fin.sum_univ_succ] <;> ring

private def filtration (m : ℕ) : Submodule ℚ A :=
  Submodule.span ℚ {z | ∃ i : Fin 15, m ≤ weight i ∧ v i = z}

private theorem v_mem (i : Fin 15) {m : ℕ} (h : m ≤ weight i) :
    v i ∈ filtration m := Submodule.subset_span ⟨i, h, rfl⟩

private theorem filtration_first : (⊤ : Submodule ℚ A) ≤ filtration 1 := by
  intro x _
  rw [← reconstruction x]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (v_mem i (by fin_cases i <;> decide))

private def output : Fin 15 → Fin 15 → Option (Fin 15) := ![
  ![some 1,none,none,none,none,none,none,none,none,none,none,none,none,none,none],
  ![none,some 5,some 3,some 5,some 5,none,none,none,none,none,none,none,none,none,none],
  ![none,some 3,some 3,none,none,none,none,none,none,none,none,none,none,none,none],
  ![none,some 5,none,none,some 5,none,none,none,none,none,none,none,none,none,none],
  ![none,some 5,none,some 5,some 5,none,none,none,none,none,none,none,none,none,none],
  ![none,none,none,none,none,some 6,some 8,some 8,none,none,none,none,none,none,none],
  ![none,none,none,none,none,some 8,some 9,some 8,some 9,none,none,none,some 14,some 14,none],
  ![none,none,none,none,none,some 8,some 8,some 8,none,none,none,none,none,none,none],
  ![none,none,none,none,none,none,some 9,none,some 9,none,none,none,some 14,some 14,none],
  ![none,none,none,none,none,none,none,none,none,some 10,none,none,none,none,none],
  ![none,none,none,none,none,none,none,none,none,none,some 11,none,none,none,none],
  ![none,none,none,none,none,none,none,none,none,none,none,some 12,none,none,none],
  ![none,none,none,none,none,none,some 14,none,some 14,none,none,none,none,some 14,none],
  ![none,none,none,none,none,none,some 14,none,some 14,none,none,none,some 14,some 14,none],
  ![none,none,none,none,none,none,none,none,none,none,none,none,none,none,none]]

set_option maxHeartbeats 2000000 in
-- Normalize all fifteen coordinate polynomials in the natural square table.
private theorem product_coordinates (x y : A) : product x y =
    ![0,
      x 0 * y 0,
      x 0 * y 0,
      x 2 * y 2 - x 1 * y 1,
      x 0 * y 0 + x 2 * y 2 - x 1 * y 1,
      x 4 * y 4 - x 3 * y 3,
      x 5 * y 5,
      x 4 * y 4 - x 3 * y 3 + x 5 * y 5,
      x 7 * y 7 - x 6 * y 6,
      x 8 * y 8,
      x 9 * y 9,
      x 10 * y 10,
      x 11 * y 11,
      x 7 * y 7 - x 6 * y 6 + x 11 * y 11,
      x 13 * y 13 - x 12 * y 12] := by
  ext l
  fin_cases l <;> norm_num [product, rows, Fin.sum_univ_succ] <;> ring

set_option maxHeartbeats 2000000 in
-- Normalize every ordered pair in the fifteen-vector multiplication table.
private theorem product_table : ∀ i j : Fin 15,
    product (v i) (v j) = match output i j with | none => 0 | some k => v k := by
  intro i j
  rw [product_coordinates]
  fin_cases i <;> fin_cases j <;> norm_num [v, output]
  all_goals exact Subsingleton.elim _ _

set_option maxHeartbeats 2000000 in
-- Decide the finite implication for every triple of table indices.
private theorem weight_table : ∀ i j k : Fin 15,
    output i j = some k → weight i + weight j ≤ weight k := by decide

private theorem filtration_mul (r s : ℕ) (x y : A)
    (hx : x ∈ filtration r) (hy : y ∈ filtration s) : product x y ∈ filtration (r + s) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨i, hi, rfl⟩
    induction hy using Submodule.span_induction with
    | mem y hy =>
      rcases hy with ⟨j, hj, rfl⟩
      rw [product_table]
      cases h : output i j with
      | none => exact Submodule.zero_mem _
      | some k => exact v_mem k (by have := weight_table i j k h; omega)
    | zero => simp
    | add a b _ _ ha hb => simpa using (Submodule.add_mem _ ha hb)
    | smul a b _ hb => simpa using (Submodule.smul_mem _ a hb)
  | zero => simp
  | add a b _ _ ha hb => simpa using (Submodule.add_mem _ ha hb)
  | smul a b _ hb => simpa using (Submodule.smul_mem _ a hb)

private theorem power_upper (m : ℕ) : ordinaryPower product m ≤ filtration m :=
  power_le_filtration product filtration filtration_first filtration_mul m

private theorem filtration_256 : filtration 256 = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro x ⟨i, hi, rfl⟩
  have hw : weight i ≤ 255 := by fin_cases i <;> decide
  omega

private theorem power_256 : ordinaryPower product 256 = ⊥ := by
  apply le_antisymm _ bot_le
  rw [← filtration_256]
  exact power_upper 256


private theorem witness_step (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (i j k : Fin 15) (h : output i j = some k)
    (hx : v i ∈ ordinaryPower product a) (hy : v j ∈ ordinaryPower product b) :
    v k ∈ ordinaryPower product (a + b) := by
  have hh := mul_mem_power product a b ha hb hx hy
  rwa [product_table, h] at hh

private theorem witness_255 : v 14 ∈ ordinaryPower product 255 := by
  have h1 : v 0 ∈ ordinaryPower product 1 := by simp [ordinaryPower]
  have he3 : v 2 ∈ ordinaryPower product 1 := by simp [ordinaryPower]
  have h2 := witness_step 1 1 (by decide) (by decide) 0 0 1 (by decide) h1 h1
  have h3 := witness_step 2 1 (by decide) (by decide) 1 2 3 (by decide) h2 he3
  have h5 := witness_step 3 2 (by decide) (by decide) 3 1 5 (by decide) h3 h2
  have h10 := witness_step 5 5 (by decide) (by decide) 5 5 6 (by decide) h5 h5
  have h15 := witness_step 10 5 (by decide) (by decide) 6 5 8 (by decide) h10 h5
  have h30 := witness_step 15 15 (by decide) (by decide) 8 8 9 (by decide) h15 h15
  have h60 := witness_step 30 30 (by decide) (by decide) 9 9 10 (by decide) h30 h30
  have h120 := witness_step 60 60 (by decide) (by decide) 10 10 11 (by decide) h60 h60
  have h240 := witness_step 120 120 (by decide) (by decide) 11 11 12 (by decide) h120 h120
  exact witness_step 240 15 (by decide) (by decide) 12 8 14 (by decide) h240 h15

private theorem power_255_ne : ordinaryPower product 255 ≠ ⊥ := by
  intro h
  have hh := witness_255
  rw [h, Submodule.mem_bot] at hh
  have hz := congrFun hh 14
  norm_num [v] at hz

private theorem rational_instance : indexExists ℚ 15 255 := by
  refine ⟨A, inferInstance, inferInstance, inferInstance, product, ?_,
    product_evolution, power_256, power_255_ne⟩
  simp [A]

private theorem arithmetic_failure : ¬ predicted 15 255 := by
  rintro (⟨a, hk, ha⟩ | h)
  · have hb : a ≤ 14 := by omega
    interval_cases a <;> norm_num at hk
  · have hn : ¬ (2 ≤ (Nat.digits 2 255).count 1 ∧
        (Nat.log 2 255 : ℤ) + ((Nat.digits 2 255).count 1 : ℤ) ≤ (15 : ℤ) - 1) := by
      decide
    exact hn h

/-- The complete original universal equivalence is false. -/
theorem result : ¬ claim := by
  intro h
  exact arithmetic_failure ((h ℚ 15 255 (by decide) (by decide)).mp rational_instance)

end D5.S3.QuadraticForms.EvolutionAlgebras.NilpotencySpectrumRefutation
