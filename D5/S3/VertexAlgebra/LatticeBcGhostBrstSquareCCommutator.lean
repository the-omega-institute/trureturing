/- GID: D5/S3/VertexAlgebra/LatticeBcGhostBrstSquareCCommutator
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/LatticeBcGhostBrstSquareCCommutator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cyclic ghost cancellation makes the actual BRST square commute with every c mode. -/

import D5.S3.VertexAlgebra.LatticeBcGhostBrstCAction
import Mathlib.Algebra.FiniteSupport.Basic

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.LatticeBcGhostBrstSquareCCommutator

open LatticeGeneratingFieldLocality LatticeBcGhostBrstCharge LatticeBcGhostBrstCAction
  BcGhostFockSupport BcGhostStressCurrent
open scoped BigOperators TensorProduct

noncomputable section

private theorem tensor_cc (D : LatticeData) (a b : ℤ) :
    C D a * C D b + C D b * C D a = 0 := by
  have h := congrArg (LinearMap.lTensorHom (Carrier D)) (c_c (K := ℂ) a b)
  simp only [map_add, map_zero, LinearMap.coe_lTensorHom, LinearMap.lTensor_mul] at h
  simpa only [C, LinearMap.lTensor_def] using h

private theorem cc_swap (D : LatticeData) (a b : ℤ) (psi : State D) :
    C D a (C D b psi) = -C D b (C D a psi) := by
  apply eq_neg_of_add_eq_zero_left
  have h := congrArg (fun operator : Module.End ℂ (State D) => operator psi)
    (tensor_cc D a b)
  simpa only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply] using h

private theorem c_upper (D : LatticeData) (psi : State D) :
    ∃ bound : ℤ, 1 ≤ bound ∧ ∀ q : ℤ, bound < q → C D q psi = 0 := by
  induction psi using TensorProduct.induction_on with
  | zero =>
      refine ⟨1, le_rfl, ?_⟩
      intro q _
      exact map_zero (C D q)
  | tmul matter ghost =>
      let bound : ℤ := (((occupied ghost).sup id : ℕ) : ℤ) + 4
      have hsup : (0 : ℤ) ≤ (((occupied ghost).sup id : ℕ) : ℤ) :=
        Int.natCast_nonneg _
      refine ⟨bound, by dsimp [bound]; omega, ?_⟩
      intro q hq
      have hbranch : ¬ q ≤ 1 := by dsimp [bound] at hq; omega
      have hnonneg : 0 ≤ q - 2 := by dsimp [bound] at hq; omega
      have hcast := Int.toNat_of_nonneg hnonneg
      have hsite : (occupied ghost).sup id < 2 * (q - 2).toNat := by
        dsimp [bound] at hq
        omega
      have hghost : c (K := ℂ) q ghost = 0 := by
        simp only [c, if_neg hbranch, annihilate_eq_zero_of_sup_lt ghost _ hsite]
      simp only [C, TensorProduct.map_tmul, LinearMap.id_apply, hghost,
        TensorProduct.tmul_zero]
  | add psi chi hpsi hchi =>
      obtain ⟨first, hfirst, hkillFirst⟩ := hpsi
      obtain ⟨second, hsecond, hkillSecond⟩ := hchi
      refine ⟨max first second, le_trans hfirst (le_max_left _ _), ?_⟩
      intro q hq
      have hqFirst : first < q := lt_of_le_of_lt (le_max_left _ _) hq
      have hqSecond : second < q := lt_of_le_of_lt (le_max_right _ _) hq
      simp only [map_add, hkillFirst q hqFirst, hkillSecond q hqSecond, add_zero]

private theorem pair_finite (D : LatticeData) (p : ℤ) (psi : State D) :
    Function.HasFiniteSupport (fun n : ℤ => (C D (-n) * C D (n + p)) psi) := by
  obtain ⟨bound, _, hupper⟩ := c_upper D psi
  apply (Set.finite_Icc (-bound) (bound - p)).subset
  intro n hn
  constructor
  · by_contra hlow
    have hhigh : bound < -n := by omega
    have hzero : C D (-n) (C D (n + p) psi) = 0 := by
      rw [cc_swap D (-n) (n + p) psi, hupper (-n) hhigh, map_zero, neg_zero]
    exact hn (by simpa only [Module.End.mul_apply] using hzero)
  · by_contra hhigh
    have hmode : bound < n + p := by omega
    exact hn (by simp only [Module.End.mul_apply, hupper (n + p) hmode, map_zero])

private theorem weight_finite {D : LatticeData} {index : Type*}
    {family : index → State D} (hfinite : Function.HasFiniteSupport family)
    (weight : index → ℂ) :
    Function.HasFiniteSupport (fun index => weight index • family index) := by
  apply hfinite.subset
  intro index hnonzero hzero
  exact hnonzero (by simp only [hzero, smul_zero])

private theorem V_row_finite (D : LatticeData) (p : ℤ) (psi : State D) :
    Function.HasFiniteSupport
      (fun n : ℤ => (2 * n + p : ℂ) • ((C D (-n) * C D (n + p)) psi)) :=
  weight_finite (pair_finite D p psi) (fun n => (2 * n + p : ℂ))

private def triple (D : LatticeData) (a b c : ℤ) (psi : State D) : State D :=
  C D a (C D b (C D c psi))

private theorem triple_cycle (D : LatticeData) (a b c : ℤ) (psi : State D) :
    triple D a b c psi = triple D b c a psi := by
  unfold triple
  rw [cc_swap D a b (C D c psi), cc_swap D a c psi]
  simp only [map_neg, neg_neg]

private theorem triple_zero_high (D : LatticeData) (psi : State D) (bound : ℤ)
    (hupper : ∀ q : ℤ, bound < q → C D q psi = 0) (a b c : ℤ)
    (hhigh : bound < a ∨ bound < b ∨ bound < c) : triple D a b c psi = 0 := by
  rcases hhigh with ha | hb | hc
  · rw [triple_cycle D a b c psi]
    simp only [triple, hupper a ha, map_zero]
  · rw [triple_cycle D a b c psi, triple_cycle D b c a psi]
    simp only [triple, hupper b hb, map_zero]
  · simp only [triple, hupper c hc, map_zero]

private def tripleRow (D : LatticeData) (p : ℤ) (psi : State D)
    (modes : ℤ × ℤ) : State D :=
  triple D modes.1 modes.2 (p - modes.1 - modes.2) psi

private theorem triple_finite (D : LatticeData) (p : ℤ) (psi : State D) :
    Function.HasFiniteSupport (tripleRow D p psi) := by
  classical
  obtain ⟨bound, _, hupper⟩ := c_upper D psi
  let interval := Finset.Icc (p - 2 * bound) bound
  let domain := (interval.product interval).filter
    (fun modes : ℤ × ℤ => p - modes.1 - modes.2 ∈ interval)
  apply domain.finite_toSet.subset
  rintro ⟨a, b⟩ hnonzero
  have hnohigh : ¬ (bound < a ∨ bound < b ∨ bound < p - a - b) := by
    intro hhigh
    exact hnonzero (triple_zero_high D psi bound hupper a b (p - a - b) hhigh)
  have ha : p - 2 * bound ≤ a ∧ a ≤ bound := by omega
  have hb : p - 2 * bound ≤ b ∧ b ≤ bound := by omega
  have hc : p - 2 * bound ≤ p - a - b ∧ p - a - b ≤ bound := by omega
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ha, Finset.mem_Icc.mpr hb⟩, Finset.mem_Icc.mpr hc⟩

private def rotate (p : ℤ) : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun modes := (modes.2, p - modes.1 - modes.2)
  invFun modes := (p - modes.1 - modes.2, modes.1)
  left_inv modes := by
    rcases modes with ⟨a, b⟩
    apply Prod.ext <;> dsimp <;> omega
  right_inv modes := by
    rcases modes with ⟨a, b⟩
    apply Prod.ext <;> dsimp <;> omega

private theorem row_rotate (D : LatticeData) (p : ℤ) (psi : State D)
    (modes : ℤ × ℤ) :
    tripleRow D p psi (rotate p modes) = tripleRow D p psi modes := by
  rcases modes with ⟨a, b⟩
  have hmode : p - b - (p - a - b) = a := by omega
  change triple D b (p - a - b) (p - b - (p - a - b)) psi =
    triple D a b (p - a - b) psi
  rw [hmode]
  exact (triple_cycle D a b (p - a - b) psi).symm

private def jacobiWeight (p : ℤ) (modes : ℤ × ℤ) : ℂ :=
  (2 * ((p - modes.1 - modes.2 : ℤ) : ℂ) - (p : ℂ)) *
    ((modes.2 : ℂ) - (modes.1 : ℂ))

private def jacobiTerm (D : LatticeData) (p : ℤ) (psi : State D)
    (modes : ℤ × ℤ) : State D :=
  jacobiWeight p modes • tripleRow D p psi modes

private theorem jacobi_finite (D : LatticeData) (p : ℤ) (psi : State D) :
    Function.HasFiniteSupport (jacobiTerm D p psi) :=
  weight_finite (triple_finite D p psi) (jacobiWeight p)

private theorem jacobi_balance (D : LatticeData) (p : ℤ) (psi : State D)
    (modes : ℤ × ℤ) :
    jacobiTerm D p psi modes + jacobiTerm D p psi (rotate p modes) +
      jacobiTerm D p psi (rotate p (rotate p modes)) = 0 := by
  have hcoefficient : jacobiWeight p modes + jacobiWeight p (rotate p modes) +
      jacobiWeight p (rotate p (rotate p modes)) = 0 := by
    rcases modes with ⟨a, b⟩
    dsimp [jacobiWeight, rotate]
    push_cast
    ring
  simp only [jacobiTerm, row_rotate, ← add_smul, hcoefficient, zero_smul]

private theorem jacobi_sum_zero (D : LatticeData) (p : ℤ) (psi : State D) :
    (∑ᶠ modes : ℤ × ℤ, jacobiTerm D p psi modes) = 0 := by
  have hfinite := jacobi_finite D p psi
  have hrotate := Function.HasFiniteSupport.fun_comp_of_injective
    (rotate p).injective hfinite
  have hrotateTwice := Function.HasFiniteSupport.fun_comp_of_injective
    (rotate p).injective hrotate
  have hsum : (∑ᶠ modes : ℤ × ℤ,
      (jacobiTerm D p psi modes + jacobiTerm D p psi (rotate p modes) +
        jacobiTerm D p psi (rotate p (rotate p modes)))) = 0 := by
    simp only [jacobi_balance, finsum_zero]
  have hsplit : (∑ᶠ modes : ℤ × ℤ,
      (jacobiTerm D p psi modes + jacobiTerm D p psi (rotate p modes) +
        jacobiTerm D p psi (rotate p (rotate p modes)))) =
      (∑ᶠ modes : ℤ × ℤ,
        (jacobiTerm D p psi modes + jacobiTerm D p psi (rotate p modes))) +
        (∑ᶠ modes : ℤ × ℤ, jacobiTerm D p psi (rotate p (rotate p modes))) := by
    simpa only [Pi.add_apply] using
      finsum_add_distrib (hfinite.add hrotate) hrotateTwice
  rw [hsplit, finsum_add_distrib hfinite hrotate] at hsum
  have hfirst : (∑ᶠ modes : ℤ × ℤ, jacobiTerm D p psi (rotate p modes)) =
      ∑ᶠ modes : ℤ × ℤ, jacobiTerm D p psi modes := finsum_comp_equiv (rotate p)
  have hsecond :
      (∑ᶠ modes : ℤ × ℤ, jacobiTerm D p psi (rotate p (rotate p modes))) =
      ∑ᶠ modes : ℤ × ℤ, jacobiTerm D p psi modes :=
    (finsum_comp_equiv (rotate p)
      (f := fun modes => jacobiTerm D p psi (rotate p modes))).trans hfirst
  rw [hfirst, hsecond] at hsum
  have hthree : (3 : ℂ) • (∑ᶠ modes : ℤ × ℤ, jacobiTerm D p psi modes) = 0 := by
    calc
      (3 : ℂ) • (∑ᶠ modes : ℤ × ℤ, jacobiTerm D p psi modes) =
          ((∑ᶠ modes : ℤ × ℤ, jacobiTerm D p psi modes) +
            (∑ᶠ modes : ℤ × ℤ, jacobiTerm D p psi modes)) +
            (∑ᶠ modes : ℤ × ℤ, jacobiTerm D p psi modes) := by module
      _ = 0 := hsum
  have hscalar : (3 : ℂ)⁻¹ * (3 : ℂ) = 1 := by norm_num
  have hcancel := congrArg (fun vector : State D => (3 : ℂ)⁻¹ • vector) hthree
  simpa only [smul_smul, hscalar, one_smul, smul_zero] using hcancel

private def leftIndex : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun indices := (-indices.2, indices.2 - indices.1)
  invFun modes := (-modes.1 - modes.2, -modes.1)
  left_inv indices := by
    rcases indices with ⟨n, k⟩
    apply Prod.ext <;> dsimp <;> omega
  right_inv modes := by
    rcases modes with ⟨a, b⟩
    apply Prod.ext <;> dsimp <;> omega

private def rightIndex : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun indices := (-indices.1, -indices.2)
  invFun modes := (-modes.1, -modes.2)
  left_inv indices := by simp
  right_inv modes := by simp

private def leftTerm (D : LatticeData) (p : ℤ) (psi : State D)
    (indices : ℤ × ℤ) : State D :=
  (2 * indices.1 + p : ℂ) • ((2 * indices.2 - indices.1 : ℂ) •
    triple D (-indices.2) (indices.2 - indices.1) (indices.1 + p) psi)

private def rightTerm (D : LatticeData) (p : ℤ) (psi : State D)
    (indices : ℤ × ℤ) : State D :=
  (2 * indices.1 + p : ℂ) • ((2 * indices.2 + (indices.1 + p) : ℂ) •
    triple D (-indices.1) (-indices.2) (indices.2 + (indices.1 + p)) psi)

private theorem left_term_eq (D : LatticeData) (p : ℤ) (psi : State D)
    (indices : ℤ × ℤ) :
    leftTerm D p psi indices = jacobiTerm D p psi (leftIndex indices) := by
  rcases indices with ⟨n, k⟩
  have hmode : p - (-k) - (k - n) = n + p := by omega
  change (2 * n + p : ℂ) • ((2 * k - n : ℂ) •
      triple D (-k) (k - n) (n + p) psi) =
    jacobiWeight p (-k, k - n) • triple D (-k) (k - n) (p - (-k) - (k - n)) psi
  rw [hmode, smul_smul]
  congr 1
  dsimp [jacobiWeight]
  push_cast
  ring

private theorem right_term_eq (D : LatticeData) (p : ℤ) (psi : State D)
    (indices : ℤ × ℤ) :
    rightTerm D p psi indices = -jacobiTerm D p psi (rotate p (rightIndex indices)) := by
  rw [jacobiTerm, row_rotate]
  rcases indices with ⟨n, k⟩
  have hmode : p - (-n) - (-k) = k + (n + p) := by omega
  have hweight : (2 * n + p : ℂ) * (2 * k + (n + p) : ℂ) =
      -jacobiWeight p (rotate p (-n, -k)) := by
    dsimp [jacobiWeight, rotate]
    push_cast
    ring
  change (2 * n + p : ℂ) • ((2 * k + (n + p) : ℂ) •
      triple D (-n) (-k) (k + (n + p)) psi) =
    -(jacobiWeight p (rotate p (-n, -k)) •
      triple D (-n) (-k) (p - (-n) - (-k)) psi)
  rw [hmode, smul_smul, hweight, neg_smul]

private theorem left_finite (D : LatticeData) (p : ℤ) (psi : State D) :
    Function.HasFiniteSupport (leftTerm D p psi) := by
  have hfinite := Function.HasFiniteSupport.fun_comp_of_injective
    leftIndex.injective (jacobi_finite D p psi)
  apply hfinite.subset
  intro indices hnonzero hzero
  change jacobiTerm D p psi (leftIndex indices) = 0 at hzero
  exact hnonzero (by rw [left_term_eq, hzero])

private theorem right_finite (D : LatticeData) (p : ℤ) (psi : State D) :
    Function.HasFiniteSupport (rightTerm D p psi) := by
  have hrotate := Function.HasFiniteSupport.fun_comp_of_injective
    (rotate p).injective (jacobi_finite D p psi)
  have hfinite := Function.HasFiniteSupport.fun_comp_of_injective
    rightIndex.injective hrotate
  apply hfinite.subset
  intro indices hnonzero hzero
  change jacobiTerm D p psi (rotate p (rightIndex indices)) = 0 at hzero
  exact hnonzero (by rw [right_term_eq, hzero, neg_zero])

private theorem left_sum_zero (D : LatticeData) (p : ℤ) (psi : State D) :
    (∑ᶠ indices : ℤ × ℤ, leftTerm D p psi indices) = 0 := by
  calc
    _ = ∑ᶠ indices : ℤ × ℤ, jacobiTerm D p psi (leftIndex indices) :=
      finsum_congr (left_term_eq D p psi)
    _ = ∑ᶠ modes : ℤ × ℤ, jacobiTerm D p psi modes := finsum_comp_equiv leftIndex
    _ = 0 := jacobi_sum_zero D p psi

private theorem right_sum_zero (D : LatticeData) (p : ℤ) (psi : State D) :
    (∑ᶠ indices : ℤ × ℤ, rightTerm D p psi indices) = 0 := by
  calc
    _ = ∑ᶠ indices : ℤ × ℤ, -jacobiTerm D p psi (rotate p (rightIndex indices)) :=
      finsum_congr (right_term_eq D p psi)
    _ = -(∑ᶠ indices : ℤ × ℤ, jacobiTerm D p psi (rotate p (rightIndex indices))) :=
      finsum_neg_distrib _
    _ = -(∑ᶠ modes : ℤ × ℤ, jacobiTerm D p psi (rotate p modes)) :=
      congrArg (fun vector : State D => -vector)
        (finsum_comp_equiv rightIndex
          (f := fun modes : ℤ × ℤ => jacobiTerm D p psi (rotate p modes)))
    _ = -(∑ᶠ modes : ℤ × ℤ, jacobiTerm D p psi modes) :=
      congrArg (fun vector : State D => -vector)
        (finsum_comp_equiv (rotate p) (f := jacobiTerm D p psi))
    _ = 0 := by rw [jacobi_sum_zero D p psi, neg_zero]

private theorem product_comm (D : LatticeData) (operator first second : Module.End ℂ (State D)) :
    operator * (first * second) - (first * second) * operator =
      (operator * first + first * operator) * second -
        first * (operator * second + second * operator) := by
  simp only [add_mul, mul_add, mul_assoc]
  abel

private theorem Q_pair (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (a b : ℤ) :
    Q D H * (C D a * C D b) - (C D a * C D b) * Q D H =
      -(2 : ℂ)⁻¹ • (V D a * C D b - C D a * V D b) := by
  rw [product_comm]
  simp only [c_action, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, ← smul_sub]

private theorem complete_row (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (p n : ℤ) (psi : State D) :
    Q D H ((2 * n + p : ℂ) • ((C D (-n) * C D (n + p)) psi)) -
      (2 * n + p : ℂ) • ((C D (-n) * C D (n + p)) (Q D H psi)) =
      -(2 : ℂ)⁻¹ • (∑ᶠ k : ℤ, (leftTerm D p psi (n, k) - rightTerm D p psi (n, k))) := by
  have hpoint := congrArg (fun operator : Module.End ℂ (State D) => operator psi)
    (Q_pair D H (-n) (n + p))
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    RingHom.id_apply] at hpoint
  have hleft : (2 * n + p : ℂ) • V D (-n) (C D (n + p) psi) =
      ∑ᶠ k : ℤ, leftTerm D p psi (n, k) := by
    simp only [V, LinearMap.coe_mk, AddHom.coe_mk]
    rw [smul_finsum' _ (V_row_finite D (-n) (C D (n + p) psi))]
    apply finsum_congr
    intro k
    simp only [leftTerm, triple, Module.End.mul_apply, sub_eq_add_neg, Int.cast_neg]
  have hright : (2 * n + p : ℂ) • C D (-n) (V D (n + p) psi) =
      ∑ᶠ k : ℤ, rightTerm D p psi (n, k) := by
    have hmap := (C D (-n)).toAddMonoidHom.map_finsum (V_row_finite D (n + p) psi)
    simp only [LinearMap.toAddMonoidHom_coe] at hmap
    simp only [V, LinearMap.coe_mk, AddHom.coe_mk]
    rw [hmap, smul_finsum' _
      ((V_row_finite D (n + p) psi).fun_comp (map_zero (C D (-n))))]
    apply finsum_congr
    intro k
    simp only [rightTerm, triple, Module.End.mul_apply, map_smul, RingHom.id_apply,
      Int.cast_add]
  have hinjective : Function.Injective (fun k : ℤ => (n, k)) := by
    intro first second hequal
    exact congrArg Prod.snd hequal
  have hleftFinite := Function.HasFiniteSupport.fun_comp_of_injective
    hinjective (left_finite D p psi)
  have hrightFinite := Function.HasFiniteSupport.fun_comp_of_injective
    hinjective (right_finite D p psi)
  simp only [map_smul, RingHom.id_apply, Module.End.mul_apply, ← smul_sub]
  rw [hpoint, smul_comm (2 * n + p : ℂ) (-(2 : ℂ)⁻¹)]
  congr 1
  rw [smul_sub, hleft, hright]
  exact (finsum_sub_distrib hleftFinite hrightFinite).symm

private theorem Q_V_commutator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (p : ℤ) :
    Q D H * V D p - V D p * Q D H = 0 := by
  apply LinearMap.ext
  intro psi
  have hrow := V_row_finite D p psi
  have hpost := hrow.fun_comp (map_zero (Q D H))
  have hQrow := V_row_finite D p (Q D H psi)
  have hmap := (Q D H).toAddMonoidHom.map_finsum hrow
  simp only [LinearMap.toAddMonoidHom_coe] at hmap
  have hleft := left_finite D p psi
  have hright := right_finite D p psi
  have hdifference : Function.HasFiniteSupport
      (fun indices : ℤ × ℤ => leftTerm D p psi indices - rightTerm D p psi indices) := by
    apply (hleft.union hright).subset
    intro indices hnonzero
    by_cases hzero : leftTerm D p psi indices = (0 : State D)
    · right
      intro hother
      exact hnonzero (by simp only [hzero, hother, sub_zero])
    · exact Or.inl hzero
  have hscaled := weight_finite hdifference (fun _ => -(2 : ℂ)⁻¹)
  change Q D H (∑ᶠ n : ℤ,
    (2 * n + p : ℂ) • ((C D (-n) * C D (n + p)) psi)) -
    (∑ᶠ n : ℤ, (2 * n + p : ℂ) • ((C D (-n) * C D (n + p)) (Q D H psi))) = 0
  rw [hmap, ← finsum_sub_distrib hpost hQrow]
  calc
    (∑ᶠ n : ℤ, (Q D H ((2 * n + p : ℂ) • ((C D (-n) * C D (n + p)) psi)) -
      (2 * n + p : ℂ) • ((C D (-n) * C D (n + p)) (Q D H psi)))) =
        ∑ᶠ n : ℤ, -(2 : ℂ)⁻¹ •
          (∑ᶠ k : ℤ, (leftTerm D p psi (n, k) - rightTerm D p psi (n, k))) :=
      finsum_congr (fun n => complete_row D H p n psi)
    _ = ∑ᶠ n : ℤ, ∑ᶠ k : ℤ,
        -(2 : ℂ)⁻¹ • (leftTerm D p psi (n, k) - rightTerm D p psi (n, k)) := by
      apply finsum_congr
      intro n
      have hinjective : Function.Injective (fun k : ℤ => (n, k)) := by
        intro first second hequal
        exact congrArg Prod.snd hequal
      exact smul_finsum' _
        (Function.HasFiniteSupport.fun_comp_of_injective hinjective hdifference)
    _ = ∑ᶠ indices : ℤ × ℤ,
        -(2 : ℂ)⁻¹ • (leftTerm D p psi indices - rightTerm D p psi indices) :=
      (finsum_curry _ hscaled).symm
    _ = -(2 : ℂ)⁻¹ • ((∑ᶠ indices : ℤ × ℤ, leftTerm D p psi indices) -
        (∑ᶠ indices : ℤ × ℤ, rightTerm D p psi indices)) := by
      calc
        _ = -(2 : ℂ)⁻¹ • (∑ᶠ indices : ℤ × ℤ,
            (leftTerm D p psi indices - rightTerm D p psi indices)) :=
          (smul_finsum' (-(2 : ℂ)⁻¹) hdifference).symm
        _ = _ := congrArg (fun vector : State D => -(2 : ℂ)⁻¹ • vector)
          (finsum_sub_distrib hleft hright)
    _ = 0 := by rw [left_sum_zero, right_sum_zero, sub_self, smul_zero]

theorem square_c_commutator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (p : ℤ) :
    (Q D H * Q D H) * C D p - C D p * (Q D H * Q D H) = 0 := by
  calc
    (Q D H * Q D H) * C D p - C D p * (Q D H * Q D H) =
        Q D H * (Q D H * C D p + C D p * Q D H) -
          (Q D H * C D p + C D p * Q D H) * Q D H := by
      simp only [mul_add, add_mul, mul_assoc]
      abel
    _ = -(2 : ℂ)⁻¹ • (Q D H * V D p - V D p * Q D H) := by
      simp only [c_action, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ← smul_sub]
    _ = 0 := by rw [Q_V_commutator, smul_zero]

#print axioms square_c_commutator

end

end D5.S3.VertexAlgebra.LatticeBcGhostBrstSquareCCommutator
