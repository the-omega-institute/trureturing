/- GID: D5/S3/Matrix/QubitProductDistance
   generality: G
   mirror-B: none(waiver:covered-by-pure-gnsextension-sectors-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite qubit product-ray projections give norm-attaining local state tests. -/

import D5.S3.Matrix.QubitProductSectors

/-! Omega original.

Finite qubit product-ray projections give norm-attaining local state tests.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped InnerProductSpace BigOperators ComplexOrder
open Omega.Analysis.TailProducts

namespace Omega.QubitProduct

private def distanceRotationUnitary (r : Overlaps) (k : ℕ) : unitary (Matrix Bool Bool ℂ) :=
  ⟨rotation (r k), rotation_unitary (r k) (r k).2⟩

private def ray (r : Overlaps) (k : ℕ) : Matrix Bool Bool ℂ :=
  star (rotation (r k)) * vacuumMatrix * rotation (r k)

private theorem ray_star (r : Overlaps) (k : ℕ) : star (ray r k) = ray r k := by
  simp [ray, star_mul, mul_assoc]

private theorem ray_proj (r : Overlaps) (k : ℕ) : ray r k * ray r k = ray r k := by
  let U := rotation (r k)
  have h := (rotation_unitary (r k) (r k).2).2
  change (star U * vacuumMatrix * U) * (star U * vacuumMatrix * U) = _
  calc
    _ = star U * vacuumMatrix * (U * star U) * vacuumMatrix * U := by noncomm_ring
    _ = ray r k := by
      rw [show U * star U = 1 from h, mul_one,
        mul_assoc (star U) vacuumMatrix vacuumMatrix, vacuumMatrix_mul]
      rfl

private theorem conjugate_ray (r : Overlaps) (k : ℕ) :
    rotation (r k) * ray r k * star (rotation (r k)) = vacuumMatrix := by
  let U := rotation (r k)
  have h := (rotation_unitary (r k) (r k).2).2
  change U * (star U * vacuumMatrix * U) * star U = _
  calc
    _ = (U * star U) * vacuumMatrix * (U * star U) := by noncomm_ring
    _ = _ := by rw [show U * star U = 1 from h, one_mul, mul_one]

private theorem ray_entry (r : Overlaps) (k : ℕ) :
    ray r k false false = ((overlaps r k ^ 2 : ℝ) : ℂ) := by
  simp [ray, vacuumMatrix, rotation, Matrix.mul_apply, Matrix.star_apply, overlaps, pow_two]

private theorem vacuum_sandwich (M : Matrix Bool Bool ℂ) :
    vacuumMatrix * M * vacuumMatrix = M false false • vacuumMatrix := by
  ext i j
  cases i <;> cases j <;> simp [vacuumMatrix, Matrix.mul_apply]

private theorem ray_sandwich (r : Overlaps) (k : ℕ) :
    ray r k * vacuumMatrix * ray r k = ((overlaps r k ^ 2 : ℝ) : ℂ) • ray r k := by
  let U := rotation (r k)
  have hd := conjugate_vacuum_diag (r k : ℝ) false
  change (star U * vacuumMatrix * U) * vacuumMatrix * (star U * vacuumMatrix * U) = _
  calc
    _ = star U * (vacuumMatrix * (U * vacuumMatrix * star U) * vacuumMatrix) * U := by
      noncomm_ring
    _ = _ := by
      rw [vacuum_sandwich, hd]
      simp [ray, U, overlaps]

private def element (r : Overlaps) (k : ℕ) : Matrix Bool Bool ℂ →⋆ₐ[ℂ] pairAlgebra r where
  toFun := site r k
  map_one' := by
    apply Subtype.ext
    exact map_one ((siteRep k).prod ((siteRep k).comp
      (Unitary.conjStarAlgAut ℂ _ (distanceRotationUnitary r k)).toStarAlgHom))
  map_zero' := by
    apply Subtype.ext
    exact map_zero ((siteRep k).prod ((siteRep k).comp
      (Unitary.conjStarAlgAut ℂ _ (distanceRotationUnitary r k)).toStarAlgHom))
  map_mul' A B := by
    apply Subtype.ext
    exact map_mul ((siteRep k).prod ((siteRep k).comp
      (Unitary.conjStarAlgAut ℂ _ (distanceRotationUnitary r k)).toStarAlgHom)) A B
  map_add' A B := by
    apply Subtype.ext
    exact map_add ((siteRep k).prod ((siteRep k).comp
      (Unitary.conjStarAlgAut ℂ _ (distanceRotationUnitary r k)).toStarAlgHom)) A B
  commutes' z := by
    apply Subtype.ext
    exact AlgHom.commutes ((siteRep k).prod ((siteRep k).comp
      (Unitary.conjStarAlgAut ℂ _ (distanceRotationUnitary r k)).toStarAlgHom)).toAlgHom z
  map_star' A := by
    apply Subtype.ext
    exact map_star ((siteRep k).prod ((siteRep k).comp
      (Unitary.conjStarAlgAut ℂ _ (distanceRotationUnitary r k)).toStarAlgHom)) A

private theorem commute_element_block (r : Overlaps) {k s n : ℕ} (hk : s + n ≤ k)
    (A : Matrix Bool Bool ℂ) (M : ℕ → Matrix Bool Bool ℂ) :
    Commute (element r k A) (block (fun j => element r j (M j)) s n) := by
  change _ * _ = _ * _
  apply Subtype.ext
  apply Prod.ext
  · change firstRep r (_ * _) = firstRep r (_ * _)
    simp only [map_mul, map_block (firstRep r)]
    exact (localAction_commute_block (Or.inr hk) A M).eq
  · change secondRep r (_ * _) = secondRep r (_ * _)
    simp only [map_mul, map_block (secondRep r)]
    exact (localAction_commute_block (Or.inr hk) _ _).eq

private theorem element_block_mul (r : Overlaps) (A B : ℕ → Matrix Bool Bool ℂ) (s n : ℕ) :
    block (fun j => element r j (A j)) s n * block (fun j => element r j (B j)) s n =
      block (fun j => element r j (A j * B j)) s n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [block_succ, block_succ, block_succ, map_mul,
      ← (commute_element_block r le_rfl (B (s + n)) A).mul_mul_mul_comm, ih]

private theorem element_block_star (r : Overlaps) (A : ℕ → Matrix Bool Bool ℂ) (s n : ℕ)
    (hA : ∀ k, star (A k) = A k) :
    star (block (fun j => element r j (A j)) s n) = block (fun j => element r j (A j)) s n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [block_succ, star_mul, ih, ← map_star, hA]
    exact (commute_element_block r le_rfl (A (s + n)) A).eq.symm

private theorem element_block_smul (r : Overlaps) (c : ℕ → ℂ) (A : ℕ → Matrix Bool Bool ℂ)
    (s n : ℕ) :
    block (fun j => element r j (c j • A j)) s n =
      (∏ k ∈ Finset.range n, c (s + k)) • block (fun j => element r j (A j)) s n := by
  induction n with
  | zero => simp only [block_zero, Finset.range_zero, Finset.prod_empty, one_smul]
  | succ n ih =>
    rw [block_succ, block_succ, map_smul, ih, Finset.prod_range_succ, smul_mul_assoc,
      mul_smul_comm, smul_smul, mul_comm (c (s + n))]

private theorem tailPrefix_mem (r : Overlaps) (s n : ℕ) :
    tailPrefix (overlaps r) s n ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨tailPrefix_nonneg (overlaps r) (fun k => (r k).2) s n, ?_⟩
  exact Finset.prod_le_one₀ (fun k _ => (r (s + k)).2.1) (fun k _ => (r (s + k)).2.2)

private theorem difference_cube {A : Type*} [Ring A] [Algebra ℂ A] (P Q : A) (z : ℂ)
    (hp : P * P = P) (hq : Q * Q = Q) (hpq : P * Q * P = z • P)
    (hqp : Q * P * Q = z • Q) : (P - Q) ^ 3 = (1 - z) • (P - Q) := by
  have hs : (P - Q)^2 = P + Q - P * Q - Q * P := by
    rw [pow_two, sub_mul, mul_sub P, mul_sub Q, hp, hq]
    abel
  rw [show (3 : ℕ) = 2 + 1 by decide, pow_succ, hs]
  simp only [sub_mul, add_mul, mul_sub, hp, hq, hpq, hqp, sub_smul, one_smul, smul_sub,
    mul_assoc P Q Q, mul_assoc Q P P]
  abel

private theorem norm_projection_difference {A : Type*} [NormedRing A] [StarRing A]
    [CStarRing A] [NormedAlgebra ℂ A] (P Q : A) (p : ℝ)
    (hc : 0 ≤ 1 - p ^ 2) (hp : IsSelfAdjoint P) (hq : IsSelfAdjoint Q)
    (hp₂ : P * P = P) (hq₂ : Q * Q = Q)
    (hpq : P * Q * P = ((p ^ 2 : ℝ) : ℂ) • P)
    (hqp : Q * P * Q = ((p ^ 2 : ℝ) : ℂ) • Q) :
    ‖P - Q‖ ≤ Real.sqrt (1 - p ^ 2) := by
  let X := P - Q
  let c := 1 - p ^ 2
  have hXs : IsSelfAdjoint X := hp.sub hq
  have hXcube : X ^ 3 = (c : ℂ) • X := by
    simp only [X, c, Complex.ofReal_sub, Complex.ofReal_one]
    exact difference_cube P Q _ hp₂ hq₂ hpq hqp
  have hXquad : X ^ 4 = (c : ℂ) • X ^ 2 := by
    rw [show (4 : ℕ) = 3 + 1 by decide, pow_add, hXcube, pow_one, smul_mul_assoc, pow_two]
  have hnorm2 : ‖X ^ 2‖ = ‖X‖ ^ 2 := by simpa using hXs.norm_pow_two_pow 1
  have hnorm4 : ‖X ^ 4‖ = ‖X‖ ^ 4 := by simpa using hXs.norm_pow_two_pow 2
  have h := congrArg norm hXquad
  rw [hnorm4, norm_smul, hnorm2, Complex.norm_real, Real.norm_of_nonneg hc] at h
  change ‖X‖ ≤ Real.sqrt c
  by_cases h0 : ‖X‖ = 0
  · rw [h0]; exact Real.sqrt_nonneg c
  · have hn : ‖X‖ ^ 2 = c := mul_right_cancel₀ (pow_ne_zero 2 h0) (by nlinarith)
    exact (sq_le_sq₀ (norm_nonneg X) (Real.sqrt_nonneg c)).mp (by rw [hn, Real.sq_sqrt hc])

set_option maxHeartbeats 1800000 in
/-- A local contraction attains the ray distance at each finite cut. -/
theorem finite_distance_test (r : Overlaps) (n : ℕ) :
    ∃ a : pairAlgebra r, ‖a‖ ≤ 1 ∧
      ‖⟪basisVector ∅, firstRep r a (basisVector ∅)⟫_ℂ -
        ⟪basisVector ∅, secondRep r a (basisVector ∅)⟫_ℂ‖ =
        2 * Real.sqrt (1 - tailPrefix (overlaps r) 0 n ^ 2) := by
  let p := tailPrefix (overlaps r) 0 n
  let c := 1 - p ^ 2
  let Ω := basisVector ∅
  have hpm := tailPrefix_mem r 0 n
  have hc : 0 ≤ c := by
    dsimp [c, p]
    nlinarith [mul_nonneg hpm.1 (sub_nonneg.mpr hpm.2)]
  let P := block (fun k => element r k vacuumMatrix) 0 n
  let Q := block (fun k => element r k (ray r k)) 0 n
  have hPP : P * P = P := by simp [P, element_block_mul]
  have hQQ : Q * Q = Q := by simp [Q, element_block_mul, ray_proj]
  have hPQP : P * Q * P = ((p ^ 2 : ℝ) : ℂ) • P := by
    dsimp only [P, Q]
    simp only [element_block_mul, vacuum_sandwich, ray_entry, element_block_smul,
      ← Complex.ofReal_prod, Finset.prod_pow, p, tailPrefix]
    <;> rfl
  have hQPQ : Q * P * Q = ((p ^ 2 : ℝ) : ℂ) • Q := by
    dsimp only [P, Q]
    simp only [element_block_mul, ray_sandwich, element_block_smul,
      ← Complex.ofReal_prod, Finset.prod_pow, p, tailPrefix]
    <;> rfl
  let X := P - Q
  have hPstar : star (P : Operator × Operator) = (P : Operator × Operator) :=
    congrArg Subtype.val (element_block_star r _ _ _ (fun _ => vacuumMatrix_star))
  have hQstar : star (Q : Operator × Operator) = (Q : Operator × Operator) :=
    congrArg Subtype.val (element_block_star r _ _ _ (ray_star r))
  have hNx : ‖X‖ ≤ Real.sqrt c :=
    norm_projection_difference (P : Operator × Operator) (Q : Operator × Operator)
      p hc hPstar hQstar (congrArg Subtype.val hPP) (congrArg Subtype.val hQQ)
      (congrArg Subtype.val hPQP) (congrArg Subtype.val hQPQ)
  let f (a : pairAlgebra r) := ⟪Ω, firstRep r a Ω⟫_ℂ
  let g (a : pairAlgebra r) := ⟪Ω, secondRep r a Ω⟫_ℂ
  have hPf : f P = 1 := by
    change ⟪Ω, firstRep r (block (fun k => site r k vacuumMatrix) 0 n) Ω⟫_ℂ = _
    rw [first_vacuum_product]
    simp [vacuumMatrix]
  have hPg : g P = ((p ^ 2 : ℝ) : ℂ) := second_vacuum_projection_product r 0 n
  have hQf : f Q = ((p ^ 2 : ℝ) : ℂ) := by
    change ⟪Ω, firstRep r (block (fun k => site r k (ray r k)) 0 n) Ω⟫_ℂ = _
    rw [first_vacuum_product]
    simp [ray_entry, ← Complex.ofReal_prod, Finset.prod_pow, p, tailPrefix]
  have hQg : g Q = 1 := by
    change ⟪Ω, secondRep r (block (fun k => site r k (ray r k)) 0 n) Ω⟫_ℂ = _
    rw [second_vacuum_product]
    simp [conjugate_ray, vacuumMatrix]
  have hdiff : f X - g X = (2 * c : ℝ) := by
    dsimp [X, f, g]
    rw [map_sub (firstRep r) P Q, map_sub (secondRep r) P Q, sub_apply, sub_apply,
      inner_sub_right, inner_sub_right]
    change (f P - f Q) - (g P - g Q) = _
    rw [hPf, hPg, hQf, hQg]
    push_cast
    dsimp [c]
    simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow]
    ring
  by_cases hz : Real.sqrt c = 0
  · refine ⟨0, by simp, ?_⟩
    change ‖f 0 - g 0‖ = 2 * Real.sqrt c
    simp [hz, f, g]
  let b := (Real.sqrt c)⁻¹
  refine ⟨(b : ℂ) • X, ?_, ?_⟩
  · change ‖(b : ℂ) • (X : Operator × Operator)‖ ≤ 1
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg c))]
    exact (mul_le_mul_of_nonneg_left hNx (inv_nonneg.mpr (Real.sqrt_nonneg c))).trans_eq
      (inv_mul_cancel₀ hz)
  · change ‖f ((b : ℂ) • X) - g ((b : ℂ) • X)‖ = 2 * Real.sqrt c
    have hfg : f ((b : ℂ) • X) - g ((b : ℂ) • X) = (b : ℂ) * (f X - g X) := by
      dsimp only [f, g]
      rw [show firstRep r ((b : ℂ) • X) = (b : ℂ) • firstRep r X from
          (firstRep r).toLinearMap.map_smul _ _,
        show secondRep r ((b : ℂ) • X) = (b : ℂ) • secondRep r X from
          (secondRep r).toLinearMap.map_smul _ _,
        smul_apply, smul_apply, inner_smul_right, inner_smul_right]
      ring
    rw [hfg, hdiff, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    dsimp [b]
    field_simp
    nlinarith [Real.sq_sqrt hc]

end Omega.QubitProduct
