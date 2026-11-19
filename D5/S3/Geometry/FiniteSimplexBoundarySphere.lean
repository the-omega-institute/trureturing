/- GID: D5/S3/Geometry/FiniteSimplexBoundarySphere
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteSimplexBoundarySphere
   mirror-E: none(waiver:finite-simplex-boundary-sphere)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.PiL2, mathlib/module/Mathlib.Topology.Homeomorph.Lemmas]
   utility: none
   digest: Rational Psi on the literal finite simplex, its full-boundary quotient, the Euclidean unit sphere and the original supported coordinate realization. -/

import D5.S3.Geometry.FiniteConeCollapse
import D5.S3.Geometry.EuclideanSphereJoin
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Constructions
import Mathlib.Tactic

noncomputable section
open Set Finset Topology
open scoped BigOperators InnerProductSpace

namespace D5.S3.Geometry.FiniteSimplexBoundarySphere

abbrev E (Λ : Type*) := EuclideanSpace ℝ Λ
abbrev ObservedSimplex (Λ : Type*) [Fintype Λ] [DecidableEq Λ] :=
  ↥(FiniteConeCollapse.faceSimplex (Finset.univ : Finset Λ))

/-- The nonnegative, sum-one simplex in the actual Euclidean L2 space. -/
abbrev Simplex (Λ : Type*) [Fintype Λ] : Type _ :=
  {x : E Λ // (∀ i, 0 ≤ x i) ∧ (∑ i, x i) = 1}

def boundary {Λ : Type*} [Fintype Λ] (x : Simplex Λ) : Prop := ∃ i, x.1 i = 0

def boundaryRelation {Λ : Type*} [Fintype Λ] (x y : Simplex Λ) : Prop :=
  x = y ∨ (boundary x ∧ boundary y)

def boundarySetoid {Λ : Type*} [Fintype Λ] : Setoid (Simplex Λ) where
  r := boundaryRelation
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := by
      rintro x y (h | ⟨hx, hy⟩)
      · exact Or.inl h.symm
      · exact Or.inr ⟨hy, hx⟩
    trans := by
      rintro x y z (h | ⟨hx, hy⟩) hyz
      · exact h ▸ hyz
      · rcases hyz with h | ⟨_, hz⟩
        · exact Or.inr ⟨hx, h ▸ hy⟩
        · exact Or.inr ⟨hx, hz⟩ }

abbrev BoundaryQuotient (Λ : Type*) [Fintype Λ] :=
  Quotient (boundarySetoid (Λ := Λ))

variable {Λ : Type*} [Fintype Λ]

private def coordinateToEuclidean [DecidableEq Λ] (x : ObservedSimplex Λ) : Simplex Λ :=
  ⟨WithLp.toLp 2 x.1, x.2.1, x.2.2.1⟩

private def euclideanToCoordinate [DecidableEq Λ] (x : Simplex Λ) : ObservedSimplex Λ :=
  ⟨WithLp.ofLp x.1, x.2.1, x.2.2, fun i hi => (hi (Finset.mem_univ i)).elim⟩

/-- Only topology is transported here; no plain-function norm is used. -/
def coordinateBridge [DecidableEq Λ] : ObservedSimplex Λ ≃ₜ Simplex Λ where
  toFun := coordinateToEuclidean
  invFun := euclideanToCoordinate
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl
  continuous_toFun :=
    ((PiLp.continuous_toLp 2 (fun _ : Λ => ℝ)).comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((PiLp.continuous_ofLp 2 (fun _ : Λ => ℝ)).comp continuous_subtype_val).subtype_mk _

def cardR (Λ : Type*) [Fintype Λ] : ℝ := Fintype.card Λ

def barycenter (Λ : Type*) [Fintype Λ] : E Λ :=
  WithLp.toLp 2 (fun _ => (cardR Λ)⁻¹)

def pole (Λ : Type*) [Fintype Λ] : E Λ :=
  WithLp.toLp 2 (fun _ => (Real.sqrt (cardR Λ))⁻¹)

variable [Nonempty Λ]

theorem cardR_pos : 0 < cardR Λ := by
  change (0 : ℝ) < (Fintype.card Λ : ℝ)
  exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Λ)

theorem cardR_ne : cardR Λ ≠ 0 := (cardR_pos (Λ := Λ)).ne'

private def displacement (x : Simplex Λ) : E Λ := x.1 - barycenter Λ
def minCoord (x : Simplex Λ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => x.1 i)
def sigma (x : Simplex Λ) : ℝ := cardR Λ * minCoord x
private def displacementSq (x : Simplex Λ) : ℝ := ‖displacement x‖ ^ 2
def psiDenominator (x : Simplex Λ) : ℝ := sigma x ^ 2 + displacementSq x
private def psiNumerator (x : Simplex Λ) : E Λ :=
  (2 * sigma x) • displacement x + (sigma x ^ 2 - displacementSq x) • pole Λ

def psiRaw (x : Simplex Λ) : E Λ := (psiDenominator x)⁻¹ • psiNumerator x

theorem minCoord_attained (x : Simplex Λ) : ∃ i, x.1 i = minCoord x := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun i => x.1 i)
  exact ⟨i, hi.symm⟩

theorem minCoord_le (x : Simplex Λ) (i : Λ) : minCoord x ≤ x.1 i :=
  Finset.inf'_le _ (Finset.mem_univ i)

private theorem minCoord_nonneg (x : Simplex Λ) : 0 ≤ minCoord x :=
  Finset.le_inf' _ _ (fun i _ => x.2.1 i)

theorem sigma_nonneg (x : Simplex Λ) : 0 ≤ sigma x :=
  mul_nonneg (cardR_pos (Λ := Λ)).le (minCoord_nonneg x)

theorem sigma_eq_zero_iff (x : Simplex Λ) : sigma x = 0 ↔ boundary x := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := minCoord_attained x
    have hmin : minCoord x = 0 := (mul_eq_zero.mp h).resolve_left (cardR_ne (Λ := Λ))
    exact ⟨i, hi.trans hmin⟩
  · rintro ⟨i, hi⟩
    have hmin : minCoord x = 0 := le_antisymm (hi ▸ minCoord_le x i) (minCoord_nonneg x)
    simp [sigma, hmin]

private theorem barycenter_data :
    (∀ i : Λ, 0 ≤ barycenter Λ i) ∧ (∑ i, barycenter Λ i) = 1 := by
  constructor
  · intro i
    exact inv_nonneg.mpr (cardR_pos (Λ := Λ)).le
  · change (∑ _ : Λ, (cardR Λ)⁻¹) = 1
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (cardR_ne (Λ := Λ))

private theorem displacement_sum_zero (x : Simplex Λ) :
    (∑ i, displacement x i) = 0 := by
  simp only [displacement, PiLp.sub_apply, Finset.sum_sub_distrib,
    x.2.2, (barycenter_data (Λ := Λ)).2, sub_self]

private theorem pole_norm_sq : ‖pole Λ‖ ^ 2 = 1 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ _ : Λ, (Real.sqrt (cardR Λ))⁻¹ ^ 2) = 1
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc
    cardR Λ * (Real.sqrt (cardR Λ))⁻¹ ^ 2 =
        cardR Λ / (Real.sqrt (cardR Λ)) ^ 2 := by rw [div_eq_mul_inv, inv_pow]
    _ = 1 := by rw [Real.sq_sqrt (cardR_pos (Λ := Λ)).le]; exact div_self (cardR_ne (Λ := Λ))

private theorem pole_norm : ‖pole Λ‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  simpa only [one_pow] using pole_norm_sq (Λ := Λ)

omit [Nonempty Λ] in
private theorem inner_pole (v : E Λ) :
    ⟪v, pole Λ⟫_ℝ = (Real.sqrt (cardR Λ))⁻¹ * ∑ i, v i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, pole, ← Finset.mul_sum]

private theorem displacement_inner_pole (x : Simplex Λ) :
    ⟪displacement x, pole Λ⟫_ℝ = 0 := by
  rw [inner_pole, displacement_sum_zero, mul_zero]

omit [Nonempty Λ] in
private theorem norm_smul_sq (a : ℝ) (v : E Λ) : ‖a • v‖ ^ 2 = a ^ 2 * ‖v‖ ^ 2 := by
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

/-- Scalar completed square; the coordinate estimate supplies its second term. -/
private theorem denominator_scalar_bound {m s a : ℝ} (hm : 0 < m)
    (ha : (s - 1) ^ 2 ≤ m ^ 2 * a) : 1 / (m ^ 2 + 1) ≤ s ^ 2 + a := by
  have hm2 : 0 < m ^ 2 := sq_pos_of_pos hm
  have hd : 0 < m ^ 2 + 1 := by positivity
  have hres : 0 ≤ a - (s - 1) ^ 2 / m ^ 2 :=
    sub_nonneg.mpr ((div_le_iff₀ hm2).2 (by nlinarith [ha]))
  have hsq : 0 ≤ ((m ^ 2 + 1) * s - 1) ^ 2 / (m ^ 2 * (m ^ 2 + 1)) :=
    div_nonneg (sq_nonneg _) (mul_pos hm2 hd).le
  have hid : s ^ 2 + a - 1 / (m ^ 2 + 1) =
      ((m ^ 2 + 1) * s - 1) ^ 2 / (m ^ 2 * (m ^ 2 + 1)) +
        (a - (s - 1) ^ 2 / m ^ 2) := by
    field_simp [hm.ne', hd.ne']
    <;> ring
  linarith

/-- The stated uniform lower bound (in fact valid for every nonempty label type). -/
theorem psiDenominator_lower_bound (x : Simplex Λ) :
    1 / ((Fintype.card Λ : ℝ) ^ 2 + 1) ≤ psiDenominator x := by
  obtain ⟨j, hj⟩ := minCoord_attained x
  have hjz : cardR Λ * displacement x j = sigma x - 1 := by
    simp only [displacement, PiLp.sub_apply, barycenter, PiLp.toLp_apply, hj, sigma]
    field_simp [cardR_ne (Λ := Λ)]
    <;> ring
  have hc : (displacement x j) ^ 2 ≤ displacementSq x := by
    have h := PiLp.norm_apply_le (displacement x) j
    rw [Real.norm_eq_abs] at h
    have hsq := mul_self_le_mul_self (abs_nonneg (displacement x j)) h
    simpa only [← sq, sq_abs, displacementSq] using hsq
  apply denominator_scalar_bound (cardR_pos (Λ := Λ))
  have hmul := mul_le_mul_of_nonneg_left hc (sq_nonneg (cardR Λ))
  rw [← mul_pow, hjz] at hmul
  exact hmul

private theorem denominator_pos (x : Simplex Λ) : 0 < psiDenominator x :=
  lt_of_lt_of_le (by positivity) (psiDenominator_lower_bound x)

private theorem psiRaw_split (x : Simplex Λ) : psiRaw x =
    (2 * sigma x / psiDenominator x) • displacement x +
      ((sigma x ^ 2 - displacementSq x) / psiDenominator x) • pole Λ := by
  simp only [psiRaw, psiNumerator, smul_add, smul_smul, div_eq_mul_inv]
  congr 1 <;> congr 1 <;> ring

/-- The cross term vanishes in the L2 norm expansion. -/
theorem psiRaw_norm_sq (x : Simplex Λ) : ‖psiRaw x‖ ^ 2 = 1 := by
  have hD := (denominator_pos x).ne'
  have hn : ‖psiNumerator x‖ ^ 2 = psiDenominator x ^ 2 := by
    rw [psiNumerator, norm_add_sq_real, norm_smul_sq, norm_smul_sq,
      real_inner_smul_left, real_inner_smul_right, displacement_inner_pole, pole_norm_sq]
    dsimp [psiDenominator, displacementSq]
    ring
  rw [psiRaw, norm_smul_sq, hn]
  field_simp [hD]

abbrev Sphere (Λ : Type*) [Fintype Λ] := EuclideanSphereJoin.UnitSphere (E Λ)

def south : Sphere Λ := ⟨-pole Λ, mem_sphere_zero_iff_norm.mpr (by rw [norm_neg, pole_norm])⟩

def psi (x : Simplex Λ) : Sphere Λ :=
  ⟨psiRaw x, mem_sphere_zero_iff_norm.mpr (by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    simpa only [one_pow] using psiRaw_norm_sq x)⟩

theorem continuous_minCoord : Continuous (minCoord (Λ := Λ)) :=
  Continuous.finset_inf'_apply Finset.univ_nonempty (fun i _ =>
    (PiLp.continuous_apply 2 (fun _ : Λ => ℝ) i).comp continuous_subtype_val)

/-- Rational continuity uses nonvanishing already for cardinality one. -/
theorem continuous_psiRaw : Continuous (psiRaw (Λ := Λ)) := by
  have hz : Continuous (displacement (Λ := Λ)) := continuous_subtype_val.sub continuous_const
  have hs : Continuous (sigma (Λ := Λ)) := continuous_const.mul continuous_minCoord
  have ha : Continuous (displacementSq (Λ := Λ)) := hz.norm.pow 2
  have hD : Continuous (psiDenominator (Λ := Λ)) := (hs.pow 2).add ha
  exact (hD.inv₀ (fun x => (denominator_pos x).ne')).smul
    (((continuous_const.mul hs).smul hz).add (((hs.pow 2).sub ha).smul continuous_const))

private theorem continuous_psi : Continuous (psi (Λ := Λ)) :=
  continuous_psiRaw.subtype_mk _

/-- Every full-boundary representative has the same south image. -/
theorem psi_boundary {x : Simplex Λ} (hx : boundary x) :
    psi x = south := by
  have hs := (sigma_eq_zero_iff x).2 hx
  have ha : displacementSq x ≠ 0 := by
    have hpos := denominator_pos x
    simpa only [psiDenominator, hs, zero_pow (by decide : 2 ≠ 0), zero_add] using hpos.ne'
  apply Subtype.ext
  simp [psi, psiRaw, psiNumerator, psiDenominator, hs, south, smul_smul, ha]

private theorem psiRaw_inner_pole (x : Simplex Λ) :
    ⟪psiRaw x, pole Λ⟫_ℝ = (sigma x ^ 2 - displacementSq x) / psiDenominator x := by
  rw [psiRaw_split, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    displacement_inner_pole, real_inner_self_eq_norm_sq, pole_norm_sq]
  ring

private theorem psiRaw_one_add_inner (x : Simplex Λ) :
    1 + ⟪psiRaw x, pole Λ⟫_ℝ = 2 * sigma x ^ 2 / psiDenominator x := by
  rw [psiRaw_inner_pole]
  field_simp [(denominator_pos x).ne']
  dsimp [psiDenominator]
  ring

/-- The south converse detects exactly the vanishing minimum over face labels. -/
theorem psi_south_iff (x : Simplex Λ) :
    psi x = south ↔ boundary x := by
  constructor
  · intro h
    have hv : psiRaw x = -pole Λ := congrArg Subtype.val h
    have hc : (sigma x ^ 2 - displacementSq x) / psiDenominator x = -1 := by
      rw [← psiRaw_inner_pole, hv, inner_neg_left, real_inner_self_eq_norm_sq, pole_norm_sq]
    have he := (div_eq_iff (denominator_pos x).ne').mp hc
    have hs : sigma x = 0 := sq_eq_zero_iff.mp (by
      dsimp [psiDenominator] at he
      linarith)
    exact (sigma_eq_zero_iff x).1 hs
  · exact psi_boundary

private def maxNeg (v : E Λ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => -v i)

private theorem neg_coord_le_maxNeg (v : E Λ) (i : Λ) : -v i ≤ maxNeg v :=
  Finset.le_sup' (fun j => -v j) (Finset.mem_univ i)

private theorem maxNeg_attained (v : E Λ) : ∃ i, -v i = maxNeg v := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => -v i)
  exact ⟨i, hi.symm⟩

private theorem maxNeg_nonneg {v : E Λ} (hv : ∑ i, v i = 0) : 0 ≤ maxNeg v := by
  by_contra h
  have hi : ∀ i, 0 < v i := fun i => by
    have := neg_coord_le_maxNeg v i
    linarith [lt_of_not_ge h]
  have hp : 0 < ∑ i, v i := Finset.sum_pos (fun i _ => hi i) Finset.univ_nonempty
  linarith

private theorem maxNeg_smul {a : ℝ} (ha : 0 ≤ a) (v : E Λ) :
    maxNeg (a • v) = a * maxNeg v := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    have := mul_le_mul_of_nonneg_left (neg_coord_le_maxNeg v i) ha
    change -(a * v i) ≤ a * maxNeg v
    linarith
  · obtain ⟨i, hi⟩ := maxNeg_attained v
    have := neg_coord_le_maxNeg (a • v) i
    change -(a * v i) ≤ maxNeg (a • v) at this
    rw [← hi]
    linarith

private theorem maxNeg_displacement (x : Simplex Λ) :
    maxNeg (displacement x) = (cardR Λ)⁻¹ - minCoord x := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    have := minCoord_le x i
    change -(x.1 i - (cardR Λ)⁻¹) ≤ (cardR Λ)⁻¹ - minCoord x
    linarith
  · obtain ⟨i, hi⟩ := minCoord_attained x
    have := neg_coord_le_maxNeg (displacement x) i
    simpa only [displacement, PiLp.sub_apply, barycenter, PiLp.toLp_apply, hi, neg_sub] using this

/-- Both components, divided by 1+alpha, recover the projective displacement. -/
private def recover (y : E Λ) : E Λ :=
  (1 + ⟪y, pole Λ⟫_ℝ)⁻¹ • (y - ⟪y, pole Λ⟫_ℝ • pole Λ)

private theorem recover_psi (x : Simplex Λ) (hs : sigma x ≠ 0) :
    recover (psiRaw x) = (sigma x)⁻¹ • displacement x := by
  have hD := (denominator_pos x).ne'
  have ht : psiRaw x - ⟪psiRaw x, pole Λ⟫_ℝ • pole Λ =
      (2 * sigma x / psiDenominator x) • displacement x := by
    rw [psiRaw_inner_pole, psiRaw_split]
    exact add_sub_cancel_right _ _
  rw [recover, ht, psiRaw_one_add_inner, smul_smul]
  congr 1
  field_simp [hD, hs]
  <;> ring

/-- The finite minimum fixes the remaining scale, rather than the pole alone. -/
private theorem gauge_reconstruction (x : Simplex Λ) (hs : sigma x ≠ 0) :
    sigma x * (1 + cardR Λ * maxNeg ((sigma x)⁻¹ • displacement x)) = 1 := by
  rw [maxNeg_smul (inv_nonneg.mpr (sigma_nonneg x)), maxNeg_displacement]
  field_simp [hs, cardR_ne (Λ := Λ)]
  dsimp [sigma]
  ring

private theorem interior_injective {x y : Simplex Λ} (hxy : psiRaw x = psiRaw y)
    (hx : sigma x ≠ 0) (hy : sigma y ≠ 0) : x = y := by
  have hw : (sigma x)⁻¹ • displacement x = (sigma y)⁻¹ • displacement y := by
    rw [← recover_psi x hx, ← recover_psi y hy, hxy]
  have hscale := gauge_reconstruction x hx
  have hscale' := gauge_reconstruction y hy
  rw [hw] at hscale
  have hF : 1 + cardR Λ * maxNeg ((sigma y)⁻¹ • displacement y) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hscale'
    exact zero_ne_one hscale'
  have hs : sigma x = sigma y := mul_right_cancel₀ hF (hscale.trans hscale'.symm)
  have hz : displacement x = displacement y := by
    rw [hs] at hw
    exact (smul_right_injective (E Λ) (inv_ne_zero hy)) hw
  apply Subtype.ext
  have he := congrArg (fun v : E Λ => v + barycenter Λ) hz
  simpa only [displacement, sub_add_cancel] using he

/-- Equality of outputs is exactly equality or the full-boundary relation. -/
theorem psi_eq_iff (x y : Simplex Λ) :
    psi x = psi y ↔ boundaryRelation x y := by
  constructor
  · intro h
    by_cases hx : boundary x
    · right
      exact ⟨hx, (psi_south_iff y).1 (h.symm.trans (psi_boundary hx))⟩
    · left
      have hy : ¬ boundary y := fun hy => hx ((psi_south_iff x).1 (h.trans (psi_boundary hy)))
      exact interior_injective (congrArg Subtype.val h)
        (fun hs => hx ((sigma_eq_zero_iff x).1 hs))
        (fun hs => hy ((sigma_eq_zero_iff y).1 hs))
  · rintro (h | ⟨hx, hy⟩)
    · exact congrArg (psi) h
    · exact (psi_boundary hx).trans (psi_boundary hy).symm

private def alpha (y : E Λ) : ℝ := ⟪y, pole Λ⟫_ℝ
private def tangent (y : E Λ) : E Λ := y - alpha y • pole Λ
private def kappa (y : E Λ) : ℝ := 1 + alpha y + cardR Λ * maxNeg (tangent y)

private theorem tangent_inner (y : E Λ) : ⟪tangent y, pole Λ⟫_ℝ = 0 := by
  simp only [tangent, inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, pole_norm_sq, mul_one, alpha, sub_self]

private theorem tangent_sum (y : E Λ) : (∑ i, tangent y i) = 0 := by
  have h := tangent_inner y
  rw [inner_pole] at h
  have hc : Real.sqrt (cardR Λ) ≠ 0 := (Real.sqrt_pos.mpr (cardR_pos (Λ := Λ))).ne'
  exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero hc)

private theorem tangent_norm_sq (y : Sphere Λ) : ‖tangent y.1‖ ^ 2 = 1 - alpha y.1 ^ 2 := by
  have hy : ‖y.1‖ = 1 := mem_sphere_zero_iff_norm.mp y.2
  rw [tangent, norm_sub_sq_real, norm_smul_sq, real_inner_smul_right, pole_norm_sq, hy]
  dsimp [alpha]
  ring

private theorem alpha_gt_neg_one (y : Sphere Λ) (hy : y.1 ≠ -pole Λ) : -1 < alpha y.1 := by
  have hsq : 0 ≤ 1 - alpha y.1 ^ 2 := by rw [← tangent_norm_sq y]; positivity
  have habs : |alpha y.1| ≤ 1 :=
    (sq_le_one_iff_abs_le_one _).mp (by linarith)
  have hle : -1 ≤ alpha y.1 := (abs_le.mp habs).1
  apply lt_of_le_of_ne hle
  intro he
  have hnorm : ‖y.1 + pole Λ‖ ^ 2 = 0 := by
    rw [norm_add_sq_real, mem_sphere_zero_iff_norm.mp y.2, pole_norm_sq]
    change 1 ^ 2 + 2 * alpha y.1 + 1 = 0
    rw [← he]
    norm_num
  have hz : y.1 + pole Λ = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  exact hy (eq_neg_iff_add_eq_zero.mpr hz)

private theorem kappa_pos (y : Sphere Λ) (hy : y.1 ≠ -pole Λ) : 0 < kappa y.1 := by
  have hM := maxNeg_nonneg (tangent_sum y.1)
  have hm := cardR_pos (Λ := Λ)
  have ha := alpha_gt_neg_one y hy
  dsimp [kappa]
  nlinarith [mul_nonneg hm.le hM]

private def inverseRaw (y : E Λ) : E Λ := barycenter Λ + (kappa y)⁻¹ • tangent y

private theorem inverseRaw_sum (y : E Λ) : (∑ i, inverseRaw y i) = 1 := by
  simp only [inverseRaw, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum, tangent_sum,
    (barycenter_data (Λ := Λ)).2, mul_zero, add_zero]

private theorem inverseRaw_coordinate (y : Sphere Λ) (hy : y.1 ≠ -pole Λ) (i : Λ) :
    inverseRaw y.1 i = (1 + alpha y.1) / (cardR Λ * kappa y.1) +
      (tangent y.1 i + maxNeg (tangent y.1)) / kappa y.1 := by
  change (cardR Λ)⁻¹ + (kappa y.1)⁻¹ * tangent y.1 i = _
  field_simp [cardR_ne (Λ := Λ), (kappa_pos y hy).ne']
  dsimp [kappa]
  ring

private theorem inverseRaw_lower (y : Sphere Λ) (hy : y.1 ≠ -pole Λ) (i : Λ) :
    (1 + alpha y.1) / (cardR Λ * kappa y.1) ≤ inverseRaw y.1 i := by
  rw [inverseRaw_coordinate y hy]
  have hc : 0 ≤ tangent y.1 i + maxNeg (tangent y.1) := by
    linarith [neg_coord_le_maxNeg (tangent y.1) i]
  exact le_add_of_nonneg_right (div_nonneg hc (kappa_pos y hy).le)

private theorem inverseRaw_positive (y : Sphere Λ) (hy : y.1 ≠ -pole Λ) (i : Λ) :
    0 < inverseRaw y.1 i :=
  lt_of_lt_of_le (div_pos (by linarith [alpha_gt_neg_one y hy])
    (mul_pos (cardR_pos (Λ := Λ)) (kappa_pos y hy))) (inverseRaw_lower y hy i)

/-- The explicit rational inverse away from south, including at north. -/
def nonSouthInverse (y : Sphere Λ) (hy : y.1 ≠ -pole Λ) : Simplex Λ :=
  ⟨inverseRaw y.1, (fun i => (inverseRaw_positive y hy i).le), inverseRaw_sum y.1⟩

private theorem inverse_minCoord (y : Sphere Λ) (hy : y.1 ≠ -pole Λ) :
    minCoord (nonSouthInverse y hy) = (1 + alpha y.1) / (cardR Λ * kappa y.1) := by
  apply le_antisymm
  · obtain ⟨i, hi⟩ := maxNeg_attained (tangent y.1)
    have he : (nonSouthInverse y hy).1 i = (1 + alpha y.1) / (cardR Λ * kappa y.1) := by
      change inverseRaw y.1 i = _
      rw [inverseRaw_coordinate y hy, ← hi]
      simp
    exact he ▸ minCoord_le (nonSouthInverse y hy) i
  · exact Finset.le_inf' _ _ (fun i _ => inverseRaw_lower y hy i)

private theorem inverse_sigma (y : Sphere Λ) (hy : y.1 ≠ -pole Λ) :
    sigma (nonSouthInverse y hy) = (1 + alpha y.1) / kappa y.1 := by
  rw [sigma, inverse_minCoord]
  field_simp [cardR_ne (Λ := Λ), (kappa_pos y hy).ne']
  <;> ring

private theorem inverse_displacement (y : Sphere Λ) (hy : y.1 ≠ -pole Λ) :
    displacement (nonSouthInverse y hy) = (kappa y.1)⁻¹ • tangent y.1 := by
  change barycenter Λ + (kappa y.1)⁻¹ • tangent y.1 - barycenter Λ = _
  abel

private theorem inverse_displacementSq (y : Sphere Λ) (hy : y.1 ≠ -pole Λ) :
    displacementSq (nonSouthInverse y hy) = (1 - alpha y.1 ^ 2) / kappa y.1 ^ 2 := by
  rw [displacementSq, inverse_displacement, norm_smul_sq, tangent_norm_sq]
  simp only [div_eq_mul_inv, inv_pow]
  ring

private theorem inverse_denominator (y : Sphere Λ) (hy : y.1 ≠ -pole Λ) :
    psiDenominator (nonSouthInverse y hy) = 2 * (1 + alpha y.1) / kappa y.1 ^ 2 := by
  rw [psiDenominator, inverse_sigma, inverse_displacementSq]
  field_simp [(kappa_pos y hy).ne']
  <;> ring

/-- Substitution verifies both coefficients of the explicit non-south inverse. -/
theorem psi_nonSouthInverse
    (y : Sphere Λ) (hy : y.1 ≠ -pole Λ) : psi (nonSouthInverse y hy) = y := by
  have hk := (kappa_pos y hy).ne'
  have ha : 1 + alpha y.1 ≠ 0 := ne_of_gt (by linarith [alpha_gt_neg_one y hy])
  have ht : (2 * ((1 + alpha y.1) / kappa y.1) /
      (2 * (1 + alpha y.1) / kappa y.1 ^ 2)) * (kappa y.1)⁻¹ = 1 := by
    field_simp [hk, ha]
    <;> ring
  have hp : (((1 + alpha y.1) / kappa y.1) ^ 2 -
      (1 - alpha y.1 ^ 2) / kappa y.1 ^ 2) /
      (2 * (1 + alpha y.1) / kappa y.1 ^ 2) = alpha y.1 := by
    field_simp [hk, ha]
    <;> ring
  apply Subtype.ext
  change psiRaw (nonSouthInverse y hy) = y.1
  rw [psiRaw_split, inverse_sigma, inverse_displacementSq, inverse_denominator,
    inverse_displacement, smul_smul, ht, hp, one_smul]
  exact sub_add_cancel _ _

def vertex (i : Λ) : Simplex Λ := by
  classical
  exact ⟨WithLp.toLp 2 (Pi.single i (1 : ℝ)), by
    constructor
    · intro j; simp only [PiLp.toLp_apply, Pi.single_apply]; split_ifs <;> norm_num
    · simp⟩

omit [Nonempty Λ] in
theorem vertex_boundary (hm : 2 ≤ Fintype.card Λ) (i : Λ) : boundary (vertex i) := by
  classical
  have hn : 1 < Fintype.card Λ := by omega
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card hn i
  exact ⟨j, by simp [vertex, Pi.single_apply, hj, Ne.symm hj]⟩

/-- South uses a different vertex coordinate as its actual zero witness. -/
theorem psi_surjective (hm : 2 ≤ Fintype.card Λ) : Function.Surjective (psi (Λ := Λ)) := by
  intro y
  by_cases hy : y.1 = -pole Λ
  · have hey : y = south := Subtype.ext hy
    exact ⟨vertex (Classical.choice ‹Nonempty Λ›),
      (psi_boundary (vertex_boundary hm _)).trans hey.symm⟩
  · exact ⟨nonSouthInverse y hy, psi_nonSouthInverse y hy⟩

/-- Native quotient descent through the full boundary relation. -/
def psiQuotientMap : BoundaryQuotient Λ → Sphere Λ :=
  Quotient.lift (psi) (fun x y h => (psi_eq_iff x y).2 h)

private theorem continuous_psiQuotientMap :
    Continuous (psiQuotientMap (Λ := Λ)) :=
  (continuous_psi).quotient_lift _

omit [Nonempty Λ] in
private theorem compact_observedSimplex [DecidableEq Λ] : IsCompact
    (FiniteConeCollapse.faceSimplex (Finset.univ : Finset Λ)) := by
  rw [FiniteConeCollapse.faceSimplex_eq_convexHull]
  exact (Finset.univ.finite_toSet.image _).isCompact_convexHull ℝ

private def compactSimplex : CompactSpace (Simplex Λ) := by
  classical
  letI : CompactSpace (ObservedSimplex Λ) := isCompact_iff_compactSpace.mp compact_observedSimplex
  exact Function.Surjective.compactSpace (coordinateBridge (Λ := Λ)).continuous
    (coordinateBridge (Λ := Λ)).surjective

/-- Compactness is proved from the existing finite convex hull, before the
    quotient map is upgraded to a homeomorphism. This includes inverse continuity
    at the single collapsed boundary class. -/
def simplexBoundaryHomeomorph (hm : 2 ≤ Fintype.card Λ) : BoundaryQuotient Λ ≃ₜ Sphere Λ := by
  letI : CompactSpace (Simplex Λ) := compactSimplex
  have hb : Function.Bijective (psiQuotientMap (Λ := Λ)) := by
    constructor
    · intro p q
      refine Quotient.inductionOn₂ p q ?_
      intro x y hxy
      exact Quotient.sound ((psi_eq_iff x y).1 hxy)
    · intro y
      obtain ⟨x, hx⟩ := psi_surjective hm y
      exact ⟨Quotient.mk _ x, hx⟩
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (psiQuotientMap (Λ := Λ)) hb) (continuous_psiQuotientMap)

/-- Retain the isometry structure throughout sphere restriction. -/
private def reindexLinear (e : Λ ≃ Fin ((Fintype.card Λ - 1) + 1)) :
    E Λ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin ((Fintype.card Λ - 1) + 1)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e

def reindexSphere (e : Λ ≃ Fin ((Fintype.card Λ - 1) + 1)) :
    Sphere Λ ≃ₜ EuclideanSphereJoin.StdSphere (Fintype.card Λ - 1) where
  toFun x := ⟨reindexLinear e x.1, mem_sphere_zero_iff_norm.mpr (by
    rw [(reindexLinear e).norm_map, mem_sphere_zero_iff_norm.mp x.2])⟩
  invFun y := ⟨(reindexLinear e).symm y.1, mem_sphere_zero_iff_norm.mpr (by
    rw [(reindexLinear e).symm.norm_map, mem_sphere_zero_iff_norm.mp y.2])⟩
  left_inv x := Subtype.ext ((reindexLinear e).symm_apply_apply x.1)
  right_inv y := Subtype.ext ((reindexLinear e).apply_symm_apply y.1)
  continuous_toFun := ((reindexLinear e).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((reindexLinear e).symm.continuous.comp continuous_subtype_val).subtype_mk _

/-- The exact coordinate equivalence chosen for the existing StdSphere. -/
def stdIndex (hm : 2 ≤ Fintype.card Λ) : Λ ≃ Fin ((Fintype.card Λ - 1) + 1) :=
  (Fintype.equivFin Λ).trans (finCongr (by omega))

/-- The actual existing StdSphere endpoint, not merely an index existence claim. -/
def simplexBoundaryStdSphere (hm : 2 ≤ Fintype.card Λ) :
    BoundaryQuotient Λ ≃ₜ EuclideanSphereJoin.StdSphere (Fintype.card Λ - 1) :=
  (simplexBoundaryHomeomorph hm).trans (reindexSphere (stdIndex hm))

/-! The remaining constructions keep the original ambient ground and its ghosts.
    No extremum or boundary witness below ranges over an off-face coordinate. -/

abbrev FaceIndex (G : Type*) [Fintype G] [DecidableEq G] (face : Finset G) := {g // g ∈ face}

section Ambient
variable {G : Type*} [Fintype G] [DecidableEq G] (face : Finset G)

abbrev AmbientFace := ↥(FiniteConeCollapse.faceSimplex face)

def zeroExtend (v : E (FaceIndex G face)) : E G :=
  WithLp.toLp 2 (fun g => if hg : g ∈ face then v ⟨g, hg⟩ else 0)

theorem zeroExtend_apply_ghost (v : E (FaceIndex G face)) (g : G) (hg : g ∉ face) :
    zeroExtend face v g = 0 := by simp [zeroExtend, hg]

private theorem sum_supported (f : FaceIndex G face → ℝ) :
    (∑ g : G, if hg : g ∈ face then f ⟨g, hg⟩ else 0) = ∑ i, f i := by
  simpa only [Finset.attach_eq_univ] using (Finset.sum_attach_eq_sum_dite face f).symm

private theorem zeroExtend_sum (v : E (FaceIndex G face)) :
    (∑ g, zeroExtend face v g) = ∑ i, v i := sum_supported face _

private theorem restrict_sum (f : G → ℝ) (hf : ∀ g ∉ face, f g = 0) :
    (∑ i : FaceIndex G face, f i.1) = ∑ g, f g := by
  rw [← sum_supported face (fun i => f i.1)]
  apply Finset.sum_congr rfl
  intro g _
  by_cases hg : g ∈ face
  · simp [hg]
  · simp [hg, hf g hg]

private def extendFace (x : Simplex (FaceIndex G face)) : AmbientFace face :=
  ⟨WithLp.ofLp (zeroExtend face x.1), by
    refine ⟨?_, (zeroExtend_sum face x.1).trans x.2.2, ?_⟩
    · intro g
      by_cases hg : g ∈ face
      · simpa [zeroExtend, hg] using x.2.1 ⟨g, hg⟩
      · simp [zeroExtend, hg]
    · intro g hg
      exact zeroExtend_apply_ghost face x.1 g hg⟩

private def restrictFace (x : AmbientFace face) : Simplex (FaceIndex G face) :=
  ⟨WithLp.toLp 2 (fun i => x.1 i.1),
    (fun i => x.2.1 i.1), (restrict_sum face x.1 x.2.2.2).trans x.2.2.1⟩

/-- Zero extension and coordinate restriction are inverse homeomorphisms to the
    existing plain finite-product faceSimplex, including all ambient ghosts. -/
def faceCoordinateHomeomorph : Simplex (FaceIndex G face) ≃ₜ AmbientFace face where
  toFun := extendFace face
  invFun := restrictFace face
  left_inv x := by
    apply Subtype.ext
    ext i
    simp [extendFace, restrictFace, zeroExtend, i.2]
  right_inv x := by
    apply Subtype.ext
    funext g
    by_cases hg : g ∈ face
    · simp [extendFace, restrictFace, zeroExtend, hg]
    · simp [extendFace, restrictFace, zeroExtend, hg, x.2.2.2 g hg]
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro g
    by_cases hg : g ∈ face
    · change Continuous (fun x : Simplex (FaceIndex G face) =>
        if h : g ∈ face then x.1 ⟨g, h⟩ else 0)
      simp only [dif_pos hg]
      exact (PiLp.continuous_apply 2 (fun _ : FaceIndex G face => ℝ) ⟨g, hg⟩).comp
        continuous_subtype_val
    · change Continuous (fun x : Simplex (FaceIndex G face) =>
        if h : g ∈ face then x.1 ⟨g, h⟩ else 0)
      simp only [dif_neg hg]
      exact continuous_const
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (PiLp.continuous_toLp 2 (fun _ : FaceIndex G face => ℝ)).comp
      (continuous_pi (fun i => (continuous_apply i.1).comp continuous_subtype_val))

/-- Boundary of the ambient face, with witnesses restricted to the face itself. -/
def faceBoundary (x : AmbientFace face) : Prop := ∃ g, ∃ _ : g ∈ face, x.1 g = 0

theorem faceCoordinateHomeomorph_boundary (x : Simplex (FaceIndex G face)) :
    faceBoundary face (faceCoordinateHomeomorph face x) ↔ boundary x := by
  constructor
  · rintro ⟨g, hg, h⟩
    change zeroExtend face x.1 g = 0 at h
    exact ⟨⟨g, hg⟩, by simpa [zeroExtend, hg] using h⟩
  · rintro ⟨i, hi⟩
    refine ⟨i.1, i.2, ?_⟩
    change zeroExtend face x.1 i.1 = 0
    simpa [zeroExtend, i.2] using hi

/-- The ambient source quotient is literal equality or both face-boundary points. -/
def faceBoundarySetoid : Setoid (AmbientFace face) where
  r x y := x = y ∨ (faceBoundary face x ∧ faceBoundary face y)
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := by
      rintro x y (h | ⟨hx, hy⟩)
      · exact Or.inl h.symm
      · exact Or.inr ⟨hy, hx⟩
    trans := by
      rintro x y z (h | ⟨hx, hy⟩) hyz
      · exact h ▸ hyz
      · rcases hyz with h | ⟨_, hz⟩
        · exact Or.inr ⟨hx, h ▸ hy⟩
        · exact Or.inr ⟨hx, hz⟩ }

private theorem restriction_boundary (x : AmbientFace face) :
    boundary ((faceCoordinateHomeomorph face).symm x) ↔ faceBoundary face x := by
  have h := faceCoordinateHomeomorph_boundary face ((faceCoordinateHomeomorph face).symm x)
  rw [(faceCoordinateHomeomorph face).apply_symm_apply] at h
  exact h.symm

variable [Nonempty (FaceIndex G face)]

private def ambientPsi (x : AmbientFace face) :
    Sphere (FaceIndex G face) := psi ((faceCoordinateHomeomorph face).symm x)

private theorem ambientPsi_eq_iff
    (x y : AmbientFace face) :
    ambientPsi face x = ambientPsi face y ↔ (faceBoundarySetoid face).r x y := by
  rw [ambientPsi, ambientPsi, psi_eq_iff]
  change (_ = _ ∨ (_ ∧ _)) ↔ (x = y ∨ (_ ∧ _))
  rw [(faceCoordinateHomeomorph face).symm.injective.eq_iff,
    restriction_boundary, restriction_boundary]

private def ambientPsiQuotient :
    Quotient (faceBoundarySetoid face) → Sphere (FaceIndex G face) :=
  Quotient.lift (ambientPsi face) (fun x y h => (ambientPsi_eq_iff face x y).2 h)

/-- The same sphere bridge, starting from the original ambient face quotient. -/
def ambientBoundaryHomeomorph (hm : 2 ≤ Fintype.card (FaceIndex G face)) :
    Quotient (faceBoundarySetoid face) ≃ₜ Sphere (FaceIndex G face) := by
  letI : CompactSpace (AmbientFace face) := isCompact_iff_compactSpace.mp (by
    rw [FiniteConeCollapse.faceSimplex_eq_convexHull]
    exact (face.finite_toSet.image _).isCompact_convexHull ℝ)
  have hc : Continuous (ambientPsi face) :=
    (continuous_psi).comp (faceCoordinateHomeomorph face).symm.continuous
  have hb : Function.Bijective (ambientPsiQuotient face) := by
    constructor
    · intro p q
      refine Quotient.inductionOn₂ p q ?_
      intro x y h
      exact Quotient.sound ((ambientPsi_eq_iff face x y).1 h)
    · intro y
      obtain ⟨x, hx⟩ := psi_surjective hm y
      refine ⟨Quotient.mk _ (faceCoordinateHomeomorph face x), ?_⟩
      change psi ((faceCoordinateHomeomorph face).symm (faceCoordinateHomeomorph face x)) = y
      rw [(faceCoordinateHomeomorph face).symm_apply_apply, hx]
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (ambientPsiQuotient face) hb) (hc.quotient_lift _)

end Ambient
end D5.S3.Geometry.FiniteSimplexBoundarySphere
