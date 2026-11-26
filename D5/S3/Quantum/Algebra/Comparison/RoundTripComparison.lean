/- GID: D5/S3/Quantum/Algebra/Comparison/RoundTripComparison
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/Comparison/RoundTripComparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Faithful bounded duplication fixes exponential periods and a positive metric. -/


import D5.S3.Analytic.Dilation.DuplicationQuadraticGerm
import D5.S3.QuadraticForms.QuadraticGermInvariance
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Tactic


/-! The metric and exponential consequences of bounded faithful duplication. -/

namespace D5.S3.Quantum.Algebra.Comparison.RoundTripComparison

open Filter Asymptotics
open scoped Topology
noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
set_option backward.isDefEq.respectTransparency false

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [FiniteDimensional ℝ A]

local instance : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A

/-- The algebra exponential, regarded as a unit with its explicit inverse. -/
def expUnit (a : A) : Aˣ where
  val := NormedSpace.exp a
  inv := NormedSpace.exp (-a)
  val_inv := by
    rw [← NormedSpace.exp_add_of_commute (Commute.refl a).neg_right,
      add_neg_cancel, NormedSpace.exp_zero]
  inv_val := by
    rw [← NormedSpace.exp_add_of_commute (Commute.refl a).neg_left,
      neg_add_cancel, NormedSpace.exp_zero]

/-- The comparison hypotheses on a commutator-closed subspace and a group of units. -/
structure Data (L : LieSubalgebra ℝ A) (G : Subgroup Aˣ) where
  exp_mem : ∀ X : L, expUnit (X : A) ∈ G
  conj_mem : ∀ (g : G) (X : L), (g : Aˣ) * (X : A) * ↑((g : Aˣ)⁻¹) ∈ L
  phi : G → ℝ
  h : LinearMap.BilinForm ℝ L
  symmetric : h.IsSymm
  bounded : ∀ g, 0 ≤ phi g ∧ phi g ≤ 1
  faithful : ∀ g, phi g = 1 ↔ g = 1
  duplication : ∀ g, phi (g * g) = (2 * phi g - 1)^2
  conjugation : ∀ g k, phi (k * g * k⁻¹) = phi g
  expansion :
    (fun X : L => phi ⟨expUnit (X : A), exp_mem X⟩ - (1 - h X X / 2))
      =o[𝓝 0] (fun X : L => ‖X‖^2)

variable {L : LieSubalgebra ℝ A} {G : Subgroup Aˣ}

/-- Exponentiation into the given subgroup. -/
def Data.exp (D : Data L G) (X : L) : G := ⟨expUnit (X : A), D.exp_mem X⟩

private theorem exp_add (D : Data L G) (X Y : L)
    (hXY : Commute (X : A) (Y : A)) : D.exp (X + Y) = D.exp X * D.exp Y := by
  apply Subtype.ext
  apply Units.ext
  exact NormedSpace.exp_add_of_commute hXY

private theorem exp_double (D : Data L G) (t : ℝ) (X : L) :
    D.exp ((2*t) • X) = D.exp (t • X) * D.exp (t • X) := by
  rw [show (2*t) • X = t • X + t • X by module]
  exact exp_add D _ _ (Commute.refl _)

private theorem coefficient_nonneg {f : ℝ → ℝ} {q : ℝ}
    (hf : ∀ t, f t ≤ 1)
    (hg : (fun t => f t - (1 - q*t^2/2)) =o[𝓝 0] (fun t => t^2)) : 0 ≤ q := by
  by_contra hn
  have hq : q < 0 := lt_of_not_ge hn
  have he := hg.bound (show 0 < -q/4 by linarith)
  obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff.mp he
  have hb := hδbound (show dist (δ/2) 0 < δ by
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
    linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg (δ/2))] at hb
  have hnabs := neg_le_abs (f (δ/2) - (1 - q*(δ/2)^2/2))
  have hprod : q*(δ/2)^2 < 0 := mul_neg_of_neg_of_pos hq (sq_pos_of_pos (half_pos hδ))
  have hfone := hf (δ/2)
  nlinarith

private theorem ray_germ (D : Data L G) (X : L) :
    (fun t : ℝ => D.phi (D.exp (t • X)) - (1 - D.h X X*t^2/2))
      =o[𝓝 0] (fun t : ℝ => t^2) :=
  D5.S3.QuadraticForms.QuadraticGermInvariance.quadratic_germ_on_ray
    (fun Z => D.phi (D.exp Z)) D.h D.expansion X

private theorem diagonal_nonneg (D : Data L G) (X : L) : 0 ≤ D.h X X :=
  coefficient_nonneg (fun t => (D.bounded (D.exp (t • X))).2) (ray_germ D X)

private theorem cosine_on_ray (D : Data L G) (t : ℝ) (X : L) :
    D.phi (D.exp (t • X)) = Real.cos (t * Real.sqrt (D.h X X/2))^2 := by
  let f : ℝ → ℝ := fun s => 2*D.phi (D.exp (s • X))-1
  have hq := diagonal_nonneg D X
  have hs : (Real.sqrt (2*D.h X X))^2 = 2*D.h X X :=
    Real.sq_sqrt (by positivity)
  have hf : ∀ s, |f s| ≤ 1 := by
    intro s
    obtain ⟨hl, hu⟩ := D.bounded (D.exp (s • X))
    exact abs_le.mpr ⟨by dsimp [f]; linarith, by dsimp [f]; linarith⟩
  have hd : ∀ s, f (2*s) = 2*(f s)^2-1 := by
    intro s
    dsimp [f]
    rw [exp_double, D.duplication]
  have hg : (fun s => f s - (1 - ((Real.sqrt (2*D.h X X))^2/2)*s^2))
      =o[𝓝 0] (fun s : ℝ => s^2) := by
    have hh := (ray_germ D X).const_mul_left (2 : ℝ)
    refine hh.congr_left (fun s => ?_)
    dsimp [f]
    rw [hs]
    ring
  have he := D5.S3.Analytic.Dilation.DuplicationQuadraticGerm.eq_cos_of_quadratic_germ
    hf hd hg t
  have hroot : Real.sqrt (2*D.h X X) = 2*Real.sqrt (D.h X X/2) := by
    have hs' := Real.sq_sqrt (show 0 ≤ D.h X X/2 by positivity)
    have hn := Real.sqrt_nonneg (2*D.h X X)
    have hn' := Real.sqrt_nonneg (D.h X X/2)
    nlinarith
  rw [hroot, show 2*Real.sqrt (D.h X X/2)*t =
    2*(t*Real.sqrt (D.h X X/2)) by ring, Real.cos_two_mul] at he
  dsimp [f] at he
  linarith

private theorem diagonal_definite (D : Data L G) (X : L) (hX : D.h X X = 0) : X = 0 := by
  have he (t : ℝ) : NormedSpace.exp (t • (X : A)) = 1 := by
    have hp : D.phi (D.exp (t • X)) = 1 := by simp [cosine_on_ray, hX]
    have hg := (D.faithful _).mp hp
    exact congrArg (fun g : G => ((g : Aˣ) : A)) hg
  have hd := hasDerivAt_exp_smul_const (X : A) (0 : ℝ)
  have hf : (fun t : ℝ => NormedSpace.exp (t • (X : A))) = fun _ => (1 : A) :=
    funext he
  rw [hf] at hd
  have hz := hd.unique (hasDerivAt_const (0 : ℝ) (1 : A))
  apply Subtype.ext
  simpa using hz

private theorem period_iff (D : Data L G) (t : ℝ) (X : L) :
    D.exp (t • X) = 1 ↔ ∃ n : ℤ, t*Real.sqrt (D.h X X/2) = Real.pi*n := by
  rw [← D.faithful, cosine_on_ray]
  have hs := Real.sin_sq_add_cos_sq (t*Real.sqrt (D.h X X/2))
  have he : Real.cos (t*Real.sqrt (D.h X X/2))^2 = 1 ↔
      Real.sin (t*Real.sqrt (D.h X X/2)) = 0 := by
    constructor
    · intro h
      nlinarith [sq_nonneg (Real.sin (t*Real.sqrt (D.h X X/2)))]
    · intro h
      rw [h] at hs
      nlinarith
  rw [he, Real.sin_eq_zero_iff]
  constructor <;> rintro ⟨n, hn⟩ <;> exact ⟨n, by linarith⟩

private theorem ad_invariance (D : Data L G) (C X Y : L) :
    D.h ⁅C, X⁆ Y + D.h X ⁅C, Y⁆ = 0 := by
  let hmem (C : L) (t : ℝ) (X : L) :
      NormedSpace.exp (t • (C : A)) * (X : A) *
        NormedSpace.exp (-(t • (C : A))) ∈ L :=
    D.conj_mem (D.exp (t • C)) X
  apply D5.S3.QuadraticForms.QuadraticGermInvariance.ad_invariant_of_exp_conjugation
    L (fun Z => D.phi (D.exp Z)) D.h D.symmetric D.expansion hmem
  intro C t Z
  have he :
      D.exp ⟨NormedSpace.exp (t • (C : A)) * (Z : A) *
        NormedSpace.exp (-(t • (C : A))), hmem C t Z⟩ =
      D.exp (t • C) * D.exp Z * (D.exp (t • C))⁻¹ := by
    apply Subtype.ext
    apply Units.ext
    exact NormedSpace.exp_units_conj (expUnit (t • (C : A))) (Z : A)
  rw [he, D.conjugation]

/-- The comparison germ becomes a positive metric, fixes all exponential periods,
and is invariant under the infinitesimal conjugation action. -/
theorem metric_consequences (D : Data L G) :
    (∀ X : L, 0 ≤ D.h X X) ∧
    (∀ X : L, D.h X X = 0 → X = 0) ∧
    (∀ (t : ℝ) (X : L),
      D.phi (D.exp (t • X)) = Real.cos (t*Real.sqrt (D.h X X/2))^2) ∧
    (∀ (t : ℝ) (X : L),
      D.exp (t • X) = 1 ↔ ∃ n : ℤ, t*Real.sqrt (D.h X X/2) = Real.pi*n) ∧
    (∀ C X Y : L, D.h ⁅C, X⁆ Y + D.h X ⁅C, Y⁆ = 0) :=
  ⟨diagonal_nonneg D, diagonal_definite D, cosine_on_ray D, period_iff D, ad_invariance D⟩

end
end D5.S3.Quantum.Algebra.Comparison.RoundTripComparison
