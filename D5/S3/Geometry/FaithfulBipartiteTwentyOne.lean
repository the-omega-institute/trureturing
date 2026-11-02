/- GID: D5/S3/Geometry/FaithfulBipartiteTwentyOne
   generality: G
   mirror-B: D5/B/S3/Geometry/FaithfulBipartiteTwentyOne
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Geometry/FiveAnchorFaithfulPlacement, D5/S3/Geometry/LowDegreeFaithfulExtension]
   utility: none
   digest: Faithful realizations of finite bipartite graphs with at most twenty-one edges in real five-space. -/
module

public import D5.S3.Geometry.FiveAnchorFaithfulPlacement
import all D5.S3.Geometry.FiveAnchorFaithfulPlacement
public import D5.S3.Geometry.LowDegreeFaithfulExtension
import all D5.S3.Geometry.CosphericalUnitLocus

/-! Exceptional latitudes, followed by fixed-label low-degree restoration.
The final carrier includes every original isolated vertex. -/

noncomputable section
public section

open Set Metric
open scoped InnerProductSpace

namespace D5.S3.Geometry.FaithfulBipartiteTwentyOne

local notation "E₅" => EuclideanSpace ℝ (Fin 5)

open FiveAnchorFaithfulPlacement

private def equatorialProjection : E₅ →ₗ[ℝ] E₅ where
  toFun p := p - p 4 • EuclideanSpace.single 4 1
  map_add' p q := by simp only [PiLp.add_apply, add_smul]; module
  map_smul' t p := by simp only [PiLp.smul_apply, smul_eq_mul]; module

private theorem projection_latitude (p : E₅) (hp : p 4 = 0) (s t : ℝ) :
    equatorialProjection (s • p + EuclideanSpace.single 4 t) = s • p := by
  simp [equatorialProjection, hp, ← EuclideanSpace.single_smul]

/-- The two latitude signs retain every affine independence visible in the
uniform nonzero equatorial projection. The pole is checked against each
label, including every label outside the exceptional neighborhood. -/
private theorem latitude_anchors {α : Type*} [Fintype α] (H : Finset α) :
    ∃ x : α → E₅, Function.Injective x ∧
      (∀ a, ‖x a‖ = 1 / 4) ∧
      (∀ T : Finset α, T.card ≤ 5 → AffineIndepOn ℝ x (T : Set α)) ∧
      ∃ p : E₅, (1 / 4 : ℝ) < ‖p‖ ∧
        ∀ a, dist p (x a) = 1 ↔ a ∈ H := by
  classical
  obtain ⟨y, hyi, hyn, _, hyr, hyg⟩ := general_anchors (α := α) 4 (by norm_num) (by norm_num)
  have hy4 (a : α) : y a 4 = 0 := by
    obtain ⟨z, hz⟩ := hyr a
    rw [← hz]
    exact embed_last (by norm_num : 4 ≤ 4) z
  let s : ℝ := Real.sqrt 3 / 2
  have hs : s ≠ 0 := ne_of_gt (by dsimp [s]; positivity)
  have hs2 : s ^ 2 = 3 / 4 := by
    dsimp [s]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  let t : α → ℝ := fun a => if a ∈ H then 1 / 8 else -1 / 8
  let x : α → E₅ := fun a => s • y a + EuclideanSpace.single 4 (t a)
  have ht2 (a : α) : t a ^ 2 = 1 / 64 := by dsimp [t]; split <;> norm_num
  have hx4 (a : α) : x a 4 = t a := by simp [x, hy4]
  have hxnorm (a : α) : ‖x a‖ = 1 / 4 := by
    have hi : ⟪s • y a, EuclideanSpace.single 4 (t a)⟫_ℝ = 0 := by
      simp [EuclideanSpace.inner_single_right, hy4]
    have hh := norm_add_sq_real (s • y a) (EuclideanSpace.single 4 (t a))
    simp only [hi, mul_zero, add_zero, norm_smul, Real.norm_eq_abs,
      PiLp.norm_single, mul_pow, sq_abs, hyn, hs2, ht2] at hh
    change ‖x a‖ ^ 2 = _ at hh
    nlinarith [norm_nonneg (x a)]
  have hproj (a : α) : equatorialProjection (x a) = s • y a :=
    projection_latitude (y a) (hy4 a) s (t a)
  have hxgp (T : Finset α) (hT : T.card ≤ 5) : AffineIndepOn ℝ x (T : Set α) := by
    apply AffineIndepOn.of_comp equatorialProjection.toAffineMap
    have hi := (hyg T hT).map' (s • (LinearMap.id : E₅ →ₗ[ℝ] E₅)).toAffineMap
      (by intro u v h; exact (smul_right_injective _ hs) h)
    simpa only [Function.comp_def, LinearMap.toAffineMap_coe, LinearMap.smul_apply,
      LinearMap.id_apply, hproj] using hi
  have hxi : Function.Injective x := by
    intro a b hab
    apply hyi
    exact (smul_right_injective _ hs) (by simpa only [hproj] using congrArg equatorialProjection hab)
  let k : ℝ := (1 + Real.sqrt 61) / 8
  have hk2 : k ^ 2 - k / 4 = 15 / 16 := by
    dsimp [k]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 61)]
  have hk : 1 / 4 < k := by
    dsimp [k]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 61), Real.sqrt_nonneg 61]
  let p : E₅ := EuclideanSpace.single 4 k
  have hpn : ‖p‖ = k := by simp [p, PiLp.norm_single, abs_of_pos (by linarith : 0 < k)]
  have hdist (a : α) : dist p (x a) ^ 2 = k ^ 2 + 1 / 16 - 2 * k * t a := by
    rw [dist_eq_norm, norm_sub_sq_real, hpn, hxnorm]
    simp [p, EuclideanSpace.inner_single_left, hx4]
    <;> ring
  refine ⟨x, hxi, hxnorm, hxgp, p, by rw [hpn]; exact hk, fun a => ?_⟩
  by_cases ha : a ∈ H
  · have ht : t a = 1 / 8 := by simp [t, ha]
    constructor
    · intro _; exact ha
    · intro _
      have hh := hdist a
      rw [ht] at hh
      nlinarith [dist_nonneg (x := p) (y := x a)]
  · have ht : t a = -1 / 8 := by simp [t, ha]
    constructor
    · intro hd
      have hh := hdist a
      rw [ht, hd] at hh
      nlinarith
    · exact fun h => (ha h).elim

end D5.S3.Geometry.FaithfulBipartiteTwentyOne
