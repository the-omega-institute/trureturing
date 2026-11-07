/- GID: D5/S3/Quantum/Analysis/CStarTriangleEqualityHereditary
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/CStarTriangleEqualityHereditary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Triangle-equality rigidity for complex C-star algebras. -/

/-
admission_basis: escape-witness
escape_witness: seminorm_cross_scale_of_continuous
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/27516
Declarations (definition rows carry no proof-shape claim):
scalar_local_cutoffs: proof_shape: bind-only; consumers: exists_close_selfadjoint_with_local_identity.
exists_close_selfadjoint_with_local_identity: proof_shape: bind-only; consumers: exists_joint_local_corner.
localIdentityCorner: definition; consumers: localIdentityCorner_inner, localIdentityCorner_isClosed, sandwich_mem_localIdentityCorner, seminorm_cross_scale_of_continuous, seminorm_local_corner_cross.
localIdentityCorner_isClosed: proof_shape: bind-only; consumers: seminorm_local_corner_cross.
localIdentityCorner_inner: proof_shape: bind-only; consumers: sandwich_mem_localIdentityCorner.
sandwich_mem_localIdentityCorner: proof_shape: bind-only; consumers: seminorm_cross_scale_of_continuous.
seminorm_algebraically_unital_rigidity: proof_shape: content; consumers: seminorm_local_corner_cross, D5.S3.Quantum.Analysis.CStarTriangleEqualityPreservers.seminorm_rigidity.
seminorm_local_corner_cross: proof_shape: content; consumers: seminorm_cross_scale_of_continuous.
norm_sandwich_sub_sandwich_le: proof_shape: bind-only; consumers: exists_joint_local_corner.
norm_sub_sandwich_lt: proof_shape: bind-only; consumers: exists_joint_local_corner.
exists_joint_local_corner: proof_shape: bind-only; consumers: seminorm_cross_scale_of_continuous.
seminorm_cross_scale_of_continuous: proof_shape: content; consumers: D5.S3.Quantum.Analysis.CStarTriangleEqualityPreservers.seminorm_rigidity.
-/

import D5.S3.Quantum.Analysis.CStarTriangleEqualityLocalUnitization
import D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane
import D5.S3.Quantum.Analysis.CStarTriangleEqualityUnital
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NoncommRing

namespace D5.S3.Quantum.Analysis.CStarTriangleEqualityHereditary

section

/-- Scalar clipping and its contractive local identity. -/
private theorem scalar_local_cutoffs (δ : ℝ) (hδ : 0 < δ) :
    ∃ e g : ℝ → ℝ, Continuous e ∧ Continuous g ∧ e 0 = 0 ∧ g 0 = 0 ∧
      (∀ t, 0 ≤ e t ∧ e t ≤ 1) ∧ (∀ t, e t * g t = g t) ∧
      (∀ t, ‖t - g t‖ ≤ δ) ∧ ∀ t, ‖g t‖ ≤ ‖t‖ := by
  let c : ℝ → ℝ := fun t => min (max t (-δ)) δ
  let g : ℝ → ℝ := fun t => t - c t
  let e : ℝ → ℝ := fun t => min (|t| / δ) 1
  have hc (t : ℝ) : -δ ≤ c t ∧ c t ≤ δ := by
    exact ⟨le_min (le_max_right _ _) (by linarith), min_le_right _ _⟩
  have hc0 : c 0 = 0 := by simp [c, hδ.le, neg_nonpos.mpr hδ.le]
  have hgm (t : ℝ) : |g t| ≤ |t| := by
    by_cases ht : t < -δ
    · have ht0 : t ≤ 0 := by linarith
      simp only [g, c, max_eq_right ht.le, min_eq_left (by linarith : -δ ≤ δ)]
      rw [abs_of_nonpos (by linarith), abs_of_nonpos ht0]
      linarith
    · by_cases ht' : δ < t
      · simp only [g, c, max_eq_left (by linarith : -δ ≤ t), min_eq_right ht'.le]
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith : 0 ≤ t)]
        linarith
      · have hct : c t = t := by
          dsimp only [c]
          rw [max_eq_left (le_of_not_gt ht), min_eq_left (le_of_not_gt ht')]
        simp only [g, hct, sub_self, abs_zero]
        exact abs_nonneg t
  refine ⟨e, g, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [e]
    fun_prop
  · dsimp [g, c]
    fun_prop
  · simp [e]
  · simp only [g, hc0, sub_self]
  · intro t
    exact ⟨le_min (div_nonneg (abs_nonneg t) hδ.le) (by norm_num), min_le_right _ _⟩
  · intro t
    by_cases ht : |t| ≤ δ
    · have hct : c t = t := by
        dsimp only [c]
        rw [max_eq_left (abs_le.mp ht).1, min_eq_left (abs_le.mp ht).2]
      simp [g, hct]
    · have hge : 1 ≤ |t| / δ := (le_div_iff₀ hδ).mpr (by linarith [lt_of_not_ge ht])
      simp only [e, min_eq_right hge, one_mul]
  · intro t
    have he : t - g t = c t := sub_sub_self t (c t)
    rw [he, Real.norm_eq_abs, abs_le]
    exact hc t
  · intro t
    simpa only [Real.norm_eq_abs] using hgm t

/-- Every selfadjoint element can be approximated by an element with a contractive local identity. -/
private theorem exists_close_selfadjoint_with_local_identity {A : Type*} [NonUnitalCStarAlgebra A]
    (d : A) (hd : IsSelfAdjoint d) (δ : ℝ) (hδ : 0 < δ) :
    ∃ e g : A, IsSelfAdjoint e ∧ IsSelfAdjoint g ∧ ‖e‖ ≤ 1 ∧
      e*g=g ∧ g*e=g ∧ ‖d-g‖ ≤ δ ∧ ‖g‖ ≤ ‖d‖ := by
  obtain ⟨E, G, hE, hG, hE0, hG0, hEb, hEG, hdiff, hGn⟩ := scalar_local_cutoffs δ hδ
  let e : A := cfcₙ E d
  let g : A := cfcₙ G d
  have he : IsSelfAdjoint e := cfcₙ_predicate E d
  have hg : IsSelfAdjoint g := cfcₙ_predicate G d
  have hen : ‖e‖ ≤ 1 := by
    apply norm_cfcₙ_le
    intro t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hEb t).1]
    exact (hEb t).2
  have heg : e*g=g := by
    change cfcₙ E d * cfcₙ G d = cfcₙ G d
    rw [← cfcₙ_mul E G d hE.continuousOn hE0 hG.continuousOn hG0]
    exact cfcₙ_congr fun t ht => hEG t
  have hge : g*e=g := by
    simpa only [star_mul, he.star_eq, hg.star_eq] using congrArg star heg
  have hdist : ‖d-g‖ ≤ δ := by
    have heq : cfcₙ (fun t => t-G t) d = d-g := by
      calc
        cfcₙ (fun t => t-G t) d = cfcₙ (id : ℝ → ℝ) d - cfcₙ G d :=
          cfcₙ_sub id G d continuous_id.continuousOn rfl hG.continuousOn hG0
        _ = d-g := by rw [cfcₙ_id ℝ d (ha := hd)]
    rw [← heq]
    exact norm_cfcₙ_le fun t ht => hdiff t
  have hgn : ‖g‖ ≤ ‖d‖ := by
    apply norm_cfcₙ_le
    intro t ht
    exact (hGn t).trans (NonUnitalIsometricContinuousFunctionalCalculus.norm_quasispectrum_le d ht hd)
  exact ⟨e, g, he, hg, hen, heg, hge, hdist, hgn⟩

end
section

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- The closed star subalgebra on which a selfadjoint element acts as a two-sided identity. -/
private def localIdentityCorner (e : A) (he : IsSelfAdjoint e) : NonUnitalStarSubalgebra ℂ A where
  carrier := {a | e * a = a ∧ a * e = a}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    exact ⟨by rw [mul_add, ha.1, hb.1], by rw [add_mul, ha.2, hb.2]⟩
  mul_mem' := by
    intro a b ha hb
    exact ⟨by rw [← mul_assoc, ha.1], by rw [mul_assoc, hb.2]⟩
  smul_mem' := by
    intro c a ha
    exact ⟨by rw [mul_smul_comm, ha.1], by rw [smul_mul_assoc, ha.2]⟩
  star_mem' := by
    intro a ha
    constructor
    · simpa only [star_mul, he.star_eq] using congrArg star ha.2
    · simpa only [star_mul, he.star_eq] using congrArg star ha.1

private instance localIdentityCorner_isClosed (e : A) (he : IsSelfAdjoint e) :
    IsClosed (localIdentityCorner e he : Set A) :=
  (isClosed_eq (continuous_const.mul continuous_id) continuous_id).inter
    (isClosed_eq (continuous_id.mul continuous_const) continuous_id)

/-- The local-identity corner is closed under ambient inner products. -/
private theorem localIdentityCorner_inner (e : A) (he : IsSelfAdjoint e)
    (x y : localIdentityCorner e he) (a : A) :
    (x : A) * a * (y : A) ∈ localIdentityCorner e he := by
  constructor
  · rw [← mul_assoc, ← mul_assoc, x.property.1]
  · rw [mul_assoc, y.property.2]

/-- Sandwiches supported by a local identity belong to its closed corner. -/
private theorem sandwich_mem_localIdentityCorner (e g a : A) (he : IsSelfAdjoint e)
    (heg : e * g = g) (hge : g * e = g) :
    g * a * g ∈ localIdentityCorner e he :=
  localIdentityCorner_inner e he ⟨g, heg, hge⟩ ⟨g, heg, hge⟩ a

/-- An algebraically unital C*-algebra satisfies the unital seminorm conclusion. -/
theorem seminorm_algebraically_unital_rigidity
    (hu : ∃ q : A, ∀ a : A, q * a = a ∧ a * q = a)
    (p : Seminorm ℂ A)
    (hp : ∀ a b : A, D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair a b → p (a+b) = p a + p b) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ a : A, p a = c * ‖a‖ := by
  classical
  letI : IsUnital A := ⟨hu⟩
  letI : CStarAlgebra A := IsUnital.toCStarAlgebra
  cases subsingleton_or_nontrivial A with
  | inl hs =>
    letI := hs
    exact ⟨0, le_rfl, fun a => by rw [Subsingleton.elim a 0]; simp⟩
  | inr hn =>
    letI := hn
    exact ⟨p 1, apply_nonneg p 1, D5.S3.Quantum.Analysis.CStarTriangleEqualityUnital.seminorm_unital_rigidity p hp⟩

/-- Every closed local-identity corner has one common seminorm scale. -/
private theorem seminorm_local_corner_cross (e : A) (he : IsSelfAdjoint e) (hen : ‖e‖ ≤ 1)
    (p : Seminorm ℂ A)
    (hp : ∀ a b : A, D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair a b → p (a+b) = p a + p b)
    (a b : localIdentityCorner e he) :
    p (a : A) * ‖(b : A)‖ = p (b : A) * ‖(a : A)‖ := by
  classical
  let S := localIdentityCorner e he
  let q : Seminorm ℂ S := p.comp S.toSubmodule.subtype
  have hq : ∀ a b : S, D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair a b → q (a+b) = q a + q b := by
    intro a b hab
    exact hp a b hab
  by_cases hu : ∃ u : S, ∀ a : S, u * a = a ∧ a * u = a
  · obtain ⟨c, hc, hscale⟩ := seminorm_algebraically_unital_rigidity hu q hq
    change q a * ‖b‖ = q b * ‖a‖
    rw [hscale, hscale]
    ring
  · have hscale (x : S) : p (x : A) = p e * ‖x‖ := by
      exact D5.S3.Quantum.Analysis.CStarTriangleEqualityLocalUnitization.local_unitization_seminorm_scale (NonUnitalStarSubalgebraClass.subtype S)
        Subtype.val_injective hu e hen (fun x => x.property.1)
        (fun r hr x => D5.S3.Quantum.Analysis.CStarTriangleEqualityUnital.seminorm_unital_rigidity r hr x) p hp x
    rw [hscale a, hscale b]
    change p e * ‖a‖ * ‖b‖ = p e * ‖b‖ * ‖a‖
    ring

end


section
open Filter
open scoped Topology
variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- Changing a contractive sandwiching element is uniformly controlled on each input. -/
private theorem norm_sandwich_sub_sandwich_le (f g a : A) (hf : ‖f‖ ≤ 1) (hg : ‖g‖ ≤ 1)
    (δ : ℝ) (hδ : ‖f-g‖ ≤ δ) :
    ‖g*a*g-f*a*f‖ ≤ 2*δ*‖a‖ := by
  have hδnonneg : 0 ≤ δ := (norm_nonneg (f-g)).trans hδ
  have hgf : ‖g-f‖ ≤ δ := by simpa only [norm_sub_rev] using hδ
  have heq : g*a*g-f*a*f = (g-f)*a*g + f*a*(g-f) := by
    simpa only [sub_mul, mul_sub] using
      (sub_add_sub_cancel (g*a*g) (f*a*g) (f*a*f)).symm
  calc
    ‖g*a*g-f*a*f‖ = ‖(g-f)*a*g + f*a*(g-f)‖ := congrArg norm heq
    _ ≤ ‖(g-f)*a*g‖ + ‖f*a*(g-f)‖ := norm_add_le _ _
    _ ≤ ‖g-f‖*‖a‖*‖g‖ + ‖f‖*‖a‖*‖g-f‖ := by
      exact add_le_add
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
    _ ≤ δ*‖a‖*1 + 1*‖a‖*δ := by gcongr
    _ = 2*δ*‖a‖ := by ring

/-- Left and right approximate identities give a simultaneous sandwich approximation. -/
private theorem norm_sub_sandwich_lt (f a : A) (hf : ‖f‖ ≤ 1) (η : ℝ)
    (haL : ‖a-f*a‖ < η) (haR : ‖a-a*f‖ < η) : ‖a-f*a*f‖ < 2*η := by
  have heq : a-f*a*f = (a-f*a)+f*(a-a*f) := by
    simpa only [mul_sub, ← mul_assoc] using
      (sub_add_sub_cancel a (f*a) (f*a*f)).symm
  calc
    ‖a-f*a*f‖ = ‖(a-f*a)+f*(a-a*f)‖ := congrArg norm heq
    _ ≤ ‖a-f*a‖ + ‖f*(a-a*f)‖ := norm_add_le _ _
    _ ≤ ‖a-f*a‖ + ‖f‖*‖a-a*f‖ := add_le_add (le_refl _) (norm_mul_le _ _)
    _ ≤ ‖a-f*a‖ + 1*‖a-a*f‖ := by gcongr
    _ < 2*η := by linarith

/-- Two elements can be approximated jointly inside a single closed local-identity corner. -/
private theorem exists_joint_local_corner (a b : A) (ε : ℝ) (hε : 0 < ε) :
    ∃ e g : A, IsSelfAdjoint e ∧ ‖e‖ ≤ 1 ∧ e*g=g ∧ g*e=g ∧
      ‖a-g*a*g‖ < ε ∧ ‖b-g*b*g‖ < ε := by
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let l := CStarAlgebra.approximateUnit A
  have hl := CStarAlgebra.increasingApproximateUnit A
  have hε4 : 0 < ε/4 := by positivity
  have hnear (x : A) : ∀ᶠ f in l, ‖x-f*x‖ < ε/4 ∧ ‖x-x*f‖ < ε/4 := by
    have hL := (hl.tendsto_mul_right x).eventually (Metric.ball_mem_nhds x hε4)
    have hR := (hl.tendsto_mul_left x).eventually (Metric.ball_mem_nhds x hε4)
    filter_upwards [hL, hR] with f hfL hfR
    exact ⟨by simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hfL,
      by simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hfR⟩
  obtain ⟨f, hfsa, hfn, hfa, hfb⟩ :=
    (hl.eventually_isSelfAdjoint.and (hl.eventually_norm.and ((hnear a).and (hnear b)))).exists
  let S : ℝ := ‖a‖+‖b‖+1
  have hS : 0 < S := by dsimp [S]; positivity
  let δ : ℝ := ε/(8*S)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hS)
  have hδS : 8*δ*S = ε := by dsimp [δ]; field_simp [hS.ne']
  obtain ⟨e, g, he, hg, hen, heg, hge, hfg, hgn⟩ :=
    exists_close_selfadjoint_with_local_identity f hfsa δ hδ
  have hgn1 : ‖g‖ ≤ 1 := hgn.trans hfn
  have happrox (x : A) (hx : ‖x‖ ≤ S)
      (hxL : ‖x-f*x‖ < ε/4) (hxR : ‖x-x*f‖ < ε/4) : ‖x-g*x*g‖ < ε := by
    have h1 := norm_sub_sandwich_lt f x hfn (ε/4) hxL hxR
    have h2 := norm_sandwich_sub_sandwich_le f g x hfn hgn1 δ hfg
    have h3 : 2*δ*‖x‖ ≤ ε/4 := by nlinarith [mul_le_mul_of_nonneg_left hx hδ.le]
    calc
      ‖x-g*x*g‖ ≤ ‖x-f*x*f‖ + ‖f*x*f-g*x*g‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖x-f*x*f‖ + ‖g*x*g-f*x*f‖ := by rw [norm_sub_rev (f*x*f) (g*x*g)]
      _ < ε := by linarith
  refine ⟨e, g, he, hen, heg, hge, ?_, ?_⟩
  · exact happrox a (by dsimp [S]; linarith [norm_nonneg b]) hfa.1 hfa.2
  · exact happrox b (by dsimp [S]; linarith [norm_nonneg a]) hfb.1 hfb.2

/-- Continuity passes the common-corner cross-scale identity to every pair. -/
theorem seminorm_cross_scale_of_continuous (p : Seminorm ℂ A) (hcont : Continuous p)
    (hp : ∀ a b : A, D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair a b → p (a+b) = p a + p b) (a b : A) :
    p a * ‖b‖ = p b * ‖a‖ := by
  let Z : Set (A × A) := {x | p x.1 * ‖x.2‖ = p x.2 * ‖x.1‖}
  have hZ : IsClosed Z := isClosed_eq
    ((hcont.comp continuous_fst).mul (continuous_snd.norm))
    ((hcont.comp continuous_snd).mul (continuous_fst.norm))
  change (a, b) ∈ Z
  rw [← hZ.closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨e, g, he, hen, heg, hge, ha, hb⟩ := exists_joint_local_corner a b ε hε
  let a' : localIdentityCorner e he := ⟨g*a*g, sandwich_mem_localIdentityCorner e g a he heg hge⟩
  let b' : localIdentityCorner e he := ⟨g*b*g, sandwich_mem_localIdentityCorner e g b he heg hge⟩
  refine ⟨((a' : A), (b' : A)), seminorm_local_corner_cross e he hen p hp a' b', ?_⟩
  rw [Prod.dist_eq, max_lt_iff]
  exact ⟨by simpa only [dist_eq_norm] using ha, by simpa only [dist_eq_norm] using hb⟩

end

end D5.S3.Quantum.Analysis.CStarTriangleEqualityHereditary
