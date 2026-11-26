/- GID: D5/S3/Quantum/Foundation/FaceProjectionPurity
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/FaceProjectionPurity
   mirror-E: none(waiver:general-structural-mathematics)
   anchors: []
   utility: none
   digest: Full least confirmation forces purity of positive orthogonal face projections. -/

import D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
import Mathlib.Geometry.Convex.Cone.Face.Lattice
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
The cone, normalized base, extreme points and full proper-effect interval are those
of CircuitBalancedConfirmation. The symmetric positive definite pairing represents
the original least confirmers. Its self-duality and the positive orthogonal face
projection are explicit suppliers. No compatibility with the numerical values of
the ambient norm is imposed. All continuity uses the original finite dimensional
topology. Literature priority is not asserted.
-/

noncomputable section

namespace D5.S3.Quantum.Foundation.FaceProjectionPurity

open CircuitBalancedConfirmation

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A]

private theorem diagonal_continuous (B : A →ₗ[ℝ] A →ₗ[ℝ] ℝ) :
    Continuous (fun x => B x x) := by
  let T : A →ₗ[ℝ] A →L[ℝ] ℝ := LinearMap.toContinuousLinearMap.toLinearMap.comp B
  exact T.continuous_of_finiteDimensional.clm_apply continuous_id

private theorem pairing_bound {C : PointedCone ℝ A} {u : A →ₗ[ℝ] ℝ}
    (B : A →ₗ[ℝ] A →ₗ[ℝ] ℝ) (hsym : ∀ x y, B x y = B y x)
    (hK : IsCompact (base C u))
    (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hc : ∀ p : pure C u, confirms C u p (B p))
    {x y : A} (hx : x ∈ C) (hy : y ∈ C) : B x y ≤ u x * u y := by
  have hh := nonneg_on_cone (f := (u y) • u - B y) hK hu (fun p => ?_) x hx
  · simpa only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      hsym y x, sub_nonneg, mul_comm (u y)] using hh
  · simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, (pure_mem p).2,
      mul_one, sub_nonneg, hsym y p]
    exact ((hc p).1 y hy).2

private theorem pure_locus {C : PointedCone ℝ A} {u : A →ₗ[ℝ] ℝ}
    (B : A →ₗ[ℝ] A →ₗ[ℝ] ℝ) (hsym : ∀ x y, B x y = B y x)
    (hpos : ∀ x : A, x ≠ 0 → 0 < B x x)
    (hK : IsCompact (base C u))
    (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hc : ∀ p : pure C u, confirms C u p (B p)) :
    pure C u = {x | x ∈ base C u ∧ B x x = 1} := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.1, (hc ⟨x, hx⟩).2⟩
  · rintro ⟨hx, hxx⟩
    have hb (y : A) (hy : y ∈ base C u) : B y y ≤ 1 := by
      simpa only [hy.2, mul_one] using pairing_bound B hsym hK hu hc hy.1 hy.1
    have hxy (y : A) (hy : y ∈ base C u) : B x y ≤ 1 := by
      simpa only [hx.2, hy.2, mul_one] using pairing_bound B hsym hK hu hc hx.1 hy.1
    have heq (y : A) (hy : y ∈ base C u) (h : B x y = 1) : y = x := by
      apply sub_eq_zero.mp
      by_contra hne
      have hp := hpos (y - x) hne
      simp only [map_sub, LinearMap.sub_apply] at hp
      rw [hsym y x, h, hxx] at hp
      linarith [hb y hy]
    refine ⟨hx, ?_⟩
    intro y hy z hz hseg
    obtain ⟨a, b, ha, hb', hab, he⟩ := hseg
    have hv : a * B x y + b * B x z = 1 := by
      simpa only [map_add, map_smul, smul_eq_mul, hxx] using congrArg (B x) he
    have hxy1 : B x y = 1 := by
      have := hxy y hy
      have := hxy z hz
      nlinarith
    exact heq y hy hxy1

private theorem unit_representative (B : A →ₗ[ℝ] A →ₗ[ℝ] ℝ)
    (hpos : ∀ x : A, x ≠ 0 → 0 < B x x) (u : A →ₗ[ℝ] ℝ) :
    ∃ U : A, B U = u := by
  have hinj : Function.Injective B := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro x hx
    change x = 0
    by_contra hne
    have hh := hpos x hne
    have hz : B x = 0 := hx
    simp [hz] at hh
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [Subspace.dual_finrank_eq])).mp hinj u

omit [FiniteDimensional ℝ A] in
private theorem augmented_cauchy (B : A →ₗ[ℝ] A →ₗ[ℝ] ℝ)
    (hsym : ∀ x y, B x y = B y x) (hnon : ∀ x, 0 ≤ B x x)
    (a b : ℝ) (x y : A) :
    (a * b + B x y) ^ 2 ≤ (a ^ 2 + B x x) * (b ^ 2 + B y y) := by
  let : PreInnerProductSpace.Core ℝ (ℝ × A) := {
    inner := fun v w => v.1 * w.1 + B v.2 w.2
    conj_inner_symm := by intro v w; simp only [RCLike.conj_to_real]; rw [hsym]; ring
    re_inner_nonneg := fun v => by
      simpa only [RCLike.re_to_real, pow_two] using add_nonneg (sq_nonneg v.1) (hnon v.2)
    add_left := by intro v w z; simp only [Prod.fst_add, Prod.snd_add, map_add,
      LinearMap.add_apply]; ring
    smul_left := by intro v w r; simp only [Prod.smul_fst, Prod.smul_snd, map_smul,
      LinearMap.smul_apply, smul_eq_mul, RCLike.conj_to_real]; ring }
  have hh := InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℝ) (a, x) (b, y)
  change |a * b + B x y| * |b * a + B y x| ≤
    (a * a + B x x) * (b * b + B y y) at hh
  rw [hsym y x, mul_comm b a, abs_mul_abs_self] at hh
  simpa only [pow_two] using hh

/-- On the original full-effect carrier, least confirmation represented by a
self-dual positive definite pairing forces every positive orthogonal face
projection to send every original pure point to zero or an original pure ray.
The entire pure locus is characterized and proved compact and nonempty. -/
theorem least_confirmation_face_purity
    (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hne : ∃ x ∈ C, x ≠ (0 : A))
    (B : A →ₗ[ℝ] A →ₗ[ℝ] ℝ)
    (hsym : ∀ x y, B x y = B y x)
    (hpos : ∀ x : A, x ≠ 0 → 0 < B x x)
    (hdual : ∀ x, x ∈ C ↔ ∀ y ∈ C, 0 ≤ B x y)
    (hc : ∀ p : pure C u, confirms C u p (B p))
    (hleast : ∀ (p : pure C u) f, confirms C u p f → ∀ x ∈ C, B p x ≤ f x)
    (F : PointedCone.Face C) (Q : A →ₗ[ℝ] A)
    (hadj : ∀ x y, B (Q x) y = B x (Q y))
    (hface : ∀ x ∈ C, Q x ∈ F)
    (hfix : ∀ x ∈ F, Q x = x) :
    pure C u = {x | x ∈ base C u ∧ B x x = 1} ∧
      IsCompact (pure C u) ∧ (pure C u).Nonempty ∧
      ∀ p : pure C u, Q p = 0 ∨
        (0 < u (Q p) ∧ (u (Q p))⁻¹ • Q p ∈ pure C u ∧
          Q p = u (Q p) • ((u (Q p))⁻¹ • Q p)) := by
  have hclosed : IsClosed (C : Set A) := by
    have hset : (C : Set A) = ⋂ y ∈ C, {x | 0 ≤ B x y} := by
      ext x
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      exact hdual x
    rw [hset]
    exact isClosed_biInter fun y _ =>
      isClosed_le continuous_const (B.flip y).continuous_of_finiteDimensional
  have hid (x : A) : Q (Q x) = Q x := by
    apply sub_eq_zero.mp
    have hzero (y : A) (hy : y ∈ C) : B (Q (Q x) - Q x) y = 0 := by
      rw [map_sub, LinearMap.sub_apply, hadj (Q x) y, hadj x (Q y), hadj x y,
        hfix (Q y) (hface y hy), sub_self]
    have hv : Q (Q x) - Q x ∈ C := (hdual _).mpr fun y hy => (hzero y hy).ge
    by_contra hv0
    have hp := hpos (Q (Q x) - Q x) hv0
    linarith [hzero _ hv]
  have hK := base_compact hclosed hu
  have hlocus := pure_locus B hsym hpos hK hu hc
  have hPcompact : IsCompact (pure C u) := by
    rw [hlocus]
    exact hK.inter_right (isClosed_eq (diagonal_continuous B) continuous_const)
  have hPne : (pure C u).Nonempty := by
    obtain ⟨x, hx, hx0⟩ := hne
    exact hK.extremePoints_nonempty ⟨_, normalized_mem hu hx hx0⟩
  have hnon (x : A) : 0 ≤ B x x := by
    by_cases hx : x = 0
    · simp [hx]
    · exact (hpos x hx).le
  obtain ⟨U, hU⟩ := unit_representative B hpos u
  have horder {x : A} (hx : x ∈ C) : u x • U - x ∈ C := by
    apply (hdual _).mpr
    intro y hy
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, hU]
    exact sub_nonneg.mpr (pairing_bound B hsym hK hu hc hx hy)
  let I : A → ℝ := fun x => (u x) ^ 2 - B x x
  have hI {x : A} (hx : x ∈ C) : 0 ≤ I x := by
    have hh := pairing_bound B hsym hK hu hc hx hx
    dsimp [I]
    nlinarith
  have hIpure (r : pure C u) : I r = 0 := by
    simp only [I, (pure_mem r).2, (hc r).2, one_pow, sub_self]
  have hIcont : Continuous (fun r => I (Q r)) := by
    exact ((u.continuous_of_finiteDimensional.pow 2).sub (diagonal_continuous B)).comp
      Q.continuous_of_finiteDimensional
  obtain ⟨p, hp, hmax⟩ := hPcompact.exists_isMaxOn hPne hIcont.continuousOn
  let d := I (Q p)
  have hd : 0 ≤ d := hI (F.isFaceOf.le (hface p hp.1.1))
  have hden : 0 < 1 + d := by linarith
  have hproj (x y : A) : B (Q x) (Q y) = B (Q x) y := by
    rw [← hadj, hid]
  have hUQ (r : A) : B (Q U) r = u (Q r) := by rw [hadj, hU]
  let z := Q p
  let a := u z
  let g := a • Q U - z
  have hgF : g ∈ F := by
    have hh := hface _ (horder (F.isFaceOf.le (hface p hp.1.1)))
    simpa only [map_sub, map_smul, hid] using hh
  have hgC : g ∈ C := F.isFaceOf.le hgF
  have hgp : B g p = d := by
    dsimp [g, a, z, d, I]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, hUQ, ← hproj p p, pow_two]
  have hpp : B p p = 1 := (hc ⟨p, hp⟩).2
  have hcross (r : A) :
      a * u (Q r) + B (p - Q p) (r - Q r) = B (p + g) r := by
    dsimp [g, z]
    simp only [map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, hUQ]
    rw [← hadj p r, hproj p r]
    ring
  have hlength (r : pure C u) :
      (u (Q r)) ^ 2 + B ((r : A) - Q r) ((r : A) - Q r) = 1 + I (Q r) := by
    simp only [I, map_sub, LinearMap.sub_apply]
    rw [(hc r).2, ← hadj (r : A) (r : A), hproj (r : A) (r : A)]
    ring
  have hpurebound (r : pure C u) : 0 ≤ B (p + g) r ∧ B (p + g) r ≤ 1 + d := by
    have hlow : 0 ≤ B (p + g) r :=
      (hdual _).mp (C.add_mem hp.1.1 hgC) r (pure_mem r).1
    have hcs := augmented_cauchy B hsym hnon a (u (Q r)) (p - Q p) ((r : A) - Q r)
    rw [hcross, show a ^ 2 + B (p - Q p) (p - Q p) = 1 + d from
      hlength ⟨p, hp⟩, hlength r] at hcs
    have hm : I (Q r) ≤ d := hmax r.property
    have hh := mul_le_mul_of_nonneg_left (show 1 + I (Q r) ≤ 1 + d by linarith) hden.le
    refine ⟨hlow, ?_⟩
    nlinarith
  let f : A →ₗ[ℝ] ℝ := (1 + d)⁻¹ • B (p + g)
  have hf : confirms C u p f := by
    refine ⟨cone_bound hK hu (fun r => ?_), ?_⟩
    · change 0 ≤ (1 + d)⁻¹ * B (p + g) r ∧ (1 + d)⁻¹ * B (p + g) r ≤ 1
      exact ⟨mul_nonneg (inv_nonneg.mpr hden.le) (hpurebound r).1,
        by simpa only [← div_eq_inv_mul] using
          (div_le_one hden).mpr (hpurebound r).2⟩
    · change (1 + d)⁻¹ * B (p + g) p = 1
      simp only [map_add, LinearMap.add_apply, hpp, hgp, inv_mul_cancel₀ hden.ne']
  have hres : g - d • p ∈ C := by
    apply (hdual _).mpr
    intro x hx
    have hh := hleast ⟨p, hp⟩ f hf x hx
    change B p x ≤ (1 + d)⁻¹ * B (p + g) x at hh
    rw [← div_eq_inv_mul] at hh
    have hh' := (le_div_iff₀ hden).mp hh
    simp only [map_add, LinearMap.add_apply] at hh'
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    nlinarith
  have hd0 : d = 0 := by
    by_contra hne'
    have hdp : 0 < d := lt_of_le_of_ne hd (Ne.symm hne')
    have hpF : p ∈ F := by
      apply F.isFaceOf.mem_of_smul_add_mem hp.1.1 hres hdp
      have hsum : d • p + (g - d • p) = g := by abel
      rw [hsum]
      exact hgF
    have hQp := hfix p hpF
    have hh : d = 0 := by
      change I (Q p) = 0
      rw [hQp]
      exact hIpure ⟨p, hp⟩
    exact hne' hh
  refine ⟨hlocus, hPcompact, hPne, fun r => ?_⟩
  have hrC : Q r ∈ C := F.isFaceOf.le (hface r (pure_mem r).1)
  have hrmax : I (Q r) ≤ d := hmax r.property
  have hrI : I (Q r) = 0 := le_antisymm (hrmax.trans_eq hd0) (hI hrC)
  by_cases hr0 : Q r = 0
  · exact Or.inl hr0
  have hur := hu (Q r) hrC hr0
  refine Or.inr ⟨hur, ?_, ?_⟩
  · apply (Set.ext_iff.mp hlocus _).mpr
    refine ⟨normalized_mem hu hrC hr0, ?_⟩
    have he : B (Q r) (Q r) = (u (Q r)) ^ 2 := by dsimp [I] at hrI; linarith
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, he]
    field_simp [hur.ne']
  · simp only [smul_smul, mul_inv_cancel₀ hur.ne', one_smul]

#print axioms least_confirmation_face_purity

end D5.S3.Quantum.Foundation.FaceProjectionPurity
