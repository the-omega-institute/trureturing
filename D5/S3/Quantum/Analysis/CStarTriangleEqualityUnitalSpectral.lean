/- GID: D5/S3/Quantum/Analysis/CStarTriangleEqualityUnitalSpectral
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/CStarTriangleEqualityUnitalSpectral
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Triangle-equality rigidity for complex C-star algebras. -/

/-
admission_basis: escape-witness
escape_witness: seminorm_spectral_plane_scale
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/27516
Declarations (definition rows carry no proof-shape claim):
seminorm_spectral_plane_scale: proof_shape: content; consumers: D5.S3.Quantum.Analysis.CStarTriangleEqualityUnital.seminorm_spectral_real_direction_lower, seminorm_selfadjoint_scale, seminorm_tea_at_one.
seminorm_selfadjoint_scale: proof_shape: content; consumers: seminorm_tea_at_one, seminorm_unital_bound.
seminorm_unital_bound: proof_shape: content; consumers: seminorm_unital_lipschitz.
seminorm_unital_lipschitz: proof_shape: content; consumers: D5.S3.Quantum.Analysis.CStarTriangleEqualityUnital.seminorm_unital_rigidity.
norm_one_add_skew_quadratic: proof_shape: bind-only; consumers: D5.S3.Quantum.Analysis.CStarTriangleEqualityUnital.seminorm_spectral_real_direction_lower, seminorm_tea_at_one.
tea_smul_right: proof_shape: bind-only; consumers: seminorm_tea_smul.
seminorm_tea_smul: proof_shape: bind-only; consumers: tea_slope_eq_of_quadratic_direction.
tea_slope_eq_of_quadratic_direction: proof_shape: content; consumers: seminorm_tea_at_one.
tea_realpart: proof_shape: bind-only; consumers: seminorm_tea_at_one.
seminorm_tea_at_one: proof_shape: content; consumers: seminorm_scale_of_spectral_norm_attainment.
seminorm_scale_of_spectral_norm_attainment: proof_shape: content; consumers: seminorm_normal_scale.
seminorm_normal_scale: proof_shape: content; consumers: D5.S3.Quantum.Analysis.CStarTriangleEqualityUnital.seminorm_unital_rigidity.
-/

import D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.CStarAlgebra.Unitary.Maps
import Mathlib.Tactic.FieldSimp

namespace D5.S3.Quantum.Analysis.CStarTriangleEqualityUnitalSpectral

section

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

/-- TEA additivity fixes the seminorm of every selfadjoint element before continuity is known. -/
theorem seminorm_spectral_plane_scale (p : Seminorm ℂ A)
    (hp : ∀ a b : A, D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair a b → p (a + b) = p a + p b)
    (h : A) (hh : IsSelfAdjoint h) (α β : ℂ) :
    p (α • (1 : A) + β • h) = p 1 * ‖α • (1 : A) + β • h‖ := by
  let K := spectrum ℂ h
  letI : Nonempty K := (spectrum.nonempty h).to_subtype
  let r : C(K, ℝ) := ⟨fun z => z.val.re, by fun_prop⟩
  obtain ⟨m, hm⟩ := (isCompact_range r.continuous).exists_isLeast (Set.range_nonempty r)
  obtain ⟨M, hM⟩ := (isCompact_range r.continuous).exists_isGreatest (Set.range_nonempty r)
  obtain ⟨x₀, hx₀⟩ := hm.1
  obtain ⟨x₁, hx₁⟩ := hM.1
  have hbounds (z : K) : m ≤ r z ∧ r z ≤ M :=
    ⟨hm.2 (Set.mem_range_self z), hM.2 (Set.mem_range_self z)⟩
  have hmM : m ≤ M := (hbounds x₁).1.trans_eq hx₁
  by_cases hEq : m = M
  · have hspec : spectrum ℂ h ⊆ {(m : ℂ)} := by
      intro z hz
      have hlo : m ≤ z.re := (hbounds ⟨z, hz⟩).1
      have hhi : z.re ≤ M := (hbounds ⟨z, hz⟩).2
      have hr : z.re = m := le_antisymm (hhi.trans_eq hEq.symm) hlo
      change z = (m : ℂ)
      exact (hh.mem_spectrum_eq_re hz).trans (congrArg Complex.ofReal hr)
    have hscalar : h = (m : ℂ) • (1 : A) := by
      simpa only [Algebra.algebraMap_eq_smul_one] using
        CFC.eq_algebraMap_of_spectrum_subset_singleton h (m : ℂ) hspec hh.isStarNormal
    rw [hscalar, smul_smul, ← add_smul, map_smul_eq_mul, norm_smul, norm_one, mul_one, mul_comm]
  · have hlt : m < M := lt_of_le_of_ne hmM hEq
    have hden : M - m ≠ 0 := sub_ne_zero.mpr hlt.ne'
    let t : C(K, ℝ) := ⟨fun z => (r z - m) / (M - m), by fun_prop⟩
    have ht (z : K) : t z ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr (hbounds z).1) (sub_pos.mpr hlt).le
      · apply (div_le_one (sub_pos.mpr hlt)).mpr
        exact sub_le_sub_right (hbounds z).2 m
    have ht₀ : t x₀ = 0 := by change (r x₀ - m) / (M - m) = 0; rw [hx₀]; simp
    have ht₁ : t x₁ = 1 := by change (r x₁ - m) / (M - m) = 1; rw [hx₁]; exact div_self hden
    let J := D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.affineFacePlane t ht x₀ x₁ ht₀ ht₁
    let L := ((cfcHom hh.isStarNormal).toAlgHom.toLinearMap.toLinearIsometry (isometry_cfcHom h hh.isStarNormal)).comp J
    have hJone : J (1, 1) = 1 := by
      ext z
      change (1 - (t z : ℂ)) * 1 + (t z : ℂ) * 1 = 1
      simpa only [mul_one] using sub_add_cancel (1 : ℂ) (t z : ℂ)
    have hLone : L (1, 1) = 1 := by
      change cfcHom hh.isStarNormal (J (1, 1)) = 1
      rw [hJone, map_one]
    have hJid : J ((m : ℂ), (M : ℂ)) = (ContinuousMap.id ℂ).restrict K := by
      ext z
      change (1 - (((r z - m) / (M - m) : ℝ) : ℂ)) * (m : ℂ) +
        (((r z - m) / (M - m) : ℝ) : ℂ) * (M : ℂ) = z.val
      calc
        _ = (r z : ℂ) := by
          have he : (1 - (r z - m) / (M - m)) * m +
              ((r z - m) / (M - m)) * M = r z := by
            field_simp [hden]
            ring
          exact_mod_cast he
        _ = z.val := (hh.mem_spectrum_eq_re z.property).symm
    have hLh : L ((m : ℂ), (M : ℂ)) = h := by
      change cfcHom hh.isStarNormal (J ((m : ℂ), (M : ℂ))) = h
      rw [hJid, cfcHom_id]
    have hscale := D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.seminorm_on_isometric_plane p hp L (1, 1)
    have hc : p (L (1, 0)) = p 1 := by simpa [hLone, Prod.norm_def] using hscale.symm
    let v : ℂ × ℂ := α • (1, 1) + β • ((m : ℂ), (M : ℂ))
    have hLv : L v = α • (1 : A) + β • h := by
      dsimp only [v]
      rw [map_add, map_smul, map_smul, hLone, hLh]
    have he := D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.seminorm_on_isometric_plane p hp L v
    rw [hc, ← L.norm_map, hLv] at he
    exact he

/-- The selfadjoint axis of a spectral plane has the identity's norm scale. -/
private theorem seminorm_selfadjoint_scale (p : Seminorm ℂ A)
    (hp : ∀ a b : A, D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair a b → p (a + b) = p a + p b)
    (h : A) (hh : IsSelfAdjoint h) : p h = p 1 * ‖h‖ := by
  simpa only [zero_smul, one_smul, zero_add] using
    seminorm_spectral_plane_scale p hp h hh 0 1

end

section
open scoped ComplexStarModule
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

/-- The unital two-sided real/imaginary decomposition gives an a priori norm bound. -/
private theorem seminorm_unital_bound (p : Seminorm ℂ A)
    (hp : ∀ a b : A, D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair a b → p (a + b) = p a + p b) (a : A) :
    p a ≤ 2 * p 1 * ‖a‖ := by
  calc
    p a = p ((realPart a : A) + Complex.I • (imaginaryPart a : A)) := by
      rw [realPart_add_I_smul_imaginaryPart]
    _ ≤ p (realPart a : A) + p (Complex.I • (imaginaryPart a : A)) := map_add_le_add p _ _
    _ = p 1 * ‖realPart a‖ + p 1 * ‖imaginaryPart a‖ := by
      rw [map_smul_eq_mul, Complex.norm_I, one_mul,
        seminorm_selfadjoint_scale p hp _ (realPart a).property,
        seminorm_selfadjoint_scale p hp _ (imaginaryPart a).property]
      rfl
    _ ≤ p 1 * ‖a‖ + p 1 * ‖a‖ := add_le_add
      (mul_le_mul_of_nonneg_left (realPart.norm_le a) (apply_nonneg p 1))
      (mul_le_mul_of_nonneg_left (imaginaryPart.norm_le a) (apply_nonneg p 1))
    _ = 2 * p 1 * ‖a‖ := by ring

/-- Continuity is deduced rather than assumed. -/
theorem seminorm_unital_lipschitz (p : Seminorm ℂ A)
    (hp : ∀ a b : A, D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair a b → p (a + b) = p a + p b) :
    LipschitzWith ⟨2 * p 1, mul_nonneg (by norm_num) (apply_nonneg p 1)⟩ p := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  exact (p.norm_sub_map_le_sub x y).trans (seminorm_unital_bound p hp (x - y))

end

section

open Filter
open scoped Topology


variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

/-- The norm has a quadratic increment in a skew-adjoint direction at the identity. -/
theorem norm_one_add_skew_quadratic (h : A) (hh : IsSelfAdjoint h) (s : ℝ) :
    0 ≤ ‖(1 : A) + s • (Complex.I • h)‖ - 1 ∧
    ‖(1 : A) + s • (Complex.I • h)‖ - 1 ≤ s ^ 2 * ‖h‖ ^ 2 := by
  let k : A := Complex.I • h
  have hk : star k = -k := by simp [k, star_smul, hh.star_eq]
  have hkk : k * k = -(h * h) := by
    simp only [k, smul_mul_assoc, mul_smul_comm, smul_smul, Complex.I_mul_I, neg_one_smul]
  have hsum : ((1 : A) + s • k) + star (1 + s • k) = (2 : ℝ) • (1 : A) := by
    simp only [star_add, star_one, star_smul, star_trivial, hk, smul_neg, two_smul]
    simpa only [add_neg_cancel, add_zero] using
      add_add_add_comm (1 : A) (s • k) 1 (-(s • k))
  have hl : 1 ≤ ‖(1 : A) + s • k‖ := by
    have ht := norm_add_le ((1 : A) + s • k) (star (1 + s • k))
    rw [hsum, norm_smul, norm_one, norm_star] at ht
    norm_num at ht
    linarith
  have hprod : star ((1 : A) + s • k) * (1 + s • k) =
      1 + (s * s) • (h * h) := by
    calc
      _ = ((1 : A) - s • k) * (1 + s • k) := by
        simp only [star_add, star_one, star_smul, star_trivial, hk, smul_neg, sub_eq_add_neg]
      _ = 1 - (s • k) * (s • k) := by
        simpa only [one_mul] using
          (Commute.one_left (s • k)).mul_self_sub_mul_self_eq'.symm
      _ = 1 + (s * s) • (h * h) := by
        simp only [smul_mul_assoc, mul_smul_comm, smul_smul, hkk, smul_neg, sub_neg_eq_add]
  have hsq : ‖(1 : A) + s • k‖ * ‖(1 : A) + s • k‖ ≤
      1 + (s * s) * (‖h‖ * ‖h‖) := by
    calc
      _ = ‖star ((1 : A) + s • k) * (1 + s • k)‖ := (CStarRing.norm_star_mul_self (x := (1 : A) + s • k)).symm
      _ = ‖(1 : A) + (s * s) • (h * h)‖ := congrArg norm hprod
      _ ≤ ‖(1 : A)‖ + ‖(s * s) • (h * h)‖ := norm_add_le _ _
      _ ≤ 1 + (s * s) * (‖h‖ * ‖h‖) := by
        rw [norm_one, norm_smul, Real.norm_of_nonneg (mul_self_nonneg s)]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (norm_mul_le h h) (mul_self_nonneg s))
  constructor
  · exact sub_nonneg.mpr hl
  · change ‖(1 : A) + s • k‖ - 1 ≤ _
    nlinarith


end

section

open Filter NormedSpace
open scoped Topology


variable {A : Type*} [CStarAlgebra A] [Nontrivial A]


end

section

open Filter
open scoped Topology

/-- Triangle equality persists under nonnegative real rescaling of either summand. -/
private theorem tea_smul_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : E) (hab : D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair a b) (s : ℝ) (hs : 0 ≤ s) : D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair a (s • b) := by
  unfold D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair at hab ⊢
  rw [norm_smul, Real.norm_of_nonneg hs]
  apply le_antisymm
  · simpa only [norm_smul, Real.norm_of_nonneg hs] using norm_add_le a (s • b)
  · by_cases hsmall : s ≤ 1
    · have he : a + b = (a + s • b) + (1 - s) • b := by
        rw [sub_smul, one_smul, add_add_sub_cancel]
      have ht := norm_add_le (a + s • b) ((1 - s) • b)
      rw [← he, hab, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr hsmall)] at ht
      nlinarith
    · have he : s • (a + b) = (a + s • b) + (s - 1) • a := by module
      have ht := norm_add_le (a + s • b) ((s - 1) • a)
      rw [← he, norm_smul, Real.norm_of_nonneg hs, hab, norm_smul,
        Real.norm_of_nonneg (sub_nonneg.mpr (le_of_not_ge hsmall))] at ht
      nlinarith

private theorem seminorm_tea_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : Seminorm ℂ E)
    (hp : ∀ a b : E, D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair a b → p (a + b) = p a + p b)
    (a b : E) (hab : D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair a b) (s : ℝ) (hs : 0 ≤ s) :
    p (a + s • b) = p a + s * p b := by
  rw [hp a (s • b) (tea_smul_right a b hab s hs)]
  rw [← Complex.coe_smul, map_smul_eq_mul, Complex.norm_real, Real.norm_of_nonneg hs]

/-- A direction with quadratic seminorm increment does not change the TEA slope. -/
private theorem tea_slope_eq_of_quadratic_direction {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (p : Seminorm ℂ E)
    (hp : ∀ a b : E, D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair a b → p (a + b) = p a + p b)
    (u a b d : E) (had : a = b + d) (hua : D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair u a) (hub : D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair u b)
    (C : ℝ) (hquad : ∀ s : ℝ, p (u + s • d) ≤ p u + C * s ^ 2) : p a = p b := by
  have htwo (x : E) : p ((2 : ℝ) • x) = 2 * p x := by
    rw [← Complex.coe_smul, map_smul_eq_mul]
    norm_num
  have hupper (t : ℝ) (ht : 0 < t) : p a ≤ p b + 2 * C * t := by
    have he : (2 : ℝ) • (u + t • a) = (u + (2 * t) • b) + (u + (2 * t) • d) := by
      rw [had]
      module
    have hi := map_add_le_add p (u + (2 * t) • b) (u + (2 * t) • d)
    rw [← he, htwo, seminorm_tea_smul p hp u a hua t ht.le,
      seminorm_tea_smul p hp u b hub (2 * t) (by positivity)] at hi
    have hq := hquad (2 * t)
    apply (mul_le_mul_iff_right₀ ht).mp
    nlinarith
  have hlower (t : ℝ) (ht : 0 < t) : p b ≤ p a + 2 * C * t := by
    have he : (2 : ℝ) • (u + t • b) = (u + (2 * t) • a) + (u + (-2 * t) • d) := by
      rw [had]
      module
    have hi := map_add_le_add p (u + (2 * t) • a) (u + (-2 * t) • d)
    rw [← he, htwo, seminorm_tea_smul p hp u b hub t ht.le,
      seminorm_tea_smul p hp u a hua (2 * t) (by positivity)] at hi
    have hq := hquad (-2 * t)
    apply (mul_le_mul_iff_right₀ ht).mp
    nlinarith
  have hlim (x : ℝ) : Tendsto (fun t : ℝ => x + 2 * C * t) (𝓝[>] 0) (𝓝 x) := by
    have hc : Continuous (fun t : ℝ => x + 2 * C * t) := by fun_prop
    simpa only [mul_zero, add_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply le_antisymm
  · exact le_of_tendsto_of_tendsto tendsto_const_nhds (hlim (p b)) (eventually_mem_nhdsWithin.mono fun t ht => hupper t ht)
  · exact le_of_tendsto_of_tendsto tendsto_const_nhds (hlim (p a)) (eventually_mem_nhdsWithin.mono fun t ht => hlower t ht)

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
open scoped ComplexStarModule

/-- Triangle equality at the identity passes to the real part with the same norm. -/
private theorem tea_realpart (b : A) (hb : D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair (1 : A) b) :
    ‖realPart b‖ = ‖b‖ ∧ D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair (1 : A) (realPart b : A) := by
  let h : A := realPart b
  have hre : (2 : ℝ) • h = b + star b := by
    exact smul_eq_iff_eq_invOf_smul.mpr rfl
  have he : star ((1 : A) + b) * (1 + b) = (1 + (2 : ℝ) • h) + star b * b := by
    rw [hre, star_add, star_one]
    noncomm_ring
  have hi := norm_add_le ((1 : A) + (2 : ℝ) • h) (star b * b)
  rw [← he, CStarRing.norm_star_mul_self, CStarRing.norm_star_mul_self] at hi
  have hb' : ‖(1 : A) + b‖ = 1 + ‖b‖ := by simpa only [D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair, norm_one] using hb
  rw [hb'] at hi
  have hu : ‖(1 : A) + (2 : ℝ) • h‖ ≤ 1 + 2 * ‖h‖ := by
    simpa only [norm_one, norm_smul, Real.norm_ofNat] using norm_add_le (1 : A) ((2 : ℝ) • h)
  have hle : ‖h‖ ≤ ‖b‖ := realPart.norm_le b
  have hn : ‖h‖ = ‖b‖ := by nlinarith
  have hn2 : ‖(1 : A) + (2 : ℝ) • h‖ = 1 + 2 * ‖b‖ := by nlinarith
  have hsum : (((1 : A) + h) + h) = 1 + (2 : ℝ) • h := by simp only [two_smul]; abel
  have hi1 := norm_add_le ((1 : A) + h) h
  rw [hsum, hn2, hn] at hi1
  have hi2 := norm_add_le (1 : A) h
  rw [norm_one, hn] at hi2
  refine ⟨hn, ?_⟩
  change ‖(1 : A) + h‖ = ‖(1 : A)‖ + ‖h‖
  rw [norm_one, hn]
  linarith

end

section

open scoped ComplexStarModule
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

/-- TEA at the identity determines the seminorm of its other summand. -/
private theorem seminorm_tea_at_one (p : Seminorm ℂ A)
    (hp : ∀ a b : A, D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair a b → p (a + b) = p a + p b)
    (a : A) (ha : D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair (1 : A) a) : p a = p 1 * ‖a‖ := by
  let h : A := realPart a
  let k : A := imaginaryPart a
  have hh : IsSelfAdjoint h := (realPart a).property
  have hk : IsSelfAdjoint k := (imaginaryPart a).property
  have hreal := tea_realpart a ha
  have hdecomp : a = h + Complex.I • k := (realPart_add_I_smul_imaginaryPart a).symm
  have hquad (s : ℝ) : p ((1 : A) + s • (Complex.I • k)) ≤
      p 1 + (p 1 * ‖k‖ ^ 2) * s ^ 2 := by
    have he : p ((1 : A) + s • (Complex.I • k)) =
        p 1 * ‖(1 : A) + s • (Complex.I • k)‖ := by
      simpa only [one_smul, mul_smul, Complex.coe_smul] using
        seminorm_spectral_plane_scale p hp k hk 1 ((s : ℂ) * Complex.I)
    rw [he]
    have hq := (norm_one_add_skew_quadratic k hk s).2
    have hm := mul_le_mul_of_nonneg_left hq (apply_nonneg p 1)
    nlinarith
  rw [tea_slope_eq_of_quadratic_direction p hp 1 a h (Complex.I • k)
    hdecomp ha hreal.2 _ hquad, seminorm_selfadjoint_scale p hp h hh]
  exact congrArg (p 1 * ·) hreal.1


end

section
end

section

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

/-- Spectral norm attainment supplies a scalar phase norming the TEA relation. -/
private theorem seminorm_scale_of_spectral_norm_attainment (p : Seminorm ℂ A)
    (hp : ∀ a b : A, D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair a b → p (a + b) = p a + p b)
    (a : A) (hspec : ∃ z ∈ spectrum ℂ a, ‖z‖ = ‖a‖) : p a = p 1 * ‖a‖ := by
  by_cases ha : a = 0
  · simp [ha]
  have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  obtain ⟨z, hz, hzn⟩ := hspec
  have hz0 : z ≠ 0 := by
    intro hz0
    apply hna
    simpa only [hz0, norm_zero] using hzn.symm
  let r : ℂˣ := Units.mk0 z hz0
  let b : A := z⁻¹ • a
  have hbn : ‖b‖ = 1 := by
    simp only [b, norm_smul, norm_inv, hzn, inv_mul_cancel₀ hna]
  have hs1 : (1 : ℂ) ∈ spectrum ℂ b := by
    have hs := (spectrum.smul_mem_smul_iff (R := ℂ) (A := A)
      (r := r⁻¹) (s := z)).mpr hz
    simpa [Units.smul_def, r, smul_eq_mul, b, hz0] using hs
  have hs2 : (2 : ℂ) ∈ spectrum ℂ ((1 : A) + b) := by
    have hs := (spectrum.add_mem_add_iff (R := ℂ) (A := A)
      (r := 1) (s := 1) (a := b)).mpr hs1
    convert hs using 1 <;> norm_num
  have htea : D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair (1 : A) b := by
    unfold D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair
    apply le_antisymm (norm_add_le _ _)
    have hs := spectrum.norm_le_norm_of_mem hs2
    simpa only [norm_one, hbn, one_add_one_eq_two, Complex.norm_ofNat] using hs
  have hpbn := seminorm_tea_at_one p hp b htea
  have he : a = z • b := by simp [b, smul_inv_smul₀ hz0]
  calc
    p a = p (z • b) := congrArg p he
    _ = ‖z‖ * p b := map_smul_eq_mul p z b
    _ = p 1 * ‖a‖ := by rw [hpbn, hbn, mul_one, hzn, mul_comm]

/-- Every normal element has the seminorm scale already determined by the identity. -/
theorem seminorm_normal_scale (p : Seminorm ℂ A)
    (hp : ∀ a b : A, D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair a b → p (a + b) = p a + p b)
    (a : A) [IsStarNormal a] : p a = p 1 * ‖a‖ := by
  exact seminorm_scale_of_spectral_norm_attainment p hp a
    (IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum (𝕜 := ℂ) a).1

end

section


end

section
end

section


end

end D5.S3.Quantum.Analysis.CStarTriangleEqualityUnitalSpectral
