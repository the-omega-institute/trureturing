/- GID: D5/S3/Quantum/Analysis/CStarTriangleEqualityUnital
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/CStarTriangleEqualityUnital
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Triangle-equality rigidity for complex C-star algebras. -/

/-
admission_basis: escape-witness
escape_witness: seminorm_spectral_real_direction_lower
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/27516
Declarations (definition rows carry no proof-shape claim):
seminorm_spectral_real_direction_lower: proof_shape: content; consumers: seminorm_realPart_le.
seminorm_realPart_le: proof_shape: content; consumers: seminorm_unital_rigidity.
seminorm_bound_of_unitary_bound: proof_shape: bind-only; consumers: seminorm_unital_rigidity.
seminorm_unital_rigidity: proof_shape: content; consumers: D5.S3.Quantum.Analysis.CStarTriangleEqualityHereditary.seminorm_algebraically_unital_rigidity, D5.S3.Quantum.Analysis.CStarTriangleEqualityHereditary.seminorm_local_corner_cross.
-/

import D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane
import D5.S3.Quantum.Analysis.CStarTriangleEqualityUnitalSpectral
import D5.S3.Quantum.Analysis.RussoDye

namespace D5.S3.Quantum.Analysis.CStarTriangleEqualityUnital

open Metric
open scoped Topology
section
open scoped Topology ComplexStarModule NNReal
open Filter
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

/-- The spectral directional lower bound is controlled by the seminorm of the full direction. -/
private theorem seminorm_spectral_real_direction_lower (p : Seminorm ℂ A)
    (hp : ∀ a b : A, D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair a b → p (a+b)=p a+p b)
    (a h k : A) (hh : IsSelfAdjoint h) (hk : IsSelfAdjoint k)
    (ha : a = h + Complex.I • k) (r : ℝ) (hr : r ∈ spectrum ℝ h) :
    p 1 * r ≤ p a := by
  let C : ℝ := p 1 * ‖k‖ ^ 2
  have hq (s : ℝ) : p ((1 : A) + s • (Complex.I • k)) ≤ p 1 + C * s ^ 2 := by
    have he : p ((1 : A) + s • (Complex.I • k)) =
        p 1 * ‖(1 : A) + s • (Complex.I • k)‖ := by
      simpa only [one_smul, mul_smul, Complex.coe_smul] using
        D5.S3.Quantum.Analysis.CStarTriangleEqualityUnitalSpectral.seminorm_spectral_plane_scale p hp k hk 1 ((s : ℂ) * Complex.I)
    rw [he]
    have h := mul_le_mul_of_nonneg_left (D5.S3.Quantum.Analysis.CStarTriangleEqualityUnitalSpectral.norm_one_add_skew_quadratic k hk s).2
      (apply_nonneg p 1)
    dsimp [C]
    nlinarith
  have hbound (t : ℝ) (ht : 0 < t) : p 1 * r ≤ p a + 2 * C * t := by
    have hspec : 1 + t*r ∈ spectrum ℝ ((1 : A) + t • h) := by
      let u : ℝˣ := Units.mk0 t ht.ne'
      have hs := (spectrum.smul_mem_smul_iff (R := ℝ) (A := A) (r := u) (s := r)).mpr hr
      have hs' : t*r ∈ spectrum ℝ (t • h) := by
        exact spectrum.mem_iff.mpr hs
      have hs'' := (spectrum.add_mem_add_iff (R := ℝ) (A := A)
        (r := t*r) (s := 1) (a := t • h)).mpr hs'
      simpa only [Algebra.algebraMap_eq_smul_one, one_smul, add_comm] using hs''
    have hn : 1 + t*r ≤ ‖(1 : A) + t • h‖ :=
      (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using spectrum.norm_le_norm_of_mem hspec)
    have he : (2 : ℝ) • ((1 : A) + t • h) =
        ((1 : A) + (2*t) • a) + ((1 : A) + (-2*t) • (Complex.I • k)) := by
      rw [ha]
      module
    have hadd := map_add_le_add p ((1 : A) + (2*t) • a)
      ((1 : A) + (-2*t) • (Complex.I • k))
    rw [← he, ← Complex.coe_smul, map_smul_eq_mul] at hadd
    norm_num at hadd
    have hreal : p ((1 : A) + t • h) = p 1 * ‖(1 : A) + t • h‖ := by
      simpa only [one_smul, Complex.coe_smul] using
        D5.S3.Quantum.Analysis.CStarTriangleEqualityUnitalSpectral.seminorm_spectral_plane_scale p hp h hh 1 (t : ℂ)
    have htri := map_add_le_add p (1 : A) ((2*t) • a)
    have hmul : p ((2*t : ℝ) • a) = (2*t) * p a := by
      rw [← Complex.coe_smul, map_smul_eq_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [hmul] at htri
    have hquad := hq (-2*t)
    simp only [neg_mul, neg_smul] at hquad
    have hm := mul_le_mul_of_nonneg_left hn (apply_nonneg p 1)
    rw [hreal] at hadd
    apply (mul_le_mul_iff_right₀ ht).mp
    nlinarith
  have hlim : Tendsto (fun t : ℝ => p a + 2*C*t) (𝓝[>] 0) (𝓝 (p a)) := by
    have hc : Continuous (fun t : ℝ => p a + 2*C*t) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    (eventually_mem_nhdsWithin.mono fun t ht => hbound t ht)

/-- Dropping the imaginary part cannot increase a TEA-additive seminorm. -/
private theorem seminorm_realPart_le (p : Seminorm ℂ A)
    (hp : ∀ a b : A, D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair a b → p (a+b)=p a+p b) (a : A) :
    p 1 * ‖realPart a‖ ≤ p a := by
  let h : A := realPart a
  let k : A := imaginaryPart a
  have hh : IsSelfAdjoint h := (realPart a).property
  have hk : IsSelfAdjoint k := (imaginaryPart a).property
  obtain ⟨r, hr, hrn⟩ :=
    (IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum (𝕜 := ℝ) h).1
  change ‖r‖ = ‖h‖ at hrn
  have ha : a = h + Complex.I • k := (realPart_add_I_smul_imaginaryPart a).symm
  have hlo := seminorm_spectral_real_direction_lower p hp a h k hh hk ha r hr
  have hrneg : -r ∈ spectrum ℝ (-h) := by
    rw [← spectrum.neg_eq]
    exact Set.neg_mem_neg.mpr hr
  have haneg : -a = -h + Complex.I • (-k) := by rw [ha]; module
  have hhi := seminorm_spectral_real_direction_lower p hp (-a) (-h) (-k)
    hh.neg hk.neg haneg (-r) hrneg
  rw [map_neg_eq_map p] at hhi
  change p 1 * ‖h‖ ≤ p a
  rw [← hrn, Real.norm_eq_abs]
  rcases le_total 0 r with hs | hs
  · simpa only [abs_of_nonneg hs] using hlo
  · simpa only [abs_of_nonpos hs] using hhi

end

section
open scoped Topology ComplexStarModule NNReal
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

/-- Russo–Dye converts a uniform unitary bound on a continuous real seminorm to its sharp norm bound. -/
private theorem seminorm_bound_of_unitary_bound (q : Seminorm ℝ A) (hq : Continuous q)
    (M : ℝ) (hM : 0 ≤ M) (hu : ∀ u : unitary A, q (u : A) ≤ M) (a : A) :
    q a ≤ M * ‖a‖ := by
  have hclosed : IsClosed (q.closedBall 0 M) := by
    rw [q.closedBall_zero_eq]
    exact isClosed_le hq continuous_const
  have hsub : (unitary A : Set A) ⊆ q.closedBall 0 M := by
    intro u hu'
    exact q.mem_closedBall_zero.mpr (hu ⟨u, hu'⟩)
  have hball : Metric.closedBall (0 : A) 1 ⊆ q.closedBall 0 M := by
    rw [← D5.S3.Quantum.Analysis.RussoDye.closedConvexHull_unitary]
    exact closedConvexHull_min hsub (q.convex_closedBall 0 M) hclosed
  by_cases ha : a = 0
  · simp [ha]
  have hn : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hnorm : ‖(‖a‖⁻¹ : ℝ) • a‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg a)), inv_mul_cancel₀ hn]
  have hqa : q ((‖a‖⁻¹ : ℝ) • a) ≤ M := q.mem_closedBall_zero.mp
    (hball (by simpa only [Metric.mem_closedBall, dist_zero_right, hnorm] using (le_refl (1 : ℝ))))
  rw [map_smul_eq_mul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg a))] at hqa
  have hi := mul_le_mul_of_nonneg_left hqa (norm_nonneg a)
  simpa only [← mul_assoc, mul_inv_cancel₀ hn, one_mul, mul_comm ‖a‖ M] using hi

/-- The full unital seminorm theorem follows from Russo–Dye and the directional real-part bound. -/
theorem seminorm_unital_rigidity {A : Type*} [CStarAlgebra A] [Nontrivial A]
    (p : Seminorm ℂ A)
    (hp : ∀ a b : A, D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair a b → p (a+b)=p a+p b) (a : A) :
    p a = p 1 * ‖a‖ := by
  have hpcont : Continuous p := (D5.S3.Quantum.Analysis.CStarTriangleEqualityUnitalSpectral.seminorm_unital_lipschitz p hp).continuous
  have hu (u : unitary A) : p (u : A) = p 1 := by
    simpa only [CStarRing.norm_coe_unitary, mul_one] using D5.S3.Quantum.Analysis.CStarTriangleEqualityUnitalSpectral.seminorm_normal_scale p hp (u : A)
  have hupper : p a ≤ p 1 * ‖a‖ :=
    seminorm_bound_of_unitary_bound (p.restrictScalars ℝ) hpcont (p 1) (apply_nonneg p 1)
      (fun u => (hu u).le) a
  by_cases ha : a = 0
  · simp [ha]
  let L : A →L[ℝ] selfAdjoint A :=
    (realPart.comp (LinearMap.mulRight ℝ a)).mkContinuous ‖a‖ (by
      intro x
      exact (realPart.norm_le (x*a)).trans (by simpa only [mul_comm] using norm_mul_le x a))
  let q : Seminorm ℝ A := (normSeminorm ℝ (selfAdjoint A)).comp L.toLinearMap
  let Q : Seminorm ℝ A := Seminorm.of (fun x => p 1 * q x)
    (by
      intro x y
      have hi := mul_le_mul_of_nonneg_left (map_add_le_add q x y) (apply_nonneg p 1)
      simpa only [mul_add] using hi)
    (by
      intro c x
      rw [map_smul_eq_mul]
      ring)
  have hQ (x : A) : Q x = p 1 * ‖realPart (x*a)‖ := rfl
  have hQcont : Continuous Q := by
    change Continuous (fun x : A => p 1 * ‖L x‖)
    fun_prop
  have hQunit (u : unitary A) : Q (u : A) ≤ p a := by
    let J := (Unitary.mulLeft ℂ A (star u)).toLinearIsometry
    let p' : Seminorm ℂ A := p.comp J.toLinearMap
    have hp' : ∀ x y : A, D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair x y → p' (x+y)=p' x+p' y := by
      intro x y hxy
      change p (J (x+y)) = p (J x) + p (J y)
      rw [map_add]
      apply hp
      simpa only [D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair, ← map_add, J.norm_map] using hxy
    have h := seminorm_realPart_le p' hp' ((u : A)*a)
    have hJone : J 1 = (star u : unitary A) := by
      change (star u : unitary A) * (1 : A) = (star u : unitary A)
      exact mul_one _
    have hJa : J ((u : A)*a) = a := by
      change (star u : unitary A) * ((u : A)*a) = a
      rw [Unitary.coe_star, ← mul_assoc, u.property.1, one_mul]
    change p (J 1) * ‖realPart ((u : A)*a)‖ ≤ p (J ((u : A)*a)) at h
    rw [hJone, hJa, hu (star u)] at h
    simpa only [hQ] using h
  have hbound := seminorm_bound_of_unitary_bound Q hQcont (p a) (apply_nonneg p a) hQunit (star a)
  rw [hQ, norm_star] at hbound
  have hre : ‖realPart (star a*a)‖ = ‖a‖*‖a‖ := by
    rw [← AddSubgroup.norm_coe, (IsSelfAdjoint.star_mul_self a).coe_realPart,
      CStarRing.norm_star_mul_self]
  rw [hre] at hbound
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr ha
  exact le_antisymm hupper ((mul_le_mul_iff_right₀ hn).mp (by nlinarith [hbound]))

end

end D5.S3.Quantum.Analysis.CStarTriangleEqualityUnital
