/- GID: D5/S3/Quantum/Algebra/NormalizedSingularHermitianKernel
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/NormalizedSingularHermitianKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Normalized singular Hermitian coefficient kernels admit a common vector, neutral plane, or primitive congruence form. -/

import Mathlib
import D5.S3.Quantum.Algebra.CommonCoefficientPlane

/-!
# Normalized singular Hermitian kernel identities

The normalized graph alternatives are established here, including zero,
proper, and surjective coefficient images.  The native width-three compression
geometry combines these alternatives to prove `normalizedGraphTrichotomy`.
The determinant, shear, and final-unitary congruences give its coordinate route.
-/

noncomputable section

open Matrix
open scoped BigOperators ComplexConjugate

namespace D5.S3.Quantum.Algebra.NormalizedSingularHermitianKernel

abbrev M := Matrix (Fin 3) (Fin 3) ℂ

def D : M := !![(1 : ℂ), 0, 0; 0, -1, 0; 0, 0, 0]

def hermitianMatrix (a b : ℝ) (z u v : ℂ) : M :=
  !![(a : ℂ), z, u; conj z, (b : ℂ), v; conj u, conj v, 0]

def shear (p : ℂ) : M := !![1, 0, 0; 0, 1, 0; 0, -p, 1]

def finalUnitary : M :=
  let r : ℝ := Real.sqrt 2
  !![((r⁻¹ : ℝ) : ℂ), Complex.I * ((r⁻¹ : ℝ) : ℂ), 0;
     ((r⁻¹ : ℝ) : ℂ), -Complex.I * ((r⁻¹ : ℝ) : ℂ), 0;
     0, 0, Complex.I]

def skew3 : Set M :=
  {A | ∃ x y z : ℝ,
      A = !![0, (x : ℂ), (y : ℂ); (-x : ℂ), 0, (z : ℂ);
        (-y : ℂ), (-z : ℂ), 0]}

def iSkew3 : Set M :=
  {A | ∃ x y z : ℝ,
      A = Complex.I • !![0, (x : ℂ), (y : ℂ); (-x : ℂ), 0, (z : ℂ);
        (-y : ℂ), (-z : ℂ), 0]}

def e3 : Fin 3 → ℂ := ![0, 0, 1]

def neutralGenerator (c : ℂ) : Fin 3 → ℂ := ![1, -c, 0]

theorem hermitian_coordinates {H : M} (hH : H.IsHermitian) :
    ∃ a b c : ℝ, ∃ z u v : ℂ,
      H = !![(a : ℂ), z, u; conj z, (b : ℂ), v;
        conj u, conj v, (c : ℂ)] := by
  have hH' := Matrix.IsHermitian.ext_iff.mp hH
  have h00 : H 0 0 = ((H 0 0).re : ℂ) :=
    (Complex.conj_eq_iff_re.mp (hH' 0 0)).symm
  have h11 : H 1 1 = ((H 1 1).re : ℂ) :=
    (Complex.conj_eq_iff_re.mp (hH' 1 1)).symm
  have h22 : H 2 2 = ((H 2 2).re : ℂ) :=
    (Complex.conj_eq_iff_re.mp (hH' 2 2)).symm
  refine ⟨(H 0 0).re, (H 1 1).re, (H 2 2).re, H 0 1, H 0 2, H 1 2, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · simpa using h00
  · rfl
  · rfl
  · simpa using (hH' 1 0).symm
  · simpa using h11
  · rfl
  · simpa using (hH' 2 0).symm
  · simpa using (hH' 2 1).symm
  · simpa using h22

theorem determinant_pencil_general (a b c : ℝ) (z u v : ℂ) (t : ℝ) :
    (D + (t : ℂ) •
        !![(a : ℂ), z, u; conj z, (b : ℂ), v;
          conj u, conj v, (c : ℂ)]).det =
      -(t : ℂ) * (c : ℂ) +
        (t : ℂ) ^ 2 *
          ((b : ℂ) * (c : ℂ) - (a : ℂ) * (c : ℂ) +
            conj u * u - conj v * v) +
        (t : ℂ) ^ 3 *
          ((a : ℂ) * (b : ℂ) * (c : ℂ) -
            (a : ℂ) * (conj v * v) -
            (b : ℂ) * (conj u * u) + z * v * conj u +
            conj z * conj v * u - (c : ℂ) * (z * conj z)) := by
  rw [Matrix.det_fin_three]
  simp [D, Matrix.add_apply, Matrix.smul_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  ring

theorem hermitianMatrix_det (a b : ℝ) (z u v : ℂ) :
    (hermitianMatrix a b z u v).det =
      -(a : ℂ) * (conj v * v) - (b : ℂ) * (conj u * u) +
        z * v * conj u + conj z * conj v * u := by
  rw [Matrix.det_fin_three]
  simp [hermitianMatrix, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]
  ring

theorem shear_identity (a b : ℝ) (p u : ℂ)
    (hsum : (a + b : ℂ) = conj p * u + p * conj u) :
    (shear p)ᴴ * hermitianMatrix a b (p * u) u (conj u) * shear p =
      !![(a : ℂ), 0, u; 0, (-a : ℂ), conj u; conj u, u, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shear, hermitianMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_three, hsum, mul_add, add_mul,
      sub_eq_add_neg]
  all_goals try ring
  · calc
      (b : ℂ) - conj p * u - conj u * p =
          (b : ℂ) - (conj p * u + p * conj u) := by ring
      _ = -(a : ℂ) := by rw [← hsum]; ring

theorem final_unitary_identity (a : ℝ) (x y : ℝ) :
    (finalUnitary)ᴴ *
        !![(a : ℂ), 0, (x + Complex.I * y : ℂ);
          0, (-a : ℂ), (x - Complex.I * y : ℂ);
          (x - Complex.I * y : ℂ), (x + Complex.I * y : ℂ), 0] *
        finalUnitary =
      Complex.I •
        !![(0 : ℂ), (a : ℂ), (Real.sqrt 2 * x : ℂ);
          (-a : ℂ), 0, (Real.sqrt 2 * y : ℂ);
          (-Real.sqrt 2 * x : ℂ), (-Real.sqrt 2 * y : ℂ), 0] := by
  have hr : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by norm_num
  have hrC : (Real.sqrt 2 : ℂ) ^ 2 = (2 : ℂ) := by exact_mod_cast hr
  have hr0 : Real.sqrt 2 ≠ 0 := by positivity
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [finalUnitary, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_three, Complex.conj_ofReal, hr0,
      div_eq_mul_inv, sub_eq_add_neg]
  all_goals field_simp [hr0] <;> ring_nf <;> simp [hrC]

theorem finalUnitary_isUnit : IsUnit (finalUnitary : M) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  apply isUnit_iff_ne_zero.mpr
  have hr0 : Real.sqrt 2 ≠ 0 := by positivity
  simp [finalUnitary, Matrix.det_fin_three, div_eq_mul_inv, hr0]
  field_simp [hr0]
  norm_num

theorem zero_graph_common_kernel
    (K : Submodule ℝ M)
    (hzero : ∀ H ∈ K, H 0 2 = 0 ∧ H 1 2 = 0 ∧ H 2 2 = 0) :
    ∃ v : Fin 3 → ℂ, v ≠ 0 ∧ ∀ H ∈ K, H *ᵥ v = 0 := by
  refine ⟨e3, ?_, ?_⟩
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp [e3] at h0 h1 h2
  · intro H hH
    ext i
    fin_cases i
    · convert (hzero H hH).1 using 1 <;>
        simp [Matrix.mulVec, e3, Fin.sum_univ_three, Matrix.vecHead,
          Matrix.vecTail]
    · convert (hzero H hH).2.1 using 1 <;>
        simp [Matrix.mulVec, e3, Fin.sum_univ_three, Matrix.vecHead,
          Matrix.vecTail]
    · convert (hzero H hH).2.2 using 1 <;>
        simp [Matrix.mulVec, e3, Fin.sum_univ_three, Matrix.vecHead,
          Matrix.vecTail]

theorem universal_coefficient_constraints
    (K : Submodule ℝ M)
    (hD : D ∈ K)
    (hHerm : ∀ H : M, H ∈ K → H.IsHermitian)
    (hSing : ∀ H : M, H ∈ K → H.det = 0) :
    ∀ H ∈ K, H 2 2 = 0 ∧ conj (H 0 2) * H 0 2 = conj (H 1 2) * H 1 2 := by
  intro H hH
  obtain ⟨a, b, c, z, u, v, rfl⟩ := hermitian_coordinates (hHerm H hH)
  let q : ℂ := (b : ℂ) * (c : ℂ) - (a : ℂ) * (c : ℂ) +
    conj u * u - conj v * v
  let r : ℂ := (a : ℂ) * (b : ℂ) * (c : ℂ) -
    (a : ℂ) * (conj v * v) - (b : ℂ) * (conj u * u) +
      z * v * conj u + conj z * conj v * u - (c : ℂ) * (z * conj z)
  have hdet (t : ℝ) :
      (D + t •
          (!![(a : ℂ), z, u; conj z, (b : ℂ), v;
            conj u, conj v, (c : ℂ)] : M)).det = 0 := by
    apply hSing
    exact K.add_mem hD (K.smul_mem t hH)
  have hp (t : ℝ) :
      -(t : ℂ) * (c : ℂ) + (t : ℂ) ^ 2 * q + (t : ℂ) ^ 3 * r = 0 := by
    have ht := hdet t
    have hsmul :
        (t : ℝ) •
            (!![(a : ℂ), z, u; conj z, (b : ℂ), v;
              conj u, conj v, (c : ℂ)] : M) =
          (t : ℂ) •
            (!![(a : ℂ), z, u; conj z, (b : ℂ), v;
              conj u, conj v, (c : ℂ)] : M) := by
      ext i j
      simp [Matrix.smul_apply, smul_eq_mul]
    rw [hsmul, determinant_pencil_general] at ht
    exact ht
  have h1 := hp 1
  have hm1 := hp (-1)
  have h2 := hp 2
  have hm2 := hp (-2)
  norm_num at h1 hm1 h2 hm2
  have hq : q = 0 := by
    linear_combination (h1 + hm1) / 2
  have hcr : (c : ℂ) - r = 0 := by
    linear_combination (hm1 - h1) / 2
  have hcC : (c : ℂ) = 0 := by
    have h6 : (6 : ℂ) * (c : ℂ) = 0 := by
      linear_combination h2 - 4 * hq + 8 * hcr
    exact (mul_eq_zero.mp h6).resolve_left (by norm_num)
  have hc : c = 0 := by exact_mod_cast hcC
  have huv : conj u * u = conj v * v := by
    have hq' := hq
    simp [q, hc] at hq'
    exact sub_eq_zero.mp hq'
  exact ⟨by simp [hc], huv⟩

theorem universal_faithful_coordinate_representation
    (K : Submodule ℝ M)
    (hD : D ∈ K)
    (hHerm : ∀ H : M, H ∈ K → H.IsHermitian)
    (hSing : ∀ H : M, H ∈ K → H.det = 0) :
    ∀ H ∈ K, ∃ a b : ℝ, ∃ z u v : ℂ,
      H = hermitianMatrix a b z u v ∧
        conj u * u = conj v * v ∧
        ((a + b : ℝ) : ℂ) * (conj u * u) =
          z * v * conj u + conj z * conj v * u := by
  intro H hH
  obtain ⟨a, b, c, z, u, v, hcoord⟩ := hermitian_coordinates (hHerm H hH)
  have hconstraints := universal_coefficient_constraints K hD hHerm hSing H hH
  have hc : c = 0 := by
    have hcC := congrArg Complex.re hconstraints.1
    simpa [hcoord] using hcC
  have hcoord0 : H = hermitianMatrix a b z u v := by
    rw [hcoord]
    simp [hermitianMatrix, hc]
  have huv : conj u * u = conj v * v := by
    simpa [hcoord] using hconstraints.2
  have hdetH : (hermitianMatrix a b z u v).det = 0 := by
    rw [← hcoord0]
    exact hSing H hH
  rw [hermitianMatrix_det] at hdetH
  rw [← huv] at hdetH
  refine ⟨a, b, z, u, v, hcoord0, huv, ?_⟩
  rw [Complex.ofReal_add]
  linear_combination -hdetH

/-- One phase and one orientation work simultaneously for the whole real
submodule, including when its coefficient image has dimension zero or one. -/
theorem universal_common_graph_orientation
    (K : Submodule ℝ M)
    (hD : D ∈ K)
    (hHerm : ∀ H : M, H ∈ K → H.IsHermitian)
    (hSing : ∀ H : M, H ∈ K → H.det = 0) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      ((∀ H ∈ K, H 1 2 = c * H 0 2) ∨
        (∀ H ∈ K, H 1 2 = c * conj (H 0 2))) := by
  let u : K →ₗ[ℝ] ℂ :=
    { toFun := fun H => (H : M) 0 2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let v : K →ₗ[ℝ] ℂ :=
    { toFun := fun H => (H : M) 1 2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hnorm (H : K) : ‖u H‖ = ‖v H‖ := by
    have h := (universal_coefficient_constraints K hD hHerm hSing H H.property).2
    have hsq := congrArg Complex.re h
    simp only [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq] at hsq
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  have hker : LinearMap.ker u ≤ LinearMap.ker v := by
    intro H hH
    rw [LinearMap.mem_ker] at hH ⊢
    apply norm_eq_zero.mp
    rw [← hnorm H, hH, norm_zero]
  let L : LinearMap.range u →ₗ[ℝ] ℂ :=
    ((LinearMap.ker u).liftQ v hker).comp u.quotKerEquivRange.symm.toLinearMap
  have hL (H : K) : L ⟨u H, LinearMap.mem_range_self u H⟩ = v H := by
    change ((LinearMap.ker u).liftQ v hker)
      (u.quotKerEquivRange.symm ⟨u H, LinearMap.mem_range_self u H⟩) = v H
    rw [u.quotKerEquivRange_symm_apply_image]
    exact Submodule.liftQ_apply _ _ _
  let Li : LinearMap.range u →ₗᵢ[ℝ] ℂ :=
    { L with
      norm_map' := by
        rintro ⟨x, H, rfl⟩
        rw [hL]
        exact (hnorm H).symm }
  let E : ℂ ≃ₗᵢ[ℝ] ℂ := Li.extend.toLinearIsometryEquiv rfl
  have hE (H : K) : E (u H) = v H := by
    change Li.extend (u H) = v H
    rw [LinearIsometry.extend_apply Li ⟨u H, LinearMap.mem_range_self u H⟩]
    exact hL H
  obtain ⟨c, hc | hc⟩ := linear_isometry_complex E
  · refine ⟨c, Circle.norm_coe c, Or.inl ?_⟩
    intro H hH
    have h := hE ⟨H, hH⟩
    rw [hc, rotation_apply] at h
    exact h.symm
  · refine ⟨c, Circle.norm_coe c, Or.inr ?_⟩
    intro H hH
    have h := hE ⟨H, hH⟩
    rw [hc] at h
    exact h.symm

/-- The complex-linear orientation gives one of the first two geometric
alternatives, without a lower bound on the graph image dimension. -/
theorem linear_graph_common_kernel_or_neutral_plane
    (K : Submodule ℝ M)
    (hD : D ∈ K)
    (hHerm : ∀ H : M, H ∈ K → H.IsHermitian)
    (hSing : ∀ H : M, H ∈ K → H.det = 0)
    (c : ℂ) (hc : ‖c‖ = 1)
    (hgraph : ∀ H ∈ K, H 1 2 = c * H 0 2) :
    (∃ v : Fin 3 → ℂ, v ≠ 0 ∧ ∀ H ∈ K, H *ᵥ v = 0) ∨
    (∃ W : Submodule ℂ (Fin 3 → ℂ), Module.finrank ℂ W = 2 ∧
      ∀ H ∈ K, ∀ w ∈ W, ∀ w' ∈ W,
        star w ⬝ᵥ (H *ᵥ w') = 0) := by
  classical
  by_cases hzero : ∀ H ∈ K, H 0 2 = 0
  · left
    apply zero_graph_common_kernel K
    intro H hH
    exact ⟨hzero H hH, by rw [hgraph H hH, hzero H hH, mul_zero],
      (universal_coefficient_constraints K hD hHerm hSing H hH).1⟩
  · right
    push_neg at hzero
    obtain ⟨H₀, hH₀, hu₀⟩ := hzero
    have hcprod : conj c * c = 1 := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hc]
      norm_num
    have hcprod' : c * conj c = 1 := by simpa [mul_comm] using hcprod
    have hpoint (H : M) (hH : H ∈ K) (hu : H 0 2 ≠ 0) :
        H 0 0 + H 1 1 - H 0 1 * c - conj (H 0 1) * conj c = 0 := by
      obtain ⟨a, b, z, u, v, hcoord, _, he⟩ :=
        universal_faithful_coordinate_representation K hD hHerm hSing H hH
      have hv : v = c * u := by simpa [hcoord, hermitianMatrix] using hgraph H hH
      have hune : u ≠ 0 := by simpa [hcoord, hermitianMatrix] using hu
      have hnorm : conj u * u ≠ 0 := mul_ne_zero (by simpa using hune) hune
      have he' : ((a : ℂ) + (b : ℂ) - z * c - conj z * conj c) *
          (conj u * u) = 0 := by
        rw [hv, map_mul, Complex.ofReal_add] at he
        linear_combination he
      have hsum := (mul_eq_zero.mp he').resolve_right hnorm
      simpa [hcoord, hermitianMatrix] using hsum
    have htrace (H : M) (hH : H ∈ K) :
        H 0 0 + H 1 1 - H 0 1 * c - conj (H 0 1) * conj c = 0 := by
      by_cases hu : H 0 2 = 0
      · have hp := hpoint H₀ hH₀ hu₀
        have hsum : (H + H₀) 0 2 ≠ 0 := by
          simpa only [Matrix.add_apply, hu, zero_add] using hu₀
        have he := hpoint (H + H₀) (K.add_mem hH hH₀) hsum
        simp only [Matrix.add_apply, map_add] at he
        linear_combination he - hp
      · exact hpoint H hH hu
    apply CommonCoefficientPlane.phase_plane (K : Set M) (-c)
    intro H hH
    have hHerm' := Matrix.IsHermitian.ext_iff.mp (hHerm H hH)
    have h10 : H 1 0 = conj (H 0 1) := (hHerm' 1 0).symm
    have h20 : H 2 0 = conj (H 0 2) := (hHerm' 2 0).symm
    have h21 : H 2 1 = conj (H 1 2) := (hHerm' 2 1).symm
    refine ⟨hHerm H hH,
      (universal_coefficient_constraints K hD hHerm hSing H hH).1, ?_, ?_⟩
    · rw [h20, h21, hgraph H hH, map_mul]
      linear_combination -(conj (H 0 2)) * hcprod'
    · rw [CommonCoefficientPlane.phaseVector_quad, h10]
      simp only [map_neg, Complex.star_def]
      linear_combination htrace H hH + H 1 1 * hcprod

/-- A conjugate orientation with proper real coordinate image reduces to a
complex-linear orientation, including the zero image. -/
theorem conjugate_graph_proper_image_common_kernel_or_neutral_plane
    (K : Submodule ℝ M)
    (hD : D ∈ K)
    (hHerm : ∀ H : M, H ∈ K → H.IsHermitian)
    (hSing : ∀ H : M, H ∈ K → H.det = 0)
    (c : ℂ) (hc : ‖c‖ = 1)
    (hgraph : ∀ H ∈ K, H 1 2 = c * conj (H 0 2))
    (hnotonto : ¬ ∀ u : ℂ, ∃ H ∈ K, H 0 2 = u) :
    (∃ v : Fin 3 → ℂ, v ≠ 0 ∧ ∀ H ∈ K, H *ᵥ v = 0) ∨
    (∃ W : Submodule ℂ (Fin 3 → ℂ), Module.finrank ℂ W = 2 ∧
      ∀ H ∈ K, ∀ w ∈ W, ∀ w' ∈ W,
        star w ⬝ᵥ (H *ᵥ w') = 0) := by
  classical
  by_cases hzero : ∀ H ∈ K, H 0 2 = 0
  · apply linear_graph_common_kernel_or_neutral_plane K hD hHerm hSing c hc
    intro H hH
    simp only [hgraph H hH, hzero H hH, map_zero, mul_zero]
  · push Not at hzero
    obtain ⟨H₀, hH₀, hu₀⟩ := hzero
    let u : K →ₗ[ℝ] ℂ :=
      { toFun := fun H => (H : M) 0 2
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hproper : LinearMap.range u ≠ ⊤ := by
      intro htop
      apply hnotonto
      intro z
      have hz : z ∈ LinearMap.range u := by rw [htop]; exact Submodule.mem_top
      obtain ⟨H, hH⟩ := hz
      exact ⟨H, H.property, hH⟩
    have hnonzero : LinearMap.range u ≠ ⊥ := by
      intro hbot
      have hmem := LinearMap.mem_range_self u ⟨H₀, hH₀⟩
      rw [hbot, Submodule.mem_bot] at hmem
      exact hu₀ hmem
    have hdim : Module.finrank ℝ (LinearMap.range u) = 1 := by
      have hlt := Submodule.finrank_lt hproper
      rw [Complex.finrank_real_complex] at hlt
      have hpos := Submodule.one_le_finrank_iff.mpr hnonzero
      omega
    have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hdim
      (LinearMap.mem_range_self u ⟨H₀, hH₀⟩) hu₀
    have hline (H : M) (hH : H ∈ K) :
        ∃ t : ℝ, (t : ℂ) * H₀ 0 2 = H 0 2 := by
      have hmem := LinearMap.mem_range_self u ⟨H, hH⟩
      rw [hspan] at hmem
      exact Submodule.mem_span_singleton.mp hmem
    let d : ℂ := c * conj (H₀ 0 2) / H₀ 0 2
    have hd : ‖d‖ = 1 := by
      dsimp [d]
      rw [norm_div, norm_mul, hc, Complex.norm_conj, one_mul,
        div_self (norm_ne_zero_iff.mpr hu₀)]
    apply linear_graph_common_kernel_or_neutral_plane K hD hHerm hSing d hd
    intro H hH
    obtain ⟨t, ht⟩ := hline H hH
    rw [hgraph H hH, ← ht, map_mul, Complex.conj_ofReal]
    dsimp [d]
    field_simp [hu₀]

def normalizedGraphTrichotomy : Prop :=
  ∀ (K : Submodule ℝ M), D ∈ K →
    (∀ H : M, H ∈ K → H.IsHermitian) →
    (∀ H : M, H ∈ K → H.det = 0) →
    (∃ v : Fin 3 → ℂ, v ≠ 0 ∧ ∀ H ∈ K, H *ᵥ v = 0) ∨
    (∃ W : Submodule ℂ (Fin 3 → ℂ), Module.finrank ℂ W = 2 ∧
      ∀ H ∈ K, ∀ w ∈ W, ∀ w' ∈ W,
        star w ⬝ᵥ (H *ᵥ w') = 0) ∨
    (∃ C : M, IsUnit C ∧
      ∀ H, H ∈ K ↔ Cᴴ * H * C ∈ (iSkew3 : Set M))

private theorem surjective_cubic_graph_rigidity
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (u z : V →ₗ[ℝ] ℂ) (s : V →ₗ[ℝ] ℝ)
    (hu : Function.Surjective u)
    (h : ∀ X, s X * ((u X).re ^ 2 + (u X).im ^ 2) =
      2 * (z X).re * ((u X).re ^ 2 - (u X).im ^ 2) +
        4 * (z X).im * (u X).re * (u X).im) :
    ∃ p : ℂ, ∀ X, z X = p * u X ∧
      s X = 2 * (p.re * (u X).re + p.im * (u X).im) := by
  obtain ⟨A, hA⟩ := hu 1
  obtain ⟨B, hB⟩ := hu Complex.I
  have h1 := h A
  have hi := h B
  have hp := h (A + B)
  have hm := h (A - B)
  simp [hA] at h1
  simp [hB] at hi
  simp [map_add, hA, hB] at hp
  simp [map_sub, hA, hB] at hm
  have hzB : z B = Complex.I * z A := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> linarith
  have hi' : s B = 2 * (z A).im := by simpa [hzB] using hi
  have hker (X : V) (hX : u X = 0) : z X = 0 ∧ s X = 0 := by
    have hXA := h (X + A)
    have hXB := h (X + B)
    have hXAB := h (X + (A + B))
    simp [map_add, hX, hA] at hXA
    simp [map_add, hX, hB] at hXB
    simp [map_add, hX, hA, hB] at hXAB
    have hs : s X = 0 := by linarith
    refine ⟨?_, hs⟩
    apply Complex.ext <;> simp <;> linarith
  refine ⟨z A, ?_⟩
  intro X
  let Q := X - (u X).re • A - (u X).im • B
  have huQ : u Q = 0 := by
    apply Complex.ext <;>
      simp [Q, map_sub, map_smul, hA, hB, Complex.real_smul]
  obtain ⟨hzQ, hsQ⟩ := hker Q huQ
  have hzQr := congrArg Complex.re hzQ
  have hzQi := congrArg Complex.im hzQ
  simp [Q, map_sub, map_smul, hzB, Complex.real_smul] at hzQr hzQi hsQ
  constructor
  · apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> linarith
  · rw [h1, hi'] at hsQ
    linarith

private theorem surjective_conjugate_graph_coefficients
    (K : Submodule ℝ M)
    (hD : D ∈ K)
    (hHerm : ∀ H : M, H ∈ K → H.IsHermitian)
    (hSing : ∀ H : M, H ∈ K → H.det = 0)
    (c : ℂ)
    (hgraph : ∀ H ∈ K, H 1 2 = c * conj (H 0 2))
    (honto : ∀ u : ℂ, ∃ H ∈ K, H 0 2 = u) :
    ∃ p : ℂ, ∀ H ∈ K,
      c * H 0 1 = p * H 0 2 ∧
        ((H 0 0).re + (H 1 1).re : ℂ) =
          conj p * H 0 2 + p * conj (H 0 2) := by
  let u : K →ₗ[ℝ] ℂ :=
    { toFun := fun H => (H : M) 0 2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let z : K →ₗ[ℝ] ℂ :=
    { toFun := fun H => c * (H : M) 0 1
      map_add' := by intros; simp [mul_add]
      map_smul' := by intros; simp [smul_eq_mul, mul_left_comm] }
  let s : K →ₗ[ℝ] ℝ :=
    { toFun := fun H => ((H : M) 0 0).re + ((H : M) 1 1).re
      map_add' := by intros; simp; ring
      map_smul' := by intros; simp [Complex.real_smul, mul_add] }
  have hu : Function.Surjective u := by
    intro w
    obtain ⟨H, hH, hw⟩ := honto w
    exact ⟨⟨H, hH⟩, hw⟩
  have heq (X : K) : s X * ((u X).re ^ 2 + (u X).im ^ 2) =
      2 * (z X).re * ((u X).re ^ 2 - (u X).im ^ 2) +
        4 * (z X).im * (u X).re * (u X).im := by
    obtain ⟨a, b, z₀, u₀, v₀, hcoord, _, hcoef⟩ :=
      universal_faithful_coordinate_representation K hD hHerm hSing X X.property
    have hv : v₀ = c * conj u₀ := by
      simpa [hcoord, hermitianMatrix] using hgraph X X.property
    have hcubic : ((a + b : ℝ) : ℂ) * (conj u₀ * u₀) =
        (c * z₀) * conj u₀ ^ 2 + conj (c * z₀) * u₀ ^ 2 := by
      rw [hv] at hcoef
      convert hcoef using 1 <;> simp [map_mul, pow_two] <;> ring
    have hr := congrArg Complex.re hcubic
    simp [pow_two, Complex.mul_re, Complex.mul_im] at hr
    change (((X : M) 0 0).re + ((X : M) 1 1).re) *
        (((X : M) 0 2).re ^ 2 + ((X : M) 0 2).im ^ 2) =
      2 * (c * (X : M) 0 1).re *
        (((X : M) 0 2).re ^ 2 - ((X : M) 0 2).im ^ 2) +
      4 * (c * (X : M) 0 1).im * ((X : M) 0 2).re * ((X : M) 0 2).im
    rw [hcoord]
    simp [hermitianMatrix, Complex.mul_re, Complex.mul_im]
    linear_combination hr
  obtain ⟨p, hp⟩ := surjective_cubic_graph_rigidity u z s hu heq
  refine ⟨p, ?_⟩
  intro H hH
  obtain ⟨hz, hs⟩ := hp ⟨H, hH⟩
  refine ⟨hz, ?_⟩
  rw [← Complex.ofReal_add]
  change (((s ⟨H, hH⟩ : ℝ) : ℂ)) =
    conj p * u ⟨H, hH⟩ + p * conj (u ⟨H, hH⟩)
  rw [hs]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- A surjective conjugate coefficient graph gives the exact primitive space,
with one congruence matrix working for every ambient complex matrix. -/
theorem surjective_conjugate_graph_primitive
    (K : Submodule ℝ M)
    (hD : D ∈ K)
    (hHerm : ∀ H : M, H ∈ K → H.IsHermitian)
    (hSing : ∀ H : M, H ∈ K → H.det = 0)
    (c : ℂ) (hc : ‖c‖ = 1)
    (hgraph : ∀ H ∈ K, H 1 2 = c * conj (H 0 2))
    (honto : ∀ u : ℂ, ∃ H ∈ K, H 0 2 = u) :
    ∃ C : M, IsUnit C ∧
      ∀ H : M, H ∈ K ↔ Cᴴ * H * C ∈ (iSkew3 : Set M) := by
  obtain ⟨p, hp⟩ :=
    surjective_conjugate_graph_coefficients K hD hHerm hSing c hgraph honto
  have hc0 : c ≠ 0 := by
    intro h
    simpa [h] using hc
  have hcc : conj c * c = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self]
    simp [Complex.normSq_eq_norm_sq, hc]
  let P : M := !![1, 0, 0; 0, c, 0; 0, 0, 1]
  have hP : IsUnit P := by
    apply (Matrix.isUnit_iff_isUnit_det P).mpr
    simpa [P, Matrix.det_fin_three] using
      (isUnit_iff_ne_zero.mpr hc0 : IsUnit c)
  have hS : IsUnit (shear p) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    simp [shear, Matrix.det_fin_three]
  let C := P * shear p * finalUnitary
  have hC : IsUnit C := (hP.mul hS).mul finalUnitary_isUnit
  have hphase (a b : ℝ) (z u : ℂ) :
      Pᴴ * hermitianMatrix a b z u (c * conj u) * P =
        hermitianMatrix a b (c * z) u (conj u) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, hermitianMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_three]
    all_goals grind
  have hF (H : M) (hH : H ∈ K) :
      Cᴴ * H * C = Complex.I •
        !![0, ((H 0 0).re : ℂ), ((Real.sqrt 2 * (H 0 2).re : ℝ) : ℂ);
          (-(H 0 0).re : ℂ), 0, ((Real.sqrt 2 * (H 0 2).im : ℝ) : ℂ);
          -((Real.sqrt 2 * (H 0 2).re : ℝ) : ℂ),
          -((Real.sqrt 2 * (H 0 2).im : ℝ) : ℂ), 0] := by
    obtain ⟨a, b, z, u, v, hcoord, _, _⟩ :=
      universal_faithful_coordinate_representation K hD hHerm hSing H hH
    have hv : v = c * conj u := by
      simpa [hcoord, hermitianMatrix] using hgraph H hH
    obtain ⟨hz, hsum⟩ := hp H hH
    simp [hcoord, hermitianMatrix] at hz hsum
    have hphaseH : Pᴴ * H * P = hermitianMatrix a b (p * u) u (conj u) := by
      rw [hcoord, hv, hphase, hz]
    have hcomp : Cᴴ * H * C =
        finalUnitaryᴴ * ((shear p)ᴴ * (Pᴴ * H * P) * shear p) * finalUnitary := by
      simp [C, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    have hu : (u.re + Complex.I * u.im : ℂ) = u := by
      apply Complex.ext <;> simp
    have hconju : (u.re - Complex.I * u.im : ℂ) = conj u := by
      apply Complex.ext <;> simp
    have hnormal : Cᴴ * H * C = Complex.I •
        !![0, (a : ℂ), (Real.sqrt 2 * u.re : ℂ);
          (-a : ℂ), 0, (Real.sqrt 2 * u.im : ℂ);
          (-Real.sqrt 2 * u.re : ℂ), (-Real.sqrt 2 * u.im : ℂ), 0] := by
      rw [hcomp, hphaseH, shear_identity a b p u hsum]
      simpa only [hu, hconju] using final_unitary_identity a u.re u.im
    simpa [hcoord, hermitianMatrix] using hnormal
  refine ⟨C, hC, ?_⟩
  intro H
  constructor
  · intro hH
    exact ⟨(H 0 0).re, Real.sqrt 2 * (H 0 2).re,
      Real.sqrt 2 * (H 0 2).im, hF H hH⟩
  · rintro ⟨x, y, z, hH⟩
    have hr0 : Real.sqrt 2 ≠ 0 := by positivity
    let u : ℂ := (y / Real.sqrt 2 : ℝ) + Complex.I * (z / Real.sqrt 2 : ℝ)
    obtain ⟨H₀, hH₀, hu₀⟩ := honto u
    let G := H₀ + (x - (H₀ 0 0).re) • D
    have hG : G ∈ K := K.add_mem hH₀ (K.smul_mem _ hD)
    have ha : (G 0 0).re = x := by
      simp [G, D, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
    have hu : G 0 2 = u := by
      simp [G, D, Matrix.add_apply, Matrix.smul_apply, hu₀]
    have hy : Real.sqrt 2 * (G 0 2).re = y := by
      simp [hu, u]
      field_simp
    have hz : Real.sqrt 2 * (G 0 2).im = z := by
      simp [hu, u]
      field_simp
    have hGH : Cᴴ * G * C = Cᴴ * H * C := by
      rw [hF G hG, hH, ha, hy, hz]
    have hCstar : IsUnit Cᴴ := hC.star
    have hGeq : G = H := hCstar.mul_left_cancel (hC.mul_right_cancel hGH)
    exact hGeq ▸ hG

end D5.S3.Quantum.Algebra.NormalizedSingularHermitianKernel
