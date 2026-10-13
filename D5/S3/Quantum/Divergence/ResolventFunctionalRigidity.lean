/- GID: D5/S3/Quantum/Divergence/ResolventFunctionalRigidity
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/ResolventFunctionalRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Zero resolvent defects determine the finite spectral calculus. -/

import D5.S3.Quantum.Divergence.ResolventDefectRigidity
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic

noncomputable section
open Matrix Polynomial
open scoped BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Divergence.ResolventFunctionalRigidity

/-- Clearing the common denominator turns a finite Stieltjes readout into a
polynomial; infinitely many positive samples then determine every residue. -/
private theorem stieltjes_coefficients_zero (s : Finset ℝ) (c : ℝ → ℂ)
    (hs : ∀ z ∈ s, 0 ≤ z)
    (h : ∀ t : ℝ, 0 < t → ∑ z ∈ s, ((z + t : ℝ) : ℂ)⁻¹ * c z = 0) :
    ∀ z ∈ s, c z = 0 := by
  classical
  let P : ℂ[X] := ∑ z ∈ s, C (c z) * ∏ w ∈ s.erase z, (X + C (w : ℂ))
  have heval (t : ℝ) (ht : 0 < t) : P.eval (t : ℂ) = 0 := by
    have hne (z : ℝ) (hz : z ∈ s) : ((z + t : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (add_pos_of_nonneg_of_pos (hs z hz) ht))
    have heq : P.eval (t : ℂ) =
        (∏ z ∈ s, ((z + t : ℝ) : ℂ)) *
          (∑ z ∈ s, ((z + t : ℝ) : ℂ)⁻¹ * c z) := by
      simp only [P, eval_finsetSum, eval_mul, eval_C, eval_prod, eval_add, eval_X]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      rw [← Finset.mul_prod_erase s (fun w : ℝ => ((w + t : ℝ) : ℂ)) hz]
      simp only [Complex.ofReal_add]
      have hp : (∏ x ∈ s.erase z, ((t : ℂ) + (x : ℂ))) =
          ∏ x ∈ s.erase z, ((x : ℂ) + (t : ℂ)) :=
        Finset.prod_congr rfl (fun x hx => add_comm _ _)
      rw [hp]
      have hh := hne z hz
      push_cast at hh
      field_simp [hh]
    rw [heq, h t ht, mul_zero]
  have hP : P = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply ((Set.Ioi_infinite (0 : ℝ)).image Complex.ofReal_injective.injOn).mono
    rintro _ ⟨t, ht, rfl⟩
    exact heval t ht
  intro z hz
  have hp := congrArg (fun p : ℂ[X] => p.eval (-(z : ℂ))) hP
  have hisolate : P.eval (-(z : ℂ)) = c z * ∏ w ∈ s.erase z, ((w - z : ℝ) : ℂ) := by
    simp only [P, eval_finsetSum, eval_mul, eval_C, eval_prod, eval_add, eval_X]
    rw [Finset.sum_eq_single z]
    · congr 1
      apply Finset.prod_congr rfl
      intro w hw
      push_cast
      ring
    · intro w hw hwz
      have hzmem : z ∈ s.erase w := Finset.mem_erase.mpr ⟨Ne.symm hwz, hz⟩
      have hzero : ∏ a ∈ s.erase w, (-(z : ℂ) + (a : ℂ)) = 0 :=
        Finset.prod_eq_zero hzmem (by ring)
      rw [hzero, mul_zero]
    · exact fun hn => (hn hz).elim
  rw [hisolate, eval_zero] at hp
  have hn : (∏ w ∈ s.erase z, ((w - z : ℝ) : ℂ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro w hw
    exact Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (Finset.ne_of_mem_erase hw))
  exact (mul_eq_zero.mp hp).resolve_right hn

/-- Group repeated eigenvalues before applying residue uniqueness. -/
private theorem finite_spectral_readout_rigidity {ι : Type*} [Fintype ι]
    (eig : ι → ℝ) (d : ι → ℂ) (heig : ∀ i, 0 ≤ eig i)
    (h : ∀ t : ℝ, 0 < t → ∑ i, ((eig i + t : ℝ) : ℂ)⁻¹ * d i = 0)
    (f : ℝ → ℂ) : ∑ i, f (eig i) * d i = 0 := by
  classical
  let s := Finset.univ.image eig
  let c := fun z : ℝ => ∑ i, if eig i = z then d i else 0
  have group (g : ℝ → ℂ) : ∑ z ∈ s, g z * c z = ∑ i, g (eig i) * d i := by
    simp only [c, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [mul_ite, mul_zero]
    simp [eq_comm, s]
  have hc : ∀ z ∈ s, c z = 0 := stieltjes_coefficients_zero s c
    (by intro z hz; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz; exact heig i)
    (by intro t ht; rw [group]; exact h t ht)
  rw [← group]
  exact Finset.sum_eq_zero fun z hz => by rw [hc z hz, mul_zero]

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

private theorem cfc_vector_expansion (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (f : ℝ → ℝ) (a : n → ℂ) (i : n) :
    (cfc f A *ᵥ a) i = ∑ j, (f (hA.eigenvalues j) : ℂ) *
      hA.eigenvectorUnitary i j * (hA.eigenvectorUnitaryᴴ *ᵥ a) j := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  simp only [← Matrix.mulVec_mulVec, Matrix.star_eq_conjTranspose]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Matrix.mulVec_diagonal, Function.comp_apply,
    RCLike.ofReal_eq_complex_ofReal]
  ring

theorem cfc_shift_inverse (A : Matrix n n ℂ) (hA : A.PosSemidef)
    (t : ℝ) (ht : 0 < t) :
    cfc (fun z : ℝ => (z + t)⁻¹) A = (A + t • (1 : Matrix n n ℂ))⁻¹ := by
  have hcont (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) :=
    A.finite_real_spectrum.continuousOn f
  have hne : ∀ z ∈ spectrum ℝ A, z + t ≠ 0 := by
    intro z hz
    rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hz
    obtain ⟨i, rfl⟩ := hz
    exact ne_of_gt (add_pos_of_nonneg_of_pos (hA.eigenvalues_nonneg i) ht)
  have heq : cfc (fun z : ℝ => z + t) A = A + t • (1 : Matrix n n ℂ) := by
    rw [cfc_add_const t (fun z : ℝ => z) A (hcont _) hA.isHermitian.isSelfAdjoint,
      cfc_id' ℝ A hA.isHermitian.isSelfAdjoint]
    rw [Algebra.algebraMap_eq_smul_one]
  rw [cfc_inv (fun z : ℝ => z + t) A hne (hcont _) hA.isHermitian.isSelfAdjoint, heq,
    ← Matrix.nonsing_inv_eq_ringInverse]

/-- Equality of the actual positive-shift resolvent vectors forces equality
for every real finite spectral function, with repeated spectra allowed. -/
private theorem resolvents_determine_cfc (A : Matrix n n ℂ) (B : Matrix m m ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (V : Matrix n m ℂ)
    (a : n → ℂ) (b : m → ℂ)
    (h : ∀ t : ℝ, 0 < t → (A + t • (1 : Matrix n n ℂ))⁻¹ *ᵥ a =
      V *ᵥ ((B + t • (1 : Matrix m m ℂ))⁻¹ *ᵥ b)) (f : ℝ → ℝ) :
    cfc f A *ᵥ a = V *ᵥ (cfc f B *ᵥ b) := by
  classical
  let eig : n ⊕ m → ℝ := Sum.elim hA.isHermitian.eigenvalues hB.isHermitian.eigenvalues
  ext i
  let d : n ⊕ m → ℂ := Sum.elim
    (fun j => hA.isHermitian.eigenvectorUnitary i j *
      (hA.isHermitian.eigenvectorUnitaryᴴ *ᵥ a) j)
    (fun k => -(∑ r, V i r * hB.isHermitian.eigenvectorUnitary r k *
      (hB.isHermitian.eigenvectorUnitaryᴴ *ᵥ b) k))
  have expansion (g : ℝ → ℝ) :
      ∑ j, (g (eig j) : ℂ) * d j =
        (cfc g A *ᵥ a) i - (V *ᵥ (cfc g B *ᵥ b)) i := by
    have hleft : (∑ j, (g (hA.isHermitian.eigenvalues j) : ℂ) *
        (hA.isHermitian.eigenvectorUnitary i j *
          (hA.isHermitian.eigenvectorUnitaryᴴ *ᵥ a) j)) = (cfc g A *ᵥ a) i := by
      rw [cfc_vector_expansion A hA.isHermitian]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have hright : (∑ k, (g (hB.isHermitian.eigenvalues k) : ℂ) *
        (∑ r, V i r * hB.isHermitian.eigenvectorUnitary r k *
          (hB.isHermitian.eigenvectorUnitaryᴴ *ᵥ b) k)) =
        (V *ᵥ (cfc g B *ᵥ b)) i := by
      change _ = ∑ r, V i r * (cfc g B *ᵥ b) r
      simp_rw [cfc_vector_expansion B hB.isHermitian, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro k hk
      ring
    simpa only [Fintype.sum_sum_type, eig, d, Sum.elim_inl, Sum.elim_inr,
      mul_neg, Finset.sum_neg_distrib, sub_eq_add_neg] using
      congrArg₂ (fun x y : ℂ => x - y) hleft hright
  have hr : ∀ t : ℝ, 0 < t → ∑ j, ((eig j + t : ℝ) : ℂ)⁻¹ * d j = 0 := by
    intro t ht
    have hx := congrFun (h t ht) i
    rw [← cfc_shift_inverse A hA t ht, ← cfc_shift_inverse B hB t ht] at hx
    simpa only [Complex.ofReal_inv] using (expansion (fun z => (z + t)⁻¹)).trans
      (sub_eq_zero.mpr hx)
  have hz := finite_spectral_readout_rigidity eig d
    (by intro j; cases j with
        | inl j => exact hA.eigenvalues_nonneg j
        | inr j => exact hB.eigenvalues_nonneg j)
    hr (fun z => (f z : ℂ))
  rw [expansion f] at hz
  exact sub_eq_zero.mp hz

/-- Zero comparison defect for every positive shift determines the entire
finite spectral calculus on the distinguished vector, rather than assuming
an intertwining identity or a recovery equation. -/
theorem zero_resolvent_defects_force_functional_intertwining
    (A : Matrix n n ℂ) (B : Matrix m m ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (V : Matrix n m ℂ) (hV : Vᴴ * V ≤ 1) (hAB : Vᴴ * A * V ≤ B)
    (b : m → ℂ)
    (hb : (star (V *ᵥ b) ⬝ᵥ (V *ᵥ b)).re = (star b ⬝ᵥ b).re)
    (hzero : ∀ t : ℝ, 0 < t →
      (star (V *ᵥ b) ⬝ᵥ ((A + t • (1 : Matrix n n ℂ))⁻¹ *ᵥ (V *ᵥ b))).re -
      (star b ⬝ᵥ ((B + t • (1 : Matrix m m ℂ))⁻¹ *ᵥ b)).re = 0)
    (f : ℝ → ℝ) : cfc f A *ᵥ (V *ᵥ b) = V *ᵥ (cfc f B *ᵥ b) := by
  apply resolvents_determine_cfc A B hA hB V (V *ᵥ b) b
  intro t ht
  have hdefect :=
    D5.S3.Quantum.Divergence.ResolventDefectRigidity.resolvent_defect_identity_and_bound
      A B hA hB V hV hAB b hb t ht
  have hz := hdefect.2.2.mp (hzero t ht)
  exact sub_eq_zero.mp hz.1

#print axioms zero_resolvent_defects_force_functional_intertwining

end D5.S3.Quantum.Divergence.ResolventFunctionalRigidity
