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
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic

noncomputable section
open Matrix Polynomial
open scoped BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Divergence.ResolventFunctionalRigidity

/-- The number of distinct positive samples needed to identify the residues
is at most the number of distinct spectral sites, including a possible zero site. -/
private theorem stieltjes_coefficients_zero {κ : Type*} [Fintype κ]
    (s : Finset ℝ) (c : ℝ → ℂ) (samples : κ → ℝ)
    (hs : ∀ z ∈ s, 0 ≤ z) (hpositive : ∀ k, 0 < samples k)
    (hinjective : Function.Injective samples) (hcard : s.card ≤ Fintype.card κ)
    (h : ∀ k, ∑ z ∈ s, ((z + samples k : ℝ) : ℂ)⁻¹ * c z = 0) :
    ∀ z ∈ s, c z = 0 := by
  classical
  by_cases hempty : s = ∅
  · simp [hempty]
  have hspos : 0 < s.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
  let P : ℂ[X] := ∑ z ∈ s, C (c z) * ∏ w ∈ s.erase z, (X + C (w : ℂ))
  have heval (k : κ) : P.eval (samples k : ℂ) = 0 := by
    let t := samples k
    have ht : 0 < t := hpositive k
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
    rw [heq, h k, mul_zero]
  have hdegree : P.natDegree ≤ s.card - 1 := by
    dsimp only [P]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro z hz
    have hprod := Polynomial.natDegree_prod_le (s.erase z)
      (fun w : ℝ => (X + C (w : ℂ) : ℂ[X]))
    have hprod' : (∏ w ∈ s.erase z, (X + C (w : ℂ) : ℂ[X])).natDegree ≤
        s.card - 1 := by
      simpa [Polynomial.natDegree_X_add_C, Finset.card_erase_of_mem hz] using hprod
    exact Polynomial.natDegree_mul_le.trans (by simpa using hprod')
  have hP : P = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P
      (Complex.ofReal_injective.comp hinjective) heval
    omega
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
private theorem finite_spectral_readout_rigidity {ι κ : Type*} [Fintype ι] [Fintype κ]
    (eig : ι → ℝ) (d : ι → ℂ) (heig : ∀ i, 0 ≤ eig i)
    (samples : κ → ℝ) (hpositive : ∀ k, 0 < samples k)
    (hinjective : Function.Injective samples)
    (hcard : (Finset.univ.image eig).card ≤ Fintype.card κ)
    (h : ∀ k, ∑ i, ((eig i + samples k : ℝ) : ℂ)⁻¹ * d i = 0)
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
  have hc : ∀ z ∈ s, c z = 0 := stieltjes_coefficients_zero s c samples
    (by intro z hz; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz; exact heig i)
    hpositive hinjective hcard
    (by intro k; rw [group]; exact h k)
  rw [← group]
  exact Finset.sum_eq_zero fun z hz => by rw [hc z hz, mul_zero]

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

theorem cfc_vector_expansion (A : Matrix n n ℂ) (hA : A.IsHermitian)
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
private theorem resolvents_determine_cfc {κ : Type*} [Fintype κ] (A : Matrix n n ℂ) (B : Matrix m m ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (V : Matrix n m ℂ)
    (a : n → ℂ) (b : m → ℂ)
    (samples : κ → ℝ) (hpositive : ∀ k, 0 < samples k)
    (hinjective : Function.Injective samples)
    (hcard : (Finset.univ.image
      (Sum.elim hA.isHermitian.eigenvalues hB.isHermitian.eigenvalues)).card ≤
        Fintype.card κ)
    (h : ∀ k, (A + samples k • (1 : Matrix n n ℂ))⁻¹ *ᵥ a =
      V *ᵥ ((B + samples k • (1 : Matrix m m ℂ))⁻¹ *ᵥ b)) (f : ℝ → ℝ) :
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
  have hr : ∀ k, ∑ j, ((eig j + samples k : ℝ) : ℂ)⁻¹ * d j = 0 := by
    intro k
    let t := samples k
    have ht : 0 < t := hpositive k
    have hx := congrFun (h k) i
    rw [← cfc_shift_inverse A hA t ht, ← cfc_shift_inverse B hB t ht] at hx
    simpa only [Complex.ofReal_inv] using (expansion (fun z => (z + t)⁻¹)).trans
      (sub_eq_zero.mpr hx)
  have hz := finite_spectral_readout_rigidity eig d
    (by intro j; cases j with
        | inl j => exact hA.eigenvalues_nonneg j
        | inr j => exact hB.eigenvalues_nonneg j)
    samples hpositive hinjective hcard hr (fun z => (f z : ℂ))
  rw [expansion f] at hz
  exact sub_eq_zero.mp hz

/-- A finite family of distinct positive shifts detects complete spectral
intertwining when it has at least as many points as the union of the two spectra.
Repeated eigenvalues and zero eigenvalues are allowed. -/
theorem finite_resolvent_defects_force_functional_intertwining {κ : Type*} [Fintype κ]
    (A : Matrix n n ℂ) (B : Matrix m m ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (V : Matrix n m ℂ) (hV : Vᴴ * V ≤ 1) (hAB : Vᴴ * A * V ≤ B)
    (b : m → ℂ)
    (hb : (star (V *ᵥ b) ⬝ᵥ (V *ᵥ b)).re = (star b ⬝ᵥ b).re)
    (samples : κ → ℝ) (hpositive : ∀ k, 0 < samples k)
    (hinjective : Function.Injective samples)
    (hcard : (Finset.univ.image
      (Sum.elim hA.isHermitian.eigenvalues hB.isHermitian.eigenvalues)).card ≤
        Fintype.card κ)
    (hzero : ∀ k,
      (star (V *ᵥ b) ⬝ᵥ ((A + samples k • (1 : Matrix n n ℂ))⁻¹ *ᵥ (V *ᵥ b))).re -
      (star b ⬝ᵥ ((B + samples k • (1 : Matrix m m ℂ))⁻¹ *ᵥ b)).re = 0)
    (f : ℝ → ℝ) : cfc f A *ᵥ (V *ᵥ b) = V *ᵥ (cfc f B *ᵥ b) := by
  apply resolvents_determine_cfc A B hA hB V (V *ᵥ b) b
    samples hpositive hinjective hcard
  intro k
  have hdefect :=
    D5.S3.Quantum.Divergence.ResolventDefectRigidity.resolvent_defect_identity_and_bound
      A B hA hB V hV hAB b hb (samples k) (hpositive k)
  have hz := hdefect.2.2.mp (hzero k)
  exact sub_eq_zero.mp hz.1

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
  classical
  let samples : Fin (Fintype.card (n ⊕ m)) → ℝ := fun k => (k.val : ℝ) + 1
  apply finite_resolvent_defects_force_functional_intertwining A B hA hB V hV hAB b hb
    samples (fun k => by dsimp only [samples]; positivity)
    (by intro i j hij
        apply Fin.ext
        have hval : (i.val : ℝ) = (j.val : ℝ) := add_right_cancel hij
        exact_mod_cast hval)
    (by
      have hbound := Finset.card_image_le
        (s := (Finset.univ : Finset (n ⊕ m)))
        (f := Sum.elim hA.isHermitian.eigenvalues hB.isHermitian.eigenvalues)
      simpa using hbound)
    (fun k => hzero (samples k) (by dsimp only [samples]; positivity)) f

#print axioms finite_resolvent_defects_force_functional_intertwining

#print axioms zero_resolvent_defects_force_functional_intertwining

end D5.S3.Quantum.Divergence.ResolventFunctionalRigidity
