/- GID: D5/S3/VertexAlgebra/Energy/OriginalCurrentEnergy
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Energy/OriginalCurrentEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original Hermitian norm and uniform factorial current estimates. -/

import D5.S3.VertexAlgebra.SourceBPZ.TransverseHermitian
import D5.S3.VertexAlgebra.SourceBPZ.ChargedRawTranspose
import D5.S3.VertexAlgebra.LatticeActualStateFieldCalculus
import D5.S3.VertexAlgebra.LatticeActualLZeroGrading
import D5.S3.VertexAlgebra.Lattice.LatticeLightConeCoordinates
import D5.S3.VertexAlgebra.Energy.LatticeCoefficientEnergy
import D5.S3.VertexAlgebra.LatticeActualConformalState
import Mathlib.Data.Nat.Choose.Bounds

/-! The original Hermitian norm and uniform current estimates.

This support module retains the full-frame positivity proof and the exact
integer-frequency factorial estimates from OriginalChargedEnergy. Mixed colour
directions, all original charge sectors and the zero-current estimate are kept.
All moved estimates remain consumed proof components, with no new novelty claim.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators VertexOperator Matrix
open ComplexConjugate

namespace D5.S3.VertexAlgebra.Lattice.OriginalChargedEnergy

open LatticeGeneratingFieldLocality LatticeInvolution LatticePositiveEnergy
open SourceBPZ.OriginalMatterHermitian SourceBPZ.OriginalSourcePairing
open SourceBPZ.TransverseHermitian OriginalGram
open LatticeSugawaraCurrents LatticeAllStateField LatticeAllStateReconstruction
open LatticeActualGeneratorLocality
open private Hm_finsum_right Hm_finset_sum_left Hm_finset_sum_right from
  D5.S3.VertexAlgebra.SourceBPZ.OriginalMatterHermitian

variable {D : LatticeData}

private theorem full_frame_matrix (hD : (gramReal D).PosDef) :
    (RC D hD)ᵀ * gramComplex D * RC D hD = 1 := by
  have hG : (SC D hD)ᵀ * SC D hD = gramComplex D := by
    ext i j
    exact SC_gram D hD i j
  rw [← hG]
  calc
    _ = (SC D hD * RC D hD)ᵀ * (SC D hD * RC D hD) := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [SC_mul_RC]; simp

private def fullFrame (hD : (gramReal D).PosDef) : RealOrthonormalFrame D D.rank where
  B j i := RC D hD i j
  real_B j i := by simp [RC]
  orthonormal j k := by
    have h := congrFun (congrFun (full_frame_matrix hD) j) k
    change (∑ i, (∑ l, RC D hD l j * (D.G l i : ℂ)) * RC D hD i k) = _ at h
    rw [Matrix.one_apply] at h
    change (∑ i, ∑ l, RC D hD i j * (D.G i l : ℂ) * RC D hD l k) = _
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_mul] at h
    exact h

private def fullOscillatorEquiv (hD : (gramReal D).PosDef) :
    Oscillator D ≃ₐ[ℂ] Oscillator D :=
  OriginalCurrentMetric.substitutionEquiv
    (fun _ => RC D hD) (fun _ => SC D hD)
    (fun _ => RC_mul_SC D hD) (fun _ => SC_mul_RC D hD)

private theorem fullFrame_phi (hD : (gramReal D).PosDef) :
    phi (fullFrame hD) = (fullOscillatorEquiv hD).toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro x
  rfl

private theorem fullFrame_surjective (hD : (gramReal D).PosDef) :
    Function.Surjective (transverseEmbed (fullFrame hD)) := by
  intro v
  let x : Charge D →₀ Oscillator D :=
    v.mapRange (fullOscillatorEquiv hD).symm (map_zero _)
  refine ⟨x, ?_⟩
  apply Finsupp.ext
  intro a
  change phi (fullFrame hD) ((fullOscillatorEquiv hD).symm (v a)) = v a
  rw [fullFrame_phi]
  exact (fullOscillatorEquiv hD).apply_symm_apply (v a)

private theorem original_positive (hD : (gramReal D).PosDef) {v : Carrier D}
    (hv : v ≠ 0) : (Hm (D := D) v v).im = 0 ∧ 0 < (Hm (D := D) v v).re := by
  obtain ⟨x, rfl⟩ := fullFrame_surjective hD v
  apply Hm_self_strict_positive
  intro hx
  apply hv
  simp [hx, transverseEmbed]

private theorem original_nonnegative (hD : (gramReal D).PosDef) (v : Carrier D) :
    0 ≤ (Hm (D := D) v v).re := by
  by_cases hv : v = 0
  · subst v
    simp [Hm]
  · exact (original_positive hD hv).2.le

def normD (v : Carrier D) : ℝ := Real.sqrt (Hm (D := D) v v).re

private theorem normD_sq (hD : (gramReal D).PosDef) (v : Carrier D) :
    normD v ^ 2 = (Hm (D := D) v v).re :=
  Real.sq_sqrt (original_nonnegative hD v)

open private target target_creation rescale_monomial rescale_coeff frequencyAmplitude
  frequencyAmplitude_real frequencyAmplitude_square from
  D5.S3.VertexAlgebra.SourceBPZ.TransverseHermitian

private def fockInner {t : ℕ} (P Q : Polynomial t) : ℂ :=
  FactorialFockMetric.inner (rescale t P) (rescale t Q)

private def fockQ {t : ℕ} (P : Polynomial t) : ℝ := (fockInner P P).re

private theorem fockInner_coeff {t : ℕ} (P Q : Polynomial t) :
    fockInner P Q = ∑ e ∈ P.support,
      (exactWeight e : ℂ) * conj (P.coeff e) * Q.coeff e := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum P]
  simp only [fockInner, FactorialFockMetric.inner, map_sum, sum_inner]
  apply Finset.sum_congr rfl
  intro e he
  change FactorialFockMetric.inner (rescale t (MvPolynomial.monomial e (P.coeff e)))
    (rescale t Q) = _
  rw [rescale_monomial, FactorialFockMetric.inner_monomial_left,
    rescale_coeff, map_mul, frequencyAmplitude_real]
  calc
    _ = (FactorialFockMetric.weight e : ℂ) *
        (frequencyAmplitude e * frequencyAmplitude e) * conj (P.coeff e) * Q.coeff e := by ring
    _ = _ := by rw [frequencyAmplitude_square]; simp only [exactWeight, Nat.cast_mul]

private theorem fockQ_coeff {t : ℕ} (P : Polynomial t) :
    fockQ P = ∑ e ∈ P.support, (exactWeight e : ℝ) * Complex.normSq (P.coeff e) := by
  rw [fockQ, fockInner, rescaled_inner_coeff_sum]
  simp

private def frequencyNumber {t : ℕ} (r : ℕ) (P : Polynomial t) : Polynomial t :=
  ∑ i : Fin t, ((r : ℂ) + 1) • (MvPolynomial.X (i,r) * MvPolynomial.pderiv (i,r) P)

private theorem frequencyNumber_coeff {t : ℕ} (r : ℕ) (P : Polynomial t)
    (e : Occupation t) :
    (frequencyNumber r P).coeff e =
      ((∑ i : Fin t, e (i,r) * (r+1) : ℕ) : ℂ) * P.coeff e := by
  classical
  have hx (i : Fin t) :
      (MvPolynomial.X (i,r) * MvPolynomial.pderiv (i,r) P).coeff e =
        (e (i,r) : ℂ) * P.coeff e := by
    induction P using MvPolynomial.induction_on' with
    | monomial d c =>
      rw [MvPolynomial.X_mul_pderiv_monomial]
      rw [MvPolynomial.coeff_smul]
      by_cases h : d = e
      · subst d; simp
      · simp [MvPolynomial.coeff_monomial, h]
    | add P Q hP hQ => simp [mul_add, hP, hQ]
  simp only [frequencyNumber, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, hx,
    smul_eq_mul, Nat.cast_sum, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem frequency_occupation_le {t : ℕ} (r : ℕ) (e : Occupation t) :
    ∑ i : Fin t, e (i,r) * (r+1) ≤
      Finsupp.weight (fun x : Fin t × ℕ => x.2+1) e := by
  classical
  let s : Finset (Fin t × ℕ) := Finset.univ ×ˢ {r}
  let f : Fin t × ℕ → ℕ := fun x => e x * (x.2+1)
  have hs : (∑ x ∈ s, f x) = ∑ i : Fin t, e (i,r) * (r+1) := by
    simp [s, f]
  have he : (∑ x ∈ e.support ∪ s, f x) =
      Finsupp.weight (fun x : Fin t × ℕ => x.2+1) e := by
    rw [Finsupp.weight_apply]
    change _ = ∑ x ∈ e.support, e x * (x.2+1)
    symm
    apply Finset.sum_subset (Finset.subset_union_left)
    intro x hx hxe
    simp [Finsupp.notMem_support_iff.mp hxe]
  rw [← hs, ← he]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right (by
    intro x _ _; exact Nat.zero_le _)

private theorem fock_derivative_sum {t : ℕ} (r : ℕ) (P : Polynomial t) :
    (∑ i : Fin t, fockQ (((r : ℂ)+1) • MvPolynomial.pderiv (i,r) P)) =
      ∑ e ∈ P.support, (exactWeight e : ℝ) * Complex.normSq (P.coeff e) *
        (∑ i : Fin t, e (i,r) * (r+1) : ℕ) := by
  classical
  have ha (i : Fin t) :
      fockQ (((r : ℂ)+1) • MvPolynomial.pderiv (i,r) P) =
        (fockInner (MvPolynomial.X (i,r) *
          (((r : ℂ)+1) • MvPolynomial.pderiv (i,r) P)) P).re := by
    have h := target_creation (((r : ℂ)+1) • MvPolynomial.pderiv (i,r) P) P i r
    change fockInner _ _ = ((r : ℂ)+1) *
      fockInner (((r : ℂ)+1) • MvPolynomial.pderiv (i,r) P)
        (MvPolynomial.pderiv (i,r) P) at h
    rw [h]
    simp only [fockQ, fockInner, FactorialFockMetric.inner, map_smul,
      inner_smul_left, inner_smul_right]
  simp_rw [ha]
  have he : (∑ i : Fin t, fockInner (MvPolynomial.X (i,r) *
      (((r : ℂ)+1) • MvPolynomial.pderiv (i,r) P)) P) =
      fockInner (frequencyNumber r P) P := by
    simp only [frequencyNumber, fockInner, FactorialFockMetric.inner, map_sum,
      mul_smul_comm, sum_inner]
  rw [← Complex.re_sum, he]
  have hc : conj (fockInner P (frequencyNumber r P)) =
      fockInner (frequencyNumber r P) P := inner_conj_symm _ _
  rw [← hc, Complex.conj_re, fockInner_coeff]
  rw [Complex.re_sum]
  simp only [frequencyNumber_coeff]
  apply Finset.sum_congr rfl
  intro e he
  rw [Complex.normSq_apply]
  simp [Complex.mul_re, Complex.mul_im]
  ring

private theorem fock_derivative_sum_le {t : ℕ} (r F : ℕ) (P : Polynomial t)
    (hP : ∀ e ∈ P.support, Finsupp.weight (fun x : Fin t × ℕ => x.2+1) e ≤ F) :
    (∑ i : Fin t, fockQ (((r : ℂ)+1) • MvPolynomial.pderiv (i,r) P)) ≤
      (F : ℝ) * fockQ P := by
  rw [fock_derivative_sum, fockQ_coeff, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  have hf : ((∑ i : Fin t, e (i,r) * (r+1) : ℕ) : ℝ) ≤ F := by
    exact_mod_cast (frequency_occupation_le r e).trans (hP e he)
  have hp : 0 ≤ (exactWeight e : ℝ) * Complex.normSq (P.coeff e) :=
    mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
  nlinarith

private def fockEmbedding (t : ℕ) : Polynomial t →ₗ[ℂ] FactorialFockMetric.Hilbert (Fin t × ℕ) :=
  (FactorialFockMetric.embedding (Fin t × ℕ)).comp (rescale t).toLinearMap

private theorem fockQ_norm {t : ℕ} (P : Polynomial t) :
    fockQ P = ‖fockEmbedding t P‖ ^ 2 := by
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) (fockEmbedding t P)).symm

private def fockD {t : ℕ} (a : Fin t → ℂ) (r : ℕ) :
    Derivation ℂ (Polynomial t) (Polynomial t) :=
  ∑ i : Fin t, conj (a i) • (((r : ℂ)+1) • MvPolynomial.pderiv (i,r))

private theorem fockD_apply {t : ℕ} (a : Fin t → ℂ) (r : ℕ) (P : Polynomial t) :
    fockD a r P = ∑ i : Fin t, conj (a i) •
      (((r : ℂ)+1) • MvPolynomial.pderiv (i,r) P) := by
  unfold fockD
  change (Derivation.coeFnAddMonoidHom _) P = _
  rw [map_sum]
  simp only [Finset.sum_apply, Derivation.coeFnAddMonoidHom_apply,
    Derivation.coe_smul, Pi.smul_apply]

set_option maxHeartbeats 4000000 in
-- Elaborating the finite Hilbert-space Cauchy--Schwarz application unfolds two linear maps.
private theorem fock_directional_annihilate_le {t : ℕ} (a : Fin t → ℂ)
    (r F : ℕ) (P : Polynomial t)
    (hP : ∀ e ∈ P.support, Finsupp.weight (fun x : Fin t × ℕ => x.2+1) e ≤ F) :
    fockQ (fockD a r P) ≤ (∑ i, Complex.normSq (a i)) * F * fockQ P := by
  classical
  let V (i : Fin t) := fockEmbedding t (((r : ℂ)+1) • MvPolynomial.pderiv (i,r) P)
  have hn : ‖fockEmbedding t (fockD a r P)‖ ≤ ∑ i : Fin t, ‖a i‖ * ‖V i‖ := by
    rw [fockD_apply, map_sum]
    simpa only [V, map_smul, norm_smul, Complex.norm_conj] using
      norm_sum_le Finset.univ (fun i : Fin t => conj (a i) • V i)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : Fin t => ‖a i‖) (fun i : Fin t => ‖V i‖)
  have hs : (∑ i : Fin t, ‖V i‖ ^ 2) ≤ (F : ℝ) * fockQ P := by
    simpa only [V, ← fockQ_norm] using fock_derivative_sum_le r F P hP
  rw [fockQ_norm]
  calc
    _ ≤ (∑ i : Fin t, ‖a i‖ * ‖V i‖) ^ 2 := by
      nlinarith [norm_nonneg (fockEmbedding t (fockD a r P)),
        Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => mul_nonneg (norm_nonneg (a i))
          (norm_nonneg (V i)))]
    _ ≤ (∑ i : Fin t, ‖a i‖ ^ 2) * ∑ i : Fin t, ‖V i‖ ^ 2 := hc
    _ ≤ (∑ i : Fin t, ‖a i‖ ^ 2) * ((F : ℝ) * fockQ P) :=
      mul_le_mul_of_nonneg_left hs (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ = _ := by simp only [Complex.normSq_eq_norm_sq]; ring

private def fockVariable {t : ℕ} (a : Fin t → ℂ) (r : ℕ) : Polynomial t :=
  ∑ i : Fin t, a i • MvPolynomial.X (i,r)

private theorem fock_directional_pairing {t : ℕ} (a : Fin t → ℂ) (r : ℕ)
    (P Q : Polynomial t) :
    fockInner (fockVariable a r * P) Q = fockInner P (fockD a r Q) := by
  classical
  have hx (i : Fin t) : fockInner (MvPolynomial.X (i,r) * P) Q =
      ((r : ℂ)+1) * fockInner P (MvPolynomial.pderiv (i,r) Q) :=
    target_creation P Q i r
  simp only [fockVariable, Finset.sum_mul, smul_mul_assoc, fockD_apply,
    fockInner, FactorialFockMetric.inner, map_sum, map_smul, sum_inner,
    inner_sum, inner_smul_left, inner_smul_right]
  change (∑ i : Fin t, conj (a i) * fockInner (MvPolynomial.X (i,r) * P) Q) =
    ∑ i : Fin t, conj (a i) * (((r : ℂ)+1) * fockInner P (MvPolynomial.pderiv (i,r) Q))
  simp only [hx]

private theorem fockD_variable {t : ℕ} (a : Fin t → ℂ) (r : ℕ) :
    fockD a r (fockVariable a r) =
      (((r : ℂ)+1) * ((∑ i : Fin t, Complex.normSq (a i) : ℝ) : ℂ)) •
        (1 : Polynomial t) := by
  classical
  rw [fockD_apply]
  have hd (i : Fin t) : MvPolynomial.pderiv (i,r) (fockVariable a r) =
      a i • (1 : Polynomial t) := by
    simp [fockVariable, MvPolynomial.pderiv_X, Pi.single_apply, Prod.mk.injEq,
      eq_comm]
  simp_rw [hd, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  simp only [Complex.ofReal_sum, Finset.mul_sum, Complex.normSq_eq_conj_mul_self]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem fock_creation_square {t : ℕ} (a : Fin t → ℂ) (r : ℕ) (P : Polynomial t) :
    fockQ (fockVariable a r * P) = fockQ (fockD a r P) +
      ((r : ℝ)+1) * (∑ i : Fin t, Complex.normSq (a i)) * fockQ P := by
  have hadj : fockInner P (fockVariable a r * fockD a r P) =
      fockInner (fockD a r P) (fockD a r P) := by
    have h := congrArg conj (fock_directional_pairing a r (fockD a r P) P)
    simpa only [fockInner, FactorialFockMetric.inner, inner_conj_symm] using h
  unfold fockQ
  rw [fock_directional_pairing, (fockD a r).leibniz, fockD_variable]
  have hm : P •
      (((((r : ℂ)+1) * ((∑ i : Fin t, Complex.normSq (a i) : ℝ) : ℂ))) •
        (1 : Polynomial t)) =
      (((r : ℂ)+1) * ((∑ i : Fin t, Complex.normSq (a i) : ℝ) : ℂ)) • P := by
    simp [smul_eq_mul]
  rw [hm]
  have he : fockInner P
      (fockVariable a r • fockD a r P +
        (((r : ℂ)+1) * ((∑ i : Fin t, Complex.normSq (a i) : ℝ) : ℂ)) • P) =
      fockInner P (fockVariable a r * fockD a r P) +
        (((r : ℂ)+1) * ((∑ i : Fin t, Complex.normSq (a i) : ℝ) : ℂ)) * fockInner P P := by
    rw [show fockVariable a r • fockD a r P = fockVariable a r * fockD a r P from
      smul_eq_mul _ _]
    simp only [fockInner, FactorialFockMetric.inner, map_add, map_smul,
      inner_add_right, inner_smul_right]
  rw [he, hadj]
  simp [Complex.mul_re, Complex.mul_im]

private theorem fock_directional_create_le {t : ℕ} (a : Fin t → ℂ)
    (r F : ℕ) (P : Polynomial t)
    (hP : ∀ e ∈ P.support, Finsupp.weight (fun x : Fin t × ℕ => x.2+1) e ≤ F) :
    fockQ (fockVariable a r * P) ≤
      (∑ i, Complex.normSq (a i)) * ((F : ℝ)+r+1) * fockQ P := by
  rw [fock_creation_square]
  have h := fock_directional_annihilate_le a r F P hP
  nlinarith

private def fullU (hD : (gramReal D).PosDef) : Oscillator D ≃ₐ[ℂ] Oscillator D :=
  (fullOscillatorEquiv hD).symm

private theorem fullU_X (hD : (gramReal D).PosDef) (x : Index D) :
    fullU hD (MvPolynomial.X x) =
      OriginalCurrentMetric.variableImage (fun _ => SC D hD) x :=
  OriginalCurrentMetric.substitution_X (fun _ => SC D hD) x

private theorem fullU_positive (hD : (gramReal D).PosDef) (i : Fin D.rank)
    (b : Charge D) (r : ℕ) (p : Oscillator D) :
    fullU hD (LatticeFiniteNegativeGeneration.neutralPolynomialMode D i b ((r : ℤ)+1) p) =
      fockD (fun j => SC D hD j i) r (fullU hD p) := by
  classical
  let d : Derivation ℂ (Oscillator D) (Oscillator D) :=
    ((r : ℂ)+1) • LatticeActualAnnihilation.annihilationDerivation D i r
  have hd (q : Oscillator D) : fockD (fun j => SC D hD j i) r q =
      ((r : ℂ)+1) • OriginalCurrentMetric.lowering (fun _ => SC D hD) i r q := by
    rw [fockD_apply, OriginalCurrentMetric.lowering_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hr : conj (SC D hD j i) = SC D hD j i := by simp [SC]
    rw [hr, smul_smul, smul_smul]
    congr 1
    ring
  have hx (x : Index D) :
      fullU hD (d (MvPolynomial.X x)) =
        fockD (fun j => SC D hD j i) r (fullU hD (MvPolynomial.X x)) := by
    rcases x with ⟨j,s⟩
    rw [fullU_X, hd, OriginalCurrentMetric.lowering_variableImage, SC_gram]
    simp only [d, Derivation.coe_smul, Pi.smul_apply,
      LatticeActualAnnihilation.annihilation_apply, LatticeActualAnnihilation.annihilate_X]
    split_ifs <;> simp
  have hp : fullU hD (d p) = fockD (fun j => SC D hD j i) r (fullU hD p) := by
    induction p using MvPolynomial.induction_on with
    | C c =>
      rw [MvPolynomial.derivation_C, map_zero,
        show fullU hD (MvPolynomial.C c) = MvPolynomial.C c from (fullU hD).commutes c,
        MvPolynomial.derivation_C]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p x hp =>
      rw [d.leibniz]
      simp only [smul_eq_mul, map_add, map_mul]
      rw [hp, hx, (fockD (fun j => SC D hD j i) r).leibniz]
      simp only [smul_eq_mul]
  rw [neutralPolynomialMode_positive]
  simpa only [d, Derivation.coe_smul, Pi.smul_apply,
    LatticeActualAnnihilation.annihilation_apply, LinearMap.smul_apply] using hp

private theorem fullU_negative (hD : (gramReal D).PosDef) (i : Fin D.rank)
    (b : Charge D) (r : ℕ) (p : Oscillator D) :
    fullU hD (LatticeFiniteNegativeGeneration.neutralPolynomialMode D i b (-(r : ℤ)-1) p) =
      fockVariable (fun j => SC D hD j i) r * fullU hD p := by
  rw [neutralPolynomialMode_negative, LinearMap.mulLeft_apply, map_mul, fullU_X]
  rfl

private theorem fullU_direction_norm (hD : (gramReal D).PosDef) (i : Fin D.rank) :
    (∑ j : Fin D.rank, Complex.normSq (SC D hD j i)) = (D.G i i : ℝ) := by
  have h := congrFun (congrFun (S_transpose_mul D hD) i) i
  change (∑ j : Fin D.rank, S D hD j i * S D hD j i) = (D.G i i : ℝ) at h
  simpa [SC, Complex.normSq_apply, pow_two] using h

private theorem Hm_single_coordinates (hD : (gramReal D).PosDef)
    (a b : Charge D) (p q : Oscillator D) :
    Hm (D := D) (Finsupp.single a p) (Finsupp.single b q) =
      if a = b then fockInner (fullU hD p) (fullU hD q) else 0 := by
  have hs (p : Oscillator D) : phi (fullFrame hD) (fullU hD p) = p := by
    rw [fullFrame_phi]
    exact (fullOscillatorEquiv hD).apply_symm_apply p
  have h := source_delta_delta_eq_factorial (fullFrame hD) a b (fullU hD p) (fullU hD q)
  simpa only [delta, hs, fockInner] using h

open private homogeneous_substitution from
  D5.S3.VertexAlgebra.Lattice.LatticeLightConeCoordinates

private theorem fullU_homogeneous (hD : (gramReal D).PosDef) (p : Oscillator D) (n : ℕ)
    (hp : MvPolynomial.IsWeightedHomogeneous (fun x : Index D => x.2+1) p n) :
    MvPolynomial.IsWeightedHomogeneous (fun x : Index D => x.2+1) (fullU hD p) n := by
  apply homogeneous_substitution (fun x : Index D => x.2+1) (fun x : Index D => x.2+1)
    (OriginalCurrentMetric.variableImage (fun _ => SC D hD)) _ hp
  intro x
  unfold OriginalCurrentMetric.variableImage
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro i _
  exact (MvPolynomial.weightedHomogeneousSubmodule ℂ (fun x : Index D => x.2+1)
    (x.2+1)).smul_mem _ (MvPolynomial.isWeightedHomogeneous_X ℂ _ (i,x.2))

private theorem fullU_grade_support (hD : (gramReal D).PosDef) (E : ℕ)
    (v : Carrier D) (hv : v ∈ grade D (E : ℤ)) (b : Charge D)
    (e : Occupation D.rank) (he : e ∈ (fullU hD (v b)).support) :
    Finsupp.weight (fun x : Index D => x.2+1) e ≤ E := by
  have hp : MvPolynomial.IsWeightedHomogeneous (fun x : Index D => x.2+1)
      (v b) ((E : ℤ)-chargeEnergy D b).toNat := by
    intro f hf
    have hg : energy D (b,f) = E := by
      by_contra hn
      exact hf ((mem_grade_iff D (E : ℤ) v).mp hv (b,f) hn)
    dsimp [energy, oscillatorEnergy] at hg
    omega
  have hu := fullU_homogeneous hD (v b) _ hp
  have hw := hu (MvPolynomial.mem_support_iff.mp he)
  have hq := chargeEnergy_nonneg D hD b
  omega

private theorem original_positive_current_sector_le (hD : (gramReal D).PosDef)
    (i : Fin D.rank) (r E : ℕ) (v : Carrier D) (hv : v ∈ grade D (E : ℤ))
    (b : Charge D) :
    (Hm (D := D)
      (LatticeFiniteNegativeGeneration.neutralMode D i ((r : ℤ)+1) (Finsupp.single b (v b)))
      (LatticeFiniteNegativeGeneration.neutralMode D i ((r : ℤ)+1) (Finsupp.single b (v b)))).re ≤
      (D.G i i : ℝ) * E * (Hm (D := D) (Finsupp.single b (v b)) (Finsupp.single b (v b))).re := by
  simp only [neutralMode_single, Hm_single_coordinates hD, ite_true]
  change fockQ (fullU hD (LatticeFiniteNegativeGeneration.neutralPolynomialMode
    D i b ((r : ℤ)+1) (v b))) ≤ (D.G i i : ℝ) * E * fockQ (fullU hD (v b))
  rw [fullU_positive]
  have h := fock_directional_annihilate_le (fun j => SC D hD j i) r E (fullU hD (v b))
    (fullU_grade_support hD E v hv b)
  rw [fullU_direction_norm] at h
  exact h

private theorem original_negative_current_sector_le (hD : (gramReal D).PosDef)
    (i : Fin D.rank) (r E : ℕ) (v : Carrier D) (hv : v ∈ grade D (E : ℤ))
    (b : Charge D) :
    (Hm (D := D)
      (LatticeFiniteNegativeGeneration.neutralMode D i (-(r : ℤ)-1) (Finsupp.single b (v b)))
      (LatticeFiniteNegativeGeneration.neutralMode D i (-(r : ℤ)-1) (Finsupp.single b (v b)))).re ≤
      (D.G i i : ℝ) * ((E : ℝ)+r+1) *
        (Hm (D := D) (Finsupp.single b (v b)) (Finsupp.single b (v b))).re := by
  simp only [neutralMode_single, Hm_single_coordinates hD, ite_true]
  change fockQ (fullU hD (LatticeFiniteNegativeGeneration.neutralPolynomialMode
    D i b (-(r : ℤ)-1) (v b))) ≤
      (D.G i i : ℝ) * ((E : ℝ)+r+1) * fockQ (fullU hD (v b))
  rw [fullU_negative]
  have h := fock_directional_create_le (fun j => SC D hD j i) r E (fullU hD (v b))
    (fullU_grade_support hD E v hv b)
  rw [fullU_direction_norm] at h
  exact h

private theorem normD_sector_sum (hD : (gramReal D).PosDef) (s : Finset (Charge D))
    (f : Charge D → Oscillator D) :
    normD (∑ b ∈ s, Finsupp.single b (f b)) ^ 2 =
      ∑ b ∈ s, normD (Finsupp.single b (f b)) ^ 2 := by
  classical
  rw [normD_sq hD, Hm_finset_sum_left, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Hm_finset_sum_right, normD_sq hD]
  congr 1
  apply Finset.sum_eq_single b
  · intro c hc hcb
    rw [Hm_single_coordinates hD, if_neg (Ne.symm hcb)]
  · exact fun h => (h hb).elim

private theorem current_norm_sector_sum (hD : (gramReal D).PosDef)
    (i : Fin D.rank) (m : ℤ) (v : Carrier D) :
    normD (LatticeFiniteNegativeGeneration.neutralMode D i m v) ^ 2 =
      ∑ b ∈ v.support,
        normD (LatticeFiniteNegativeGeneration.neutralMode D i m (Finsupp.single b (v b))) ^ 2 := by
  classical
  have he : (∑ b ∈ v.support, Finsupp.single b (v b)) = v := v.sum_single
  have hmode : LatticeFiniteNegativeGeneration.neutralMode D i m v =
      ∑ b ∈ v.support, Finsupp.single b
        (LatticeFiniteNegativeGeneration.neutralPolynomialMode D i b m (v b)) := by
    conv_lhs => rw [← he, map_sum]
    simp only [neutralMode_single]
  rw [hmode, normD_sector_sum hD]
  simp only [neutralMode_single]

private theorem original_positive_current_le (hD : (gramReal D).PosDef)
    (i : Fin D.rank) (r E : ℕ) (v : Carrier D) (hv : v ∈ grade D (E : ℤ)) :
    normD (LatticeFiniteNegativeGeneration.neutralMode D i ((r : ℤ)+1) v) ^ 2 ≤
      (D.G i i : ℝ) * E * normD v ^ 2 := by
  classical
  rw [current_norm_sector_sum hD]
  have hn : normD v ^ 2 = ∑ b ∈ v.support, normD (Finsupp.single b (v b)) ^ 2 := by
    rw [← normD_sector_sum hD]
    exact congrArg (fun z => normD z ^ 2) v.sum_single.symm
  rw [hn, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  simpa only [normD_sq hD] using original_positive_current_sector_le hD i r E v hv b

private theorem original_negative_current_le (hD : (gramReal D).PosDef)
    (i : Fin D.rank) (r E : ℕ) (v : Carrier D) (hv : v ∈ grade D (E : ℤ)) :
    normD (LatticeFiniteNegativeGeneration.neutralMode D i (-(r : ℤ)-1) v) ^ 2 ≤
      (D.G i i : ℝ) * ((E : ℝ)+r+1) * normD v ^ 2 := by
  classical
  rw [current_norm_sector_sum hD]
  have hn : normD v ^ 2 = ∑ b ∈ v.support, normD (Finsupp.single b (v b)) ^ 2 := by
    rw [← normD_sector_sum hD]
    exact congrArg (fun z => normD z ^ 2) v.sum_single.symm
  rw [hn, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  simpa only [normD_sq hD] using original_negative_current_sector_le hD i r E v hv b

open private Matrix.PosSemidef.preInnerProductSpace from Mathlib.Analysis.Matrix.PosDef

private theorem original_gram_charge_square_le (hD : (gramReal D).PosDef)
    (i : Fin D.rank) (b : Charge D) :
    (bilinear D (unitCharge D i) b : ℝ) ^ 2 ≤
      2 * (D.G i i : ℝ) * (chargeEnergy D b : ℝ) := by
  classical
  let c : PreInnerProductSpace.Core ℝ (Fin D.rank → ℝ) :=
    hD.posSemidef.preInnerProductSpace
  let u : Fin D.rank → ℝ := fun j => (unitCharge D i j : ℝ)
  let q : Fin D.rank → ℝ := fun j => (b j : ℝ)
  have hb (a b : Charge D) :
      ((gramReal D) *ᵥ (fun j => (b j : ℝ))) ⬝ᵥ (fun j => (a j : ℝ)) =
        (bilinear D a b : ℝ) := by
    simp only [gramReal, Matrix.mulVec, dotProduct, Matrix.map_apply,
      bilinear, Int.cast_sum, Int.cast_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hc := @InnerProductSpace.Core.inner_mul_inner_self_le ℝ (Fin D.rank → ℝ) _ _ _ c u q
  change ‖((gramReal D) *ᵥ q) ⬝ᵥ u‖ * ‖((gramReal D) *ᵥ u) ⬝ᵥ q‖ ≤
    (((gramReal D) *ᵥ u) ⬝ᵥ u) * (((gramReal D) *ᵥ q) ⬝ᵥ q) at hc
  dsimp only [u, q] at hc
  rw [hb, hb, hb, hb, LatticeFiniteNegativeGeneration.bilinear_symmetric D b (unitCharge D i)] at hc
  have hu : bilinear D (unitCharge D i) (unitCharge D i) = D.G i i := by
    simp [bilinear, unitCharge]
  have he : (bilinear D b b : ℝ) = 2 * (chargeEnergy D b : ℝ) := by
    exact_mod_cast (two_chargeEnergy D b).symm
  rw [hu, he, Real.norm_eq_abs, ← sq, sq_abs] at hc
  nlinarith only [hc]

private theorem chargeEnergy_le_grade (E : ℕ) (v : Carrier D)
    (hv : v ∈ grade D (E : ℤ)) (b : Charge D) (hb : v b ≠ 0) :
    chargeEnergy D b ≤ E := by
  obtain ⟨e, he⟩ := MvPolynomial.exists_coeff_ne_zero hb
  have hg : energy D (b,e) = E := by
    by_contra hn
    exact he ((mem_grade_iff D (E : ℤ) v).mp hv (b,e) hn)
  dsimp [energy] at hg
  omega

private theorem normD_real_smul_sq (hD : (gramReal D).PosDef) (c : ℝ) (v : Carrier D) :
    normD ((c : ℂ) • v) ^ 2 = c ^ 2 * normD v ^ 2 := by
  rw [normD_sq hD, normD_sq hD, Hm_smul_left, Hm_smul_right]
  simp [Complex.mul_re, Complex.mul_im, pow_two, mul_assoc]

private theorem original_zero_current_le (hD : (gramReal D).PosDef)
    (i : Fin D.rank) (E : ℕ) (v : Carrier D) (hv : v ∈ grade D (E : ℤ)) :
    normD (LatticeFiniteNegativeGeneration.neutralMode D i 0 v) ^ 2 ≤
      (2 * (D.G i i : ℝ) * E) * normD v ^ 2 := by
  classical
  rw [current_norm_sector_sum hD]
  have hn : normD v ^ 2 = ∑ b ∈ v.support, normD (Finsupp.single b (v b)) ^ 2 := by
    rw [← normD_sector_sum hD]
    exact congrArg (fun z => normD z ^ 2) v.sum_single.symm
  rw [hn, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  have hz : LatticeFiniteNegativeGeneration.neutralMode D i 0 (Finsupp.single b (v b)) =
      (((bilinear D (unitCharge D i) b : ℝ) : ℂ)) • Finsupp.single b (v b) := by
    rw [neutralMode_single]
    simp [LatticeFiniteNegativeGeneration.neutralPolynomialMode, Finsupp.smul_single]
  rw [hz, normD_real_smul_sq hD]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hc := original_gram_charge_square_le hD i b
  have he : (chargeEnergy D b : ℝ) ≤ E := by
    exact_mod_cast chargeEnergy_le_grade E v hv b (Finsupp.mem_support_iff.mp hb)
  have hg : 0 ≤ (D.G i i : ℝ) := hD.posSemidef.diag_nonneg
  exact hc.trans (mul_le_mul_of_nonneg_left he (by positivity))

private theorem original_current_energy_le (hD : (gramReal D).PosDef)
    (i : Fin D.rank) (m : ℤ) (E F M : ℕ) (hEF : (E : ℤ)-m=F)
    (hE : E ≤ M) (hF : F ≤ M) (v : Carrier D) (hv : v ∈ grade D (E : ℤ)) :
    normD (LatticeFiniteNegativeGeneration.neutralMode D i m v) ≤
      Real.sqrt (3 * (D.G i i : ℝ)) * ((M : ℝ)+1) * normD v := by
  have hg : 0 ≤ (D.G i i : ℝ) := hD.posSemidef.diag_nonneg
  have hEM : (E : ℝ) ≤ M := by exact_mod_cast hE
  have hFM : (F : ℝ) ≤ M := by exact_mod_cast hF
  have hM : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
  have hs : normD (LatticeFiniteNegativeGeneration.neutralMode D i m v) ^ 2 ≤
      (3 * (D.G i i : ℝ) * ((M : ℝ)+1)^2) * normD v ^ 2 := by
    cases m with
    | ofNat k =>
      cases k with
      | zero =>
        have h := original_zero_current_le hD i E v hv
        apply h.trans
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        have hh : 2*(E : ℝ) ≤ 3*((M : ℝ)+1)^2 := by nlinarith
        nlinarith only [mul_nonneg hg (sub_nonneg.mpr hh)]
      | succ r =>
        have h := original_positive_current_le hD i r E v hv
        rw [show Int.ofNat (Nat.succ r) = (r : ℤ)+1 from rfl]
        apply h.trans
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        have hh : (E : ℝ) ≤ 3*((M : ℝ)+1)^2 := by nlinarith
        nlinarith only [mul_nonneg hg (sub_nonneg.mpr hh)]
    | negSucc r =>
      have h := original_negative_current_le hD i r E v hv
      rw [show Int.negSucc r = -(r : ℤ)-1 by omega]
      apply h.trans
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have he : (E : ℝ)+r+1 = F := by exact_mod_cast (show E+r+1=F by omega)
      rw [he]
      have hh : (F : ℝ) ≤ 3*((M : ℝ)+1)^2 := by nlinarith
      nlinarith only [mul_nonneg hg (sub_nonneg.mpr hh)]
  have hr : (Real.sqrt (3 * (D.G i i : ℝ)) * ((M : ℝ)+1) * normD v)^2 =
      (3 * (D.G i i : ℝ) * ((M : ℝ)+1)^2) * normD v ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  have hx : 0 ≤ normD (LatticeFiniteNegativeGeneration.neutralMode D i m v) :=
    Real.sqrt_nonneg _
  have hy : 0 ≤ Real.sqrt (3 * (D.G i i : ℝ)) * ((M : ℝ)+1) * normD v :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by positivity)) (Real.sqrt_nonneg _)
  exact (sq_le_sq₀ hx hy).mp (hs.trans_eq hr.symm)

private def originalCore (hD : (gramReal D).PosDef) :
    InnerProductSpace.Core ℂ (Carrier D) where
  inner := Hm
  conj_inner_symm x y := (Hm_hermitian x y).symm
  re_inner_nonneg := original_nonnegative hD
  add_left := Hm_add_left
  smul_left x y c := Hm_smul_left c x y
  definite x hx := by
    by_contra hn
    have hp := (original_positive hD hn).2
    rw [hx] at hp
    exact (lt_irrefl 0) hp

private theorem normD_add_le (hD : (gramReal D).PosDef) (u v : Carrier D) :
    normD (u+v) ≤ normD u + normD v := by
  letI := originalCore hD
  letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := Carrier D)
  exact norm_add_le u v

private theorem normD_smul (hD : (gramReal D).PosDef) (c : ℂ) (v : Carrier D) :
    normD (c • v) = ‖c‖ * normD v := by
  letI := originalCore hD
  letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := Carrier D)
  letI := InnerProductSpace.Core.toNormedSpace (𝕜 := ℂ) (F := Carrier D)
  exact norm_smul c v

private theorem normD_sum_le (hD : (gramReal D).PosDef) {ι : Type*}
    (s : Finset ι) (f : ι → Carrier D) :
    normD (∑ i ∈ s, f i) ≤ ∑ i ∈ s, normD (f i) := by
  letI := originalCore hD
  letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := Carrier D)
  exact norm_sum_le s f

#check @original_gram_charge_square_le
#check @original_zero_current_le
#check @original_current_energy_le
#print axioms original_gram_charge_square_le
#print axioms original_zero_current_le
#print axioms original_current_energy_le

#check @original_positive_current_le
#check @original_negative_current_le
#print axioms original_positive_current_le
#print axioms original_negative_current_le

#check @original_positive_current_sector_le
#check @original_negative_current_sector_le
#print axioms original_positive_current_sector_le
#print axioms original_negative_current_sector_le

#check @fock_directional_annihilate_le
#check @fock_directional_create_le
#print axioms fock_directional_annihilate_le
#print axioms fock_directional_create_le

#check @fock_derivative_sum
#check @fock_derivative_sum_le
#print axioms fock_derivative_sum_le

#check @original_positive
#print axioms fullFrame_surjective
#print axioms original_positive
end D5.S3.VertexAlgebra.Lattice.OriginalChargedEnergy
