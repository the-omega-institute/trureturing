/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteCriticalCharZero
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteCriticalCharZero
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteCriticalResidueCertificate, lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSRealPolynomialZeros]
   utility: none
   digest: Off the mixed-trace zero locus, the real critical slice has a countable differentiable cover from three real coordinates. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteCriticalResidueCertificate
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSRealPolynomialZeros
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! The degree-saturating residue certificate for the two literal seven-site
cofactors implies a countable three-dimensional differentiable cover on the
real slice where the mixed trace is nonzero. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.SevenSiteCriticalCertificate

open MvPolynomial Set

noncomputable section

private def gaussianI : GaussianInt := Zsqrtd.sqrtd

private theorem gaussianI_sq : gaussianI ^ 2 = -1 := by
  simpa only [gaussianI, pow_two, Int.cast_neg, Int.cast_one] using
    (Zsqrtd.dmuld (d := -1))

/-- Reduce the Gaussian coefficients modulo 1009, sending the imaginary unit to 469. -/
def gaussianToResidue : GaussianInt →+* F :=
  Zsqrtd.lift ⟨imaginary, by simpa only [pow_two, Int.cast_neg, Int.cast_one] using imaginary_sq⟩

private theorem gaussianToResidue_i : gaussianToResidue gaussianI = imaginary := by
  simp [gaussianToResidue, gaussianI, Zsqrtd.lift_apply_apply]

private theorem gaussianToComplex_i : GaussianInt.toComplex gaussianI = Complex.I := by
  simp [GaussianInt.toComplex, gaussianI, Zsqrtd.lift_apply_apply]

section BaseChange

variable {R S : Type*} [CommRing R] [CommRing S]

private theorem map_valuePolynomial (f : R →+* S) (ι : R) (ab : Fin 4 × Fin 4) :
    MvPolynomial.map f (V ι ab) = V (f ι) ab := by
  simp only [V, map_slicedObservation, MvPolynomial.map_C, MvPolynomial.map_X]

private theorem map_raw_cofactor (f : R →+* S) (ι : R) (deleted : Fin 10) :
    MvPolynomial.map f (criticalMatrix ι deleted).det =
      (criticalMatrix (f ι) deleted).det := by
  rw [RingHom.map_det]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  change MvPolynomial.map f (criticalMatrix ι deleted i j) =
    criticalMatrix (f ι) deleted i j
  by_cases hp : j.val < 5
  · simp only [criticalMatrix, dif_pos hp, ← MvPolynomial.pderiv_map, map_valuePolynomial]
  · by_cases hv : j = 5
    · simp only [criticalMatrix, dif_neg hp, if_pos hv, map_valuePolynomial]
    · simp only [criticalMatrix, dif_neg hp, if_neg hv, map_rotationObservation,
        MvPolynomial.map_C, MvPolynomial.map_X]

private theorem map_cofactor_factorization (f : R →+* S) {ι : R} {deleted : Fin 10}
    {p : Slice R} (hp : (criticalMatrix ι deleted).det = X 1 * p) :
    (criticalMatrix (f ι) deleted).det = X 1 * MvPolynomial.map f p := by
  simpa only [map_raw_cofactor, map_mul, MvPolynomial.map_X] using
    congrArg (MvPolynomial.map f) hp

private theorem map_affineRestriction (f : R →+* S) (p : Slice R) :
    (affineRestriction p).map f = affineRestriction (MvPolynomial.map f p) := by
  have ho (i : Fin 5) : f (origin R i) = origin S i := by
    fin_cases i <;> simp [origin, map_ofNat]
  have hd (i : Fin 5) : f (direction R i) = direction S i := by
    fin_cases i <;> simp [direction, map_ofNat]
  have h :
      (Polynomial.mapRingHom f).comp (affineRestriction (R := R)) =
        (affineRestriction (R := S)).comp (MvPolynomial.map f) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [affineRestriction]
    · intro i
      simp [affineRestriction, eval₂Hom_X', ho i, hd i]
  exact RingHom.congr_fun h p

private theorem totalDegree_coefficient_map_le (f : R →+* S) (p : Slice R) :
    (MvPolynomial.map f p).totalDegree ≤ p.totalDegree := by
  change ((MvPolynomial.map f p).support.sup fun m => m.sum (fun _ e => e)) ≤ p.totalDegree
  exact Finset.sup_le fun _ hm => le_totalDegree (support_map_subset f p hm)

end BaseChange

/-- The full-degree resultant certificate for the actual quotients of the
cofactors deleting rows zero and one, as in `seven_site_modular_resultant`. -/
abbrev ModularCriticalCertificate : Prop :=
  ∃ p q : Slice F,
    (criticalMatrix imaginary 0).det = X 1 * p ∧
    (criticalMatrix imaginary 1).det = X 1 * q ∧
    (affineRestriction p).natDegree = 46 ∧
    (affineRestriction q).natDegree = 46 ∧
    Polynomial.resultant (affineRestriction p) (affineRestriction q) ≠ 0

private theorem reduce_quotient_restriction {deleted : Fin 10}
    {p : Slice GaussianInt} {q : Slice F}
    (hp : (criticalMatrix gaussianI deleted).det = X 1 * p)
    (hq : (criticalMatrix imaginary deleted).det = X 1 * q) :
    (affineRestriction p).map gaussianToResidue = affineRestriction q := by
  have h := map_cofactor_factorization gaussianToResidue hp
  rw [gaussianToResidue_i] at h
  rw [map_affineRestriction]
  exact congrArg affineRestriction
    (mul_left_cancel₀ (X_ne_zero (R := F) (1 : Fin 5)) (h.symm.trans hq))

private theorem complex_line_certificate (p q : Slice GaussianInt)
    (hp : p.totalDegree ≤ 46) (hq : q.totalDegree ≤ 46)
    (hdp : ((affineRestriction p).map gaussianToResidue).natDegree = 46)
    (hdq : ((affineRestriction q).map gaussianToResidue).natDegree = 46)
    (hres : Polynomial.resultant ((affineRestriction p).map gaussianToResidue)
      ((affineRestriction q).map gaussianToResidue) ≠ 0) :
    (affineRestriction (MvPolynomial.map GaussianInt.toComplex p)).natDegree = 46 ∧
    (affineRestriction (MvPolynomial.map GaussianInt.toComplex q)).natDegree = 46 ∧
    IsCoprime (affineRestriction (MvPolynomial.map GaussianInt.toComplex p))
      (affineRestriction (MvPolynomial.map GaussianInt.toComplex q)) := by
  have fullDegree (a : Slice GaussianInt) (ha : a.totalDegree ≤ 46)
      (hmod : ((affineRestriction a).map gaussianToResidue).natDegree = 46) :
      (affineRestriction (MvPolynomial.map GaussianInt.toComplex a)).natDegree = 46 := by
    rw [← map_affineRestriction, Polynomial.natDegree_map_eq_of_injective
      GaussianInt.toComplex_injective]
    refine le_antisymm ((natDegree_affineRestriction_le a).trans ha) ?_
    rw [← hmod]
    exact Polynomial.natDegree_map_le
  have hpc := fullDegree p hp hdp
  have hqc := fullDegree q hq hdq
  have hresZ : Polynomial.resultant (affineRestriction p) (affineRestriction q) 46 46 ≠ 0 := by
    intro hz
    apply hres
    rw [hdp, hdq, Polynomial.resultant_map_map, hz, map_zero]
  refine ⟨hpc, hqc, ?_⟩
  by_contra hc
  have hpne : affineRestriction (MvPolynomial.map GaussianInt.toComplex p) ≠ 0 := by
    intro hz
    rw [hz, Polynomial.natDegree_zero] at hpc
    omega
  have hz := Polynomial.resultant_eq_zero_iff.mpr ⟨Or.inl hpne, hc⟩
  rw [hpc, hqc, ← map_affineRestriction GaussianInt.toComplex p,
    ← map_affineRestriction GaussianInt.toComplex q, Polynomial.resultant_map_map] at hz
  exact hresZ (GaussianInt.toComplex_injective (hz.trans (map_zero GaussianInt.toComplex).symm))

/-- For a polynomial whose total degree survives affine restriction, every
factor retains its total degree. A common factor that becomes a unit on the
line therefore already has total degree zero. -/
private theorem isRelPrime_of_full_affine_degree (p q : Slice ℂ)
    (hpn : affineRestriction p ≠ 0) (hfull : (affineRestriction p).natDegree = p.totalDegree)
    (hc : IsCoprime (affineRestriction p) (affineRestriction q)) :
    IsRelPrime p q := by
  have hp : p ≠ 0 := fun hz => hpn (by rw [hz, map_zero])
  intro d hdp hdq
  have hunit : IsUnit (affineRestriction d) :=
    hc.isRelPrime (map_dvd affineRestriction hdp) (map_dvd affineRestriction hdq)
  obtain ⟨e, he⟩ := hdp
  have hen : affineRestriction e ≠ 0 :=
    fun hz => hpn (by rw [he, map_mul, hz, mul_zero])
  have hd0 : d ≠ 0 := fun hz => hp (by rw [he, hz, zero_mul])
  have he0 : e ≠ 0 := fun hz => hp (by rw [he, hz, mul_zero])
  have hdegrees : p.totalDegree = d.totalDegree + e.totalDegree := by
    rw [he, totalDegree_mul_of_isDomain hd0 he0]
  have hline : (affineRestriction p).natDegree = (affineRestriction e).natDegree := by
    rw [he, map_mul, Polynomial.natDegree_mul hunit.ne_zero hen,
      Polynomial.natDegree_eq_zero_of_isUnit hunit, zero_add]
  have hle := natDegree_affineRestriction_le e
  have hd : d.totalDegree = 0 := by omega
  have hconst := totalDegree_eq_zero_iff_eq_C.mp hd
  have hcoeff : d.coeff 0 ≠ 0 := by
    intro hz
    apply hd0
    simpa only [hz, map_zero] using hconst
  rw [hconst]
  exact (isUnit_iff_ne_zero.mpr hcoeff).map MvPolynomial.C

/-- The two raw cofactors have relatively prime complex quotients of total
degree 46 after division by the mixed trace. -/
theorem complex_critical_quotients (certificate : ModularCriticalCertificate) :
    ∃ p q : Slice ℂ,
      (criticalMatrix Complex.I 0).det = X 1 * p ∧
      (criticalMatrix Complex.I 1).det = X 1 * q ∧
      p.totalDegree = 46 ∧ q.totalDegree = 46 ∧
      p ≠ 0 ∧ IsRelPrime p q := by
  obtain ⟨pF, qF, hpF, hqF, hdpF, hdqF, hresF⟩ := certificate
  have hsix : (6 : GaussianInt) ≠ 0 := by
    intro hz
    have hc : (6 : ℂ) = 0 := by simpa using congrArg GaussianInt.toComplex hz
    norm_num at hc
  obtain ⟨p, hp, hdp⟩ := critical_cofactor_quotient gaussianI gaussianI_sq hsix 0
  obtain ⟨q, hq, hdq⟩ := critical_cofactor_quotient gaussianI gaussianI_sq hsix 1
  have hmapP := reduce_quotient_restriction hp hpF
  have hmapQ := reduce_quotient_restriction hq hqF
  obtain ⟨hpc, hqc, hcop⟩ := complex_line_certificate p q hdp hdq
    (by simpa only [hmapP] using hdpF) (by simpa only [hmapQ] using hdqF)
    (by
      rw [hmapP, hmapQ]
      simpa only [hdpF, hdqF] using hresF)
  let pC := MvPolynomial.map GaussianInt.toComplex p
  let qC := MvPolynomial.map GaussianInt.toComplex q
  have hfactorP : (criticalMatrix Complex.I 0).det = X 1 * pC := by
    simpa only [gaussianToComplex_i] using map_cofactor_factorization GaussianInt.toComplex hp
  have hfactorQ : (criticalMatrix Complex.I 1).det = X 1 * qC := by
    simpa only [gaussianToComplex_i] using map_cofactor_factorization GaussianInt.toComplex hq
  have hfullP : pC.totalDegree = 46 :=
    le_antisymm ((totalDegree_coefficient_map_le GaussianInt.toComplex p).trans hdp)
      (hpc.symm.le.trans (natDegree_affineRestriction_le pC))
  have hfullQ : qC.totalDegree = 46 :=
    le_antisymm ((totalDegree_coefficient_map_le GaussianInt.toComplex q).trans hdq)
      (hqc.symm.le.trans (natDegree_affineRestriction_le qC))
  have hlineP : (affineRestriction pC).natDegree = 46 := hpc
  have hlinePne : affineRestriction pC ≠ 0 := by
    intro hz
    rw [hz, Polynomial.natDegree_zero] at hlineP
    omega
  have hpne : pC ≠ 0 := fun hz => hlinePne (by rw [hz, map_zero])
  exact ⟨pC, qC, hfactorP, hfactorQ, hfullP, hfullQ, hpne,
    isRelPrime_of_full_affine_degree pC qC hlinePne (hlineP.trans hfullP.symm) hcop⟩

/-- The real slice points with nonzero mixed trace and vanishing critical
cofactors lie in a countable union of differentiable images of subsets of
three-dimensional real space. -/
theorem cover_real_critical_slice (certificate : ModularCriticalCertificate) :
    ∃ (ι : Type) (_ : Countable ι) (D : ι → Set (Fin 3 → ℝ))
      (g : ι → (Fin 3 → ℝ) → (Fin 5 → ℝ)), (∀ i, DifferentiableOn ℝ (g i) (D i)) ∧
      {x : Fin 5 → ℝ | x 1 ≠ 0 ∧ ∀ deleted : Fin 10,
        MvPolynomial.eval (fun i => (x i : ℂ)) (criticalMatrix Complex.I deleted).det = 0} ⊆
        ⋃ i, g i '' D i := by
  obtain ⟨p, q, hp, hq, _, _, hpne, hrel⟩ := complex_critical_quotients certificate
  obtain ⟨ι, hι, D, g, hdiff, hcover⟩ :=
    PeriodicMPSRealPolynomialZeros.cover_real_common_zeros (n := 3) hpne hrel
  refine ⟨ι, hι, D, g, hdiff, ?_⟩
  intro x hx
  obtain ⟨hk, hcrit⟩ := hx
  have hkC : (x 1 : ℂ) ≠ 0 := by exact_mod_cast hk
  have vanish {r : Slice ℂ} {deleted : Fin 10}
      (hr : (criticalMatrix Complex.I deleted).det = X 1 * r) :
      MvPolynomial.eval (fun i => (x i : ℂ)) r = 0 := by
    have h := hcrit deleted
    rw [hr, map_mul, MvPolynomial.eval_X] at h
    exact (mul_eq_zero.mp h).resolve_left hkC
  exact hcover ⟨vanish hp, vanish hq⟩

/-- The seven-site real slice critical set off the mixed-trace zero locus
has a countable cover by differentiable maps from three real coordinates. -/
theorem seven_site_critical_slice_cover :
    ∃ (ι : Type) (_ : Countable ι) (D : ι → Set (Fin 3 → ℝ))
      (g : ι → (Fin 3 → ℝ) → (Fin 5 → ℝ)), (∀ i, DifferentiableOn ℝ (g i) (D i)) ∧
      {x : Fin 5 → ℝ | x 1 ≠ 0 ∧ ∀ deleted : Fin 10,
        MvPolynomial.eval (fun i => (x i : ℂ)) (criticalMatrix Complex.I deleted).det = 0} ⊆
        ⋃ i, g i '' D i :=
  cover_real_critical_slice seven_site_modular_resultant

#print axioms seven_site_critical_slice_cover

end

end D5.S3.Quantum.TensorNetworks.SevenSiteCriticalCertificate
