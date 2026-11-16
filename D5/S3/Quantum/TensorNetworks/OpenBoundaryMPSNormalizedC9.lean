/- GID: D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSNormalizedC9
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/OpenBoundaryMPSNormalizedC9
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Physical-mass-one all-window recovery and individual marginal ambiguity. -/

import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSAllWindowC9
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Polynomial.Roots

/-! Positive-ray saturation uses the homogeneous components of the raw supplier's
full-amplitude polynomial. Physical mass is the sum of squared complex amplitudes.
All private helpers are consumed by the normalized all-window result.
proof_shape: bind-only for result and all 28 private lemmas.
Candidate admission_basis: open-problem-resolution under pre-probe issue #30422,
completing the same physical C9 reading with both states normalized.
No escape witness, independent priority or additional solved-problem KPI is asserted.
C9 remains OPEN; solved-open-problem KPI increment is zero.
Unfinished faithful escape audit: issue #30422. -/

set_option autoImplicit false
noncomputable section
namespace D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSNormalizedC9
open scoped BigOperators Matrix
open MvPolynomial Matrix
open PeriodicMPSParentIntersection (Word)
open OpenBoundaryMPSMarginalBirationality (openBoundaryMPS)
open OpenBoundaryMPSDensityGenericity (realCoordinates continuous_realCoordinates)
open OpenBoundaryMPSInteriorCommonCore (rawInterior interiorColumns)
open OpenBoundaryMPSInteriorGenericity (castState actual_phase)

private def radialSOS {ι : Type*} (P : MvPolynomial ι ℝ) : MvPolynomial ι ℝ :=
  ∑ d ∈ Finset.range (P.totalDegree + 1), (homogeneousComponent d P) ^ 2

private def rayPolynomial {ι : Type*} (P : MvPolynomial ι ℝ) (x : ι → ℝ) : Polynomial ℝ :=
  ∑ d ∈ Finset.range (P.totalDegree + 1),
    Polynomial.C (eval x (homogeneousComponent d P)) * Polynomial.X ^ d

private lemma homogeneous_eval_scale {ι : Type*} (P : MvPolynomial ι ℝ) (d : ℕ)
    (hP : P.IsHomogeneous d) (x : ι → ℝ) (t : ℝ) :
    eval (fun i => t * x i) P = t ^ d * eval x P := by
  classical
  rw [eval_eq, eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hd := hP.degree_eq_sum_deg_support hs
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← hd]
  ring

private lemma rayPolynomial_eval {ι : Type*} (P : MvPolynomial ι ℝ)
    (x : ι → ℝ) (t : ℝ) :
    (rayPolynomial P x).eval t = eval (fun i => t * x i) P := by
  classical
  conv_rhs => rw [← sum_homogeneousComponent P]
  simp only [rayPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [homogeneous_eval_scale _ d (homogeneousComponent_isHomogeneous d P)]
  exact mul_comm _ _

private lemma rayPolynomial_coeff {ι : Type*} (P : MvPolynomial ι ℝ)
    (x : ι → ℝ) (d : ℕ) (hd : d < P.totalDegree + 1) :
    (rayPolynomial P x).coeff d = eval x (homogeneousComponent d P) := by
  classical
  simp [rayPolynomial, Polynomial.finsetSum_coeff, hd]

private lemma radialSOS_zero_iff {ι : Type*} (P : MvPolynomial ι ℝ) (x : ι → ℝ) :
    eval x (radialSOS P) = 0 ↔ rayPolynomial P x = 0 := by
  classical
  rw [radialSOS, map_sum]
  simp only [map_pow]
  rw [Finset.sum_sq_eq_zero_iff]
  constructor
  · intro h
    unfold rayPolynomial
    apply Finset.sum_eq_zero
    intro d hd
    rw [h d hd, Polynomial.C_0, zero_mul]
  · intro h d hd
    have hc := congrArg (fun Q : Polynomial ℝ => Q.coeff d) h
    rw [rayPolynomial_coeff P x d (Finset.mem_range.mp hd)] at hc
    simpa using hc

private lemma radialSOS_ray {ι : Type*} (P : MvPolynomial ι ℝ) (x : ι → ℝ) :
    eval x (radialSOS P) ≠ 0 ↔ ∃ t : ℝ, 0 < t ∧ eval (fun i => t * x i) P ≠ 0 := by
  rw [ne_eq, radialSOS_zero_iff]
  constructor
  · intro hn
    by_contra h
    push Not at h
    apply hn
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Set.Ioi_infinite (0 : ℝ)).mono
    intro t ht
    exact (rayPolynomial_eval P x t).trans (h t ht)
  · rintro ⟨t, ht, hn⟩ he
    apply hn
    rw [← rayPolynomial_eval, he, Polynomial.eval_zero]

/-- The physical squared Hilbert mass; this is not the Pi sup norm. -/
def physicalMass {n : ℕ} (ψ : Word n → ℂ) : ℝ := ∑ w, Complex.normSq (ψ w)

/-- Actual open-boundary states with physical mass exactly one. -/
abbrev MassOne (n : ℕ) := {ψ : openBoundaryMPS n // physicalMass (ψ : Word n → ℂ) = 1}

private lemma mass_nonneg {n : ℕ} (ψ : Word n → ℂ) : 0 ≤ physicalMass ψ := by
  exact Finset.sum_nonneg (fun w _ => Complex.normSq_nonneg (ψ w))

private lemma mass_zero_iff {n : ℕ} (ψ : Word n → ℂ) : physicalMass ψ = 0 ↔ ψ = 0 := by
  rw [physicalMass, Finset.sum_eq_zero_iff_of_nonneg (fun w _ => Complex.normSq_nonneg (ψ w))]
  simp [funext_iff]

private lemma mass_pos_iff {n : ℕ} (ψ : Word n → ℂ) : 0 < physicalMass ψ ↔ ψ ≠ 0 := by
  have he : physicalMass ψ ≠ 0 ↔ ψ ≠ 0 := not_congr (mass_zero_iff ψ)
  exact ((mass_nonneg ψ).lt_iff_ne.trans ne_comm).trans he

private lemma mass_scale {n : ℕ} (ψ : Word n → ℂ) (z : ℂ) :
    physicalMass (z • ψ) = Complex.normSq z * physicalMass ψ := by
  simp [physicalMass, Complex.normSq_mul, Finset.mul_sum]

private lemma mass_real_scale {n : ℕ} (ψ : Word n → ℂ) (t : ℝ) :
    physicalMass ((t : ℂ) • ψ) = t ^ 2 * physicalMass ψ := by
  rw [mass_scale]
  simp [Complex.normSq_ofReal, pow_two]

private lemma mass_continuous (n : ℕ) : Continuous (@physicalMass n) := by
  apply continuous_finsetSum
  intro w hw
  exact Complex.continuous_normSq.comp (continuous_apply w)

private lemma raw_scale (p k q : ℕ) (ψ : Word ((p + k) + q) → ℂ) (z : ℂ) :
    rawInterior p k q (z • ψ) = (Complex.normSq z : ℂ) • rawInterior p k q ψ := by
  have hC : interiorColumns p k q (z • ψ) = z • interiorColumns p k q ψ := rfl
  rw [rawInterior, hC, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  change (z * (starRingEnd ℂ) z) • _ = _
  rw [Complex.mul_conj]
  rfl

private lemma cast_scale {n n' : ℕ} (h : n = n') (ψ : Word n' → ℂ) (z : ℂ) :
    castState h (z • ψ) = z • castState h ψ := rfl

private lemma mass_cast {n n' : ℕ} (h : n = n') (ψ : Word n' → ℂ) :
    physicalMass (castState h ψ) = physicalMass ψ := by
  subst n'
  rfl

private lemma raw_trace_mass (p k q : ℕ) (ψ : Word ((p + k) + q) → ℂ) :
    Matrix.trace (rawInterior p k q ψ) = (physicalMass ψ : ℂ) := by
  classical
  let e : (Word k × (Word p × Word q)) ≃ Word ((p + k) + q) :=
    ((Equiv.prodAssoc (Word k) (Word p) (Word q)).symm.trans
      (Equiv.prodCongr (Equiv.prodComm (Word k) (Word p)) (Equiv.refl (Word q)))).trans
      ((Equiv.prodCongr (Fin.appendEquiv p k) (Equiv.refl (Word q))).trans
        (Fin.appendEquiv (p + k) q))
  have hz (z : ℂ) : z * star z = (Complex.normSq z : ℂ) := Complex.mul_conj z
  simp only [Matrix.trace, Matrix.diag, rawInterior, Matrix.mul_apply,
    Matrix.conjTranspose_apply, interiorColumns]
  simp_rw [hz]
  calc
    _ = ∑ uw : Word k × (Word p × Word q), (Complex.normSq (ψ (e uw)) : ℂ) :=
      (Fintype.sum_prod_type _).symm
    _ = ∑ w, (Complex.normSq (ψ w) : ℂ) := Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = _ := by simp [physicalMass]

private lemma equal_raw_mass {n : ℕ} (p k q : ℕ) (h : ((p + k) + q) = n)
    (ψ φ : Word n → ℂ)
    (he : rawInterior p k q (castState h φ) = rawInterior p k q (castState h ψ)) :
    physicalMass φ = physicalMass ψ := by
  have ht := congrArg Matrix.trace he
  rw [raw_trace_mass, raw_trace_mass, mass_cast, mass_cast] at ht
  exact Complex.ofReal_injective ht

private def scaleActual {n : ℕ} (z : ℂ) (ψ : openBoundaryMPS n) : openBoundaryMPS n :=
  ⟨z • (ψ : Word n → ℂ), actual_phase n ψ z⟩

private lemma realCoordinates_scale {n : ℕ} (ψ : Word n → ℂ) (t : ℝ) :
    realCoordinates ((t : ℂ) • ψ) = fun i => t * realCoordinates ψ i := by
  funext i
  cases i <;> simp [realCoordinates, Complex.mul_re, Complex.mul_im]

private def fullLocus {n : ℕ} (P : MvPolynomial (Word n ⊕ Word n) ℝ) :
    Set (openBoundaryMPS n) := {ψ | eval (realCoordinates (ψ : Word n → ℂ)) P ≠ 0}

private lemma fullLocus_open {n : ℕ} (P : MvPolynomial (Word n ⊕ Word n) ℝ) :
    IsOpen (fullLocus P) :=
  isOpen_ne.preimage ((MvPolynomial.continuous_eval P).comp
    (continuous_realCoordinates.comp continuous_subtype_val))

private lemma fullLocus_ray {n : ℕ} (P : MvPolynomial (Word n ⊕ Word n) ℝ)
    (ψ : openBoundaryMPS n) :
    ψ ∈ fullLocus (radialSOS P) ↔
      ∃ t : ℝ, 0 < t ∧ scaleActual (t : ℂ) ψ ∈ fullLocus P := by
  simp only [fullLocus, Set.mem_ofPred_eq, scaleActual, realCoordinates_scale]
  exact radialSOS_ray P _

private lemma fullLocus_scale {n : ℕ} (P : MvPolynomial (Word n ⊕ Word n) ℝ)
    (ψ : openBoundaryMPS n) (b : ℝ) (hb : 0 < b) :
    scaleActual (b : ℂ) ψ ∈ fullLocus (radialSOS P) ↔ ψ ∈ fullLocus (radialSOS P) := by
  rw [fullLocus_ray, fullLocus_ray]
  have hh (a c : ℝ) : scaleActual (a : ℂ) (scaleActual (c : ℂ) ψ) =
      scaleActual ((a * c : ℝ) : ℂ) ψ := by
    apply Subtype.ext
    change (a : ℂ) • ((c : ℂ) • (ψ : Word n → ℂ)) = ((a * c : ℝ) : ℂ) • (ψ : Word n → ℂ)
    rw [smul_smul, Complex.ofReal_mul]
  constructor
  · rintro ⟨t, ht, h⟩
    exact ⟨t * b, mul_pos ht hb, (hh t b) ▸ h⟩
  · rintro ⟨t, ht, h⟩
    refine ⟨t / b, div_pos ht hb, ?_⟩
    rwa [hh, div_mul_cancel₀ t (ne_of_gt hb)]

private abbrev PositiveActual (n : ℕ) :=
  {ψ : openBoundaryMPS n // 0 < physicalMass (ψ : Word n → ℂ)}

private def normalizingFactor {n : ℕ} (ψ : PositiveActual n) : ℝ :=
  (Real.sqrt (physicalMass (ψ.1 : Word n → ℂ)))⁻¹

private lemma normalizingFactor_pos {n : ℕ} (ψ : PositiveActual n) :
    0 < normalizingFactor ψ := inv_pos.mpr (Real.sqrt_pos.mpr ψ.property)

private def normalize {n : ℕ} (ψ : PositiveActual n) : MassOne n :=
  ⟨scaleActual (normalizingFactor ψ : ℂ) ψ.1, by
    change physicalMass ((normalizingFactor ψ : ℂ) • (ψ.1 : Word n → ℂ)) = 1
    rw [mass_real_scale]
    simp only [normalizingFactor, inv_pow, Real.sq_sqrt ψ.property.le]
    exact inv_mul_cancel₀ (ne_of_gt ψ.property)⟩

private lemma normalize_continuous (n : ℕ) : Continuous (@normalize n) := by
  have hc : Continuous (fun ψ : PositiveActual n => physicalMass (ψ.1 : Word n → ℂ)) :=
    (mass_continuous n).comp (continuous_subtype_val.comp continuous_subtype_val)
  have hf : Continuous (@normalizingFactor n) :=
    (Real.continuous_sqrt.comp hc).inv₀ (fun ψ => ne_of_gt (Real.sqrt_pos.mpr ψ.property))
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact (Complex.continuous_ofReal.comp hf).smul
    (continuous_subtype_val.comp continuous_subtype_val)

private lemma normalize_retract {n : ℕ} (ψ : MassOne n) :
    normalize (⟨ψ.1, by rw [ψ.property]; norm_num⟩ : PositiveActual n) = ψ := by
  apply Subtype.ext
  apply Subtype.ext
  change (normalizingFactor _ : ℂ) • (ψ.1 : Word n → ℂ) = _
  simp [normalizingFactor, ψ.property]

private lemma dense_massOne {n : ℕ} (P : MvPolynomial (Word n ⊕ Word n) ℝ)
    (hd : Dense (fullLocus (radialSOS P))) :
    Dense {ψ : MassOne n | ψ.1 ∈ fullLocus (radialSOS P)} := by
  have ho : IsOpen {ψ : openBoundaryMPS n | 0 < physicalMass (ψ : Word n → ℂ)} :=
    isOpen_lt continuous_const ((mass_continuous n).comp continuous_subtype_val)
  have hd' : Dense {ψ : PositiveActual n | ψ.1 ∈ fullLocus (radialSOS P)} :=
    hd.preimage ho.isOpenMap_subtype_val
  apply dense_iff_inter_open.mpr
  intro V hV hnV
  obtain ⟨u, hu⟩ := hnV
  let v : PositiveActual n := ⟨u.1, by rw [u.property]; norm_num⟩
  have hv : normalize v = u := normalize_retract u
  obtain ⟨w, hwV, hwG⟩ := hd'.inter_open_nonempty (normalize ⁻¹' V)
    (hV.preimage (normalize_continuous n)) ⟨v, by change normalize v ∈ V; rwa [hv]⟩
  refine ⟨normalize w, hwV, ?_⟩
  exact (fullLocus_scale P w.1 (normalizingFactor w) (normalizingFactor_pos w)).mpr hwG

private lemma phase_scale_iff {n : ℕ} (ψ φ : Word n → ℂ) (a : ℂ) (ha : a ≠ 0) :
    (∃ z : ℂ, ‖z‖ = 1 ∧ a • φ = z • (a • ψ)) ↔
      ∃ z : ℂ, ‖z‖ = 1 ∧ φ = z • ψ := by
  constructor
  · rintro ⟨z, hz, he⟩
    refine ⟨z, hz, ?_⟩
    funext w
    apply mul_left_cancel₀ ha
    have hw := congrFun he w
    change a * φ w = z * (a * ψ w) at hw
    change a * φ w = a * (z * ψ w)
    rw [hw]
    ring
  · rintro ⟨z, hz, he⟩
    refine ⟨z, hz, ?_⟩
    rw [he, smul_comm]

private lemma rescale_observation {n : ℕ} (p k q : ℕ) (h : ((p + k) + q) = n)
    (ψ φ : Word n → ℂ) (t : ℝ) (ht : 0 < t)
    (he : rawInterior p k q (castState h φ) =
      rawInterior p k q (castState h ((t : ℂ) • ψ))) :
    rawInterior p k q (castState h (((t⁻¹ : ℝ) : ℂ) • φ)) =
      rawInterior p k q (castState h ψ) := by
  rw [cast_scale, raw_scale, he, cast_scale, raw_scale, smul_smul]
  have hc : (Complex.normSq ((t⁻¹ : ℝ) : ℂ) : ℂ) *
      (Complex.normSq (t : ℂ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, Complex.ofReal_eq_one]
    simp only [Complex.normSq_ofReal]
    field_simp [ne_of_gt ht]
  rw [hc, one_smul]

private lemma normalized_witness {n : ℕ} (p k q : ℕ) (h : ((p + k) + q) = n)
    (ψ : MassOne n) (t : ℝ) (ht : 0 < t) (φ : openBoundaryMPS n)
    (he : rawInterior p k q (castState h (φ : Word n → ℂ)) =
      rawInterior p k q (castState h ((t : ℂ) • (ψ.1 : Word n → ℂ))))
    (hn : ¬ ∃ z : ℂ, ‖z‖ = 1 ∧ (φ : Word n → ℂ) =
      z • ((t : ℂ) • (ψ.1 : Word n → ℂ))) :
    ∃ χ : MassOne n,
      rawInterior p k q (castState h (χ.1 : Word n → ℂ)) =
        rawInterior p k q (castState h (ψ.1 : Word n → ℂ)) ∧
      ¬ ∃ z : ℂ, ‖z‖ = 1 ∧ (χ.1 : Word n → ℂ) = z • (ψ.1 : Word n → ℂ) := by
  have hm : physicalMass (φ : Word n → ℂ) = t ^ 2 := by
    rw [equal_raw_mass p k q h _ _ he, mass_real_scale, ψ.property, mul_one]
  let χ₀ := scaleActual (((t⁻¹ : ℝ) : ℂ)) φ
  have hχ : physicalMass (χ₀ : Word n → ℂ) = 1 := by
    change physicalMass ((((t⁻¹ : ℝ) : ℂ)) • (φ : Word n → ℂ)) = 1
    rw [mass_real_scale, hm, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 (ne_of_gt ht))]
  refine ⟨⟨χ₀,hχ⟩,rescale_observation p k q h _ _ t ht he,?_⟩
  rintro ⟨z,hz,hzχ⟩
  apply hn
  refine ⟨z,hz,?_⟩
  have hh := congrArg (fun f : Word n → ℂ => (t : ℂ) • f) hzχ
  change (t : ℂ) • ((((t⁻¹ : ℝ) : ℂ)) • (φ : Word n → ℂ)) =
    (t : ℂ) • (z • (ψ.1 : Word n → ℂ)) at hh
  simpa only [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt ht),
    Complex.ofReal_one, one_smul, mul_comm (t : ℂ) z] using hh

private lemma fullLocus_phase {n : ℕ} (P : MvPolynomial (Word n ⊕ Word n) ℝ)
    (hp : ∀ (ψ : openBoundaryMPS n) (z : ℂ), ‖z‖ = 1 →
      ∃ hz : z • (ψ : Word n → ℂ) ∈ openBoundaryMPS n,
        (⟨z • (ψ : Word n → ℂ), hz⟩ ∈ fullLocus P ↔ ψ ∈ fullLocus P))
    (ψ : openBoundaryMPS n) (z : ℂ) (hz : ‖z‖ = 1) :
    scaleActual z ψ ∈ fullLocus (radialSOS P) ↔ ψ ∈ fullLocus (radialSOS P) := by
  have hh (t : ℝ) : scaleActual (t : ℂ) (scaleActual z ψ) =
      scaleActual z (scaleActual (t : ℂ) ψ) := by
    apply Subtype.ext
    exact smul_comm _ _ _
  have hpz (ξ : openBoundaryMPS n) : scaleActual z ξ ∈ fullLocus P ↔ ξ ∈ fullLocus P := by
    obtain ⟨hz',hh⟩ := hp ξ z hz
    exact hh
  simp only [fullLocus_ray, hh, hpz]

set_option maxHeartbeats 2400000 in
/-- A literal real full-amplitude polynomial supplies one nonempty relatively open dense
physical-mass-one locus, saturated under unit phase, for all individual windows. -/
theorem result (m : ℕ) :
    ∃ P H : MvPolynomial (Word (3 + m) ⊕ Word (3 + m)) ℝ,
      P ≠ 0 ∧ H = (∑ d ∈ Finset.range (P.totalDegree + 1), (homogeneousComponent d P) ^ 2) ∧
      H ≠ 0 ∧
      let G : Set (MassOne (3 + m)) :=
        {ψ | eval (realCoordinates (ψ.1 : Word (3 + m) → ℂ)) H ≠ 0}
      G.Nonempty ∧ IsOpen G ∧ Dense G ∧
      (∀ (ψ : MassOne (3 + m)) (z : ℂ), ‖z‖ = 1 →
        ∃ φ : MassOne (3 + m), (φ.1 : Word (3 + m) → ℂ) =
          z • (ψ.1 : Word (3 + m) → ℂ) ∧ (φ ∈ G ↔ ψ ∈ G)) ∧
      ∀ ψ : MassOne (3 + m), ψ ∈ G →
        (∀ p q : ℕ, p + q = m → ∀ h : ((p + 3) + q) = 3 + m,
          ∀ φ : MassOne (3 + m),
            rawInterior p 3 q (castState h (φ.1 : Word (3 + m) → ℂ)) =
              rawInterior p 3 q (castState h (ψ.1 : Word (3 + m) → ℂ)) ↔
            ∃ z : ℂ, ‖z‖ = 1 ∧
              (φ.1 : Word (3 + m) → ℂ) = z • (ψ.1 : Word (3 + m) → ℂ)) ∧
        (∀ p q : ℕ, p + q = m + 1 → ∀ h : ((p + 2) + q) = 3 + m,
          ∃ φ : MassOne (3 + m),
            rawInterior p 2 q (castState h (φ.1 : Word (3 + m) → ℂ)) =
              rawInterior p 2 q (castState h (ψ.1 : Word (3 + m) → ℂ)) ∧
            ¬ ∃ z : ℂ, ‖z‖ = 1 ∧
              (φ.1 : Word (3 + m) → ℂ) = z • (ψ.1 : Word (3 + m) → ℂ)) ∧
        (∀ p q : ℕ, p + q = m + 2 → ∀ h : ((p + 1) + q) = 3 + m,
          ∃ φ : MassOne (3 + m),
            rawInterior p 1 q (castState h (φ.1 : Word (3 + m) → ℂ)) =
              rawInterior p 1 q (castState h (ψ.1 : Word (3 + m) → ℂ)) ∧
            ¬ ∃ z : ℂ, ‖z‖ = 1 ∧
              (φ.1 : Word (3 + m) → ℂ) = z • (ψ.1 : Word (3 + m) → ℂ)) := by
  obtain ⟨P,hP,hPn,hPo,hPd,hPphase,hR⟩ := OpenBoundaryMPSAllWindowC9.result m
  change (fullLocus P).Nonempty at hPn
  change Dense (fullLocus P) at hPd
  let H := radialSOS P
  have hsub : fullLocus P ⊆ fullLocus H := by
    intro ψ hψ
    apply (fullLocus_ray P ψ).mpr
    refine ⟨1,zero_lt_one,?_⟩
    simpa [scaleActual] using hψ
  have hHd : Dense (fullLocus H) := hPd.mono hsub
  obtain ⟨ψ₀,hψ₀⟩ := hPn
  have hH : H ≠ 0 := by
    intro hz
    have hh := hsub hψ₀
    change eval (realCoordinates (ψ₀ : Word (3 + m) → ℂ)) H ≠ 0 at hh
    exact hh (by rw [hz,map_zero])
  refine ⟨P,H,hP,rfl,hH,?_,?_,dense_massOne P hHd,?_,?_⟩
  · let ξ : PositiveActual (3 + m) := ⟨ψ₀,(mass_pos_iff _).mpr (hR ψ₀ hψ₀).1⟩
    refine ⟨normalize ξ,?_⟩
    exact (fullLocus_scale P ψ₀ (normalizingFactor ξ) (normalizingFactor_pos ξ)).mpr (hsub hψ₀)
  · exact (fullLocus_open H).preimage continuous_subtype_val
  · intro ψ z hz
    have hm : physicalMass (z • (ψ.1 : Word (3 + m) → ℂ)) = 1 := by
      rw [mass_scale, ψ.property, Complex.normSq_eq_norm_sq, hz]
      norm_num
    refine ⟨⟨scaleActual z ψ.1,hm⟩,rfl,?_⟩
    exact fullLocus_phase P hPphase ψ.1 z hz
  · intro ψ hψ
    obtain ⟨t,ht,hη⟩ := (fullLocus_ray P ψ.1).mp hψ
    let η := scaleActual (t : ℂ) ψ.1
    obtain ⟨_,hr,h2,h1⟩ := hR η hη
    have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
    refine ⟨?_,?_,?_⟩
    · intro p q hpq h φ
      rw [← phase_scale_iff (ψ.1 : Word (3 + m) → ℂ) (φ.1 : Word (3 + m) → ℂ) (t : ℂ) htC]
      have hh := hr p q hpq h (scaleActual (t : ℂ) φ.1)
      dsimp only [scaleActual, η] at hh
      rw [← hh]
      simp only [scaleActual, cast_scale, raw_scale]
      constructor
      · intro he
        rw [he]
      · intro he
        ext u v
        have hc : (Complex.normSq (t : ℂ) : ℂ) ≠ 0 := by
          exact_mod_cast (Complex.normSq_pos.mpr htC).ne'
        apply mul_left_cancel₀ hc
        exact congrFun (congrFun he u) v
    · intro p q hpq h
      obtain ⟨φ,_,he,hn⟩ := h2 p q hpq h
      exact normalized_witness p 2 q h ψ t ht φ he hn
    · intro p q hpq h
      obtain ⟨φ,_,he,hn⟩ := h1 p q hpq h
      exact normalized_witness p 1 q h ψ t ht φ he hn

end D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSNormalizedC9
