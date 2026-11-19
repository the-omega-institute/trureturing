/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteGenericity
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteGenericity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A real-polynomial open dense locus of four-site periodic two-site recovery. -/

import D5.S3.Quantum.TensorNetworks.PeriodicMPSFourSiteRecovery
import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityGenericity

/-! The real certificate is intrinsic to the six amplitudes of the actual state. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFourSiteGenericity

open Matrix MvPolynomial
open scoped BigOperators
open PeriodicMPSParentIntersection (Bond Word)
open UniformMPSExpectedDimensionRefutation (traceWord)
open PeriodicMPSFourSiteRecovery
open PeriodicMPSTwoSiteAmbiguity (rawTwo)
open PeriodicMPSFourSiteResidualFormula (triplet)
open PeriodicMPSFourSiteResidueLift (certificateValue map_certificateValue tensorTriplet
  map_tensorTriplet physical_certificate_nonzero)
open OpenBoundaryMPSDensityGenericity
  (realCoeff imagCoeff coefficient_eval realCoordinates polynomial_nonzero_dense)

noncomputable section

/-- The actual four-site periodic binary bond-two state image. -/
def actualStates : Set (Word 4 → ℂ) :=
  Set.range (traceWord 2 2 4 : (Fin 2 → Bond) → Word 4 → ℂ)

private def necklaceWords : Fin 6 → Word 4 :=
  ![![0, 0, 0, 0], ![1, 0, 0, 0], ![1, 1, 0, 0], ![1, 0, 1, 0], ![1, 1, 1, 0], ![1, 1, 1, 1]]

private def tripletFrom {R : Type*} [CommRing R] (a : Fin 6 → R) :
    Matrix (Fin 3) (Fin 3) R :=
  triplet (a 0) (a 1) (a 2) (a 3) (a 4) (a 5)

private def certificatePolynomial (ι : Type*) (a : Fin 6 → ι) : MvPolynomial (ι ⊕ ι) ℂ :=
  let forward i := X (.inl (a i)) + C Complex.I * X (.inr (a i))
  let reverse i := X (.inl (a i)) - C Complex.I * X (.inr (a i))
  certificateValue (tripletFrom forward) (tripletFrom reverse)

/-- A real polynomial in the full amplitudes whose nonvanishing certifies recovery. -/
def realCertificate : MvPolynomial (Word 4 ⊕ Word 4) ℝ :=
  let p := certificatePolynomial (Word 4) necklaceWords
  realCoeff p ^ 2 + imagCoeff p ^ 2

private lemma map_tripletFrom {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a : Fin 6 → R) :
    f.mapMatrix (tripletFrom a) = tripletFrom (f ∘ a) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [tripletFrom, triplet, RingHom.mapMatrix_apply, Matrix.map_apply, map_ofNat]

private lemma certificatePolynomial_eval (ψ : Word 4 → ℂ) :
    eval (fun i => ((realCoordinates ψ i : ℝ) : ℂ))
      (certificatePolynomial (Word 4) necklaceWords) =
    certificateValue (tripletFrom (ψ ∘ necklaceWords)) (tripletFrom (star ∘ ψ ∘ necklaceWords)) := by
  unfold certificatePolynomial
  rw [map_certificateValue, map_tripletFrom, map_tripletFrom]
  have hx : (eval fun i => ((realCoordinates ψ i : ℝ) : ℂ)) ∘
      (fun i => X (.inl (necklaceWords i)) + C Complex.I * X (.inr (necklaceWords i))) =
      ψ ∘ necklaceWords := by
    funext i
    simp only [Function.comp_apply, map_add, map_mul, eval_X, eval_C, realCoordinates, Sum.elim_inl, Sum.elim_inr]
    rw [mul_comm Complex.I, Complex.re_add_im]
  have hy : (eval fun i => ((realCoordinates ψ i : ℝ) : ℂ)) ∘
      (fun i => X (.inl (necklaceWords i)) - C Complex.I * X (.inr (necklaceWords i))) =
      star ∘ ψ ∘ necklaceWords := by
    funext i
    apply Complex.ext <;> simp [realCoordinates, Complex.star_def, Complex.mul_re, Complex.mul_im]
  rw [hx, hy]

/-- The nonvanishing test depends on the full state and its conjugate amplitudes. -/
theorem realCertificate_eval (ψ : Word 4 → ℂ) :
    eval (realCoordinates ψ) realCertificate =
      Complex.normSq
        (certificateValue (tripletFrom (ψ ∘ necklaceWords)) (tripletFrom (star ∘ ψ ∘ necklaceWords))) := by
  let p := certificatePolynomial (Word 4) necklaceWords
  obtain ⟨hr, hi⟩ := coefficient_eval p (realCoordinates ψ)
  unfold realCertificate
  change eval (realCoordinates ψ) (realCoeff p ^ 2 + imagCoeff p ^ 2) = _
  rw [map_add, map_pow, map_pow, hr, hi]
  change (eval _ (certificatePolynomial (Word 4) necklaceWords)).re ^ 2 +
    (eval _ (certificatePolynomial (Word 4) necklaceWords)).im ^ 2 = _
  rw [certificatePolynomial_eval]
  simp [Complex.normSq_apply, pow_two]

private abbrev Entry := Fin 2 × Fin 2 × Fin 2

private def coordinates (A : Fin 2 → Bond) : (Entry ⊕ Entry) → ℝ :=
  realCoordinates (fun k : Entry => A k.1 k.2.1 k.2.2)

private def tensor (x : (Entry ⊕ Entry) → ℝ) : Fin 2 → Bond :=
  fun i j k => x (.inl (i, j, k)) + Complex.I * x (.inr (i, j, k))

private lemma tensor_coordinates (A : Fin 2 → Bond) : tensor (coordinates A) = A := by
  funext i j k
  simp only [tensor, coordinates, realCoordinates, Sum.elim_inl, Sum.elim_inr]
  rw [mul_comm Complex.I, Complex.re_add_im]

private def parameterPolynomial : MvPolynomial (Entry ⊕ Entry) ℂ :=
  let A : Fin 2 → Matrix (Fin 2) (Fin 2) (MvPolynomial (Entry ⊕ Entry) ℂ) :=
    fun i j k => X (.inl (i, j, k)) + C Complex.I * X (.inr (i, j, k))
  let B : Fin 2 → Matrix (Fin 2) (Fin 2) (MvPolynomial (Entry ⊕ Entry) ℂ) :=
    fun i j k => X (.inl (i, j, k)) - C Complex.I * X (.inr (i, j, k))
  certificateValue (tensorTriplet A) (tensorTriplet B)

private lemma parameter_eval (x : (Entry ⊕ Entry) → ℝ) :
    eval (fun k => (x k : ℂ)) parameterPolynomial =
      certificateValue (tensorTriplet (tensor x))
        (tensorTriplet (conjugateTensor (tensor x))) := by
  let e := eval (fun k => (x k : ℂ))
  let A : Fin 2 → Matrix (Fin 2) (Fin 2) (MvPolynomial (Entry ⊕ Entry) ℂ) :=
    fun i => Matrix.of fun j k => X (.inl (i, j, k)) + C Complex.I * X (.inr (i, j, k))
  let B : Fin 2 → Matrix (Fin 2) (Fin 2) (MvPolynomial (Entry ⊕ Entry) ℂ) :=
    fun i => Matrix.of fun j k => X (.inl (i, j, k)) - C Complex.I * X (.inr (i, j, k))
  change e (certificateValue (tensorTriplet A) (tensorTriplet B)) = _
  have hA : (fun i => e.mapMatrix (A i)) = tensor x := by
    funext i
    apply Matrix.ext
    intro j k
    simp [A, tensor, e, RingHom.mapMatrix_apply, Matrix.map_apply]
  have hB : (fun i => e.mapMatrix (B i)) = conjugateTensor (tensor x) := by
    funext i
    apply Matrix.ext
    intro j k
    apply Complex.ext <;> simp [B, tensor, conjugateTensor, e, Complex.star_def,
      Complex.mul_re, Complex.mul_im, RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [map_certificateValue, map_tensorTriplet, map_tensorTriplet, hA, hB]

private def parameterTest : MvPolynomial (Entry ⊕ Entry) ℝ :=
  realCoeff parameterPolynomial ^ 2 + imagCoeff parameterPolynomial ^ 2

private lemma parameterTest_eval (x : (Entry ⊕ Entry) → ℝ) :
    eval x parameterTest =
      Complex.normSq (certificateValue (tensorTriplet (tensor x))
        (tensorTriplet (conjugateTensor (tensor x)))) := by
  obtain ⟨hr, hi⟩ := coefficient_eval parameterPolynomial x
  rw [parameterTest, map_add, map_pow, map_pow, hr, hi, parameter_eval]
  simp [Complex.normSq_apply, pow_two]

private lemma realCertificate_actual (A : Fin 2 → Bond) :
    eval (realCoordinates (traceWord 2 2 4 A)) realCertificate ≠ 0 ↔
      certificate (tensorTriplet A) (tensorTriplet (conjugateTensor A)) := by
  have hl : (traceWord 2 2 4 A) ∘ necklaceWords = PeriodicMPSFourSiteRecovery.letters A := by
    funext i
    fin_cases i <;> rfl
  have hr : tripletFrom (star ∘ traceWord 2 2 4 A ∘ necklaceWords) =
      tensorTriplet (conjugateTensor A) := by
    have hu : star ∘ traceWord 2 2 4 A ∘ necklaceWords =
        (starRingEnd ℂ) ∘ ((traceWord 2 2 4 A) ∘ necklaceWords) := rfl
    rw [hu, ← map_tripletFrom, hl, PeriodicMPSFourSiteRecovery.letters_eq]
    exact map_tensorTriplet (starRingEnd ℂ) A
  rw [realCertificate_eval, hr, hl, PeriodicMPSFourSiteRecovery.letters_eq, certificate_iff]
  exact not_congr Complex.normSq_eq_zero

private def parameterState (x : (Entry ⊕ Entry) → ℝ) : Word 4 → ℂ :=
  traceWord 2 2 4 (tensor x)

private lemma parameterState_range : Set.range parameterState = actualStates := by
  apply Set.Subset.antisymm
  · rintro ψ ⟨x, rfl⟩
    exact ⟨tensor x, rfl⟩
  · rintro ψ ⟨A, rfl⟩
    exact ⟨coordinates A, by rw [parameterState, tensor_coordinates]⟩

private lemma parameterState_continuous : Continuous parameterState := by
  unfold parameterState tensor
  apply continuous_pi
  intro w
  change Continuous (fun x : (Entry ⊕ Entry) → ℝ => (List.ofFn (fun i : Fin 4 =>
    (Matrix.of fun j k : Fin 2 => (x (.inl (w i, j, k)) : ℂ) +
      Complex.I * x (.inr (w i, j, k))))).prod.trace)
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  fun_prop

/-- The certificate is nonzero on a nonempty relatively open dense subset
of the actual four-site state image. -/
theorem actual_locus_open_dense :
    IsOpen {ψ : actualStates | eval (realCoordinates ψ.val) realCertificate ≠ 0} ∧
    Dense {ψ : actualStates | eval (realCoordinates ψ.val) realCertificate ≠ 0} := by
  constructor
  · apply isOpen_ne_fun _ continuous_const
    exact (continuous_eval _).comp
      (OpenBoundaryMPSDensityGenericity.continuous_realCoordinates.comp continuous_subtype_val)
  · obtain ⟨A, hA⟩ := physical_certificate_nonzero
    have hpoint : eval (coordinates A) parameterTest ≠ 0 := by
      rw [parameterTest_eval, tensor_coordinates]
      exact (not_congr Complex.normSq_eq_zero).mpr hA
    have hd := polynomial_nonzero_dense parameterTest (coordinates A) hpoint
    let f : ((Entry ⊕ Entry) → ℝ) → actualStates := fun x =>
      ⟨parameterState x, ⟨tensor x, rfl⟩⟩
    have hf : Continuous f := parameterState_continuous.subtype_mk _
    have hs : Function.Surjective f := by
      rintro ⟨ψ, A, rfl⟩
      refine ⟨coordinates A, Subtype.ext ?_⟩
      change traceWord 2 2 4 (tensor (coordinates A)) = _
      rw [tensor_coordinates]
    apply dense_iff_inter_open.mpr
    intro V hv hne
    obtain ⟨ψ, hψ⟩ := hne
    obtain ⟨x, rfl⟩ := hs ψ
    obtain ⟨y, hy, hytest⟩ := hd.inter_open_nonempty _ (hv.preimage hf) ⟨x, hψ⟩
    refine ⟨f y, hy, (realCertificate_actual (tensor y)).mpr ?_⟩
    rw [certificate_iff]
    change eval y parameterTest ≠ 0 at hytest
    rw [parameterTest_eval] at hytest
    exact (not_congr Complex.normSq_eq_zero).mp hytest


/-- Over a nonempty relatively open dense part of the actual four-site periodic
state image, the adjacent two-site marginal determines the amplitude up to unit phase. -/
theorem generic_unitPhase_recovery :
    ∃ G : Set actualStates, G.Nonempty ∧ IsOpen G ∧ Dense G ∧
      ∀ (A B : Fin 2 → Bond),
        (⟨traceWord 2 2 4 A, ⟨A, rfl⟩⟩ : actualStates) ∈ G →
        rawTwo B 0 = rawTwo A 0 →
        ∃ c : ℂ, ‖c‖ = 1 ∧ traceWord 2 2 4 B = c • traceWord 2 2 4 A := by
  let G : Set actualStates := {ψ | eval (realCoordinates ψ.val) realCertificate ≠ 0}
  obtain ⟨hopen, hdense⟩ := actual_locus_open_dense
  obtain ⟨A, hA⟩ := physical_certificate_nonzero
  have hA' : (⟨traceWord 2 2 4 A, ⟨A, rfl⟩⟩ : actualStates) ∈ G :=
    (realCertificate_actual A).mpr ((certificate_iff _ _).mpr hA)
  refine ⟨G, ⟨_, hA'⟩, hopen, hdense, ?_⟩
  intro T U hT h
  exact unitPhase_of_rawTwo_eq T U ((realCertificate_actual T).mp hT) h


private lemma traceWord_scale (z : ℂ) (A : Fin 2 → Bond) :
    traceWord 2 2 4 (z • A) = z ^ 4 • traceWord 2 2 4 A := by
  funext w
  change ((z • A (w 0)) * ((z • A (w 1)) *
    ((z • A (w 2)) * ((z • A (w 3)) * 1)))).trace =
      z ^ 4 * (A (w 0) * (A (w 1) * (A (w 2) * (A (w 3) * 1)))).trace
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul, smul_eq_mul]
  ring

private lemma actual_scale (z : ℂ) (ψ : Word 4 → ℂ) (h : ψ ∈ actualStates) :
    z • ψ ∈ actualStates := by
  obtain ⟨A, rfl⟩ := h
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq z (n := 4) (by decide)
  exact ⟨t • A, (traceWord_scale t A).trans (by rw [ht])⟩

/-- The total mass of a four-site amplitude. -/
def mass (ψ : Word 4 → ℂ) : ℝ := ∑ w, Complex.normSq (ψ w)

/-- The unit-mass slice of the actual state image. -/
abbrev normalizedStates := {ψ : actualStates // mass ψ.val = 1}

private abbrev positiveStates := {ψ : actualStates // 0 < mass ψ.val}

private lemma mass_continuous : Continuous mass := by
  unfold mass
  fun_prop

private lemma mass_scale (z : ℝ) (ψ : Word 4 → ℂ) :
    mass ((z : ℂ) • ψ) = z ^ 2 * mass ψ := by
  simp only [mass, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, Complex.normSq_ofReal,
    sq, Finset.mul_sum]

private def normalize (ψ : positiveStates) : normalizedStates :=
  ⟨⟨(((Real.sqrt (mass ψ.val.val))⁻¹ : ℝ) : ℂ) • ψ.val.val,
      actual_scale _ _ ψ.val.property⟩, by
    change mass ((((Real.sqrt (mass ψ.val.val))⁻¹ : ℝ) : ℂ) • ψ.val.val) = 1
    rw [mass_scale, inv_pow, Real.sq_sqrt ψ.property.le, inv_mul_cancel₀ ψ.property.ne']⟩

private lemma normalize_continuous : Continuous normalize := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  change Continuous (fun ψ : positiveStates =>
    (((Real.sqrt (mass ψ.val.val))⁻¹ : ℝ) : ℂ) • ψ.val.val)
  have hmass : Continuous (fun ψ : positiveStates => mass ψ.val.val) :=
    mass_continuous.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hs := (Real.continuous_sqrt.comp hmass).inv₀
    (fun ψ => (Real.sqrt_pos.2 ψ.property).ne')
  exact (Complex.continuous_ofReal.comp hs).smul
    (continuous_subtype_val.comp continuous_subtype_val)

private lemma normalize_surjective : Function.Surjective normalize := by
  intro ψ
  let x : positiveStates := ⟨ψ.val, by rw [ψ.property]; exact zero_lt_one⟩
  refine ⟨x, Subtype.ext (Subtype.ext ?_)⟩
  change (((Real.sqrt (mass ψ.val.val))⁻¹ : ℝ) : ℂ) • ψ.val.val = ψ.val.val
  simp [ψ.property]

/-- The positive rays through the certified states meet the unit-mass slice
in a relatively open dense set. -/
theorem normalized_locus_open_dense :
    IsOpen {ψ : normalizedStates | ∃ t : ℝ, 0 < t ∧
      eval (realCoordinates ((t : ℂ) • ψ.val.val)) realCertificate ≠ 0} ∧
    Dense {ψ : normalizedStates | ∃ t : ℝ, 0 < t ∧
      eval (realCoordinates ((t : ℂ) • ψ.val.val)) realCertificate ≠ 0} := by
  constructor
  · have hu : {ψ : normalizedStates | ∃ t : ℝ, 0 < t ∧
        eval (realCoordinates ((t : ℂ) • ψ.val.val)) realCertificate ≠ 0} =
        ⋃ t : {r : ℝ // 0 < r}, {ψ | eval (realCoordinates ((t.val : ℂ) • ψ.val.val))
          realCertificate ≠ 0} := by
      ext ψ
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Subtype.exists]
      tauto
    rw [hu]
    apply isOpen_iUnion
    intro t
    apply isOpen_ne_fun _ continuous_const
    have hval : Continuous (fun ψ : normalizedStates => ψ.val.val) :=
      continuous_subtype_val.comp continuous_subtype_val
    have hscaled : Continuous (fun ψ : normalizedStates => (t.val : ℂ) • ψ.val.val) :=
      (continuous_const_smul (t.val : ℂ)).comp hval
    exact (continuous_eval _).comp
      (OpenBoundaryMPSDensityGenericity.continuous_realCoordinates.comp hscaled)
  · let G : Set actualStates := {ψ | eval (realCoordinates ψ.val) realCertificate ≠ 0}
    have hopen : IsOpen {ψ : actualStates | 0 < mass ψ.val} :=
      isOpen_lt continuous_const (mass_continuous.comp continuous_subtype_val)
    have hd : Dense ((Subtype.val : positiveStates → actualStates) ⁻¹' G) :=
      actual_locus_open_dense.2.preimage hopen.isOpenMap_subtype_val
    apply dense_iff_inter_open.mpr
    intro V hV hnV
    obtain ⟨ψ, hψ⟩ := hnV
    obtain ⟨x, rfl⟩ := normalize_surjective ψ
    obtain ⟨y, hy, hyG⟩ := hd.inter_open_nonempty _ (hV.preimage normalize_continuous) ⟨x, hψ⟩
    refine ⟨normalize y, hy, Real.sqrt (mass y.val.val), Real.sqrt_pos.2 y.property, ?_⟩
    have hrt : (Real.sqrt (mass y.val.val)) ≠ 0 := (Real.sqrt_pos.2 y.property).ne'
    change eval (realCoordinates
      (((Real.sqrt (mass y.val.val)) : ℂ) •
        (((Real.sqrt (mass y.val.val))⁻¹ : ℝ) : ℂ) • y.val.val)) realCertificate ≠ 0
    rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hrt, Complex.ofReal_one, one_smul]
    exact hyG


private lemma rawTwo_scale (z : ℂ) (A : Fin 2 → Bond) :
    rawTwo (z • A) 0 = (star (z ^ 4) * z ^ 4) • rawTwo A 0 := by
  have h : PeriodicMPSParentIntersection.twoFlattening (z • A) 0 =
      z ^ 4 • PeriodicMPSParentIntersection.twoFlattening A 0 := by
    apply Matrix.ext
    intro i j
    exact congrFun (traceWord_scale z A) (Fin.append ![i.1, i.2] j)
  simp only [rawTwo, h, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

/-- The unit-mass reconstruction statement on the relatively open dense
positive-ray saturation of the full-amplitude certificate. -/
theorem normalized_generic_unitPhase_recovery :
    ∃ G : Set normalizedStates, G.Nonempty ∧ IsOpen G ∧ Dense G ∧
      ∀ (A B : Fin 2 → Bond) (hA : mass (traceWord 2 2 4 A) = 1),
        (⟨⟨traceWord 2 2 4 A, ⟨A, rfl⟩⟩, hA⟩ : normalizedStates) ∈ G →
        rawTwo B 0 = rawTwo A 0 →
        ∃ c : ℂ, ‖c‖ = 1 ∧ traceWord 2 2 4 B = c • traceWord 2 2 4 A := by
  let G : Set normalizedStates := {ψ | ∃ t : ℝ, 0 < t ∧
    eval (realCoordinates ((t : ℂ) • ψ.val.val)) realCertificate ≠ 0}
  obtain ⟨hopen, hdense⟩ := normalized_locus_open_dense
  obtain ⟨A, hA⟩ := physical_certificate_nonzero
  have hcert : eval (realCoordinates (traceWord 2 2 4 A)) realCertificate ≠ 0 :=
    (realCertificate_actual A).mpr ((certificate_iff _ _).mpr hA)
  have hmass : 0 < mass (traceWord 2 2 4 A) := by
    apply lt_of_le_of_ne (Finset.sum_nonneg fun w _ => Complex.normSq_nonneg _)
    intro hzero
    have hz : traceWord 2 2 4 A = 0 := by
      funext w
      exact Complex.normSq_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => Complex.normSq_nonneg (traceWord 2 2 4 A j))).mp hzero.symm w (Finset.mem_univ w))
    rw [hz, realCertificate_eval] at hcert
    apply hcert
    have hleft : tripletFrom ((0 : Word 4 → ℂ) ∘ necklaceWords) = 0 := by
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [tripletFrom, triplet]
    rw [hleft]
    simp [certificateValue]
  let x : positiveStates := ⟨⟨traceWord 2 2 4 A, ⟨A, rfl⟩⟩, hmass⟩
  letI : Nonempty normalizedStates := ⟨normalize x⟩
  have ne : G.Nonempty := hdense.nonempty
  refine ⟨G, ne, hopen, hdense, ?_⟩
  intro T U hT hG eqGram
  obtain ⟨t, ht, hρ⟩ := hG
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (t : ℂ) (n := 4) (by decide)
  have hn : s ^ 4 ≠ 0 := by rw [hs]; exact_mod_cast ht.ne'
  have hρ' : eval (realCoordinates (traceWord 2 2 4 (s • T))) realCertificate ≠ 0 := by
    rw [traceWord_scale, hs]
    exact hρ
  have he : rawTwo (s • U) 0 = rawTwo (s • T) 0 := by
    rw [rawTwo_scale, rawTwo_scale, eqGram]
  obtain ⟨c, hc, hampl⟩ := unitPhase_of_rawTwo_eq (s • T) (s • U)
    ((realCertificate_actual (s • T)).mp hρ') he
  refine ⟨c, hc, ?_⟩
  rw [traceWord_scale, traceWord_scale, smul_comm c] at hampl
  exact smul_right_injective _ hn hampl


end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFourSiteGenericity
