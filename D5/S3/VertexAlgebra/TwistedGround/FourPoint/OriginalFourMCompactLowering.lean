/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCompactLowering
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCompactLowering
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native occupation readout of the four inverse lowerings on arbitrary finite support. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAssignedOccupation

/-! The correction endpoint partitions and surviving native creators
assemble into the product of the four lowered oscillator words. Expand that
product on occupied monomials to remove the ambient finite support. -/

set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMCompactLowering

open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeDiscriminantTheta (gramReal)
open LatticeTwistedGroundRealization.SignQuotient (ModTwoCharge reduceCharge)
open OriginalFourMChargeCoset (fourierSign quadraticSign oscillatorLower)
open OriginalFourMAssignedOverlap (assignedChargeTerm assignedSector assigned_fourier_overlap)
open FourPoint.OriginalFourMActualChart
open OriginalFourMOccupationTransport (flags)
open OriginalFourMPhysicalCovariance (relative)
open OriginalFourMPhysicalProduct (physicalChargeSummand)
open OriginalFourMChartProduct (chartTau chartPeriod chart_charge_data)
open OriginalFourMSpatialWick (spatialCoefficient)
open OriginalFourMFixedChargeWick (Mode modeMatrix nativeModeCovariance nativeModeMean
  physical_marked_coefficient_assign)
open OriginalFourMInverseJets (inverseJetWeight)
open OriginalFourMSpatialWickPartition (liftedScale)
open OriginalFourMSpatialWickExtraction (partition_eq_filters)
open OriginalFourMAssignedOccupation (compactMode compactCovariance compactMean
  compactWordReadout compactCovariance_ab_symm compactCovariance_d_symm compact_charge_eq_punctures)
open OriginalGaussianSourceRestriction (CompactExternal)
open OriginalFourMWickLowering (pairWeight eval_word_partition)
open HalfFock.OriginalHalfCurrentWickPolynomial (word creator eval_word_eq_lowering)
open AffineOccurrenceWick (wick)
open AffineWickAssignments (assign)
open AffineWickConvolution (partitions)

open LatticePositiveEnergy (Exponent chargeEnergy)
open OriginalFourMSignedOverlap (chart_parameter_ne_one)
open D5.S3.Analytic.OriginalSlitNome (rank24Determinant slitNome)
open OriginalFourMDLipNome (dNome)
open OriginalFourMSectorContinuation (slitChargeTerm)
open OriginalGaussianSourceRestriction (compactExternal externalOccupation fourSupport)
open OriginalNormalRowSource (supportLabel restricted restricted_reconstruct embedded_weight)
open OriginalChargedRowSource (affineCoefficient affineMoment_coefficient)
open FactorialFockMetric (weight)

open private assignmentPolynomial affineReadout affineReadout_monomial assigned_word_affine
  word_slots from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAssignedOccupation
open private affine_enlarge sum_embDomain from
  D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceRestriction
open private chartA_nome chartB_nome chart_charge from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAFourCurrent
open private d_chart_charge dLipChargeTerm from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDFourCurrent
open private dDeterminant dMatrix dLinear from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipChannel

private abbrev Compact (D : LatticeData) (F : Finset (Index D)) :=
  CompactExternal D F ⊕ CompactExternal D F

/-- Native Wick evaluation reads each surviving occurrence in the compact
four-slot occupation with its literal factorial weights. -/
private theorem native_word_eq_compact {X : Type*} [Finite X] (D : LatticeData)
    (q : Charge D) (c : Chart) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (hc : (c = .A ∨ c = .B) ∧ ‖parameter c (x : ℂ)‖ < 1 ∨ c = .D)
    (slot : X → Puncture) (colour : X → Fin D.rank) {n : X → ℕ} (F : Finset (Index D))
    (hF : ∀ a : Mode n, (colour a.1, a.2.val) ∈ F) (w : List (Mode n)) :
    wick (nativeModeCovariance D c x slot colour n) (nativeModeMean D q c x slot colour n) w =
      compactWordReadout D q c x slot colour F hF w := by
  apply assigned_word_affine D q c x slot colour F hF _ w
  intro a b
  rcases hc with ⟨hc, hr⟩ | rfl
  · exact compactCovariance_ab_symm D c x F hc hr a b
  · exact compactCovariance_d_symm D hx hx₁ F a b

open Classical in
/-- The native Wick sum is the readout of the product of the four
puncture polynomials before multiplying by the chart and charge factors. -/
private theorem native_partition_product {X : Type*} [Fintype X] [DecidableEq X] (D : LatticeData)
    (q : Charge D) (c : Chart) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (hc : (c = .A ∨ c = .B) ∧ ‖parameter c (x : ℂ)‖ < 1 ∨ c = .D)
    (slot : X → Puncture) (colour : X → Fin D.rank) {n : X → ℕ} (F : Finset (Index D))
    (hF : ∀ a : Mode n, (colour a.1, a.2.val) ∈ F) (l : List X) :
    let slots : Finset Puncture := {.P, .Q, .R, .S}
    let scale a := liftedScale c x (slot a) (n a)
    let correction (i : Puncture) := Matrix.of fun a b =>
      pairWeight D (-loweringParameter c i) (colour a, n a) (colour b, n b)
    let U := modeMatrix c x slot n
    let f := compactMode D c slot colour F hF
    ((partitions l).map fun p => (p.1.map scale).prod *
      (∏ i ∈ slots, wick (correction i) 0 (p.1.filter fun a => decide (slot a = i))) *
      assign U p.2
        (wick (nativeModeCovariance D c x slot colour n)
          (nativeModeMean D q c x slot colour n))).sum =
      affineReadout (compactCovariance D c x F) (compactMean D q c x F)
        (∏ i ∈ slots, ((partitions (l.filter fun a => decide (slot a = i))).map fun p =>
          MvPolynomial.C ((p.1.map scale).prod * wick (correction i) 0 p.1) *
            assignmentPolynomial U f p.2).sum) := by
  dsimp only
  have hword :
      wick (nativeModeCovariance D c x slot colour n) (nativeModeMean D q c x slot colour n) =
        compactWordReadout D q c x slot colour F hF :=
    funext (native_word_eq_compact D q c hx hx₁ hc slot colour F hF)
  rw [hword]
  apply mul_left_cancel₀ (Complex.exp_ne_zero
    ((Real.pi : ℂ) * Complex.I * chartTau true c x * (bilinear D q q : ℂ) / 2))
  apply mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 12 (chart_charge_data true c hx hx₁).1))
  exact compact_charge_eq_punctures D q c hx hx₁ hc slot colour F hF l


variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Embed the oscillator variables of a given puncture into the compact
joint polynomial, sending oscillator indices outside the support to zero. -/
def tagOscillators (D : LatticeData) (c : Chart) (i : Puncture) (F : Finset (Index D)) :
    Oscillator D →ₐ[ℂ] MvPolynomial (Compact D F) ℂ :=
  MvPolynomial.aeval fun a => if h : a ∈ F then
    let b : {j // j ∈ F} := ⟨a, h⟩
    let e : CompactExternal D F := if (flags c i).2 then .inr b else .inl b
    MvPolynomial.X (if (flags c i).1 then .inr e else .inl e)
  else 0

private theorem creator_to_compact (D : LatticeData) (c : Chart) (x : ℝ)
    (slot : X → Puncture) (colour : X → Fin D.rank) (n : X → ℕ) (F : Finset (Index D))
    (hF : ∀ a : Mode n, (colour a.1, a.2.val) ∈ F) (a : X) :
    (∑ k, modeMatrix c x slot n a k •
      MvPolynomial.X (compactMode D c slot colour F hF k)) =
      liftedScale c x (slot a) (n a) •
        tagOscillators D c (slot a) F
          ((creator D (colour a, n a)).eval (MvPolynomial.C (-loweringParameter c (slot a)))) := by
  classical
  let m := n a
  let i := slot a
  let θ := -loweringParameter c i
  let T := tagOscillators D c i F
  let W : ℕ → MvPolynomial (Compact D F) ℂ := fun k =>
    Ring.choose ((m : ℂ) + 1 / 2) k •
      (θ ^ k • T (MvPolynomial.X (colour a, m - k)))
  have hT : T ((creator D (colour a, m)).eval (MvPolynomial.C θ)) =
      ∑ k ∈ Finset.range (m + 1), W k := by
    simp only [T, creator, W, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
      map_sum, map_mul, map_pow, MvPolynomial.C_eq_algebraMap, AlgHom.commutes,
      MvPolynomial.smul_eq_C_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hT, ← Finset.sum_range_reflect W (m + 1)]
  simp only [liftedScale, Finset.smul_sum, MvPolynomial.smul_eq_C_mul,
    modeMatrix, Matrix.of_apply, Fintype.sum_sigma, apply_ite, map_zero, ite_mul, zero_mul]
  rw [Finset.sum_eq_single a]
  · simp only [ite_true]
    have he : (∑ k : Fin (m + 1),
        MvPolynomial.C (relative c i * inverseJetWeight c x i m k) *
          MvPolynomial.X (compactMode D c slot colour F hF ⟨a, k⟩)) =
        ∑ k : Fin (m + 1), MvPolynomial.C (liftedScale c x i m) * W (m - k) := by
      apply Finset.sum_congr rfl
      intro k _
      have hk : m - (m - k.val) = k.val := by omega
      simp only [W, hk, T, tagOscillators, MvPolynomial.aeval_X,
        dite_eq_left (hF ⟨a, k⟩), compactMode, θ, MvPolynomial.smul_eq_C_mul,
        inverseJetWeight, liftedScale, map_mul, map_pow]
      ring
    change _ = ∑ k ∈ Finset.range (m + 1),
      MvPolynomial.C (liftedScale c x i m) * W (m + 1 - 1 - k)
    rw [he, Fin.sum_univ_eq_sum_range
      (fun k => MvPolynomial.C (liftedScale c x i m) * W (m - k)) (m + 1)]
    simp only [Nat.add_sub_cancel]
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

private theorem word_scales {Y : Type*} {R : Type*} [CommMonoid R]
    (s : Y → R) (l : List Y) (p : List Y × List Y) (hp : p ∈ partitions l) :
    (p.1.map s).prod * (p.2.map s).prod = (l.map s).prod := by
  induction l generalizing p with
  | nil =>
    simp [partitions] at hp
    subst p
    simp
  | cons a l ih =>
    simp only [partitions, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩ <;>
      simp only [List.map_cons, List.prod_cons] <;>
      rw [← ih q hq] <;> ac_rfl

private theorem list_prod_scale {Y I : Type*} (s : Y → ℂ) (v : Y → MvPolynomial I ℂ)
    (l : List Y) : (l.map fun a => s a • v a).prod = (l.map s).prod • (l.map v).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, ih, smul_mul_smul_comm]

/-- A physical fixed-charge marked jet is the readout of the four actual
lowering words in the tagged compact algebra, with one lifted scale per occurrence. -/
theorem physical_marked_compact_lowering (D : LatticeData) (hu : IsUnit D.G.det)
    (slot : X → Puncture) (colour : X → Fin D.rank) (upperA : Bool) (c : Chart)
    {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (hc : (c = .A ∨ c = .B) ∧ ‖parameter c (x : ℂ)‖ < 1 ∨ c = .D ∧ upperA = true)
    (q : Charge D) (n : X → ℕ) (l : List X) (hl : l.Nodup)
    (F : Finset (Index D)) (hF : ∀ a : Mode n, (colour a.1, a.2.val) ∈ F) :
    spatialCoefficient (Sum.elim n (fun _ => 1)) (l.map Sum.inr ++ l.map Sum.inl)
      (physicalChargeSummand D slot colour upperA c x q) 0 =
    Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau upperA c x * (bilinear D q q : ℂ) / 2) *
      ((l.map fun a => liftedScale c x (slot a) (n a)).prod *
        affineReadout (compactCovariance D c x F) (compactMean D q c x F)
          (open Classical in ∏ i ∈ ({.P, .Q, .R, .S} : Finset Puncture),
            tagOscillators D c i F
              ((word D ((l.filter fun a => decide (slot a = i)).map fun a => (colour a, n a))).eval
                (MvPolynomial.C (-loweringParameter c i))))) := by
  classical
  let slots : Finset Puncture := {.P, .Q, .R, .S}
  let s a := liftedScale c x (slot a) (n a)
  let B i a := tagOscillators D c i F
    ((creator D (colour a, n a)).eval (MvPolynomial.C (-loweringParameter c i)))
  let R := affineReadout (compactCovariance D c x F) (compactMean D q c x F)
  let C (i : Puncture) := Matrix.of fun a b => pairWeight D (-loweringParameter c i)
    (colour a, n a) (colour b, n b)
  let subword (i : Puncture) := l.filter fun a => decide (slot a = i)
  have hcols (a : X) : slot a ∈ slots := by cases slot a <;> simp [slots]
  have hc' : (c = .A ∨ c = .B) ∧ ‖parameter c (x : ℂ)‖ < 1 ∨ c = .D :=
    hc.imp id And.left
  rw [physical_marked_coefficient_assign D hu slot colour upperA c hx hx₁ hc q n l hl,
    native_partition_product D q c hx hx₁ hc' slot colour F hF l]
  congr 1
  have hpuncture (i : Puncture) :
      ((partitions (subword i)).map fun p =>
        MvPolynomial.C ((p.1.map s).prod * wick (C i) 0 p.1) *
          assignmentPolynomial (modeMatrix c x slot n) (compactMode D c slot colour F hF) p.2).sum =
      ((subword i).map s).prod •
        tagOscillators D c i F
          ((word D ((subword i).map fun a => (colour a, n a))).eval
            (MvPolynomial.C (-loweringParameter c i))) := by
    have hfactor (p : List X × List X) (hp : p ∈ partitions (subword i)) :
        MvPolynomial.C ((p.1.map s).prod * wick (C i) 0 p.1) *
            assignmentPolynomial (modeMatrix c x slot n) (compactMode D c slot colour F hF) p.2 =
          ((subword i).map s).prod •
            (MvPolynomial.C (wick (C i) 0 p.1) * (p.2.map (B i)).prod) := by
      have hslot (a : X) (ha : a ∈ p.2) : slot a = i := by
        have hsub := (partition_eq_filters (subword i) p (hl.filter _) hp).2
        rw [← hsub] at ha
        exact of_decide_eq_true (List.mem_filter.mp (List.mem_of_mem_filter ha)).2
      simp only [assignmentPolynomial, creator_to_compact D c x slot colour n F hF]
      change _ * (p.2.map fun a => s a • B (slot a) a).prod = _
      rw [show (p.2.map fun a => s a • B (slot a) a) = p.2.map (fun a => s a • B i a) from
        List.map_congr_left fun a ha => by rw [hslot a ha], list_prod_scale]
      rw [← word_scales s _ p hp]
      simp only [MvPolynomial.smul_eq_C_mul, map_mul]
      ring
    have hsum :
        ((partitions (subword i)).map fun p =>
          ((subword i).map s).prod •
            (MvPolynomial.C (wick (C i) 0 p.1) * (p.2.map (B i)).prod)).sum =
        ((subword i).map s).prod •
          (((partitions (subword i)).map fun p =>
            MvPolynomial.C (wick (C i) 0 p.1) * (p.2.map (B i)).prod).sum) := by
      rw [List.smul_sum, List.map_map]
      rfl
    rw [show _ = _ from congrArg List.sum (List.map_congr_left hfactor), hsum]
    congr 1
    have h := congrArg (tagOscillators D c i F)
      (eval_word_partition D hu (-loweringParameter c i) (fun a => (colour a, n a)) (subword i))
    simpa only [map_list_sum, List.map_map, Function.comp_def, map_mul, map_list_prod,
      MvPolynomial.C_eq_algebraMap, AlgHom.commutes, B, C] using h.symm
  change R (∏ i ∈ slots, ((partitions (subword i)).map fun p =>
      MvPolynomial.C ((p.1.map s).prod * wick (C i) 0 p.1) *
        assignmentPolynomial (modeMatrix c x slot n)
          (compactMode D c slot colour F hF) p.2).sum) = _
  simp only [hpuncture, MvPolynomial.smul_eq_C_mul, Finset.prod_mul_distrib]
  rw [← map_prod (MvPolynomial.C (σ := Compact D F)), ← MvPolynomial.smul_eq_C_mul,
    map_smul, smul_eq_mul]
  rw [word_slots slot slots s l (fun a _ => hcols a)]

/-- The finite inverse lowering of the actual oscillator product at a
puncture. The cutoff is one past the degree of its finite Wick word. -/
def punctureLowering (D : LatticeData) (c : Chart) (i : Puncture)
    (modes : List (Index D)) : Oscillator D :=
  ∑ k ∈ Finset.range ((word D modes).natDegree + 1),
    ((-loweringParameter c i) ^ k / (k.factorial : ℂ)) •
      (oscillatorLower D ^ k) ((modes.map MvPolynomial.X).prod)

private theorem punctureLowering_eq (D : LatticeData) (hu : IsUnit D.G.det)
    (c : Chart) (i : Puncture) (modes : List (Index D)) :
    punctureLowering D c i modes =
      (word D modes).eval (MvPolynomial.C (-loweringParameter c i)) :=
  (eval_word_eq_lowering D hu modes _ _ (Nat.lt_succ_self _)).symm

open Classical in
/-- The normalized charge summand evaluated on the product of the four
actual finite inverse lowerings. -/
def loweredChargeTerm (D : LatticeData) (slot : X → Puncture) (colour : X → Fin D.rank)
    (upperA : Bool) (c : Chart) (x : ℝ) (q : Charge D) (n : X → ℕ) (l : List X)
    (F : Finset (Index D)) : ℂ :=
  (chartPeriod upperA c x ^ (12 : ℕ))⁻¹ *
    (Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau upperA c x * (bilinear D q q : ℂ) / 2) *
      ((l.map fun a => liftedScale c x (slot a) (n a)).prod *
        affineReadout (compactCovariance D c x F) (compactMean D q c x F)
          (∏ i ∈ ({.P, .Q, .R, .S} : Finset Puncture),
            tagOscillators D c i F (punctureLowering D c i
              ((l.filter fun a => decide (slot a = i)).map fun a => (colour a, n a))))))

/-- The normalized physical marked coefficient at fixed charge transports
to the native affine array on the four simultaneous inverse lowerings. -/
theorem assigned_eq_lowered (D : LatticeData) (hu : IsUnit D.G.det)
    (slot : X → Puncture) (colour : X → Fin D.rank) (upperA : Bool) (c : Chart)
    {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (hc : (c = .A ∨ c = .B) ∧ ‖parameter c (x : ℂ)‖ < 1 ∨ c = .D ∧ upperA = true)
    (q : Charge D) (n : X → ℕ) (l : List X) (hl : l.Nodup)
    (F : Finset (Index D)) (hF : ∀ a : Mode n, (colour a.1, a.2.val) ∈ F) :
    assignedChargeTerm D slot colour upperA c x q n l =
      loweredChargeTerm D slot colour upperA c x q n l F := by
  classical
  unfold assignedChargeTerm loweredChargeTerm
  simp only [punctureLowering_eq D hu]
  rw [← physical_marked_coefficient_assign D hu slot colour upperA c hx hx₁ hc q n l hl,
    physical_marked_compact_lowering D hu slot colour upperA c hx hx₁ hc q n l hl F hF]

/-- The actual four-lowering compact readout inherits both rank-24 Fourier
crossings on the real overlap for arbitrary occurrence modes. -/
theorem lowered_fourier_overlap (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (hr : D.rank = 24)
    (slot : X → Puncture) (colour : X → Fin D.rank)
    {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) {w : ℂ}
    (hwA : w ^ 2 = parameter .A x) (hw : ‖w‖ < 1)
    (a : ModTwoCharge D) (n : X → ℕ) (l : List X) (hl : l.Nodup)
    (F : Finset (Index D)) (hF : ∀ a : Mode n, (colour a.1, a.2.val) ∈ F) :
    let V := fun c b => ∑' q : {q : Charge D // reduceCharge D q = b},
      loweredChargeTerm D slot colour true c x q.val n l F
    V .D a = ((2 : ℂ) ^ (12 : ℕ))⁻¹ * (∑ b, fourierSign D a b * V .A b) ∧
    V .B a = (periodRoot .A x ^ (12 : ℕ))⁻¹ *
      (((2 : ℂ) ^ (12 : ℕ))⁻¹ * ∑ b, fourierSign D a b * quadraticSign D b * V .A b) := by
  classical
  have hA : ‖parameter .A (x : ℂ)‖ < 1 := by
    rw [← hwA, norm_pow]
    nlinarith [norm_nonneg w]
  have hB : ‖parameter .B (x : ℂ)‖ < 1 := by
    simpa [parameter, Complex.norm_real, abs_of_pos hx] using hx₁
  have he (c : Chart) (hc : (c = .A ∨ c = .B) ∧ ‖parameter c (x : ℂ)‖ < 1 ∨
      c = .D ∧ true = true) (b : ModTwoCharge D) :
      assignedSector D slot colour true c x b n l =
        ∑' q : {q : Charge D // reduceCharge D q = b},
          loweredChargeTerm D slot colour true c x q.val n l F := by
    unfold assignedSector
    exact tsum_congr fun q =>
      assigned_eq_lowered D hu slot colour true c hx hx₁ hc q.val n l hl F hF
  have h := assigned_fourier_overlap D hu hD hr slot colour hx hx₁ hwA hw a n l hl
  dsimp only at h ⊢
  simpa only [he .A (Or.inl ⟨Or.inl rfl, hA⟩), he .B (Or.inl ⟨Or.inr rfl, hB⟩),
    he .D (Or.inr ⟨rfl, rfl⟩)] using h

private def determinant (c : Chart) (x : ℝ) : ℂ :=
  match c with
  | .A | .B => rank24Determinant (parameter c (x : ℂ))
  | .D => dDeterminant true (parameter .D (x : ℂ))

private def nome (c : Chart) (x : ℝ) : ℂ :=
  match c with
  | .A | .B => slitNome (parameter c (x : ℂ))
  | .D => dNome true (parameter .D (x : ℂ))

open Classical in
/-- The literal charge-energy power and rank-24 determinant multiply the
weighted compact readout of the four original inverse lowering flows. -/
private theorem lowered_charge_normalization {X : Type*} (D : LatticeData)
    (slot : X → Puncture) (colour : X → Fin D.rank) (upperA : Bool) (c : Chart)
    {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) (hD : c = .D → upperA = true)
    (q : Charge D) (hq : 0 ≤ chargeEnergy D q) (n : X → ℕ) (l : List X)
    (F : Finset (Index D)) :
    loweredChargeTerm D slot colour upperA c x q n l F =
      (((1 - parameter c (x : ℂ)) ^ (3 : ℕ)) *
        (l.map fun a => liftedScale c x (slot a) (n a)).prod) *
        (determinant c x * nome c x ^ (chargeEnergy D q).toNat *
          affineReadout (compactCovariance D c x F) (compactMean D q c x F)
            (∏ i ∈ ({.P, .Q, .R, .S} : Finset Puncture),
              tagOscillators D c i F (punctureLowering D c i
                ((l.filter fun a => decide (slot a = i)).map fun a => (colour a, n a))))) := by
  have he : Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau upperA c x *
      (bilinear D q q : ℂ) / 2) = nome c x ^ (chargeEnergy D q).toNat := by
    cases c with
    | A => exact chart_charge D q hq upperA .A x (chartA_nome upperA hx hx₁)
    | B => exact chart_charge D q hq upperA .B x (chartB_nome upperA hx hx₁)
    | D =>
      obtain rfl := hD rfl
      exact d_chart_charge D q hq hx hx₁
  have hp : determinant c x = ((1 - parameter c (x : ℂ)) ^ (3 : ℕ))⁻¹ *
      (chartPeriod upperA c x ^ (12 : ℕ))⁻¹ := by
    cases c with
    | A => rfl
    | B => rfl
    | D =>
      obtain rfl := hD rfl
      rfl
  have hz : (1 - parameter c (x : ℂ)) ^ (3 : ℕ) ≠ 0 :=
    pow_ne_zero _ (chart_parameter_ne_one hx hx₁ c)
  rw [loweredChargeTerm, he, hp]
  generalize (1 - parameter c (x : ℂ)) ^ (3 : ℕ) = z at hz ⊢
  field_simp [hz]


/-- Native left input, left output, right input and right output, in that order. -/
def nativePuncture : Chart → Fin 4 → Puncture
  | .A => ![.P, .Q, .R, .S]
  | .B => ![.Q, .R, .P, .S]
  | .D => ![.P, .R, .Q, .S]

private def nativeTag (D : LatticeData) (F : Finset (Index D)) (i : Fin 4) :
    {b // b ∈ F} ↪ Compact D F :=
  ![Function.Embedding.inl.trans Function.Embedding.inl,
    Function.Embedding.inr.trans Function.Embedding.inl,
    Function.Embedding.inl.trans Function.Embedding.inr,
    Function.Embedding.inr.trans Function.Embedding.inr] i

private theorem tag_monomial (D : LatticeData) (c : Chart) (i : Fin 4)
    (F : Finset (Index D)) (d : Exponent D) (hd : d.support ⊆ F) (a : ℂ) :
    tagOscillators D c (nativePuncture c i) F (MvPolynomial.monomial d a) =
      MvPolynomial.monomial ((restricted D F d).embDomain (nativeTag D F i)) a := by
  have ht (b : {b // b ∈ F}) :
      (if h : b.val ∈ F then
        let e : CompactExternal D F :=
          if (flags c (nativePuncture c i)).2 then .inr ⟨b.val, h⟩ else .inl ⟨b.val, h⟩
        MvPolynomial.X (if (flags c (nativePuncture c i)).1 then .inr e else .inl e)
      else (0 : MvPolynomial (Compact D F) ℂ)) = MvPolynomial.X (nativeTag D F i b) := by
    rw [dite_eq_left b.property]
    cases c <;> fin_cases i <;> rfl
  rw [tagOscillators, MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq]
  congr 1
  conv_lhs => rw [← restricted_reconstruct D F d hd]
  rw [Finsupp.prod_embDomain, Finsupp.prod_embDomain]
  exact Finsupp.prod_congr fun b _ => congrArg (· ^ restricted D F d b) (ht b)

private theorem tagged_product (D : LatticeData) (c : Chart) (F : Finset (Index D))
    (b g d e : Exponent D) (hb : b.support ⊆ F) (hg : g.support ⊆ F)
    (hd : d.support ⊆ F) (he : e.support ⊆ F) (v w y z : ℂ) :
    tagOscillators D c (nativePuncture c 0) F (MvPolynomial.monomial b v) *
        (tagOscillators D c (nativePuncture c 1) F (MvPolynomial.monomial g w) *
          (tagOscillators D c (nativePuncture c 2) F (MvPolynomial.monomial d y) *
            tagOscillators D c (nativePuncture c 3) F (MvPolynomial.monomial e z))) =
      MvPolynomial.monomial (externalOccupation D F b g d e) (v * (w * (y * z))) := by
  classical
  rw [tag_monomial D c 0 F b hb, tag_monomial D c 1 F g hg,
    tag_monomial D c 2 F d hd, tag_monomial D c 3 F e he]
  simp only [MvPolynomial.monomial_mul_monomial]
  apply congrArg (fun d : Compact D F →₀ ℕ =>
    MvPolynomial.monomial d (v * (w * (y * z))))
  simp only [externalOccupation, Finsupp.sumElim_eq_add, Finsupp.mapDomain_add,
    Finsupp.embDomain_eq_mapDomain]
  change Finsupp.mapDomain (Sum.inl ∘ Sum.inl) (restricted D F b) +
    (Finsupp.mapDomain (Sum.inl ∘ Sum.inr) (restricted D F g) +
      (Finsupp.mapDomain (Sum.inr ∘ Sum.inl) (restricted D F d) +
        Finsupp.mapDomain (Sum.inr ∘ Sum.inr) (restricted D F e))) = _
  simp only [Finsupp.mapDomain_comp]
  ac_rfl

private def inclusion (D : LatticeData) {E F : Finset (Index D)} (h : E ⊆ F) :
    {b // b ∈ E} ↪ {b // b ∈ F} where
  toFun b := ⟨b.val, h b.property⟩
  inj' := fun _ _ hEq => Subtype.ext (congrArg (fun b : {b // b ∈ F} => b.val) hEq)

private theorem restrict_extend (D : LatticeData) {E F : Finset (Index D)}
    (h : E ⊆ F) (d : Exponent D) (hd : d.support ⊆ E) :
    (restricted D E d).embDomain (inclusion D h) = restricted D F d := by
  apply Finsupp.embDomain_injective (supportLabel D F)
  rw [← Finsupp.embDomain_trans_apply]
  change (restricted D E d).embDomain (supportLabel D E) =
    (restricted D F d).embDomain (supportLabel D F)
  rw [restricted_reconstruct D E d hd, restricted_reconstruct D F d (hd.trans h)]

private abbrev compactInclusion (D : LatticeData) {E F : Finset (Index D)}
    (h : E ⊆ F) : Compact D E ↪ Compact D F :=
  let f := inclusion D h
  (f.sumMap f).sumMap (f.sumMap f)

private theorem covariance_inclusion (D : LatticeData) (c : Chart) (x : ℝ)
    {E F : Finset (Index D)} (h : E ⊆ F) (i j : Compact D E) :
    compactCovariance D c x F (compactInclusion D h i) (compactInclusion D h j) =
      compactCovariance D c x E i j := by
  cases c <;> rcases i with (i | i) <;> rcases j with (j | j) <;>
    cases i <;> cases j <;> rfl

private theorem mean_inclusion (D : LatticeData) (q : Charge D) (c : Chart) (x : ℝ)
    {E F : Finset (Index D)} (h : E ⊆ F) (i : Compact D E) :
    compactMean D q c x F (compactInclusion D h i) = compactMean D q c x E i := by
  cases c <;> rcases i with (i | i) <;> cases i <;> rfl

/-- A common support and the four occupied supports give the same native coefficient.
The inclusion acts on oscillator indices separately in each native slot. -/
theorem affineCoefficient_fourSupport (D : LatticeData) (q : Charge D) (c : Chart) (x : ℝ)
    (F : Finset (Index D)) (b g d e : Exponent D) (h : fourSupport D b g d e ⊆ F) :
    let E := fourSupport D b g d e
    affineCoefficient (compactCovariance D c x F) (compactMean D q c x F)
        (externalOccupation D F b g d e) =
      affineCoefficient (compactCovariance D c x E) (compactMean D q c x E)
        (externalOccupation D E b g d e) := by
  classical
  let E := fourSupport D b g d e
  have hb : b.support ⊆ E := by intro i hi; simp [E, fourSupport, hi]
  have hg : g.support ⊆ E := by intro i hi; simp [E, fourSupport, hi]
  have hd : d.support ⊆ E := by intro i hi; simp [E, fourSupport, hi]
  have he : e.support ⊆ E := by intro i hi; simp [E, fourSupport, hi]
  have hocc : (externalOccupation D E b g d e).embDomain (compactInclusion D h) =
      externalOccupation D F b g d e := by
    simp only [externalOccupation, compactInclusion, sum_embDomain]
    rw [restrict_extend D h b hb, restrict_extend D h g hg,
      restrict_extend D h d hd, restrict_extend D h e he]
  change _ = affineCoefficient (compactCovariance D c x E) (compactMean D q c x E)
    (externalOccupation D E b g d e)
  rw [← hocc, affine_enlarge]
  have hC : (fun i j => compactCovariance D c x F (compactInclusion D h i)
      (compactInclusion D h j)) = compactCovariance D c x E :=
    funext fun i => funext fun j => covariance_inclusion D c x h i j
  have hM : (fun i => compactMean D q c x F (compactInclusion D h i)) =
      compactMean D q c x E := funext fun i => mean_inclusion D q c x h i
  rw [hC, hM]

private theorem external_weight (D : LatticeData) (F : Finset (Index D))
    (b g d e : Exponent D) (hb : b.support ⊆ F) (hg : g.support ⊆ F)
    (hd : d.support ⊆ F) (he : e.support ⊆ F) :
    weight (externalOccupation D F b g d e) = (weight b * weight g) * (weight d * weight e) := by
  have hw (u : Exponent D) (hu : u.support ⊆ F) : weight (restricted D F u) = weight u := by
    rw [← embedded_weight D (supportLabel D F), restricted_reconstruct D F u hu]
  calc
    weight (externalOccupation D F b g d e) =
        (weight (restricted D F b) * weight (restricted D F g)) *
          (weight (restricted D F d) * weight (restricted D F e)) := by
      simp only [externalOccupation, weight, Finsupp.prod_sumElim, Function.comp_def]
    _ = _ := by rw [hw b hb, hw g hg, hw d hd, hw e he]

/-- Multilinear evaluation of four oscillator polynomials on occupation values,
including the four separate factorial Fock weights. -/
def occupationReadout (D : LatticeData) (P Q R S : Oscillator D)
    (f : Exponent D → Exponent D → Exponent D → Exponent D → ℂ) : ℂ :=
  ∑ b ∈ P.support, ∑ g ∈ Q.support, ∑ d ∈ R.support, ∑ e ∈ S.support,
    (P.coeff b * Q.coeff g * R.coeff d * S.coeff e) *
      (weight b : ℂ) * (weight g : ℂ) * (weight d : ℂ) * (weight e : ℂ) * f b g d e

/-- Fixed-charge term in the literal native coordinate. -/
def nativeChargeTerm (D : LatticeData) (c : Chart) (x : ℝ) (q : Charge D)
    (b g d e : Exponent D) : ℂ :=
  match c with
  | .A | .B => slitChargeTerm D b g d e q (parameter c (x : ℂ))
  | .D => dLipChargeTerm D b g d e q (parameter .D (x : ℂ))

private theorem nativeChargeTerm_coeff (D : LatticeData) (c : Chart) (x : ℝ)
    (q : Charge D) (b g d e : Exponent D) :
    let E := fourSupport D b g d e
    nativeChargeTerm D c x q b g d e =
      determinant c x * nome c x ^ (chargeEnergy D q).toNat *
        affineCoefficient (compactCovariance D c x E) (compactMean D q c x E)
          (externalOccupation D E b g d e) := by
  cases c with
  | A => rfl
  | B => rfl
  | D =>
    let E := fourSupport D b g d e
    let t := parameter .D (x : ℂ)
    have hK : dMatrix D true (compactExternal D E) t = compactCovariance D .D x E := by
      funext i j
      rcases i with (i | i) | (i | i) <;> rcases j with (j | j) | (j | j) <;> rfl
    have hμ : (fun i =>
        (bilinear D (unitCharge D (Sum.elim (compactExternal D E) (compactExternal D E) i).2.1)
          q : ℂ) * dLinear D true (compactExternal D E) t i) = compactMean D q .D x E := by
      funext i
      rcases i with (i | i) | (i | i) <;> rfl
    change dDeterminant true t * dNome true t ^ (chargeEnergy D q).toNat *
        affineCoefficient _ _ (externalOccupation D E b g d e) = _
    rw [hK, hμ]
    rfl

private theorem product_native {R : Type*} [CommMonoid R] (c : Chart) (f : Puncture → R) :
    (open Classical in ∏ i ∈ ({.P, .Q, .R, .S} : Finset Puncture), f i) =
      f (nativePuncture c 0) *
        (f (nativePuncture c 1) * (f (nativePuncture c 2) * f (nativePuncture c 3))) := by
  classical
  have hP : Puncture.P ∉ ({.Q, .R, .S} : Finset Puncture) := by simp
  have hQ : Puncture.Q ∉ ({.R, .S} : Finset Puncture) := by simp
  have hR : Puncture.R ∉ ({.S} : Finset Puncture) := by simp
  rw [Finset.prod_insert hP, Finset.prod_insert hQ, Finset.prod_insert hR, Finset.prod_singleton]
  cases c with
  | A => rfl
  | B => change f .P * (f .Q * (f .R * f .S)) = f .Q * (f .R * (f .P * f .S))
         ac_rfl
  | D => change f .P * (f .Q * (f .R * f .S)) = f .P * (f .R * (f .Q * f .S))
         ac_rfl

private theorem compact_readout_eq_occupied (D : LatticeData) (q : Charge D) (c : Chart) (x : ℝ)
    (z : ℂ)
    (F : Finset (Index D)) (P Q R S : Oscillator D)
    (hP : P.vars ⊆ F) (hQ : Q.vars ⊆ F) (hR : R.vars ⊆ F) (hS : S.vars ⊆ F) :
    z *
      affineReadout (compactCovariance D c x F) (compactMean D q c x F)
        (tagOscillators D c (nativePuncture c 0) F P *
          (tagOscillators D c (nativePuncture c 1) F Q *
            (tagOscillators D c (nativePuncture c 2) F R *
              tagOscillators D c (nativePuncture c 3) F S))) =
      occupationReadout D P Q R S (fun b g d e =>
        let E := fourSupport D b g d e
        z * affineCoefficient (compactCovariance D c x E) (compactMean D q c x E)
          (externalOccupation D E b g d e)) := by
  classical
  let T := affineReadout (compactCovariance D c x F) (compactMean D q c x F)
  change _ * T _ = _
  conv_lhs => rw [P.as_sum, Q.as_sum, R.as_sum, S.as_sum]
  unfold occupationReadout
  conv_lhs =>
    simp only [map_sum, Finset.sum_mul]
    simp only [Finset.mul_sum, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro g hg
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  have hb' := (MvPolynomial.support_subset_vars_of_mem_support hb).trans hP
  have hg' := (MvPolynomial.support_subset_vars_of_mem_support hg).trans hQ
  have hd' := (MvPolynomial.support_subset_vars_of_mem_support hd).trans hR
  have he' := (MvPolynomial.support_subset_vars_of_mem_support he).trans hS
  have hF : fourSupport D b g d e ⊆ F := by
    simpa only [fourSupport, Finset.union_subset_iff] using
      And.intro (And.intro (And.intro hb' hg') hd') he'
  rw [tagged_product D c F b g d e hb' hg' hd' he']
  have hm (a : ℂ) : T (MvPolynomial.monomial (externalOccupation D F b g d e) a) =
      a * ((weight (externalOccupation D F b g d e) : ℂ) *
        affineCoefficient (compactCovariance D c x F) (compactMean D q c x F)
          (externalOccupation D F b g d e)) := by
    rw [show MvPolynomial.monomial (externalOccupation D F b g d e) a =
        a • MvPolynomial.monomial (externalOccupation D F b g d e) 1 by
          simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one],
      map_smul, smul_eq_mul]
    dsimp only [T]
    rw [affineReadout_monomial, affineMoment_coefficient]
  rw [hm, external_weight D F b g d e hb' hg' hd' he',
    affineCoefficient_fourSupport D q c x F b g d e hF]
  push_cast
  ring

/-- Expand the actual tagged Fock polynomials before choosing the support of
each individual occupation. A mode can occur with any multiplicity in every slot. -/
theorem compact_readout_eq_native (D : LatticeData) (q : Charge D) (c : Chart) (x : ℝ)
    (F : Finset (Index D)) (P Q R S : Oscillator D)
    (hP : P.vars ⊆ F) (hQ : Q.vars ⊆ F) (hR : R.vars ⊆ F) (hS : S.vars ⊆ F) :
    determinant c x * nome c x ^ (chargeEnergy D q).toNat *
      affineReadout (compactCovariance D c x F) (compactMean D q c x F)
        (tagOscillators D c (nativePuncture c 0) F P *
          (tagOscillators D c (nativePuncture c 1) F Q *
            (tagOscillators D c (nativePuncture c 2) F R *
              tagOscillators D c (nativePuncture c 3) F S))) =
      occupationReadout D P Q R S (nativeChargeTerm D c x q) := by
  have h : nativeChargeTerm D c x q = fun b g d e =>
      let E := fourSupport D b g d e
      determinant c x * nome c x ^ (chargeEnergy D q).toNat *
        affineCoefficient (compactCovariance D c x E) (compactMean D q c x E)
          (externalOccupation D E b g d e) := by
    funext b g d e
    exact nativeChargeTerm_coeff D c x q b g d e
  rw [h]
  exact compact_readout_eq_occupied D q c x
    (determinant c x * nome c x ^ (chargeEnergy D q).toNat) F P Q R S hP hQ hR hS

open Classical in
/-- The lowered polynomial at a physical puncture, before the signed spatial scales. -/
def loweredOscillator {X : Type*} (D : LatticeData) (slot : X → Puncture)
    (colour : X → Fin D.rank) (c : Chart) (n : X → ℕ) (l : List X)
    (i : Puncture) : Oscillator D :=
  punctureLowering D c i ((l.filter fun a => decide (slot a = i)).map fun a => (colour a, n a))

/-- The actual normalized four-lowering coefficient equals the native fixed-charge
readout on its variable supports, with the literal A, B and true D slot orders. -/
theorem lowered_charge_eq_native_occupations {X : Type*} (D : LatticeData)
    (slot : X → Puncture) (colour : X → Fin D.rank) (upperA : Bool) (c : Chart)
    {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) (hD : c = .D → upperA = true)
    (q : Charge D) (hq : 0 ≤ chargeEnergy D q) (n : X → ℕ) (l : List X)
    (F : Finset (Index D))
    (hF : ∀ i, (loweredOscillator D slot colour c n l i).vars ⊆ F) :
    let A := loweredOscillator D slot colour c n l ∘ nativePuncture c
    loweredChargeTerm D slot colour upperA c x q n l F =
      ((1 - parameter c (x : ℂ)) ^ (3 : ℕ) *
        (l.map fun a => liftedScale c x (slot a) (n a)).prod) *
      occupationReadout D (A 0) (A 1) (A 2) (A 3) (nativeChargeTerm D c x q) := by
  classical
  dsimp only
  rw [lowered_charge_normalization D slot colour upperA c hx hx₁ hD q hq n l F]
  rw [product_native c (fun i =>
    tagOscillators D c i F (punctureLowering D c i
      ((l.filter fun a => decide (slot a = i)).map fun a => (colour a, n a))))]
  exact congrArg (fun z : ℂ => _ * z) (compact_readout_eq_native D q c x F
    _ _ _ _ (hF (nativePuncture c 0)) (hF (nativePuncture c 1))
    (hF (nativePuncture c 2)) (hF (nativePuncture c 3)))


/-- The normalized four-lowering summand is independent of any ambient
finite set containing the variables of the four actual lowered polynomials. -/
theorem loweredChargeTerm_support_independent {X : Type*} (D : LatticeData)
    (slot : X → Puncture) (colour : X → Fin D.rank) (upperA : Bool) (c : Chart)
    (x : ℝ) (q : Charge D) (n : X → ℕ) (l : List X) (F G : Finset (Index D))
    (hF : ∀ i, (loweredOscillator D slot colour c n l i).vars ⊆ F)
    (hG : ∀ i, (loweredOscillator D slot colour c n l i).vars ⊆ G) :
    loweredChargeTerm D slot colour upperA c x q n l F =
      loweredChargeTerm D slot colour upperA c x q n l G := by
  classical
  let A := loweredOscillator D slot colour c n l
  have readout (E : Finset (Index D)) (hE : ∀ i, (A i).vars ⊆ E) :
      affineReadout (compactCovariance D c x E) (compactMean D q c x E)
          (∏ i ∈ ({.P, .Q, .R, .S} : Finset Puncture), tagOscillators D c i E (A i)) =
        occupationReadout D (A (nativePuncture c 0)) (A (nativePuncture c 1))
          (A (nativePuncture c 2)) (A (nativePuncture c 3)) (fun b g d e =>
            let B := fourSupport D b g d e
            affineCoefficient (compactCovariance D c x B) (compactMean D q c x B)
              (externalOccupation D B b g d e)) := by
    rw [product_native]
    simpa only [one_mul] using compact_readout_eq_occupied D q c x 1 E _ _ _ _
      (hE (nativePuncture c 0)) (hE (nativePuncture c 1))
      (hE (nativePuncture c 2)) (hE (nativePuncture c 3))
  unfold loweredChargeTerm
  change _ * (_ * (_ * affineReadout _ _
    (∏ i ∈ ({.P, .Q, .R, .S} : Finset Puncture), tagOscillators D c i F (A i)))) =
    _ * (_ * (_ * affineReadout _ _
      (∏ i ∈ ({.P, .Q, .R, .S} : Finset Puncture), tagOscillators D c i G (A i))))
  rw [readout F hF, readout G hG]

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMCompactLowering
