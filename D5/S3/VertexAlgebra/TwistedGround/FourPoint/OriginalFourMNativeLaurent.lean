/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeLaurent
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeLaurent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native occupation readout and its Laurent evaluation in the three charts. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeOccupation

/-! Native occupation support and Laurent evaluation after inverse lowering. -/

set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
open scoped BigOperators Matrix TensorProduct Topology

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMVariableSupport

open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeDiscriminantTheta (gramReal)
open LatticePositiveEnergy (Exponent chargeEnergy chargeEnergy_nonneg)
open LatticeTwistedGroundRealization.SignQuotient (ModTwoCharge reduceCharge)
open FourPoint.OriginalFourMActualChart
open FourPoint.OriginalFourMChargeNormal (compact_charge_normal projectOccupations)
open OriginalFourMEnergyCoefficient (selector leftExponent doubledWeight)
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod (slitDomain ball_subset_slitDomain)
open D5.S3.Analytic.OriginalSlitNome (slitNome_norm_lt_one)
open OriginalFourMDLipNome (dNome_norm_lt_one)
open OriginalFourMChargeCoset (fourierSign quadraticSign oscillatorLower)
open OriginalFourMCompactLowering (tagOscillators punctureLowering loweredChargeTerm
  assigned_eq_lowered lowered_fourier_overlap)
open OriginalFourMLoweredNormalization (lowered_charge_normalization)
open OriginalFourMOccupationTransport (flags)
open OriginalFourMSpatialWickPartition (liftedScale)
open OriginalFourMFixedChargeWick (Mode)
open OriginalFourMAssignedOccupation (compactCovariance compactMean)
open OriginalFourMAssignmentPolynomial (affineReadout)
open OriginalFourMSectorContinuation (slitMatrix slitLinear slitChargeTerm slitChargeSector
  dLipChargeSector)
open OriginalFourMChargeCoset (slitDiagonal)
open FourPoint.OriginalFourMChargeGerm (diagonalSewn)
open LatticeHalfFockChargedTensorCoefficients (ActualGround)
open LatticeHalfFockGradedTrace (actualTensorL0)
open OriginalFourMEnergyCoefficient (lowered_left_selector right_selector)
open LatticePositiveEnergy (chargeEnergy_zero)
open OriginalGaussianSourceRestriction (CompactExternal compactExternal
  externalOccupation fourSupport)
open OriginalNormalRowSource (supportLabel restricted restricted_reconstruct embedded_weight)
open OriginalChargedRowSource (affineCoefficient affineMoment_coefficient)
open FactorialFockMetric (weight)

open private affine_enlarge sum_embDomain from
  D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceRestriction
open private affineReadout_monomial from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAssignmentPolynomial
open private determinant nome from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMLoweredNormalization
open private dLipNumerator from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipChannel
open private dMatrix dLinear from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipChannel
open private dLipChargeTerm from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDFourCurrent

open private Compact product_native nativeChargeTerm_coeff from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeOccupation

open Classical in
/-- A single finite support covers the assigned modes and the variables of all
three chart transports. Each fixed native value still uses its own four supports. -/
def commonSupport {X : Type*} [Fintype X] (D : LatticeData) (slot : X → Puncture)
    (colour : X → Fin D.rank) (n : X → ℕ) (l : List X) : Finset (Index D) :=
  (Finset.univ.image fun a : Mode n => (colour a.1, a.2.val)) ∪
    (({.A, .B, .D} : Finset Chart).biUnion fun c =>
      ({.P, .Q, .R, .S} : Finset Puncture).biUnion
        fun i => (loweredOscillator D slot colour c n l i).vars)

private theorem mode_mem_common {X : Type*} [Fintype X] (D : LatticeData)
    (slot : X → Puncture) (colour : X → Fin D.rank) (n : X → ℕ) (l : List X)
    (a : Mode n) : (colour a.1, a.2.val) ∈ commonSupport D slot colour n l :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)

private theorem vars_subset_common {X : Type*} [Fintype X] (D : LatticeData)
    (slot : X → Puncture) (colour : X → Fin D.rank) (n : X → ℕ) (l : List X)
    (c : Chart) (i : Puncture) :
    (loweredOscillator D slot colour c n l i).vars ⊆ commonSupport D slot colour n l :=
  by
    classical
    intro j hj
    have hc : c ∈ ({.A, .B, .D} : Finset Chart) := by cases c <;> simp
    have hi : i ∈ ({.P, .Q, .R, .S} : Finset Puncture) := by cases i <;> simp
    exact Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨c, hc, Finset.mem_biUnion.mpr ⟨i, hi, hj⟩⟩)

/-- The literal native sector in chart coordinates. -/
def nativeSector (D : LatticeData) (c : Chart) (x : ℝ) (a : ModTwoCharge D)
    (b g d e : Exponent D) : ℂ :=
  match c with
  | .A | .B => slitChargeSector D a b g d e (parameter c (x : ℂ))
  | .D => dLipChargeSector D true a b g d e (parameter .D (x : ℂ))

private theorem sector_eq_tsum (D : LatticeData) (c : Chart) (x : ℝ)
    (a : ModTwoCharge D) (b g d e : Exponent D) :
    nativeSector D c x a b g d e =
      ∑' q : {q : Charge D // reduceCharge D q = a}, nativeChargeTerm D c x q.val b g d e := by
  classical
  let fibre : Set (Charge D) := {q | reduceCharge D q = a}
  let f (q : Charge D) := nativeChargeTerm D c x q b g d e
  calc
    _ = ∑' q, fibre.indicator f q := by
      cases c <;> apply tsum_congr <;> intro q <;> by_cases h : reduceCharge D q = a <;>
        simp [nativeSector, slitChargeSector, dLipChargeSector, fibre, Set.indicator, h, f,
          nativeChargeTerm, dLipChargeTerm]
    _ = _ := (tsum_subtype fibre f).symm

private theorem native_term_summable (D : LatticeData) (hD : (gramReal D).PosDef)
    (c : Chart) (x : ℝ) (hn : ‖nome c x‖ < 1) (a : ModTwoCharge D)
    (b g d e : Exponent D) :
    Summable (fun q : {q : Charge D // reduceCharge D q = a} =>
      nativeChargeTerm D c x q.val b g d e) := by
  let F := fourSupport D b g d e
  let k := compactExternal D F
  let r := parameter c (x : ℂ)
  let K : Matrix (Compact D F) (Compact D F) ℂ := compactCovariance D c x F
  let u : Compact D F → ℂ := fun i => match c with
    | .A | .B => slitLinear D k r i
    | .D => dLinear D true k r i
  have hm (q : Charge D) : compactMean D q c x F = fun i =>
      (bilinear D (unitCharge D (Sum.elim k k i).2.1) q : ℂ) * u i := by
    cases c <;> rfl
  obtain ⟨⟨bound, hs, hb⟩, _⟩ :=
    compact_charge_normal D hD b g d e ({0} : Set ℂ) isCompact_singleton
      (fun _ => determinant c x) (fun _ => nome c x)
      (differentiableOn_const _) (differentiableOn_const _) (fun _ _ => hn)
      (fun _ => K) (fun _ => u) (fun _ _ => differentiableOn_const _)
      (fun _ => differentiableOn_const _)
  apply Summable.of_norm_bounded (hs.subtype {q | reduceCharge D q = a})
  intro q
  rw [nativeChargeTerm_coeff, hm]
  exact hb q.val 0 (Set.mem_singleton 0)

private theorem tsum_occupationReadout {I : Type*} (D : LatticeData) (P Q R S : Oscillator D)
    (f : I → Exponent D → Exponent D → Exponent D → Exponent D → ℂ)
    (h : ∀ b g d e, Summable (fun q => f q b g d e)) :
    (∑' q, occupationReadout D P Q R S (f q)) =
      occupationReadout D P Q R S (fun b g d e => ∑' q, f q b g d e) := by
  classical
  let S₄ := P.support ×ˢ (Q.support ×ˢ (R.support ×ˢ S.support))
  let C (a : Exponent D × Exponent D × Exponent D × Exponent D) :=
    (P.coeff a.1 * Q.coeff a.2.1 * R.coeff a.2.2.1 * S.coeff a.2.2.2) *
      (weight a.1 : ℂ) * (weight a.2.1 : ℂ) *
        (weight a.2.2.1 : ℂ) * (weight a.2.2.2 : ℂ)
  have read (F : Exponent D → Exponent D → Exponent D → Exponent D → ℂ) :
      occupationReadout D P Q R S F =
        ∑ a ∈ S₄, C a * F a.1 a.2.1 a.2.2.1 a.2.2.2 := by
    simp only [occupationReadout, S₄, C, Finset.sum_product]
  simp only [read]
  rw [Summable.tsum_finsetSum]
  · exact Finset.sum_congr rfl fun a _ => tsum_mul_left
  · intro a _
    exact (h a.1 a.2.1 a.2.2.1 a.2.2.2).mul_left (C a)

private theorem nome_norm_lt_one (c : Chart) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (hc : (c = .A ∨ c = .B) ∧ ‖parameter c (x : ℂ)‖ < 1 ∨ c = .D) :
    ‖nome c x‖ < 1 := by
  rcases hc with ⟨hc, hr⟩ | rfl
  · have hm : parameter c (x : ℂ) ∈ slitDomain :=
      ball_subset_slitDomain (by rwa [Metric.mem_ball, dist_zero_right])
    rcases hc with rfl | rfl <;> exact slitNome_norm_lt_one hm
  · simpa only [nome, parameter, Complex.ofReal_inv] using
      dNome_norm_lt_one true ((one_lt_inv₀ hx).2 hx₁)

/-- Both Fourier overlaps expressed using the actual slit and true-lip charge
sectors with each term evaluated on its own four occupied supports. -/
theorem native_occupation_fourier_overlap {X : Type*} [Fintype X] [DecidableEq X]
    (D : LatticeData) (hu : IsUnit D.G.det) (hD : (gramReal D).PosDef)
    (hr : D.rank = 24) (slot : X → Puncture) (colour : X → Fin D.rank)
    {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) {w : ℂ}
    (hwA : w ^ 2 = parameter .A x) (hw : ‖w‖ < 1)
    (a : ModTwoCharge D) (n : X → ℕ) (l : List X) (hl : l.Nodup) :
    let V := fun c b =>
      let A := loweredOscillator D slot colour c n l ∘ nativePuncture c
      ((1 - parameter c (x : ℂ)) ^ (3 : ℕ) *
        (l.map fun j => liftedScale c x (slot j) (n j)).prod) *
        occupationReadout D (A 0) (A 1) (A 2) (A 3) (nativeSector D c x b)
    V .D a = ((2 : ℂ) ^ (12 : ℕ))⁻¹ * (∑ b, fourierSign D a b * V .A b) ∧
    V .B a = (periodRoot .A x ^ (12 : ℕ))⁻¹ *
      (((2 : ℂ) ^ (12 : ℕ))⁻¹ * ∑ b, fourierSign D a b * quadraticSign D b * V .A b) := by
  classical
  let F := commonSupport D slot colour n l
  have hA : ‖parameter .A (x : ℂ)‖ < 1 := by
    rw [← hwA, norm_pow]
    nlinarith [norm_nonneg w]
  have hB : ‖parameter .B (x : ℂ)‖ < 1 := by
    simpa [parameter, Complex.norm_real, abs_of_pos hx] using hx₁
  have hc (c : Chart) : (c = .A ∨ c = .B) ∧ ‖parameter c (x : ℂ)‖ < 1 ∨ c = .D := by
    cases c with
    | A => exact Or.inl ⟨Or.inl rfl, hA⟩
    | B => exact Or.inl ⟨Or.inr rfl, hB⟩
    | D => exact Or.inr rfl
  have hsector (c : Chart) (b : ModTwoCharge D) :
      let A := loweredOscillator D slot colour c n l ∘ nativePuncture c
      (∑' q : {q : Charge D // reduceCharge D q = b},
          loweredChargeTerm D slot colour true c x q.val n l F) =
        ((1 - parameter c (x : ℂ)) ^ (3 : ℕ) *
          (l.map fun j => liftedScale c x (slot j) (n j)).prod) *
          occupationReadout D (A 0) (A 1) (A 2) (A 3) (nativeSector D c x b) := by
    dsimp only
    simp_rw [fun q : {q : Charge D // reduceCharge D q = b} =>
      lowered_charge_eq_native_occupations D slot colour true c hx hx₁ (fun _ => rfl)
        q.val (chargeEnergy_nonneg D hD q.val) n l F (vars_subset_common D slot colour n l c)]
    rw [tsum_mul_left, tsum_occupationReadout]
    · congr 1
      apply congrArg (occupationReadout D _ _ _ _)
      funext b' g' d' e'
      exact (sector_eq_tsum D c x b b' g' d' e').symm
    · exact native_term_summable D hD c x (nome_norm_lt_one c hx hx₁ (hc c)) b
  have h := lowered_fourier_overlap D hu hD hr slot colour hx hx₁ hwA hw a n l hl F
    (mode_mem_common D slot colour n l)
  dsimp only at h ⊢
  simpa only [hsector] using h

private def occupationLinear (D : LatticeData) (f : Exponent D → ℂ) :
    Oscillator D →ₗ[ℂ] ℂ :=
  (Finsupp.lsum ℂ fun b =>
    ((weight b : ℂ) * f b) • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

private theorem occupationLinear_apply (D : LatticeData) (f : Exponent D → ℂ)
    (P : Oscillator D) :
    occupationLinear D f P = ∑ b ∈ P.support, (weight b : ℂ) * f b * P.coeff b := by
  simp only [occupationLinear, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    Finsupp.lsum_apply, Finsupp.sum, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul] <;>
    rfl

private theorem occupationReadout_nested (D : LatticeData) (P Q R S : Oscillator D)
    (f : Exponent D → Exponent D → Exponent D → Exponent D → ℂ) :
    occupationReadout D P Q R S f =
      occupationLinear D (fun b => occupationLinear D (fun g =>
        occupationLinear D (fun d => occupationLinear D (f b g d) S) R) Q) P := by
  simp only [occupationReadout, occupationLinear_apply, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- The finite inverse flow with lowering parameter one. -/
def inverseFlow (D : LatticeData) (N : ℕ) (P : Oscillator D) : Oscillator D :=
  ∑ j ∈ Finset.range N, ((-1 : ℂ) ^ j / (j.factorial : ℂ)) • (oscillatorLower D ^ j) P

/-- The detector for the right Laurent mode at energy zero. -/
def rightMode (D : LatticeData) (t : ℤ) (d e : Exponent D) : ℂ :=
  let w := doubledWeight D d - doubledWeight D e
  if w % 2 = 0 then if t = -1 + w / 2 then 1 else 0 else 0

private theorem selector_rightMode (D : LatticeData) (hD : (gramReal D).PosDef)
    (t : ℤ) (d e : Exponent D) :
    selector D 0 (-2 * t - 2) 0 d e = rightMode D t d e := by
  have h0 : chargeEnergy D 0 ≤ (0 : ℕ) := by simp [chargeEnergy_zero]
  simpa [rightMode, chargeEnergy_zero] using right_selector D hD 0 0 h0 t d e

private theorem phase_factor (K i j : ℕ) :
    (-1 : ℂ) ^ ((K : ℤ) - (i : ℤ) + (j : ℤ)) / ((i.factorial : ℂ) * (j.factorial : ℂ)) =
      (-1 : ℂ) ^ (K : ℤ) * ((-1 : ℂ) ^ j / (j.factorial : ℂ)) *
        ((-1 : ℂ) ^ i / (i.factorial : ℂ)) := by
  rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_sub₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  simp only [zpow_natCast, div_eq_mul_inv, mul_inv_rev, ← inv_pow, inv_neg, inv_one]
  ring

private theorem occupationLinear_sum {I : Type*} (D : LatticeData) (P : Oscillator D)
    (t : Finset I) (u : I → ℂ) (f : I → Exponent D → ℂ) :
    occupationLinear D (fun b => ∑ i ∈ t, u i * f i b) P =
      ∑ i ∈ t, u i * occupationLinear D (f i) P := by
  simp only [occupationLinear_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => by ring

/-- For homogeneous left inputs the actual left Laurent selector is one at
every supported lowered pair. The actual right selector remains the signed
weight-difference detector on the two independently occupied right slots. -/
theorem projectOccupations_eq_inverse_readout (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (h24 : D.rank = 24) (H K : ℕ) (t : ℤ)
    (P Q R S : Oscillator D) (p q : ActualGround D hu) (hp : p ≠ 0) (hq : q ≠ 0)
    (hP : actualTensorL0 D hu (P ⊗ₜ[ℂ] p) = (H : ℂ) • (P ⊗ₜ[ℂ] p))
    (hQ : actualTensorL0 D hu (Q ⊗ₜ[ℂ] q) = (K : ℂ) • (Q ⊗ₜ[ℂ] q))
    (f : Exponent D → Exponent D → Exponent D → Exponent D → ℂ) :
    projectOccupations D H K 0 t P Q R S f =
      (-1 : ℂ) ^ (K : ℤ) *
        occupationReadout D (inverseFlow D (H - 1) P) (inverseFlow D (K - 1) Q) R S
          (fun b g d e => rightMode D t d e * f b g d e) := by
  classical
  let f' := fun b g d e => rightMode D t d e * f b g d e
  have h0 : chargeEnergy D 0 ≤ (0 : ℕ) := by simp [chargeEnergy_zero]
  have hL (i j : ℕ) (b g : Exponent D)
      (hb : b ∈ ((oscillatorLower D ^ j) P).support)
      (hg : g ∈ ((oscillatorLower D ^ i) Q).support) :
      selector D 0 (leftExponent H K 0 i j) 0 b g = 1 := by
    have h := (lowered_left_selector D hu hD h24 H K 0 i j 0 h0 P Q p q
      hp hq hP hQ b g hb hg).2.2.2
    simpa [chargeEnergy_zero] using h
  have hfinite :
      projectOccupations D H K 0 t P Q R S f =
        ∑ i ∈ Finset.range (K - 1), ∑ j ∈ Finset.range (H - 1),
          ((-1 : ℂ) ^ ((K : ℤ) - (i : ℤ) + (j : ℤ)) /
            ((i.factorial : ℂ) * (j.factorial : ℂ))) *
          occupationReadout D ((oscillatorLower D ^ j) P) ((oscillatorLower D ^ i) Q) R S f' := by
    unfold projectOccupations occupationReadout
    dsimp only
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    apply congrArg (fun z : ℂ =>
      ((-1 : ℂ) ^ ((K : ℤ) - (i : ℤ) + (j : ℤ)) /
        ((i.factorial : ℂ) * (j.factorial : ℂ))) * z)
    refine Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun g hg =>
      Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
    simp only [hL i j b g hb hg, mul_one, selector_rightMode D hD, f', mul_assoc]
  rw [hfinite, Finset.sum_comm]
  simp only [occupationReadout_nested, inverseFlow, map_sum, map_smul, smul_eq_mul,
    occupationLinear_sum, Finset.mul_sum, phase_factor, mul_assoc]
  rfl

open OriginalFourMPeriodSource (dLip)
open private slitDiagonal_native from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlitChartGerms
open private dLipNumerator_eq_slitDiagonal from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipChannel

/-- The selector evaluation of the actual true-D lip numerator agrees with
the slit numerator on the open lip, after both left inverse flows. -/
theorem projected_true_lip_eq_slit (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (h24 : D.rank = 24) (H K : ℕ) (s : ℤ)
    (P Q R S : Oscillator D) (p q : ActualGround D hu) (hp : p ≠ 0) (hq : q ≠ 0)
    (hP : actualTensorL0 D hu (P ⊗ₜ[ℂ] p) = (H : ℂ) • (P ⊗ₜ[ℂ] p))
    (hQ : actualTensorL0 D hu (Q ⊗ₜ[ℂ] q) = (K : ℂ) • (Q ⊗ₜ[ℂ] q))
    (a : ModTwoCharge D) {r : ℂ} (hr : r ∈ dLip true) :
    (-1 : ℂ) ^ (K : ℤ) *
      occupationReadout D (inverseFlow D (H - 1) P) (inverseFlow D (K - 1) Q) R S
        (fun b g d e => rightMode D (s - H - K + 1) d e *
          dLipChargeSector D true a b g d e r) =
      slitDiagonal D H K s P Q R S a r := by
  rw [← dLipNumerator_eq_slitDiagonal D true H K s P Q R S a hr, dLipNumerator,
    projectOccupations_eq_inverse_readout D hu hD h24 H K _ P Q R S p q hp hq hP hQ]

/-- In the sewing disk, the same two selectors give the actual native diagonal
germ. The square pullback is taken after the native occupation readout. -/
theorem projected_slit_eq_sewn (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (h24 : D.rank = 24) (H K : ℕ) (s : ℤ)
    (P Q R S : Oscillator D) (p q : ActualGround D hu) (hp : p ≠ 0) (hq : q ≠ 0)
    (hP : actualTensorL0 D hu (P ⊗ₜ[ℂ] p) = (H : ℂ) • (P ⊗ₜ[ℂ] p))
    (hQ : actualTensorL0 D hu (Q ⊗ₜ[ℂ] q) = (K : ℂ) • (Q ⊗ₜ[ℂ] q))
    (a : ModTwoCharge D) {w : ℂ} (hw : ‖w‖ < 1) :
    (-1 : ℂ) ^ (K : ℤ) *
      occupationReadout D (inverseFlow D (H - 1) P) (inverseFlow D (K - 1) Q) R S
        (fun b g d e => rightMode D (s - H - K + 1) d e *
          slitChargeSector D a b g d e (w ^ 2)) =
      diagonalSewn D H K (s - H - K + 1) P Q R S a w := by
  rw [← slitDiagonal_native D hD h24 H K s P Q R S a hw, slitDiagonal,
    projectOccupations_eq_inverse_readout D hu hD h24 H K _ P Q R S p q hp hq hP hQ]

open HalfFock.OriginalHalfCurrentWickPolynomial (word eval_word_eq_lowering)
open FourPoint.FourPointChannelCoefficients (loweringWeight loweringCutoff laurent loweredLaurent)
open OriginalFourMChargeCoset (slitLowered slitChannelA slitChannelB dLipChannel)
open private lowering_weight from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMEnergyCoefficient
open private punctureLowering_eq from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCompactLowering

private def oscillatorWord (D : LatticeData) (modes : List (Index D)) : Oscillator D :=
  (modes.map MvPolynomial.X).prod

private theorem lowering_vanishes (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H : ℕ) (P : Oscillator D) (p : ActualGround D hu) (hp : p ≠ 0)
    (hP : actualTensorL0 D hu (P ⊗ₜ[ℂ] p) = (H : ℂ) • (P ⊗ₜ[ℂ] p))
    (j : ℕ) (hj : H - 1 ≤ j) :
    (oscillatorLower D ^ j) P = 0 := by
  apply MvPolynomial.support_eq_empty.mp
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hw := lowering_weight D hu h24 H j P p hP hp b hb
  have hnn : 0 ≤ doubledWeight D b := by
    rw [doubledWeight, Finsupp.weight_apply, Finsupp.sum]
    exact Finset.sum_nonneg fun i _ => by positivity
  omega

private theorem punctureLowering_eq_inverseFlow (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (c : Chart) (i : Puncture) (hi : loweringParameter c i = 1)
    (modes : List (Index D)) (H : ℕ) (p : ActualGround D hu) (hp : p ≠ 0)
    (hP : actualTensorL0 D hu (oscillatorWord D modes ⊗ₜ[ℂ] p) =
      (H : ℂ) • (oscillatorWord D modes ⊗ₜ[ℂ] p)) :
    punctureLowering D c i modes = inverseFlow D (H - 1) (oscillatorWord D modes) := by
  let N := max ((word D modes).natDegree + 1) (H - 1)
  have hN : (word D modes).natDegree < N :=
    (Nat.lt_succ_self _).trans_le (le_max_left _ _)
  rw [punctureLowering_eq D hu, hi, eval_word_eq_lowering D hu modes _ N hN]
  unfold inverseFlow
  symm
  apply Finset.sum_subset (Finset.range_mono (le_max_right _ _))
  intro j _ hj
  have hv := lowering_vanishes D hu h24 H (oscillatorWord D modes) p hp hP j
    (Nat.le_of_not_gt (fun h => hj (Finset.mem_range.mpr h)))
  change ((-1 : ℂ) ^ j / (j.factorial : ℂ)) • (oscillatorLower D ^ j)
    (oscillatorWord D modes) = 0
  rw [hv, smul_zero]

private theorem punctureLowering_eq_word (D : LatticeData) (c : Chart) (i : Puncture)
    (hi : loweringParameter c i = 0) (modes : List (Index D)) :
    punctureLowering D c i modes = oscillatorWord D modes := by
  rw [punctureLowering, hi, neg_zero, Finset.sum_eq_single 0]
  · simp [oscillatorWord, Module.End.one_apply]
  · intro j _ hj
    simp [hj]
  · simp

private theorem rightMode_of_shifted_weights (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (H K L J : ℕ) (s : ℤ)
    (hmode : (J : ℤ) = H + K + L - s - 2) (ell : ℕ)
    (R S : Oscillator D) (r v : ActualGround D hu) (hr : r ≠ 0) (hv : v ≠ 0)
    (hR : actualTensorL0 D hu (R ⊗ₜ[ℂ] r) = (L : ℂ) • (R ⊗ₜ[ℂ] r))
    (hS : actualTensorL0 D hu (S ⊗ₜ[ℂ] v) = (J : ℂ) • (S ⊗ₜ[ℂ] v))
    (d e : Exponent D) (hd : d ∈ R.support) (he : e ∈ ((oscillatorLower D ^ ell) S).support) :
    rightMode D (s + (ell : ℤ) - H - K + 1) d e = 1 := by
  have wd := lowering_weight D hu h24 L 0 R r hR hr d
    (by simpa [Module.End.one_apply] using hd)
  have we := lowering_weight D hu h24 J ell S v hS hv e he
  dsimp only [rightMode]
  rw [wd, we]
  split_ifs <;> first | rfl | omega

private theorem projectOccupations_shifted (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (h24 : D.rank = 24) (H K L J : ℕ) (s : ℤ)
    (hmode : (J : ℤ) = H + K + L - s - 2) (ell : ℕ)
    (P Q R S : Oscillator D) (p q r v : ActualGround D hu)
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (hv : v ≠ 0)
    (hP : actualTensorL0 D hu (P ⊗ₜ[ℂ] p) = (H : ℂ) • (P ⊗ₜ[ℂ] p))
    (hQ : actualTensorL0 D hu (Q ⊗ₜ[ℂ] q) = (K : ℂ) • (Q ⊗ₜ[ℂ] q))
    (hR : actualTensorL0 D hu (R ⊗ₜ[ℂ] r) = (L : ℂ) • (R ⊗ₜ[ℂ] r))
    (hS : actualTensorL0 D hu (S ⊗ₜ[ℂ] v) = (J : ℂ) • (S ⊗ₜ[ℂ] v))
    (f : Exponent D → Exponent D → Exponent D → Exponent D → ℂ) :
    projectOccupations D H K 0 (s + (ell : ℤ) - H - K + 1)
        P Q R ((oscillatorLower D ^ ell) S) f =
      (-1 : ℂ) ^ (K : ℤ) *
        occupationReadout D (inverseFlow D (H - 1) P) (inverseFlow D (K - 1) Q)
          R ((oscillatorLower D ^ ell) S) f := by
  rw [projectOccupations_eq_inverse_readout D hu hD h24 H K _ _ _ _ _ p q hp hq hP hQ]
  congr 1
  unfold occupationReadout
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun g _ =>
    Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun e he => ?_
  dsimp only
  rw [rightMode_of_shifted_weights D hu h24 H K L J s hmode ell R S r v hr hv hR hS d e hd he,
    one_mul]

private theorem detector_phase (s : ℤ) (ell : ℕ) :
    loweringWeight s ell =
      (-1 : ℂ) ^ (s + 2) * ((-1 : ℂ) ^ ell / (ell.factorial : ℂ)) := by
  unfold loweringWeight
  rw [show s + (ell : ℤ) + 2 = (s + 2) + (ell : ℤ) by omega,
    zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_natCast, div_eq_mul_inv, mul_assoc]

private def occupationLast (D : LatticeData) (P Q R : Oscillator D)
    (f : Exponent D → Exponent D → Exponent D → Exponent D → ℂ) :
    Oscillator D →ₗ[ℂ] ℂ :=
  ∑ b ∈ P.support, ∑ g ∈ Q.support, ∑ d ∈ R.support,
    ((P.coeff b * Q.coeff g * R.coeff d) * (weight b : ℂ) * (weight g : ℂ) *
      (weight d : ℂ)) • occupationLinear D (f b g d)

private theorem occupationLast_apply (D : LatticeData) (P Q R S : Oscillator D)
    (f : Exponent D → Exponent D → Exponent D → Exponent D → ℂ) :
    occupationLast D P Q R f S = occupationReadout D P Q R S f := by
  simp only [occupationLast, occupationReadout, LinearMap.sum_apply, LinearMap.smul_apply,
    occupationLinear_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun g _ =>
    Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => by ring

/-- The actual finite detector on the outgoing state assembles its third
inverse flow after both of the Laurent selectors have been evaluated. -/
theorem projected_lowering_sum (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (h24 : D.rank = 24) (H K L J N : ℕ) (s : ℤ)
    (hmode : (J : ℤ) = H + K + L - s - 2)
    (P Q R S : Oscillator D) (p q r v : ActualGround D hu)
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (hv : v ≠ 0)
    (hP : actualTensorL0 D hu (P ⊗ₜ[ℂ] p) = (H : ℂ) • (P ⊗ₜ[ℂ] p))
    (hQ : actualTensorL0 D hu (Q ⊗ₜ[ℂ] q) = (K : ℂ) • (Q ⊗ₜ[ℂ] q))
    (hR : actualTensorL0 D hu (R ⊗ₜ[ℂ] r) = (L : ℂ) • (R ⊗ₜ[ℂ] r))
    (hS : actualTensorL0 D hu (S ⊗ₜ[ℂ] v) = (J : ℂ) • (S ⊗ₜ[ℂ] v))
    (f : Exponent D → Exponent D → Exponent D → Exponent D → ℂ) :
    (∑ ell ∈ Finset.range N,
      loweringWeight s ell *
        projectOccupations D H K 0 (s + (ell : ℤ) - H - K + 1)
          P Q R ((oscillatorLower D ^ ell) S) f) =
      ((-1 : ℂ) ^ (s + 2) * (-1 : ℂ) ^ (K : ℤ)) *
        occupationReadout D (inverseFlow D (H - 1) P) (inverseFlow D (K - 1) Q)
          R (inverseFlow D N S) f := by
  classical
  simp only [fun ell => projectOccupations_shifted D hu hD h24 H K L J s hmode ell
    P Q R S p q r v hp hq hr hv hP hQ hR hS f, detector_phase]
  have hlast :
      occupationReadout D (inverseFlow D (H - 1) P) (inverseFlow D (K - 1) Q)
        R (inverseFlow D N S) f =
      ∑ ell ∈ Finset.range N, ((-1 : ℂ) ^ ell / (ell.factorial : ℂ)) *
        occupationReadout D (inverseFlow D (H - 1) P) (inverseFlow D (K - 1) Q)
          R ((oscillatorLower D ^ ell) S) f := by
    simp only [← occupationLast_apply, inverseFlow, map_sum, map_smul, smul_eq_mul]
  rw [hlast, Finset.mul_sum]
  exact Finset.sum_congr rfl fun ell _ => by ring

open private slitLaurent from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlitChartGerms

open Classical in
/-- The product of the unlowered creation variables at one physical puncture. -/
def wordAt {X : Type*} (D : LatticeData) (slot : X → Puncture)
    (colour : X → Fin D.rank) (n : X → ℕ) (l : List X) (i : Puncture) : Oscillator D :=
  oscillatorWord D ((l.filter fun a => decide (slot a = i)).map fun a => (colour a, n a))

/-- The original Laurent evaluations in the three native slots before
Fourier mixing. The A term has no outgoing lowering. -/
def nativeLaurent (D : LatticeData) (c : Chart) (H K L J : ℕ) (s : ℤ)
    (P Q R S : Oscillator D) (a : ModTwoCharge D) (t : ℂ) : ℂ :=
  match c with
  | .A => slitLaurent D H K s P Q R S a t
  | .B => slitLowered D K L s (J - 1) Q R P S a t
  | .D => loweredLaurent ((H : ℤ) + L) s (J - 1)
      (fun ell u => dLipNumerator D true H L (s + (ell : ℤ))
        P R Q ((oscillatorLower D ^ ell) S) a (-u)) t

private def laurentPower (H K L : ℕ) : Chart → ℤ
  | .A => (H : ℤ) + K
  | .B => (K : ℤ) + L
  | .D => (H : ℤ) + L

private def laurentPhase (K L : ℕ) (s : ℤ) : Chart → ℂ
  | .A => (-1 : ℂ) ^ (K : ℤ)
  | .B | .D => (-1 : ℂ) ^ (s + 2) * (-1 : ℂ) ^ (L : ℤ)

private theorem zpow_sign_sq (m : ℤ) : (-1 : ℂ) ^ m * (-1 : ℂ) ^ m = 1 := by
  rw [← mul_zpow, neg_mul_neg, one_mul, one_zpow]

private theorem actual_laurent_factor (u : ℂ) (h : u ≠ 0) (m : ℤ)
    (k v : ℂ) (hk : k * k = 1) :
    u ^ m * k * (u ^ (-m) * (k * v)) = v := by
  have hu : u ^ m * u ^ (-m) = 1 := by rw [← zpow_add₀ h, add_neg_cancel, zpow_zero]
  calc
    _ = (u ^ m * u ^ (-m)) * ((k * k) * v) := by ring
    _ = _ := by rw [hu, hk, one_mul, one_mul]

private theorem factor_detector (s : ℤ) (N : ℕ) (u : ℂ) (f : ℕ → ℂ) :
    (∑ ell ∈ Finset.range N, loweringWeight s ell * (u * f ell)) =
      u * ∑ ell ∈ Finset.range N, loweringWeight s ell * f ell := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun ell _ => by ring

/-- Identify the sector readout of the actual lowered words with the actual
Laurent evaluation, including the outgoing detector in B and true D. -/
theorem lowered_native_sector_eq_laurent {X : Type*} (D : LatticeData)
    (hu : IsUnit D.G.det) (hD : (gramReal D).PosDef) (h24 : D.rank = 24)
    (slot : X → Puncture) (colour : X → Fin D.rank) (n : X → ℕ) (l : List X)
    (H K L J : ℕ) (s : ℤ) (hmode : (J : ℤ) = H + K + L - s - 2)
    (p q r v : ActualGround D hu) (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (hv : v ≠ 0)
    (hP : actualTensorL0 D hu (wordAt D slot colour n l .P ⊗ₜ[ℂ] p) =
      (H : ℂ) • (wordAt D slot colour n l .P ⊗ₜ[ℂ] p))
    (hQ : actualTensorL0 D hu (wordAt D slot colour n l .Q ⊗ₜ[ℂ] q) =
      (K : ℂ) • (wordAt D slot colour n l .Q ⊗ₜ[ℂ] q))
    (hR : actualTensorL0 D hu (wordAt D slot colour n l .R ⊗ₜ[ℂ] r) =
      (L : ℂ) • (wordAt D slot colour n l .R ⊗ₜ[ℂ] r))
    (hS : actualTensorL0 D hu (wordAt D slot colour n l .S ⊗ₜ[ℂ] v) =
      (J : ℂ) • (wordAt D slot colour n l .S ⊗ₜ[ℂ] v))
    (c : Chart) (x : ℝ) (hx : parameter c (x : ℂ) ≠ 0) (a : ModTwoCharge D) :
    let A := loweredOscillator D slot colour c n l ∘ nativePuncture c
    let W := wordAt D slot colour n l
    (-parameter c (x : ℂ)) ^ laurentPower H K L c * laurentPhase K L s c *
        nativeLaurent D c H K L J s (W .P) (W .Q) (W .R) (W .S) a (parameter c (x : ℂ)) =
      occupationReadout D (A 0) (A 1) (A 2) (A 3) (nativeSector D c x a) := by
  classical
  let W := wordAt D slot colour n l
  have h1 (c : Chart) (i : Puncture) (hi : loweringParameter c i = 1)
      (M : ℕ) (g : ActualGround D hu) (hg : g ≠ 0)
      (h : actualTensorL0 D hu (W i ⊗ₜ[ℂ] g) = (M : ℂ) • (W i ⊗ₜ[ℂ] g)) :
      loweredOscillator D slot colour c n l i = inverseFlow D (M - 1) (W i) :=
    punctureLowering_eq_inverseFlow D hu h24 c i hi _ M g hg h
  have h0 (c : Chart) (i : Puncture) (hi : loweringParameter c i = 0) :
      loweredOscillator D slot colour c n l i = W i :=
    punctureLowering_eq_word D c i hi _
  have hphase (s : ℤ) (L : ℕ) :
      (((-1 : ℂ) ^ (s + 2)) * (-1 : ℂ) ^ (L : ℤ)) *
        (((-1 : ℂ) ^ (s + 2)) * (-1 : ℂ) ^ (L : ℤ)) = 1 := by
    calc
      _ = ((-1 : ℂ) ^ (s + 2) * (-1 : ℂ) ^ (s + 2)) *
          ((-1 : ℂ) ^ (L : ℤ) * (-1 : ℂ) ^ (L : ℤ)) := by ring
      _ = _ := by rw [zpow_sign_sq, zpow_sign_sq, one_mul]
  cases c with
  | A =>
    dsimp only [Function.comp_apply, nativePuncture, laurentPower, laurentPhase, nativeLaurent]
    change _ = occupationReadout D (loweredOscillator D slot colour .A n l .P)
      (loweredOscillator D slot colour .A n l .Q) (loweredOscillator D slot colour .A n l .R)
      (loweredOscillator D slot colour .A n l .S) (nativeSector D .A x a)
    rw [h1 .A .P rfl H p hp hP, h1 .A .Q rfl K q hq hQ, h0 .A .R rfl, h0 .A .S rfl,
      slitLaurent, slitDiagonal]
    have hex := projectOccupations_shifted D hu hD h24 H K L J s hmode 0
      (W .P) (W .Q) (W .R) (W .S) p q r v hp hq hr hv hP hQ hR hS
      (nativeSector D .A x a)
    simp only [Nat.cast_zero, add_zero, pow_zero, Module.End.one_apply] at hex
    change _ * _ * (_ * projectOccupations D H K 0 (s - H - K + 1)
      (W .P) (W .Q) (W .R) (W .S) (nativeSector D .A x a)) = _
    rw [hex]
    exact actual_laurent_factor _ (neg_ne_zero.mpr hx) _ _ _ (zpow_sign_sq _)
  | B =>
    dsimp only [Function.comp_apply, nativePuncture, laurentPower, laurentPhase, nativeLaurent]
    change _ = occupationReadout D (loweredOscillator D slot colour .B n l .Q)
      (loweredOscillator D slot colour .B n l .R) (loweredOscillator D slot colour .B n l .P)
      (loweredOscillator D slot colour .B n l .S) (nativeSector D .B x a)
    rw [h1 .B .Q rfl K q hq hQ, h1 .B .R rfl L r hr hR, h0 .B .P rfl, h1 .B .S rfl J v hv hS]
    simp only [slitLowered, loweredLaurent, laurent, neg_neg, slitDiagonal]
    have hex := projected_lowering_sum D hu hD h24 K L H J (J - 1) s (by omega)
      (W .Q) (W .R) (W .P) (W .S) q r p v hq hr hp hv hQ hR hP hS
      (nativeSector D .B x a)
    rw [factor_detector]
    let u := -parameter .B (x : ℂ)
    change u ^ ((K : ℤ) + L) * _ *
      (u ^ (-((K : ℤ) + L)) * (∑ ell ∈ Finset.range (J - 1), loweringWeight s ell *
        projectOccupations D K L 0 (s + (ell : ℤ) - K - L + 1)
          (W .Q) (W .R) (W .P) ((oscillatorLower D ^ ell) (W .S)) (nativeSector D .B x a))) = _
    rw [hex]
    exact actual_laurent_factor _ (neg_ne_zero.mpr hx) _ _ _ (hphase s L)
  | D =>
    dsimp only [Function.comp_apply, nativePuncture, laurentPower, laurentPhase, nativeLaurent]
    change _ = occupationReadout D (loweredOscillator D slot colour .D n l .P)
      (loweredOscillator D slot colour .D n l .R) (loweredOscillator D slot colour .D n l .Q)
      (loweredOscillator D slot colour .D n l .S) (nativeSector D .D x a)
    rw [h1 .D .P rfl H p hp hP, h1 .D .R rfl L r hr hR, h0 .D .Q rfl, h1 .D .S rfl J v hv hS]
    simp only [loweredLaurent, laurent, neg_neg, dLipNumerator]
    have hex := projected_lowering_sum D hu hD h24 H L K J (J - 1) s (by omega)
      (W .P) (W .R) (W .Q) (W .S) p r q v hp hr hq hv hP hR hQ hS
      (nativeSector D .D x a)
    rw [factor_detector]
    let u := -parameter .D (x : ℂ)
    change u ^ ((H : ℤ) + L) * _ *
      (u ^ (-((H : ℤ) + L)) * (∑ ell ∈ Finset.range (J - 1), loweringWeight s ell *
        projectOccupations D H L 0 (s + (ell : ℤ) - H - L + 1)
          (W .P) (W .R) (W .Q) ((oscillatorLower D ^ ell) (W .S)) (nativeSector D .D x a))) = _
    rw [hex]
    exact actual_laurent_factor _ (neg_ne_zero.mpr hx) _ _ _ (hphase s L)

/-- On the real overlap the literal Laurent evaluations of arbitrary
homogeneous occurrence words obey both Fourier identities. The scalar
factors are given in the physical lift, with the exact native Laurent phase. -/
theorem native_laurent_fourier_overlap {X : Type*} [Fintype X] [DecidableEq X]
    (D : LatticeData) (hu : IsUnit D.G.det) (hD : (gramReal D).PosDef)
    (h24 : D.rank = 24) (slot : X → Puncture) (colour : X → Fin D.rank)
    (n : X → ℕ) (l : List X) (hl : l.Nodup)
    (e : Puncture → ℕ) (g : Puncture → ActualGround D hu) (hg : ∀ i, g i ≠ 0)
    (he : ∀ i, actualTensorL0 D hu (wordAt D slot colour n l i ⊗ₜ[ℂ] g i) =
      (e i : ℂ) • (wordAt D slot colour n l i ⊗ₜ[ℂ] g i))
    (s : ℤ) (hmode : (e .S : ℤ) = e .P + e .Q + e .R - s - 2)
    {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) {w : ℂ}
    (hwA : w ^ 2 = parameter .A x) (hw : ‖w‖ < 1) (a : ModTwoCharge D) :
    let W := wordAt D slot colour n l
    let V := fun c b =>
      ((1 - parameter c (x : ℂ)) ^ (3 : ℕ) *
        (l.map fun j => liftedScale c x (slot j) (n j)).prod) *
      ((-parameter c (x : ℂ)) ^ laurentPower (e .P) (e .Q) (e .R) c *
        laurentPhase (e .Q) (e .R) s c *
        nativeLaurent D c (e .P) (e .Q) (e .R) (e .S) s (W .P) (W .Q) (W .R) (W .S) b
          (parameter c (x : ℂ)))
    V .D a = ((2 : ℂ) ^ (12 : ℕ))⁻¹ * (∑ b, fourierSign D a b * V .A b) ∧
    V .B a = (periodRoot .A x ^ (12 : ℕ))⁻¹ *
      (((2 : ℂ) ^ (12 : ℕ))⁻¹ * ∑ b, fourierSign D a b * quadraticSign D b * V .A b) := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hx1 : (x : ℂ) ≠ 1 := by exact_mod_cast hx₁.ne
  have ht (c : Chart) : parameter c (x : ℂ) ≠ 0 := by
    cases c with
    | A =>
      change 1 - (x : ℂ)⁻¹ ≠ 0
      exact sub_ne_zero.mpr fun h => hx1 (inv_eq_one.mp h.symm)
    | B => exact hx0
    | D => exact inv_ne_zero hx0
  have h (c : Chart) (b : ModTwoCharge D) :=
    lowered_native_sector_eq_laurent D hu hD h24 slot colour n l
      (e .P) (e .Q) (e .R) (e .S) s hmode (g .P) (g .Q) (g .R) (g .S)
      (hg .P) (hg .Q) (hg .R) (hg .S) (he .P) (he .Q) (he .R) (he .S) c x (ht c) b
  have hFourier := native_occupation_fourier_overlap D hu hD h24 slot colour hx hx₁ hwA hw a n l hl
  dsimp only at h hFourier ⊢
  simpa only [← h] using hFourier

/-- At the actual signed-mode diagonal the outgoing energy cutoff equals the
literal cutoff in both transported channels. -/
theorem cutoff_of_output_weight (H K L J : ℕ) (m n r : ℤ)
    (h : (J : ℤ) = H + K + L - (m + n + r) - 2) :
    loweringCutoff H K L m n r = J - 1 := by
  unfold loweringCutoff
  omega

/-- Both transported evaluations use the exact channel definitions once the
output weight is chosen by the right selector. -/
theorem nativeLaurent_eq_transported_channels (D : LatticeData) (H K L J : ℕ)
    (m n r : ℤ) (h : (J : ℤ) = H + K + L - (m + n + r) - 2)
    (P Q R S : Oscillator D) (a : ModTwoCharge D) (t : ℂ) :
    nativeLaurent D .B H K L J (m + n + r) P Q R S a t =
      slitChannelB D H K L m n r P Q R S a t ∧
    (∑ b, quadraticSign D (b + a) * nativeLaurent D .D H K L J (m + n + r) P Q R S b t) =
      dLipChannel D true H K L m n r P Q R S a t := by
  rw [slitChannelB, dLipChannel, cutoff_of_output_weight H K L J m n r h]
  exact ⟨rfl, rfl⟩

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMVariableSupport
