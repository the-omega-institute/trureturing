/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOccupation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact native occupations of assigned modes in the actual charts. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMAssignedOverlap
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeOccurrenceReadout
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMCurrentRegression

/-! The native chart entries of an assigned occurrence word are exactly
the compact entries of its four occupations, including repeated colours. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
open Filter

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMAssignedOccupation

open LatticeGeneratingFieldLocality LatticeHalfFock
open OriginalFourMCurrentRegression (slit_matrix_symm)
open LatticeDiscriminantTheta (gramReal)
open LatticeTwistedGroundRealization.SignQuotient (ModTwoCharge reduceCharge)
open FourPoint.OriginalFourMActualChart
open OriginalFourMChargeCoset (fourierSign quadraticSign)
open OriginalFourMChartProduct (chartPeriod chartTau)
open OriginalFourMAssignedOverlap
  (assignedChargeTerm assignedSector assigned_charge_summable_norm assigned_fourier_overlap)
open OriginalFourMWickLowering (pairWeight)
open OriginalFourMSpatialWickPartition (liftedScale)
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod
  (doubleSlit doubleSlit_preconnected midpoint_mem)
open OriginalFourMSlitMean (slitCovarianceEntry slitCovarianceEntry_analyticOnNhd slitMeanEntry)
open OriginalFourMPeriodSource (dLip dLip_mem_doubleSlit dLip_neBot)
open OriginalFourMOccupationTransport (flags)
open OriginalFourMFixedChargeWick (Mode nativeModeCovariance nativeModeMean modeMatrix)
open AffineWickAssignments (assign)
open AffineWickConvolution (partitions)
open OriginalGaussianSourceRestriction (CompactExternal compactExternal externalOccupation)
open OriginalFourMSectorContinuation (slitMatrix slitLinear dLipCovarianceEntry
  dLipCovarianceEntry_analyticAt dLipCovarianceEntry_eq_slit)
open AffineOccurrenceWick (wick affineMoment_eq_wick)
open OriginalFourMNativeOccurrenceReadout (slotOccupation native_occurrence_readout)
open NativeAffineExternalCoefficient (jetOccupation)
open OriginalChargedRowSource (affineCoefficient affineMoment_coefficient)
open MvPolynomial (monomial)
open FactorialFockMetric (weight)

section PartitionProduct

variable {Y R : Type*} [CommSemiring R]

/-- A correction endpoint partition restricted to a selected subword. -/
private def filterParts (p : Y → Bool) (s : List Y × List Y) : List Y × List Y :=
  (s.1.filter p, s.2.filter p)

/-- Two independent subwords contribute the product of their finite sums
over endpoint partitions. -/
private theorem partition_product (l : List Y) (p : Y → Bool) (f g : List Y × List Y → R) :
    ((partitions l).map fun s => f (filterParts p s) *
      g (filterParts (fun a => !p a) s)).sum =
      ((partitions (l.filter p)).map f).sum *
        ((partitions (l.filter fun a => !p a)).map g).sum := by
  induction l generalizing f g with
  | nil => simp [partitions, filterParts]
  | cons a l ih =>
    cases h : p a
    · simp only [partitions, List.map_append, List.map_map, List.sum_append, Function.comp_def,
        filterParts, List.filter_cons, h, Bool.false_eq_true, Bool.not_false, ite_false, ite_true]
      rw [mul_add, ← ih f (fun s => g (a :: s.1, s.2)),
        ← ih f (fun s => g (s.1, a :: s.2))]
      rfl
    · simp only [partitions, List.map_append, List.map_map, List.sum_append, Function.comp_def,
        filterParts, List.filter_cons, h, Bool.false_eq_true, Bool.not_true, ite_false, ite_true]
      rw [add_mul, ← ih (fun s => f (a :: s.1, s.2)) g,
        ← ih (fun s => f (s.1, a :: s.2)) g]
      rfl

/-- The sum over all correction endpoint partitions factors into the
per-puncture sums when each factor sees only its own subword. -/
private theorem partition_products {S : Type*} [DecidableEq S]
    (slot : Y → S) (s : Finset S) (l : List Y)
    (hs : ∀ a ∈ l, slot a ∈ s) (F : S → List Y × List Y → R) :
    ((partitions l).map fun p => ∏ i ∈ s, F i (filterParts (fun a => decide (slot a = i)) p)).sum =
      ∏ i ∈ s, ((partitions (l.filter fun a => decide (slot a = i))).map (F i)).sum := by
  induction s using Finset.induction_on generalizing l with
  | empty =>
    cases l with
    | nil => simp [partitions]
    | cons a l => exact (Finset.notMem_empty (slot a) (hs a List.mem_cons_self)).elim
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    let p : Y → Bool := fun a => decide (slot a = i)
    let G (w : List Y × List Y) :=
      ∏ j ∈ s, F j (filterParts (fun a => decide (slot a = j)) w)
    have hG (w : List Y × List Y) : G w = G (filterParts (fun a => !p a) w) := by
      unfold G
      apply Finset.prod_congr rfl
      intro j hj
      congr 1
      have he (w : List Y) : w.filter (fun a => decide (slot a = j)) =
          (w.filter (fun a => !p a)).filter (fun a => decide (slot a = j)) := by
        rw [List.filter_filter]
        apply List.filter_congr
        intro a _
        by_cases ha : slot a = j
        · have hji : j ≠ i := fun he => hi (he ▸ hj)
          simp [p, ha, hji]
        · simp [ha]
      exact Prod.ext (he w.1) (he w.2)
    change ((partitions l).map fun w => F i (filterParts p w) * G w).sum = _
    have he : ((partitions l).map fun w => F i (filterParts p w) * G w).sum =
        ((partitions l).map fun w =>
          F i (filterParts p w) * G (filterParts (fun a => !p a) w)).sum :=
      congrArg List.sum (List.map_congr_left fun w _ => congrArg (F i (filterParts p w) * ·) (hG w))
    rw [he, partition_product l p (F i) G]
    have hc : ∀ a ∈ l.filter (fun a => !p a), slot a ∈ s := by
      intro a ha
      have h := List.mem_filter.mp ha
      exact (Finset.mem_insert.mp (hs a h.1)).resolve_left (by simpa [p] using h.2)
    unfold G
    rw [ih _ hc]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    congr 3
    rw [List.filter_filter]
    apply List.filter_congr
    intro a _
    by_cases ha : slot a = j
    · have hji : j ≠ i := fun he => hi (he ▸ hj)
      simp [p, ha, hji]
    · simp [ha]


end PartitionProduct

section Polynomial

variable {Y J I : Type*} [Fintype J]

/-- Expand the surviving linear creators in one common oscillator algebra. -/
private def assignmentPolynomial (U : Matrix Y J ℂ) (f : J → I) (l : List Y) : MvPolynomial I ℂ :=
  (l.map fun a => ∑ j, U a j • MvPolynomial.X (f j)).prod

omit [Fintype J] in
private theorem word_product (f : J → I) (l : List J) :
    (l.map fun j => (MvPolynomial.X (f j) : MvPolynomial I ℂ)).prod =
      monomial (jetOccupation (l.map f)) 1 := by
  induction l with
  | nil => simp [jetOccupation]
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, jetOccupation]
    rw [ih, MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul, add_comm]

/-- The assignment sum is the linear readout of the product of the
surviving creators. Repetition is carried by polynomial multiplication. -/
private theorem assign_polynomial (U : Matrix Y J ℂ) (f : J → I) (l : List Y)
    (R : MvPolynomial I ℂ →ₗ[ℂ] ℂ) :
    assign U l (fun w => R (monomial (jetOccupation (w.map f)) 1)) =
      R (assignmentPolynomial U f l) := by
  simp_rw [← word_product]
  induction l generalizing R with
  | nil => rfl
  | cons a l ih =>
    simp only [assign, List.map_cons, List.prod_cons]
    have he (j : J) := ih (R.comp (LinearMap.mulLeft ℂ (MvPolynomial.X (f j) : MvPolynomial I ℂ)))
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply] at he
    simp only [he, assignmentPolynomial, List.map_cons, List.prod_cons,
      Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, smul_eq_mul]

/-- Evaluation against the actual affine coefficient array with the ordinary
Fock weight at every occupation. -/
private def affineReadout [Fintype I] (K : Matrix I I ℂ) (μ : I → ℂ) : MvPolynomial I ℂ →ₗ[ℂ] ℂ :=
  (Finsupp.lsum ℂ fun d => ((weight d : ℂ) *
    OriginalChargedRowSource.affineCoefficient K μ d) • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

omit [Fintype J] in
private theorem affineReadout_monomial [Fintype I] (K : Matrix I I ℂ) (μ : I → ℂ)
    (d : I →₀ ℕ) :
    affineReadout K μ (monomial d 1) = OriginalChargedRowSource.affineMoment K μ d := by
  classical
  rw [affineMoment_coefficient]
  simp [affineReadout, monomial, AddMonoidAlgebra.lsingle]

end Polynomial

variable {X : Type*} {n : X → ℕ}

/-- The two chart flags select the tagged leg and orientation of an assigned
oscillator in the common finite native support. -/
def compactMode (D : LatticeData) (c : Chart) (slot : X → Puncture)
    (colour : X → Fin D.rank) (F : Finset (Index D))
    (hF : ∀ a : Mode n, (colour a.1, a.2.val) ∈ F)
    (a : Mode n) : CompactExternal D F ⊕ CompactExternal D F :=
  let oscillator : {b // b ∈ F} := ⟨(colour a.1, a.2.val), hF a⟩
  let e : CompactExternal D F := if (flags c (slot a.1)).2 then .inr oscillator else .inl oscillator
  if (flags c (slot a.1)).1 then .inr e else .inl e

private def compactLabel {D : LatticeData} {F : Finset (Index D)} :
    CompactExternal D F ⊕ CompactExternal D F → OriginalGaussianExternalBlocks.External D :=
  Sum.elim (compactExternal D F) (compactExternal D F)

/-- Recover the puncture from the two tags of the D chart. -/
private def dPuncture {D : LatticeData} {F : Finset (Index D)} :
    CompactExternal D F ⊕ CompactExternal D F → Puncture
  | .inl (.inl _) => .P
  | .inl (.inr _) => .R
  | .inr (.inl _) => .Q
  | .inr (.inr _) => .S

private def topMode {D : LatticeData} {F : Finset (Index D)}
    (a : CompactExternal D F ⊕ CompactExternal D F) :
    Mode (fun b => (compactLabel (D := D) (F := F) b).2.2) :=
  ⟨a, ⟨_, Nat.lt_succ_self _⟩⟩

/-- Compact chart matrix containing exactly the native slit or true-D lip entries. -/
def compactCovariance (D : LatticeData) (c : Chart) (x : ℝ)
    (F : Finset (Index D)) : Matrix (CompactExternal D F ⊕ CompactExternal D F)
      (CompactExternal D F ⊕ CompactExternal D F) ℂ :=
  Matrix.of fun a b => match c with
    | .A | .B => slitMatrix D (compactExternal D F) (parameter c x) a b
    | .D => nativeModeCovariance D .D x dPuncture (fun i => (compactLabel i).2.1)
        (fun i => (compactLabel i).2.2) (topMode a) (topMode b)

/-- Native compact mean with the original charge bilinear on each colour. -/
def compactMean (D : LatticeData) (q : Charge D) (c : Chart) (x : ℝ)
    (F : Finset (Index D)) (a : CompactExternal D F ⊕ CompactExternal D F) : ℂ :=
  match c with
  | .A | .B => (bilinear D (unitCharge D (compactLabel a).2.1) q : ℂ) *
      slitLinear D (compactExternal D F) (parameter c x) a
  | .D => nativeModeMean D q .D x dPuncture (fun i => (compactLabel i).2.1)
      (fun i => (compactLabel i).2.2) (topMode a)

/-- Compact mode identification for the literal A, B, and D covariances
and their charge-linear means. -/
theorem mode_array_pullback (D : LatticeData) (q : Charge D) (c : Chart) (x : ℝ)
    (slot : X → Puncture) (colour : X → Fin D.rank) (F : Finset (Index D))
    (hF : ∀ a : Mode n, (colour a.1, a.2.val) ∈ F) :
    let f := compactMode D c slot colour F hF
    nativeModeCovariance D c x slot colour n = (compactCovariance D c x F).submatrix f f ∧
      nativeModeMean D q c x slot colour n = compactMean D q c x F ∘ f := by
  dsimp only
  let f := compactMode D c slot colour F hF
  have hleg (a : Mode n) :
      (compactMode D c slot colour F hF a).isRight = (flags c (slot a.1)).1 := by
    cases h : (flags c (slot a.1)).1 <;> simp [compactMode, h]
  have hlabel (a : Mode n) :
      compactLabel (compactMode D c slot colour F hF a) =
        ((flags c (slot a.1)).2, colour a.1, a.2.val) := by
    cases h₁ : (flags c (slot a.1)).1 <;> cases h₂ : (flags c (slot a.1)).2 <;>
      simp [compactMode, compactLabel, compactExternal, h₁, h₂]
  have hslot (a : Mode n) : dPuncture (compactMode D .D slot colour F hF a) = slot a.1 := by
    cases h : slot a.1 <;> simp only [compactMode, h] <;> rfl
  have hmatrix (r : ℂ) (i j : CompactExternal D F ⊕ CompactExternal D F) :
      slitMatrix D (compactExternal D F) r i j =
        slitCovarianceEntry D i.isRight j.isRight (compactLabel i) (compactLabel j) r := by
    cases i <;> cases j <;> rfl
  have hmean (r : ℂ) (i : CompactExternal D F ⊕ CompactExternal D F) :
      slitLinear D (compactExternal D F) r i =
        slitMeanEntry i.isRight (compactLabel i).1 (compactLabel i).2.2 r := by
    cases i <;> rfl
  constructor
  · ext a b
    change _ = compactCovariance D c x F (f a) (f b)
    cases c <;>
      simp only [nativeModeCovariance, compactCovariance, Matrix.of_apply,
        hmatrix, topMode, hleg, hlabel, f, hslot]
    case A => rfl
    case B => rfl
    case D =>
      have hentry (i : Mode n) :
          ((flags .D (slot i.1)).2, colour i.1, i.2.val) =
            ((flags .D (dPuncture (f i))).2, (compactLabel (f i)).2.1, i.2.val) := by
        simp only [f, hslot, hlabel]
      exact congrArg₂
        (fun e g => dLipCovarianceEntry D true (flags .D (slot a.1)).1
          (flags .D (slot b.1)).1 e g (parameter .D (x : ℂ)))
        (hentry a) (hentry b)
  · funext a
    change _ = compactMean D q c x F (f a)
    cases c <;>
      simp only [nativeModeMean, compactMean, hmean, topMode, hleg, hlabel, f, hslot]

/-- Evaluate the literal compact affine coefficient with the four factorial
weights obtained from the assigned occurrence word. -/
def compactWordReadout (D : LatticeData) (q : Charge D) (c : Chart) (x : ℝ)
    (slot : X → Puncture) (colour : X → Fin D.rank) (F : Finset (Index D))
    (hF : ∀ a : Mode n, (colour a.1, a.2.val) ∈ F) (l : List (Mode n)) : ℂ :=
  let labels := l.map (compactMode D c slot colour F hF)
  let left := labels.filterMap Sum.getLeft?
  let right := labels.filterMap Sum.getRight?
  let b := slotOccupation D F (left.filterMap Sum.getLeft?)
  let g := slotOccupation D F (left.filterMap Sum.getRight?)
  let d := slotOccupation D F (right.filterMap Sum.getLeft?)
  let e := slotOccupation D F (right.filterMap Sum.getRight?)
  (weight b : ℂ) * (weight g : ℂ) * ((weight d : ℂ) * (weight e : ℂ)) *
    affineCoefficient (compactCovariance D c x F) (compactMean D q c x F)
      (externalOccupation D F b g d e)

/-- Each native assigned word evaluates to the ordinary compact affine
coefficient multiplied by the four literal Fock factorials. -/
private theorem assigned_word_affine [Finite X] (D : LatticeData) (q : Charge D) (c : Chart) (x : ℝ)
    (slot : X → Puncture) (colour : X → Fin D.rank) (F : Finset (Index D))
    (hF : ∀ a : Mode n, (colour a.1, a.2.val) ∈ F)
    (hs : ∀ a b, compactCovariance D c x F a b = compactCovariance D c x F b a)
    (l : List (Mode n)) :
    wick (nativeModeCovariance D c x slot colour n) (nativeModeMean D q c x slot colour n) l =
    compactWordReadout D q c x slot colour F hF l := by
  let := Fintype.ofFinite X
  unfold compactWordReadout
  let f := compactMode D c slot colour F hF
  let K := compactCovariance D c x F
  let μ := compactMean D q c x F
  have ⟨hK, hμ⟩ := mode_array_pullback D q c x slot colour F hF
  rw [hK, hμ, ← affineMoment_eq_wick K μ hs f l]
  have h := native_occurrence_readout D F K μ hs f l
  rw [AffineOccurrenceWick.affineMoment_pullback K μ hs f l] at h
  exact h

/-- The compact slit array used in the A and B readouts is symmetric
throughout the original radial disk. -/
theorem compactCovariance_ab_symm (D : LatticeData) (c : Chart) (x : ℝ)
    (F : Finset (Index D)) (hc : c = .A ∨ c = .B) (hr : ‖parameter c (x : ℂ)‖ < 1)
    (a b : CompactExternal D F ⊕ CompactExternal D F) :
    compactCovariance D c x F a b = compactCovariance D c x F b a := by
  rcases hc with rfl | rfl <;> exact slit_matrix_symm D (compactExternal D F) hr a b

private theorem slit_symm_all (D : LatticeData) {Y : Type*}
    (e : Y → OriginalGaussianExternalBlocks.External D) (a b : Y ⊕ Y) :
    Set.EqOn (fun r => slitMatrix D e r a b) (fun r => slitMatrix D e r b a) doubleSlit := by
  have ha (a b : Y ⊕ Y) : AnalyticOnNhd ℂ (fun r => slitMatrix D e r a b) doubleSlit := by
    cases a <;> cases b <;>
      exact (slitCovarianceEntry_analyticOnNhd D _ _ _ _).mono fun _ hr => hr.1
  let r₀ : ℂ := 1 / 2
  have hnorm : ‖r₀‖ < 1 := by
    rw [show r₀ = ((1 / 2 : ℝ) : ℂ) by norm_num [r₀]]
    norm_num [Complex.norm_real]
  have hfreq : ∃ᶠ r : ℂ in 𝓝[≠] r₀, slitMatrix D e r a b = slitMatrix D e r b a := by
    have hb : ∀ᶠ r : ℂ in 𝓝 r₀, ‖r‖ < 1 :=
      (isOpen_lt continuous_norm continuous_const).mem_nhds hnorm
    exact ((hb.filter_mono nhdsWithin_le_nhds).mono fun r hr =>
      slit_matrix_symm D e hr a b).frequently
  exact (ha a b).eqOn_of_preconnected_of_frequently_eq
    (ha b a) doubleSlit_preconnected midpoint_mem hfreq

/-- The original D covariance is symmetric at the true boundary lip.
The proof continues the literal compact slit entries and takes their
one-sided limits in the actual D entry formula. -/
theorem compactCovariance_d_symm (D : LatticeData) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (F : Finset (Index D)) (a b : CompactExternal D F ⊕ CompactExternal D F) :
    compactCovariance D .D x F a b = compactCovariance D .D x F b a := by
  let t : ℝ := x⁻¹
  have ht : 1 < t := (one_lt_inv₀ hx).2 hx₁
  let entry (i j : CompactExternal D F ⊕ CompactExternal D F) :=
    dLipCovarianceEntry D true i.isRight j.isRight (compactLabel i) (compactLabel j)
  have ha (i j : CompactExternal D F ⊕ CompactExternal D F) :
      AnalyticAt ℂ (entry i j) (t : ℂ) :=
    dLipCovarianceEntry_analyticAt D true _ _ _ _ ht
  have he (i j : CompactExternal D F ⊕ CompactExternal D F) {r : ℂ}
      (hr : r ∈ dLip true) :
      entry i j r = slitMatrix D (compactExternal D F) r i j := by
    cases i <;> cases j <;> exact dLipCovarianceEntry_eq_slit D true _ _ _ _ hr
  have : (𝓝[dLip true] (t : ℂ)).NeBot := dLip_neBot true t
  have hEq : entry a b =ᶠ[𝓝[dLip true] (t : ℂ)] entry b a := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [he a b hr, he b a hr]
    exact slit_symm_all D (compactExternal D F) a b (dLip_mem_doubleSlit hr)
  have hc (i j : CompactExternal D F ⊕ CompactExternal D F) :
      compactCovariance D .D x F i j = entry i j (t : ℂ) := by
    have hparam : parameter .D (x : ℂ) = (t : ℂ) := by
      simp [t, parameter, Complex.ofReal_inv]
    rw [← hparam]
    rcases i with (i | i) | (i | i) <;> rcases j with (j | j) | (j | j) <;> rfl
  simp only [hc]
  exact tendsto_nhds_unique_of_eventuallyEq
    ((ha a b).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    ((ha b a).continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hEq

/-- The surviving part of each physical Wick partition is the weighted
compact occupation sum in the actual A, B or true-D chart. -/
private theorem assigned_native_part [Fintype X] [DecidableEq X] (D : LatticeData)
    (q : Charge D) (c : Chart) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (hc : (c = .A ∨ c = .B) ∧ ‖parameter c (x : ℂ)‖ < 1 ∨ c = .D)
    (slot : X → Puncture) (colour : X → Fin D.rank) (F : Finset (Index D))
    (hF : ∀ a : Mode n, (colour a.1, a.2.val) ∈ F) (l : List X) :
    assign (modeMatrix c x slot n) l
      (wick (nativeModeCovariance D c x slot colour n) (nativeModeMean D q c x slot colour n)) =
      assign (modeMatrix c x slot n) l (compactWordReadout D q c x slot colour F hF) := by
  congr 1
  funext w
  apply assigned_word_affine
  rcases hc with ⟨hc, hr⟩ | rfl
  · exact compactCovariance_ab_symm D c x F hc hr
  · exact compactCovariance_d_symm D hx hx₁ F

private theorem word_slots {Y S R : Type*} [DecidableEq S] [CommMonoid R]
    (slot : Y → S) (slots : Finset S) (v : Y → R) (l : List Y)
    (h : ∀ a ∈ l, slot a ∈ slots) :
    (l.map v).prod = ∏ i ∈ slots, ((l.filter fun a => decide (slot a = i)).map v).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]
    have ha : slot a ∈ slots := h a List.mem_cons_self
    conv_lhs => rw [← Finset.insert_erase ha, Finset.prod_insert (Finset.notMem_erase _ _)]
    conv_rhs => rw [← Finset.insert_erase ha, Finset.prod_insert (Finset.notMem_erase _ _)]
    rw [← mul_assoc]
    congr 1
    · simp
    · apply Finset.prod_congr rfl
      intro j hj
      simp [Finset.ne_of_mem_erase hj |>.symm]

open Classical in
/-- The upper-chart charge summand with each surviving assigned word read
in the four compact occupations. The correction pairs and lifted scales
are the same as in the physical Wick expansion. -/
def compactChargeTerm [Fintype X] [DecidableEq X] (D : LatticeData)
    (slot : X → Puncture) (colour : X → Fin D.rank) (c : Chart) (x : ℝ)
    (q : Charge D) (F : Finset (Index D))
    (hF : ∀ a : Mode n, (colour a.1, a.2.val) ∈ F) (l : List X) : ℂ :=
  (chartPeriod true c x ^ (12 : ℕ))⁻¹ *
    (Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau true c x * (bilinear D q q : ℂ) / 2) *
      ((partitions l).map fun p =>
        (p.1.map fun a => liftedScale c x (slot a) (n a)).prod *
        (∏ i ∈ ({.P, .Q, .R, .S} : Finset Puncture),
          wick (Matrix.of fun a b => pairWeight D (-loweringParameter c i)
            (colour a, n a) (colour b, n b)) 0 (p.1.filter fun a => decide (slot a = i))) *
        assign (modeMatrix c x slot n) p.2
          (compactWordReadout D q c x slot colour F hF)).sum)

private theorem assigned_charge_eq_compact [Fintype X] [DecidableEq X] (D : LatticeData)
    (q : Charge D) (c : Chart) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (hc : (c = .A ∨ c = .B) ∧ ‖parameter c (x : ℂ)‖ < 1 ∨ c = .D)
    (slot : X → Puncture) (colour : X → Fin D.rank) (F : Finset (Index D))
    (hF : ∀ a : Mode n, (colour a.1, a.2.val) ∈ F) (l : List X) :
    assignedChargeTerm D slot colour true c x q n l =
      compactChargeTerm D slot colour c x q F hF l := by
  unfold assignedChargeTerm compactChargeTerm
  simp only [assigned_native_part D q c hx hx₁ hc slot colour F hF]

open Classical in
/-- The compact charge term can be evaluated after multiplying the four
puncture polynomials. Each polynomial partitions its own labelled word
into correction endpoints and surviving marked modes. -/
def punctureChargeTerm [Fintype X] [DecidableEq X] (D : LatticeData)
    (slot : X → Puncture) (colour : X → Fin D.rank) (c : Chart) (x : ℝ)
    (q : Charge D) (F : Finset (Index D))
    (hF : ∀ a : Mode n, (colour a.1, a.2.val) ∈ F) (l : List X) : ℂ :=
  let punc : Finset Puncture := {.P, .Q, .R, .S}
  let scale a := liftedScale c x (slot a) (n a)
  let correction (i : Puncture) := Matrix.of fun a b =>
    pairWeight D (-loweringParameter c i) (colour a, n a) (colour b, n b)
  let U := modeMatrix c x slot n
  let f := compactMode D c slot colour F hF
  (chartPeriod true c x ^ (12 : ℕ))⁻¹ *
    (Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau true c x * (bilinear D q q : ℂ) / 2) *
      affineReadout (compactCovariance D c x F) (compactMean D q c x F)
        (∏ i ∈ punc, ((partitions (l.filter fun a => decide (slot a = i))).map fun p =>
          MvPolynomial.C ((p.1.map scale).prod * wick (correction i) 0 p.1) *
            assignmentPolynomial U f p.2).sum))

private theorem compact_word_eq_readout [Finite X] (D : LatticeData) (q : Charge D)
    (c : Chart) (x : ℝ) (slot : X → Puncture) (colour : X → Fin D.rank)
    (F : Finset (Index D)) (hF : ∀ a : Mode n, (colour a.1, a.2.val) ∈ F)
    (hs : ∀ a b, compactCovariance D c x F a b = compactCovariance D c x F b a)
    (l : List (Mode n)) :
    compactWordReadout D q c x slot colour F hF l =
      affineReadout (compactCovariance D c x F) (compactMean D q c x F)
        (monomial (jetOccupation (l.map (compactMode D c slot colour F hF))) 1) := by
  let := Fintype.ofFinite X
  rw [affineReadout_monomial]
  have h := native_occurrence_readout D F (compactCovariance D c x F) (compactMean D q c x F)
    hs (compactMode D c slot colour F hF) l
  rw [AffineOccurrenceWick.affineMoment_pullback _ _ hs] at h
  exact h.symm

/-- The original single positional partition sum equals the readout of
the product of the four puncture sums, before taking any charge sum. -/
theorem compact_charge_eq_punctures [Fintype X] [DecidableEq X] (D : LatticeData)
    (q : Charge D) (c : Chart) {x : ℝ} (hx : 0 < x) (hx₁ : x < 1)
    (hc : (c = .A ∨ c = .B) ∧ ‖parameter c (x : ℂ)‖ < 1 ∨ c = .D)
    (slot : X → Puncture) (colour : X → Fin D.rank) (F : Finset (Index D))
    (hF : ∀ a : Mode n, (colour a.1, a.2.val) ∈ F) (l : List X) :
    compactChargeTerm D slot colour c x q F hF l =
      punctureChargeTerm D slot colour c x q F hF l := by
  classical
  let punc : Finset Puncture := {.P, .Q, .R, .S}
  let scale a := liftedScale c x (slot a) (n a)
  let C (i : Puncture) := Matrix.of fun a b => pairWeight D (-loweringParameter c i)
    (colour a, n a) (colour b, n b)
  let U := modeMatrix c x slot n
  let f := compactMode D c slot colour F hF
  let R := affineReadout (compactCovariance D c x F) (compactMean D q c x F)
  let G (i : Puncture) (p : List X × List X) :=
    MvPolynomial.C ((p.1.map scale).prod * wick (C i) 0 p.1) * assignmentPolynomial U f p.2
  have hcols (a : X) : slot a ∈ punc := by cases slot a <;> simp [punc]
  have hs (a b) : compactCovariance D c x F a b = compactCovariance D c x F b a := by
    rcases hc with ⟨hc, hr⟩ | rfl
    · exact compactCovariance_ab_symm D c x F hc hr a b
    · exact compactCovariance_d_symm D hx hx₁ F a b
  have hassign (w : List X) :
      assign U w (compactWordReadout D q c x slot colour F hF) =
        R (assignmentPolynomial U f w) := by
    rw [← assign_polynomial]
    congr 1
    funext v
    exact compact_word_eq_readout D q c x slot colour F hF hs v
  have hword (w : List X) :
      assignmentPolynomial U f w =
        ∏ i ∈ punc, assignmentPolynomial U f (w.filter fun a => decide (slot a = i)) :=
    word_slots slot punc (fun a => ∑ j, U a j • MvPolynomial.X (f j)) w (fun a _ => hcols a)
  have hp (p : List X × List X) :
      (p.1.map scale).prod *
        (∏ i ∈ punc, wick (C i) 0 (p.1.filter fun a => decide (slot a = i))) *
        assign U p.2 (compactWordReadout D q c x slot colour F hF) =
        R (∏ i ∈ punc, G i (filterParts (fun a => decide (slot a = i)) p)) := by
    simp only [G, filterParts, Finset.prod_mul_distrib]
    rw [← map_prod, ← MvPolynomial.smul_eq_C_mul, map_smul, smul_eq_mul,
      ← hword, hassign, word_slots slot punc scale p.1 (fun a _ => hcols a)]
    simp only [Finset.prod_mul_distrib]
  let H (p : List X × List X) := ∏ i ∈ punc, G i (filterParts (fun a => decide (slot a = i)) p)
  have hmap : ((partitions l).map fun p => R (H p)).sum =
      R (((partitions l).map H).sum) := by
    rw [map_list_sum, List.map_map]
    rfl
  have hsum :
      ((partitions l).map fun p => (p.1.map scale).prod *
        (∏ i ∈ punc, wick (C i) 0 (p.1.filter fun a => decide (slot a = i))) *
        assign U p.2 (compactWordReadout D q c x slot colour F hF)).sum =
        R (∏ i ∈ punc, ((partitions (l.filter fun a => decide (slot a = i))).map (G i)).sum) := by
    rw [show _ = ((partitions l).map fun p => R (H p)).sum from
      congrArg List.sum (List.map_congr_left fun p _ => hp p), hmap]
    exact congrArg R (partition_products slot punc l (fun a _ => hcols a) G)
  unfold compactChargeTerm punctureChargeTerm
  exact congrArg (fun v => (chartPeriod true c x ^ (12 : ℕ))⁻¹ *
    (Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau true c x * (bilinear D q q : ℂ) / 2) *
      v)) hsum

/-- On the real overlap the three upper-chart charge expansions in compact
native occupations are absolutely summable on every charge fibre. Their
true-D and B values have the signed and quadratically signed Fourier
expansions in the A values, with the original rank-24 normalizations. -/
theorem compact_fourier_overlap [Fintype X] [DecidableEq X] (D : LatticeData)
    (hu : IsUnit D.G.det) (hD : (gramReal D).PosDef) (hr : D.rank = 24)
    (slot : X → Puncture) (colour : X → Fin D.rank)
    {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) {w : ℂ}
    (hwA : w ^ 2 = parameter .A x) (hw : ‖w‖ < 1)
    (a : ModTwoCharge D) (l : List X) (hl : l.Nodup)
    (F : Finset (Index D)) (hF : ∀ a : Mode n, (colour a.1, a.2.val) ∈ F) :
    let V := fun c b => ∑' q : {q : Charge D // reduceCharge D q = b},
      punctureChargeTerm D slot colour c x q.val F hF l
    (∀ c b, Summable (fun q : {q : Charge D // reduceCharge D q = b} =>
      ‖punctureChargeTerm D slot colour c x q.val F hF l‖)) ∧
    V .D a = ((2 : ℂ) ^ (12 : ℕ))⁻¹ * (∑ b, fourierSign D a b * V .A b) ∧
    V .B a = (periodRoot .A x ^ (12 : ℕ))⁻¹ *
      (((2 : ℂ) ^ (12 : ℕ))⁻¹ * ∑ b, fourierSign D a b * quadraticSign D b * V .A b) := by
  have hA : ‖parameter .A (x : ℂ)‖ < 1 := by
    rw [← hwA, norm_pow]
    nlinarith [norm_nonneg w]
  have hB : ‖parameter .B (x : ℂ)‖ < 1 := by
    simpa [parameter, Complex.norm_real, abs_of_pos hx] using hx₁
  have hchart (c : Chart) :
      (c = .A ∨ c = .B) ∧ ‖parameter c (x : ℂ)‖ < 1 ∨ c = .D ∧ true = true := by
    cases c
    · exact Or.inl ⟨Or.inl rfl, hA⟩
    · exact Or.inl ⟨Or.inr rfl, hB⟩
    · exact Or.inr ⟨rfl, rfl⟩
  have hterm (c : Chart) (q : Charge D) :
      assignedChargeTerm D slot colour true c x q n l =
        punctureChargeTerm D slot colour c x q F hF l :=
    (assigned_charge_eq_compact D q c hx hx₁ ((hchart c).imp id And.left) slot colour F hF l).trans
      (compact_charge_eq_punctures D q c hx hx₁ ((hchart c).imp id And.left) slot colour F hF l)
  refine ⟨?_, ?_⟩
  · intro c b
    simpa only [hterm] using
      assigned_charge_summable_norm D hu hD slot colour true c hx hx₁ (hchart c) b n l hl
  · simpa only [assignedSector, hterm] using
      assigned_fourier_overlap D hu hD hr slot colour hx hx₁ hwA hw a n l hl

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMAssignedOccupation
