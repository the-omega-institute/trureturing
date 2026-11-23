/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeOccupation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeOccupation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-charge coefficients on variable native occupation supports. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMLoweredNormalization

/-! Read the fixed-charge coefficient on the four native occupation supports. -/

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

private abbrev Compact (D : LatticeData) (F : Finset (Index D)) :=
  CompactExternal D F ⊕ CompactExternal D F

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
  cases c <;> rfl

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
  rw [hm, external_weight D F b g d e hb' hg' hd' he', nativeChargeTerm_coeff,
    affineCoefficient_fourSupport D q c x F b g d e hF]
  push_cast
  ring

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

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMVariableSupport
