/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMProjectionModes
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMProjectionModes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal four-point occupation selectors on the signed mode diagonals. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMChargeGerm
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWick
import D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentTransport

/-! The Laurent selectors are evaluated using the degrees of the supported
lowered oscillators. The detector shift is independent of both left lowerings. -/

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMProjectionModes

open MvPolynomial LatticeGeneratingFieldLocality LatticeHalfFock
open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open LatticeHalfFockChargedCoefficients (omega)
open LatticeHalfFockChargedLZero (L_zero_of_homogeneous_int)
open LatticeHalfFockChargedTensorCoefficients (chargeNorm)
open OriginalFourMChargeCoset (oscillatorLower)
open OriginalFourMEnergyCoefficient (doubledWeight selector leftExponent)
open FactorialFockMetric (weight)
open private lower_eigen from D5.S3.VertexAlgebra.HalfFock.OriginalHalfCurrentTransport
open private projectOccupations from D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeNormal

private theorem lowered_support_weight (D : LatticeData) (hu : IsUnit D.G.det)
    (P : Oscillator D) (d : ℤ) (hP : P.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) d)
    (k : ℕ) (e : Index D →₀ ℕ) (he : e ∈ ((oscillatorLower D ^ k) P).support) :
    doubledWeight D e = d - 2 * (k : ℤ) := by
  classical
  let T := (oscillatorLower D ^ k) P
  have h := lower_eigen D hu P d
    (L_zero_of_homogeneous_int D (actualInverse D) (actualInverse_left D hu)
      (actualInverse_right D hu) P d hP) k
  have heig := congrArg (fun p : Oscillator D => p.coeff e) h
  change (L D (actualInverse D) 0 T).coeff e = _ at heig
  have hcoeff : (L D (actualInverse D) 0 T).coeff e =
      ((D.rank : ℂ) / 16 + (doubledWeight D e : ℂ) / 2) * T.coeff e := by
    conv_lhs => rw [MvPolynomial.as_sum T, map_sum, coeff_sum]
    have hmon (s : Index D →₀ ℕ) :
        L D (actualInverse D) 0 (monomial s (T.coeff s)) =
          ((D.rank : ℂ) / 16 + (doubledWeight D s : ℂ) / 2) • monomial s (T.coeff s) :=
      L_zero_of_homogeneous_int D (actualInverse D) (actualInverse_left D hu)
        (actualInverse_right D hu) _ _ (isWeightedHomogeneous_monomial _ s _ rfl)
    simp only [hmon, coeff_smul, smul_eq_mul, coeff_monomial]
    rw [Finset.sum_eq_single_of_mem e he]
    · simp
    · intro s _ hs
      simp [hs]
  rw [hcoeff, coeff_smul, smul_eq_mul] at heig
  have hc := mul_right_cancel₀ (mem_support_iff.mp he) heig
  have hd : (doubledWeight D e : ℂ) = (d : ℂ) - 2 * (k : ℂ) := by
    linear_combination 2 * hc
  exact_mod_cast hd

private theorem lowering_phase (K i j : ℕ) :
    (-1 : ℂ) ^ ((K : ℤ) - (i : ℤ) + (j : ℤ)) =
      (-1 : ℂ) ^ (K : ℤ) * (-1 : ℂ) ^ i * (-1 : ℂ) ^ j := by
  have hn : (-1 : ℂ) ≠ 0 := by norm_num
  rw [sub_eq_add_neg, zpow_add₀ hn, zpow_add₀ hn, ← inv_zpow', inv_neg, inv_one]
  simp only [zpow_natCast]

/-- On the original signed diagonal the two Laurent selectors are one on
every supported occupation. The original left factorials and parity signs
become the two negative lowering coefficients with one overall sign. -/
theorem project_occupations_on_signed_diagonal (D : LatticeData) (hu : IsUnit D.G.det)
    (H K E : ℕ) (t dR dS : ℤ) (P Q R S : Oscillator D)
    (hP : P.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (H : ℤ) - 3))
    (hQ : Q.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (K : ℤ) - 3))
    (hR : R.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) dR)
    (hS : S.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) dS)
    (ht : 2 * (t - (E : ℤ) + 1) = dR - dS)
    (F : (Index D →₀ ℕ) → (Index D →₀ ℕ) → (Index D →₀ ℕ) → (Index D →₀ ℕ) → ℂ) :
    projectOccupations D H K E t P Q R S F =
      (-1 : ℂ) ^ (K : ℤ) *
        ∑ i ∈ Finset.range (K - 1), ∑ j ∈ Finset.range (H - 1),
          let PL := (oscillatorLower D ^ j) P
          let QL := (oscillatorLower D ^ i) Q
          ((-1 : ℂ) ^ i / (i.factorial : ℂ)) * ((-1 : ℂ) ^ j / (j.factorial : ℂ)) *
            ∑ betaL ∈ PL.support, ∑ gammaL ∈ QL.support,
              ∑ betaR ∈ R.support, ∑ gammaR ∈ S.support,
                PL.coeff betaL * QL.coeff gammaL * R.coeff betaR * S.coeff gammaR *
                  (weight betaL : ℂ) * (weight gammaL : ℂ) *
                  (weight betaR : ℂ) * (weight gammaR : ℂ) * F betaL gammaL betaR gammaR := by
  classical
  unfold projectOccupations
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hcoef : ((-1 : ℂ) ^ ((K : ℤ) - (i : ℤ) + (j : ℤ)) /
      ((i.factorial : ℂ) * (j.factorial : ℂ))) =
      (-1 : ℂ) ^ (K : ℤ) * (((-1 : ℂ) ^ i / (i.factorial : ℂ)) *
        ((-1 : ℂ) ^ j / (j.factorial : ℂ))) := by
    rw [lowering_phase, div_eq_mul_inv, mul_inv]
    ring
  simp only [hcoef, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro g hg
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  have hzero : chargeNorm D 0 = 0 := by simp [chargeNorm, bilinear]
  have hleft : selector D 0 (leftExponent H K E i j) E b g = 1 := by
    unfold selector
    rw [hzero, add_zero, lowered_support_weight D hu P _ hP j b hb,
      lowered_support_weight D hu Q _ hQ i g hg]
    simp only [leftExponent, ite_true]
  have hright : selector D 0 (-2 * t - 2) E r s = 1 := by
    unfold selector
    have hr' := hR (mem_support_iff.mp hr)
    have hs' := hS (mem_support_iff.mp hs)
    rw [hzero, add_zero, show doubledWeight D r = dR from hr',
      show doubledWeight D s = dS from hs']
    rw [ite_eq_left (by omega)]
  rw [hleft, hright]
  ring

/-- Lowering the detector by ell adds ell to the signed mode sum. This
identity covers each supported occupation and does not require nonnegative
signed modes or a nonzero detector. -/
theorem detector_selector_on_signed_diagonal (D : LatticeData) (hu : IsUnit D.G.det)
    (H K L E ell : ℕ) (m n r : ℤ) (R S : Oscillator D)
    (hR : R.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (L : ℤ) - 3))
    (hS : S.IsWeightedHomogeneous (fun i => (omega D i : ℤ))
      (2 * ((H : ℤ) + K + L - (m + n + r) - 2) - 3))
    (b s : Index D →₀ ℕ) (hb : b ∈ R.support) (hs : s ∈ ((oscillatorLower D ^ ell) S).support) :
    selector D 0 (-2 * ((E : ℤ) + m + n + r + ell - H - K + 1) - 2) E b s = 1 := by
  have hzero : chargeNorm D 0 = 0 := by simp [chargeNorm, bilinear]
  have hb' : doubledWeight D b = 2 * (L : ℤ) - 3 := hR (mem_support_iff.mp hb)
  unfold selector
  rw [hzero, add_zero, hb', lowered_support_weight D hu S _ hS ell s hs]
  rw [ite_eq_left (by omega)]


open OriginalFourMJointWick (BoundedExternal)
open OriginalGaussianSourceRestriction (CompactExternal compactExternal externalOccupation fourSupport)
open OriginalGaussianExternalBlocks (explicitEffectiveKernel)
open OriginalGaussianSewnAnalytic (sewn explicitMean)
open OriginalFourMChargeNormal (sewnChargeTerm)
open OriginalNormalRowSource (restricted restricted_reconstruct supportLabel embedded_weight)
open LatticePositiveEnergy (chargeEnergy)
open LatticeHalfFockChargedTensorCoefficients (chargeScalar)
open private externalLabel from D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMJointWick
open private affineCoefficient_enlarge from D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectedRowRecompositionSource

private def compactEmbedding (D : LatticeData) (N : ℕ) (F : Finset (Index D))
    (hF : ∀ i ∈ F, i.2 ≤ N) : CompactExternal D F ↪ BoundedExternal D N where
  toFun
    | .inl i => (false, i.val.1, ⟨i.val.2, Nat.lt_succ_of_le (hF i.val i.property)⟩)
    | .inr i => (true, i.val.1, ⟨i.val.2, Nat.lt_succ_of_le (hF i.val i.property)⟩)
  inj' := by
    rintro (i | i) (j | j) h
    · congr 1
      apply Subtype.ext
      exact Prod.ext (congrArg (fun z : BoundedExternal D N => z.2.1) h)
        (congrArg (fun z : BoundedExternal D N => z.2.2.val) h)
    · cases congrArg Prod.fst h
    · cases congrArg Prod.fst h
    · congr 1
      apply Subtype.ext
      exact Prod.ext (congrArg (fun z : BoundedExternal D N => z.2.1) h)
        (congrArg (fun z : BoundedExternal D N => z.2.2.val) h)

/-- Embedding the literal four compact occupations in the common finite
mode box gives the original sewn charge summand and all four of its
factorial weights. The box can extend past the largest supported mode. -/
theorem bounded_external_sewn_charge (D : LatticeData) (q : Charge D) (N : ℕ)
    (betaL gammaL betaR gammaR : Index D →₀ ℕ) (w : ℂ)
    (hF : ∀ i ∈ fourSupport D betaL gammaL betaR gammaR, i.2 ≤ N) :
    let F := fourSupport D betaL gammaL betaR gammaR
    let f := compactEmbedding D N F hF
    let d := externalOccupation D F betaL gammaL betaR gammaR
    let e := d.embDomain (f.sumMap f)
    (weight e : ℂ) * ((chargeScalar D q * chargeScalar D (-q)) *
      w ^ (2 * (chargeEnergy D q).toNat) * sewn D q (externalLabel D N) e w) =
      ((weight betaL : ℂ) * (weight gammaL : ℂ) * (weight betaR : ℂ) *
        (weight gammaR : ℂ)) * sewnChargeTerm D betaL gammaL betaR gammaR q w := by
  classical
  dsimp only
  let F := fourSupport D betaL gammaL betaR gammaR
  let f := compactEmbedding D N F hF
  let d := externalOccupation D F betaL gammaL betaR gammaR
  let e := d.embDomain (f.sumMap f)
  have hra (p : Index D →₀ ℕ) (hp : p.support ⊆ F) :
      weight (restricted D F p) = weight p := by
    rw [← embedded_weight D (supportLabel D F), restricted_reconstruct D F p hp]
  have hw : weight e = weight betaL * weight gammaL * weight betaR * weight gammaR := by
    have he : weight e = weight d := by
      unfold weight
      exact Finsupp.prod_embDomain
    rw [he]
    simp only [d, externalOccupation, weight, Finsupp.prod_sumElim]
    change (weight (restricted D F betaL) * weight (restricted D F gammaL)) *
      (weight (restricted D F betaR) * weight (restricted D F gammaR)) = _
    rw [hra betaL (by intro i hi; simp [F, fourSupport, hi]),
      hra gammaL (by intro i hi; simp [F, fourSupport, hi]),
      hra betaR (by intro i hi; simp [F, fourSupport, hi]),
      hra gammaR (by intro i hi; simp [F, fourSupport, hi])]
    simp only [weight, mul_assoc]
  have hA (i j : CompactExternal D F ⊕ CompactExternal D F) :
      explicitEffectiveKernel D (externalLabel D N) w ((f.sumMap f) i) ((f.sumMap f) j) =
        explicitEffectiveKernel D (compactExternal D F) w i j := by
    rcases i with (i | i) | (i | i) <;> rcases j with (j | j) | (j | j) <;> rfl
  have hm (i : CompactExternal D F ⊕ CompactExternal D F) :
      explicitMean D q (externalLabel D N) w ((f.sumMap f) i) =
        explicitMean D q (compactExternal D F) w i := by
    rcases i with (i | i) | (i | i) <;> rfl
  have ha := affineCoefficient_enlarge
    (explicitEffectiveKernel D (externalLabel D N) w) (explicitMean D q (externalLabel D N) w)
    (f.sumMap f) d
  have hA' : (fun i j => explicitEffectiveKernel D (externalLabel D N) w
      ((f.sumMap f) i) ((f.sumMap f) j)) = explicitEffectiveKernel D (compactExternal D F) w :=
    funext fun i => funext fun j => hA i j
  rw [hA', funext hm] at ha
  change (weight e : ℂ) * (_ * sewn D q (externalLabel D N) e w) = _
  rw [hw, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, sewn, sewnChargeTerm, sewn, ha]

open LatticeTwistedGroundRealization.SignQuotient (ModTwoCharge)
open LatticeDiscriminantTheta (gramReal)
open OriginalFourMActualChart (Chart parameter periodRoot)
open OriginalFourMChargeCoset (fourierSign quadraticSign)
open OriginalFourMSpatialWick (spatialCoefficient physical_chart_coefficient_overlap)
open OriginalFourMPhysicalProduct (physicalProduct)
open private rootZ rootZ_sq from D5.S3.VertexAlgebra.TwistedGround.OriginalFourMActualChart

/-- The real-overlap coefficient identity with the B coefficient multiplied by
the original x^(-6) factor that converts it to the native channel normalization. -/
theorem physical_chart_coefficient_overlap_normalized (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : (gramReal D).PosDef) (hr : D.rank = 24)
    {X : Type*} [Fintype X] [DecidableEq X]
    (slot : X → OriginalFourMActualChart.Puncture) (colour : X → Fin D.rank) (upperA : Bool)
    {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) {w : ℂ} (hwA : w ^ 2 = parameter .A x) (hw : ‖w‖ < 1)
    (n : X ⊕ X → ℕ) (l : List (X ⊕ X))
    (a : ModTwoCharge D) :
    let jet := fun c a => spatialCoefficient n l (fun z : (X ⊕ X) → ℂ =>
      physicalProduct D hu slot colour upperA x c a (z ∘ Sum.inl) (z ∘ Sum.inr)) 0
    (2 : ℂ) ^ (12 : ℕ) * jet .D a = ∑ b, fourierSign D a b * jet .A b ∧
    (2 : ℂ) ^ (12 : ℕ) * ((x : ℂ) ^ (6 : ℕ))⁻¹ * jet .B a =
      ∑ b, fourierSign D a b * quadraticSign D b * jet .A b := by
  have h := physical_chart_coefficient_overlap D hu hD hr slot colour upperA hx hx₁ hwA hw
    n l a
  dsimp only at h ⊢
  have hroot : (periodRoot .A x ^ (12 : ℕ))⁻¹ = (x : ℂ) ^ (6 : ℕ) := by
    change ((((rootZ x)⁻¹) ^ (12 : ℕ))⁻¹) = _
    rw [inv_pow, inv_inv, show (12 : ℕ) = 2 * 6 by decide, pow_mul, rootZ_sq hx]
  have htwo : (2 : ℂ) ^ (12 : ℕ) ≠ 0 := by norm_num
  have hx₀ : (x : ℂ) ^ (6 : ℕ) ≠ 0 := pow_ne_zero 6 (Complex.ofReal_ne_zero.mpr hx.ne')
  constructor
  · rw [h.1, ← mul_assoc, mul_inv_cancel₀ htwo, one_mul]
  · rw [h.2, hroot]
    have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    field_simp [hxC, hx₀, htwo]

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMProjectionModes
