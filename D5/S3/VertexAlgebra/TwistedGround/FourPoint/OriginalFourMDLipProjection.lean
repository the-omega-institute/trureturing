/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipProjection
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipProjection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact four-occupation readout of the normalized D charge summand. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipOccupation
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSewnProjection

/-! The D-boundary Gaussian readout in the original compact occupations. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDLipMean

open LatticeGeneratingFieldLocality LatticePositiveEnergy MvPolynomial
open OriginalChargedRowSource (affineCoefficient)
open OriginalFourMActualChart (Chart Puncture parameter)
open OriginalFourMJointWick (BoundedExternal)
open OriginalFourMCauchyTaylor (inverseLoweredWord)
open OriginalFourMOccupationTransport (flags)
open OriginalFourMSpatialWick (spatialCoefficient)
open NativeAffineExternalCoefficient (coordinateJet coordinateJet_const_mul)
open OriginalGaussianSourceRestriction
  (CompactExternal compactExternal fourSupport externalOccupation)
open OriginalNormalRowSource (restricted embedded_weight supportLabel restricted_reconstruct)
open FactorialFockMetric (weight)
open OriginalFourMDLipNome (dNome)
open OriginalFourMDLipNome (dNome_norm_lt_one)
open OriginalFourMSectorContinuation (dLipChargeSector)
open OriginalFourMChargeNormal (compact_charge_normal)
open LatticeTwistedGroundRealization.SignQuotient (ModTwoCharge reduceCharge)
open OriginalFourMPhysicalProduct (physicalProduct)
open OriginalFourMSpatialWick (physical_chart_jet_hasSum)
open private dMatrix dLinear dDeterminant from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipSector
open private boundaryMean from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipOccupation
open private externalLabel from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMJointWick
open private boundedWord nativeLabel from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMJointWick
open private compactEmbedding from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMProjectionModes
open private affineCoefficient_enlarge from
  D5.S3.VertexAlgebra.TwistedGround.OriginalCorrectedRowRecompositionSource
open private NativeModes boxedOscillator boxed_monomials_product sum_reverse_four from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSewnProjection
open private punctureWords from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSewnProjection
open private chartPeriod chartTau from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMChartProduct
open private physicalEntry physicalMean spatialCoefficient_const_mul coordinateJet_scale from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWick
open private chart_charge_data physicalChargeSummand markedQuadratic split_spatial
  mark_coefficient_eq_jet from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSpatialWick
open private relative from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPhysicalCovariance
open private dLip_charge_factor_eq_chart from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipChartSource

private def dLipChargeTerm (D : LatticeData) (q : Charge D)
    (d g r s : Index D →₀ ℕ) (z : ℝ) : ℂ :=
  let F := fourSupport D d g r s
  let e := compactExternal D F
  let label := Sum.elim e e
  let t := parameter .D (z : ℂ)
  dDeterminant true t * dNome true t ^ (chargeEnergy D q).toNat *
    affineCoefficient (dMatrix D true e t)
      (fun i => (bilinear D (unitCharge D (label i).2.1) q : ℂ) * dLinear D true e t i)
      (externalOccupation D F d g r s)

private def dLipReadout (D : LatticeData) (q : Charge D) (N : ℕ) (z : ℝ) :
    MvPolynomial (NativeModes D N) ℂ →ₗ[ℂ] ℂ :=
  let t := parameter .D (z : ℂ)
  (basisMonomials (NativeModes D N) ℂ).constr ℂ fun e =>
    (weight e : ℂ) * (dDeterminant true t * dNome true t ^ (chargeEnergy D q).toNat *
      affineCoefficient (dMatrix D true (externalLabel D N) t) (boundaryMean D q N z) e)

private theorem dLipReadout_monomial (D : LatticeData) (q : Charge D) (N : ℕ) (z : ℝ)
    (e : NativeModes D N →₀ ℕ) (c : ℂ) :
    let t := parameter .D (z : ℂ)
    dLipReadout D q N z (monomial e c) = c * ((weight e : ℂ) *
      (dDeterminant true t * dNome true t ^ (chargeEnergy D q).toNat *
        affineCoefficient (dMatrix D true (externalLabel D N) t) (boundaryMean D q N z) e)) := by
  dsimp only
  rw [show (monomial e c : MvPolynomial (NativeModes D N) ℂ) = c • monomial e 1 by
    simp [smul_monomial, smul_eq_mul], map_smul]
  change c • (basisMonomials (NativeModes D N) ℂ).constr ℂ _
    ((basisMonomials (NativeModes D N) ℂ) e) = _
  rw [Module.Basis.constr_basis, smul_eq_mul]

private theorem bounded_boundary_charge_term (D : LatticeData) (q : Charge D)
    (N : ℕ) (z : ℝ) (d g r s : Index D →₀ ℕ) (hF : ∀ i ∈ fourSupport D d g r s, i.2 ≤ N)
    (c : ℂ) :
    let F := fourSupport D d g r s
    let f := compactEmbedding D N F hF
    let e := (externalOccupation D F d g r s).embDomain (f.sumMap f)
    dLipReadout D q N z (monomial e c) =
      c * ((weight d : ℂ) * (weight g : ℂ) * (weight r : ℂ) * (weight s : ℂ)) *
        dLipChargeTerm D q d g r s z := by
  classical
  dsimp only
  let F := fourSupport D d g r s
  let f := compactEmbedding D N F hF
  let t := parameter .D (z : ℂ)
  let o := externalOccupation D F d g r s
  let e := o.embDomain (f.sumMap f)
  let A := dMatrix D true (externalLabel D N) t
  let mu := boundaryMean D q N z
  have hr (p : Index D →₀ ℕ) (hp : p.support ⊆ F) :
      weight (restricted D F p) = weight p := by
    rw [← embedded_weight D (supportLabel D F), restricted_reconstruct D F p hp]
  have hw : weight e = weight d * weight g * weight r * weight s := by
    have he : weight e = weight o := by
      unfold weight
      exact Finsupp.prod_embDomain
    rw [he]
    simp only [o, externalOccupation, weight, Finsupp.prod_sumElim]
    change (weight (restricted D F d) * weight (restricted D F g)) *
      (weight (restricted D F r) * weight (restricted D F s)) = _
    rw [hr d (by intro i hi; simp [F, fourSupport, hi]),
      hr g (by intro i hi; simp [F, fourSupport, hi]),
      hr r (by intro i hi; simp [F, fourSupport, hi]),
      hr s (by intro i hi; simp [F, fourSupport, hi])]
    simp only [weight, mul_assoc]
  have hA (i j : CompactExternal D F ⊕ CompactExternal D F) :
      A ((f.sumMap f) i) ((f.sumMap f) j) = dMatrix D true (compactExternal D F) t i j := by
    rcases i with (i | i) | (i | i) <;> rcases j with (j | j) | (j | j) <;> rfl
  let label := Sum.elim (compactExternal D F) (compactExternal D F)
  have hm (i : CompactExternal D F ⊕ CompactExternal D F) :
      mu ((f.sumMap f) i) = (bilinear D (unitCharge D (label i).2.1) q : ℂ) *
        dLinear D true (compactExternal D F) t i := by
    rcases i with (i | i) | (i | i) <;> rfl
  have ha := affineCoefficient_enlarge A mu (f.sumMap f) o
  rw [funext (fun i => funext (hA i)), funext hm] at ha
  rw [dLipReadout_monomial]
  change c * ((weight e : ℂ) * (_ * affineCoefficient A mu e)) = _
  rw [hw, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, ha]
  unfold dLipChargeTerm
  dsimp only [F, t, o, label]
  ring

/-- The joined finite D readout equals the original four-occupation
projection on a single charge, with all four factorials retained. -/
theorem dLip_four_charge_projection (D : LatticeData) (q : Charge D) (N : ℕ) (z : ℝ)
    (P Q R S : Oscillator D)
    (hP : ∀ d ∈ P.support, ∀ i ∈ d.support, i.2 ≤ N)
    (hQ : ∀ d ∈ Q.support, ∀ i ∈ d.support, i.2 ≤ N)
    (hR : ∀ d ∈ R.support, ∀ i ∈ d.support, i.2 ≤ N)
    (hS : ∀ d ∈ S.support, ∀ i ∈ d.support, i.2 ≤ N) :
    dLipReadout D q N z (boxedOscillator D N false false P * boxedOscillator D N false true Q *
        boxedOscillator D N true false R * boxedOscillator D N true true S) =
      ∑ d ∈ P.support, ∑ g ∈ Q.support, ∑ r ∈ R.support, ∑ s ∈ S.support,
        (P.coeff d * Q.coeff g * R.coeff r * S.coeff s) *
          ((weight d : ℂ) * (weight g : ℂ) * (weight r : ℂ) * (weight s : ℂ)) *
          dLipChargeTerm D q d g r s z := by
  classical
  conv_lhs => rw [P.as_sum, Q.as_sum, R.as_sum, S.as_sum]
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [sum_reverse_four]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro g hg
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  have hF : ∀ i ∈ fourSupport D d g r s, i.2 ≤ N := by
    intro i hi
    simp only [fourSupport, Finset.mem_union] at hi
    rcases hi with ((hi | hi) | hi) | hi
    · exact hP d hd i hi
    · exact hQ g hg i hi
    · exact hR r hr i hi
    · exact hS s hs i hi
  rw [boxed_monomials_product D N d g r s _ _ _ _ hF]
  exact bounded_boundary_charge_term D q N z d g r s hF _

/-- One charge in the physical D jet gives the normalized D readout of the
four inverse-lowered words in their actual order P, R, Q, S. -/
theorem dLip_spatial_four_occupation (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (q : Charge D) (N : ℕ)
    {z : ℝ} (hz : 0 < z) (hz₁ : z < 1) {X : Type*} [Fintype X] [DecidableEq X]
    (slot : X → Puncture) (mode : X → Index D) (bound : ∀ i, (mode i).2 ≤ N)
    (words : Puncture → List X) (hslot : ∀ s j, j ∈ words s → slot j = s)
    (hl : ((punctureWords words).flatMap Prod.snd).Nodup)
    (hbox : ∀ s d, d ∈ (inverseLoweredWord D .D z s ((words s).map mode)).support →
      ∀ i ∈ d.support, i.2 ≤ N) :
    let l := (punctureWords words).flatMap Prod.snd
    let colour := fun i => (mode i).1
    let sign := fun i => relative .D (slot i)
    let K := physicalEntry D true .D z slot colour
    let m := physicalMean D q true .D z slot colour
    let W := fun s => inverseLoweredWord D .D z s ((words s).map mode)
    let P := W .P
    let Q := W .R
    let R := W .Q
    let S := W .S
    spatialCoefficient (fun i => (mode i).2) l (fun u =>
      (chartPeriod true .D z ^ (12 : ℕ))⁻¹ *
      Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau true .D z * (bilinear D q q : ℂ) / 2) *
      coordinateJet l (fun v => Complex.exp (
        (1 / 2 : ℂ) * (∑ i, ∑ j, K i j (u i) (u j) * (sign i * v i) * (sign j * v j)) +
          ∑ i, m i (u i) * (sign i * v i))) 0) 0 =
      (l.map sign).prod * (1 - parameter .D (z : ℂ)) ^ (3 : ℕ) *
        ∑ d ∈ P.support, ∑ g ∈ Q.support, ∑ r ∈ R.support, ∑ s ∈ S.support,
          (P.coeff d * Q.coeff g * R.coeff r * S.coeff s) *
            ((weight d : ℂ) * (weight g : ℂ) * (weight r : ℂ) * (weight s : ℂ)) *
            dLipChargeTerm D q d g r s z := by
  classical
  dsimp only
  let l := (punctureWords words).flatMap Prod.snd
  let sign := fun i => relative .D (slot i)
  let K := physicalEntry D true .D z slot (fun i => (mode i).1)
  let m := physicalMean D q true .D z slot (fun i => (mode i).1)
  let t := parameter .D (z : ℂ)
  let p := (chartPeriod true .D z ^ (12 : ℕ))⁻¹ *
    Complex.exp ((Real.pi : ℂ) * Complex.I * chartTau true .D z * (bilinear D q q : ℂ) / 2)
  let f (u v : X → ℂ) := Complex.exp (
    (1 / 2 : ℂ) * (∑ i, ∑ j, K i j (u i) (u j) * v i * v j) + ∑ i, m i (u i) * v i)
  have he (u : X → ℂ) :
      coordinateJet l (fun v => f u (fun i => sign i * v i)) 0 =
        (l.map sign).prod * coordinateJet l (f u) 0 := by
    simpa only [Pi.zero_apply, mul_zero, ← Pi.zero_def] using coordinateJet_scale sign l (f u) 0
  have hslots : ((punctureWords words).map Prod.fst).Nodup := by simp [punctureWords]
  have hv : ∀ entry ∈ punctureWords words, ∀ j ∈ entry.2, slot j = entry.1 := by
    intro entry he'
    simp only [punctureWords, List.mem_cons, List.not_mem_nil, or_false] at he'
    rcases he' with rfl | rfl | rfl | rfl <;> exact hslot _
  let W := fun s => inverseLoweredWord D .D z s ((words s).map mode)
  let F := boxedOscillator D N false false (W .P) * boxedOscillator D N false true (W .R) *
    boxedOscillator D N true false (W .Q) * boxedOscillator D N true true (W .S)
  have hF : ((punctureWords words).map
      (fun entry => boundedWord D N .D z entry.1 (entry.2.map mode))).prod = F := by
    simp only [punctureWords, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, F, W, boundedWord, boxedOscillator, nativeLabel, flags]
    ac_rfl
  have hp : p = (1 - t) ^ (3 : ℕ) *
      (dDeterminant true t * dNome true t ^ (chargeEnergy D q).toNat) := by
    have hnt : 1 - t ≠ 0 := by
      have hn : 1 < z⁻¹ := (one_lt_inv₀ hz).2 hz₁
      apply sub_ne_zero.mpr
      dsimp only [t, parameter]
      rw [← Complex.ofReal_inv, ← Complex.ofReal_one]
      exact_mod_cast hn.ne
    unfold p
    rw [dLip_charge_factor_eq_chart D hD q hz, dDeterminant, ← mul_assoc, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero 3 hnt), one_mul]
    rfl
  have h := dLip_spatial_occupation D hu q N hz hz₁ slot mode bound
    (punctureWords words) hslots hv hl
  dsimp only at h
  rw [hF] at h
  have hproj := dLip_four_charge_projection D q N z (W .P) (W .R) (W .Q) (W .S)
    (hbox _) (hbox _) (hbox _) (hbox _)
  change dLipReadout D q N z F = _ at hproj
  change spatialCoefficient (fun i => (mode i).2) l
    (fun u => p * coordinateJet l (fun v => f u (fun i => sign i * v i)) 0) 0 = _
  simp only [he, spatialCoefficient_const_mul]
  rw [h, ← hproj, hp]
  have hRead : dLipReadout D q N z F =
      ∑ e ∈ F.support, F.coeff e * ((weight e : ℂ) *
        (dDeterminant true t * dNome true t ^ (chargeEnergy D q).toNat *
          affineCoefficient (dMatrix D true (externalLabel D N) t) (boundaryMean D q N z) e)) := by
    conv_lhs => rw [F.as_sum]
    simp only [map_sum, dLipReadout_monomial, t]
  rw [hRead]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

private theorem dLipChargeTerm_hasSum (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (a : ModTwoCharge D)
    (d g r s : Index D →₀ ℕ) {z : ℝ} (hz : 0 < z) (hz₁ : z < 1) :
    HasSum (fun q : {q : Charge D // reduceCharge D q = a} => dLipChargeTerm D q.val d g r s z)
      (dLipChargeSector D true a d g r s (parameter .D (z : ℂ))) := by
  classical
  let t := parameter .D (z : ℂ)
  let e := compactExternal D (fourSupport D d g r s)
  have ht : ‖dNome true t‖ < 1 := by
    dsimp only [t, parameter]
    rw [← Complex.ofReal_inv]
    exact dNome_norm_lt_one true ((one_lt_inv₀ hz).2 hz₁)
  obtain ⟨b, hb, hbound⟩ := (compact_charge_normal D hD d g r s
    {t} isCompact_singleton (dDeterminant true) (dNome true)
    differentiableOn_singleton differentiableOn_singleton
    (by intro u hu; simpa only [Set.mem_singleton_iff.mp hu] using ht)
    (dMatrix D true e) (dLinear D true e)
    (fun _ _ => differentiableOn_singleton) (fun _ => differentiableOn_singleton)).1
  have hsum : Summable (fun q : Charge D => dLipChargeTerm D q d g r s z) :=
    hb.of_norm_bounded fun q => hbound q t (Set.mem_singleton t)
  have hi : ∑' q : {q : Charge D // reduceCharge D q = a}, dLipChargeTerm D q.val d g r s z =
      dLipChargeSector D true a d g r s t := by
    let fiber : Set (Charge D) := {q | reduceCharge D q = a}
    calc
      _ = ∑' q : Charge D, fiber.indicator (fun q => dLipChargeTerm D q d g r s z) q :=
        tsum_subtype fiber _
      _ = _ := by
        unfold dLipChargeSector
        apply tsum_congr
        intro q
        by_cases hq : reduceCharge D q = a <;>
          simp only [fiber, Set.indicator, Set.mem_setOf_eq, hq, ite_true, ite_false,
            dLipChargeTerm, t]
  rw [← hi]
  exact (hsum.subtype (fun q => reduceCharge D q = a)).hasSum

/-- Summing the charge readouts on the original lattice fibre gives the
physical D jet with the compact continued Gaussian used in the D channel. -/
theorem dLip_sector_four_occupation (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (a : ModTwoCharge D) (N : ℕ)
    {z : ℝ} (hz : 0 < z) (hz₁ : z < 1) {X : Type*} [Fintype X] [DecidableEq X]
    (slot : X → Puncture) (mode : X → Index D) (bound : ∀ i, (mode i).2 ≤ N)
    (words : Puncture → List X) (hslot : ∀ s j, j ∈ words s → slot j = s)
    (hl : ((punctureWords words).flatMap Prod.snd).Nodup)
    (hbox : ∀ s d, d ∈ (inverseLoweredWord D .D z s ((words s).map mode)).support →
      ∀ i ∈ d.support, i.2 ≤ N) :
    let l := (punctureWords words).flatMap Prod.snd
    let colour := fun i => (mode i).1
    let sign := fun i => relative .D (slot i)
    let W := fun s => inverseLoweredWord D .D z s ((words s).map mode)
    let P := W .P
    let Q := W .R
    let R := W .Q
    let S := W .S
    let t := parameter .D (z : ℂ)
    spatialCoefficient (Sum.elim (fun i => (mode i).2) (fun _ => 1))
      (l.map Sum.inr ++ l.map Sum.inl) (fun u =>
        physicalProduct D hu slot colour true z .D a (u ∘ Sum.inl) (u ∘ Sum.inr)) 0 =
      (l.map sign).prod * (1 - t) ^ (3 : ℕ) *
        ∑ d ∈ P.support, ∑ g ∈ Q.support, ∑ r ∈ R.support, ∑ s ∈ S.support,
          (P.coeff d * Q.coeff g * R.coeff r * S.coeff s) *
            ((weight d : ℂ) * (weight g : ℂ) * (weight r : ℂ) * (weight s : ℂ)) *
            dLipChargeSector D true a d g r s t := by
  classical
  dsimp only
  let l := (punctureWords words).flatMap Prod.snd
  let sign := fun i => relative .D (slot i)
  let colour := fun i => (mode i).1
  let W := fun s => inverseLoweredWord D .D z s ((words s).map mode)
  let P := W .P
  let Q := W .R
  let R := W .Q
  let S := W .S
  let t := parameter .D (z : ℂ)
  let c := (l.map sign).prod * (1 - t) ^ (3 : ℕ)
  obtain ⟨hp, hτ⟩ := chart_charge_data true .D hz hz₁
  have hj := physical_chart_jet_hasSum D hu hD slot colour true .D hz hz₁ hp hτ a
    (Sum.elim (fun i => (mode i).2) (fun _ => 1)) (l.map Sum.inr ++ l.map Sum.inl)
  let factor (d g r s : Index D →₀ ℕ) := (P.coeff d * Q.coeff g * R.coeff r * S.coeff s) *
    ((weight d : ℂ) * (weight g : ℂ) * (weight r : ℂ) * (weight s : ℂ))
  have hsum := (hasSum_sum (s := P.support) fun d _ =>
    hasSum_sum (s := Q.support) fun g _ =>
      hasSum_sum (s := R.support) fun r _ =>
        hasSum_sum (s := S.support) fun s _ =>
          (dLipChargeTerm_hasSum D hD a d g r s hz hz₁).mul_left (factor d g r s)).mul_left c
  refine hj.unique (hsum.congr_fun ?_)
  intro q
  have h := dLip_spatial_four_occupation D hu hD q.val N hz hz₁ slot mode bound
    words hslot hl hbox
  dsimp only at h
  rw [← h, split_spatial, ← congrFun (spatialCoefficient_const_mul _ _ _ _) 0]
  apply congrArg (fun f => spatialCoefficient (fun i => (mode i).2) l f 0)
  funext u
  rw [mark_coefficient_eq_jet l hl _ 0 (fun _ _ => rfl)]
  simp only [physicalChargeSummand, markedQuadratic, Sum.elim_inl, Sum.elim_inr,
    coordinateJet_const_mul, colour, mul_assoc]
  rfl

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDLipMean
