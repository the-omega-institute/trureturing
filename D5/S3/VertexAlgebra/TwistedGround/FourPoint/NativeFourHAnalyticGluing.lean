/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeFourHAnalyticGluing
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/NativeFourHAnalyticGluing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Holomorphic gluing of the original four-H radial expansions for all Leech H states. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHRealSewing

/-! The A and upper B double-mode sums are jointly holomorphic on their
respective open domains. The common radial value gives a single correlation
function, with each original expansion on its own domain. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators Finset Topology VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHAnalyticGluing

open ActualLeechHyperbolic (leechData)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open LatticeHalfFockParityT (actualParity actualParity_on_actualGrade)
open LatticeHalfFockGradedTrace (actualGrade oddWeight)
open LatticeHalfFockCorrectedField (correctedField)
open Orbifold.NativeFixedPairField (nu)
open Orbifold.NativeFixedUpperRightSkew (rightField)
open Orbifold.NativeFullMixedField (project)
open Orbifold.NativeOddTwistedIntertwiner (TwistedEven leechUnit paritySign)
open NativeFourHRealSewing

open private BasisIndex ambientBasis projectedBasis basis_mem_grade
  FourLinear coeffAt pairWithH from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHHomogeneousExtension
open private sum_projectedBasis from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairField
open private project_val from D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeFullMixedField
open private isOpen_radial from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHRealSewing

local notation "ℒ" => leechData

private def aLinear (q : ℂ × ℂ) (p : ℤ × ℤ) : FourLinear :=
  let inner := (coeffAt p.1).comp (nu false)
  let outer := ((coeffAt p.2).comp (correctedField ℒ leechUnit)).compl₁₂
    (LatticeInvolution.fixedSpace ℒ).subtype (paritySpace ℒ leechUnit (paritySign false)).subtype
  ((q.1 - q.2) ^ (p.1 / 2) * q.2 ^ (p.2 / 2)) • inner.compr₂ (outer.compr₂ pairWithH)

private def bLinear (q : ℂ × ℂ) (p : ℤ × ℤ) : FourLinear :=
  let inner := (coeffAt p.1).comp (nu false)
  let outer := ((coeffAt p.2).comp (rightField ℒ leechUnit false)).flip
  let product := inner.compr₂ (outer.compr₂
    (pairWithH.comp (paritySpace ℒ leechUnit (paritySign false)).subtype))
  let swap : (TwistedEven →ₗ[ℂ] TwistedEven →ₗ[ℂ] TwistedEven →ₗ[ℂ] ℂ) →ₗ[ℂ]
      TwistedEven →ₗ[ℂ] TwistedEven →ₗ[ℂ] TwistedEven →ₗ[ℂ] ℂ :=
    LinearMap.lflip.toLinearMap
  (q.2 ^ (p.1 / 2) * q.1 ^ (p.2 / 2)) • (swap.comp product).flip

private theorem aLinear_apply (q : ℂ × ℂ) (p : ℤ × ℤ) (u v w b : TwistedEven) :
    aLinear q p u v w b = complexATerm q.1 q.2 u v w b p :=
  mul_comm _ _

private theorem bLinear_apply (q : ℂ × ℂ) (p : ℤ × ℤ) (u v w b : TwistedEven) :
    bLinear q p u v w b = complexBTerm q.1 q.2 u v w b p :=
  mul_comm _ _

private theorem isOpen_radialDomainA : IsOpen radialDomainA :=
  isOpen_radial (continuous_fst.sub continuous_snd) continuous_snd

private theorem isOpen_radialDomainB : IsOpen radialDomainB :=
  isOpen_radial continuous_snd continuous_fst

private def component (u : TwistedEven) (i : BasisIndex) : TwistedEven :=
  ambientBasis.repr u.val i • projectedBasis i

private theorem component_grade (u : TwistedEven) (i : BasisIndex) :
    (component u i).val ∈ actualGrade ℒ leechUnit (oddWeight ℒ i.1) := by
  have h := basis_mem_grade i
  have he := actualParity_on_actualGrade ℒ leechUnit _ ⟨ambientBasis i, h⟩
  change actualParity ℒ leechUnit (ambientBasis i) =
    (-1 : ℂ) ^ oddWeight ℒ i.1 • ambientBasis i at he
  rw [component, Submodule.coe_smul, project_val, he]
  exact (actualGrade ℒ leechUnit _).smul_mem _ ((actualGrade ℒ leechUnit _).smul_mem _
    ((actualGrade ℒ leechUnit _).add_mem h
      ((actualGrade ℒ leechUnit _).smul_mem _ ((actualGrade ℒ leechUnit _).smul_mem _ h))))

/-- Each raw channel sum is jointly holomorphic on its own radial domain for
arbitrary actual H states, and the two sums agree on the intersection. -/
theorem fourH_actual_radial (u v w b : TwistedEven) :
    ((∀ q ∈ radialDomainA, Summable (complexATerm q.1 q.2 u v w b)) ∧
      AnalyticOnNhd ℂ (fun q => ∑' p, complexATerm q.1 q.2 u v w b p) radialDomainA) ∧
    ((∀ q ∈ radialDomainB, Summable (complexBTerm q.1 q.2 u v w b)) ∧
      AnalyticOnNhd ℂ (fun q => ∑' p, complexBTerm q.1 q.2 u v w b p) radialDomainB) ∧
    Set.EqOn (fun q => ∑' p, complexATerm q.1 q.2 u v w b p)
      (fun q => ∑' p, complexBTerm q.1 q.2 u v w b p) (radialDomainA ∩ radialDomainB) := by
  classical
  let support (a : TwistedEven) := (ambientBasis.repr a.val).support
  let indices := support u ×ˢ (support v ×ˢ (support w ×ˢ support b))
  let value (F : FourLinear) (i : BasisIndex × BasisIndex × BasisIndex × BasisIndex) :=
    F (component u i.1) (component v i.2.1) (component w i.2.2.1) (component b i.2.2.2)
  have expand (F : FourLinear) : F u v w b = ∑ i ∈ indices, value F i := by
    conv_lhs =>
      rw [← sum_projectedBasis false u]
      simp only [map_sum, LinearMap.sum_apply]
      rw [← sum_projectedBasis false v]
      simp only [map_sum, LinearMap.sum_apply]
      rw [← sum_projectedBasis false w]
      simp only [map_sum, LinearMap.sum_apply]
      rw [← sum_projectedBasis false b]
      simp only [map_sum]
    simp only [indices, value, Finset.sum_product]
    rfl
  have homog (i : BasisIndex × BasisIndex × BasisIndex × BasisIndex) :=
    fourH_actual_homogeneous_radial _ _ _ _ _ _ _ _ (component_grade u i.1)
      (component_grade v i.2.1) (component_grade w i.2.2.1) (component_grade b i.2.2.2)
  have sew (i : BasisIndex × BasisIndex × BasisIndex × BasisIndex) {q : ℂ × ℂ}
      (hA : q ∈ radialDomainA) (hB : q ∈ radialDomainB) :=
    (fourH_actual_complex_sewing _ _ _ _ _ _ _ _ (component_grade u i.1)
      (component_grade v i.2.1) (component_grade w i.2.2.1) (component_grade b i.2.2.2)
      (norm_pos_iff.mp (hB.1.trans hB.2)) hB.2 hA.2).2.2.1
  let finiteSum (F : (ℂ × ℂ) → (ℤ × ℤ) → FourLinear) (q : ℂ × ℂ) :=
    ∑ i ∈ indices, ∑' p, value (F q p) i
  have finite_hasSum (F : (ℂ × ℂ) → (ℤ × ℤ) → FourLinear) (q : ℂ × ℂ)
      (h : ∀ i ∈ indices, Summable (fun p => value (F q p) i)) :
      HasSum (fun p => F q p u v w b) (finiteSum F q) :=
    (hasSum_sum fun i hi => (h i hi).hasSum).congr_fun (fun p => expand (F q p))
  have lift (F : (ℂ × ℂ) → (ℤ × ℤ) → FourLinear) (U : Set (ℂ × ℂ)) (hU : IsOpen U)
      (hs : ∀ i, ∀ q ∈ U, Summable (fun p => value (F q p) i))
      (ha : ∀ i, AnalyticOnNhd ℂ (fun q => ∑' p, value (F q p) i) U) :
      (∀ q ∈ U, HasSum (fun p => F q p u v w b) (finiteSum F q)) ∧
        AnalyticOnNhd ℂ (fun q => ∑' p, F q p u v w b) U := by
    have hsum (q : ℂ × ℂ) (hq : q ∈ U) := finite_hasSum F q (fun i _ => hs i q hq)
    refine ⟨hsum, fun q hq => ?_⟩
    have hf : AnalyticAt ℂ (finiteSum F) q :=
      Finset.analyticAt_fun_sum indices (fun i _ => ha i q hq)
    exact hf.congr (Filter.Eventually.mono (hU.mem_nhds hq) fun r hr => (hsum r hr).tsum_eq.symm)
  have hA := lift aLinear radialDomainA isOpen_radialDomainA
    (fun i => by simpa only [value, aLinear_apply] using (homog i).1.1)
    (fun i => by simpa only [value, aLinear_apply] using (homog i).1.2)
  have hB := lift bLinear radialDomainB isOpen_radialDomainB
    (fun i => by simpa only [value, bLinear_apply] using (homog i).2.1)
    (fun i => by simpa only [value, bLinear_apply] using (homog i).2.2)
  have haSum (q : ℂ × ℂ) (hq : q ∈ radialDomainA) :
      HasSum (complexATerm q.1 q.2 u v w b) (finiteSum aLinear q) := by
    simpa only [aLinear_apply] using hA.1 q hq
  have hbSum (q : ℂ × ℂ) (hq : q ∈ radialDomainB) :
      HasSum (complexBTerm q.1 q.2 u v w b) (finiteSum bLinear q) := by
    simpa only [bLinear_apply] using hB.1 q hq
  refine ⟨⟨fun q hq => (haSum q hq).summable, ?_⟩,
    ⟨fun q hq => (hbSum q hq).summable, ?_⟩, ?_⟩
  · simpa only [aLinear_apply] using hA.2
  · simpa only [bLinear_apply] using hB.2
  intro q hq
  change (∑' p, complexATerm q.1 q.2 u v w b p) = ∑' p, complexBTerm q.1 q.2 u v w b p
  rw [(haSum q hq.1).tsum_eq, (hbSum q hq.2).tsum_eq]
  exact Finset.sum_congr rfl fun i _ => by
    simpa only [value, aLinear_apply, bLinear_apply] using sew i hq.1 hq.2

open scoped Classical in
/-- The Leech four-H correlation function on the union of the two radial domains. -/
def fourHCorrelation (u v w b : TwistedEven) (q : ℂ × ℂ) : ℂ :=
  if q ∈ radialDomainA then ∑' p, complexATerm q.1 q.2 u v w b p
  else ∑' p, complexBTerm q.1 q.2 u v w b p

/-- The actual four-H correlation is jointly holomorphic on the radial union.
Each original double-mode expansion sums to this function on its entire domain. -/
theorem fourH_actual_analytic_gluing (u v w b : TwistedEven) :
    AnalyticOnNhd ℂ (fourHCorrelation u v w b) (radialDomainA ∪ radialDomainB) ∧
    (∀ q ∈ radialDomainA, HasSum (complexATerm q.1 q.2 u v w b) (fourHCorrelation u v w b q)) ∧
    (∀ q ∈ radialDomainB, HasSum (complexBTerm q.1 q.2 u v w b) (fourHCorrelation u v w b q)) := by
  classical
  obtain ⟨⟨hA, ha⟩, ⟨hB, hb⟩, heq⟩ := fourH_actual_radial u v w b
  have eqA (q : ℂ × ℂ) (hq : q ∈ radialDomainA) :
      (∑' p, complexATerm q.1 q.2 u v w b p) = fourHCorrelation u v w b q := by
    simp [fourHCorrelation, hq]
  have eqB (q : ℂ × ℂ) (hq : q ∈ radialDomainB) :
      (∑' p, complexBTerm q.1 q.2 u v w b p) = fourHCorrelation u v w b q := by
    by_cases hqA : q ∈ radialDomainA
    · simpa [fourHCorrelation, hqA] using (heq (show q ∈ radialDomainA ∩ radialDomainB
        from ⟨hqA, hq⟩)).symm
    · simp [fourHCorrelation, hqA]
  refine ⟨?_, fun q hq => eqA q hq ▸ (hA q hq).hasSum, fun q hq => eqB q hq ▸ (hB q hq).hasSum⟩
  intro q hq
  rcases hq with hq | hq
  · exact (ha q hq).congr (Filter.Eventually.mono (isOpen_radialDomainA.mem_nhds hq) eqA)
  · exact (hb q hq).congr (Filter.Eventually.mono (isOpen_radialDomainB.mem_nhds hq) eqB)

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHAnalyticGluing
