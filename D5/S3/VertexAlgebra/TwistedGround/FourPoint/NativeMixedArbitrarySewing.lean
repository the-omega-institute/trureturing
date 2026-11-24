/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeMixedArbitrarySewing
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/NativeMixedArbitrarySewing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complex HHBB sewing and analyticity for arbitrary actual Leech twisted states. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedComplexSewing
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHHomogeneousExtension

/-! Finite expansion in the actual twisted ambient basis extends complex
HHBB sewing to arbitrary external states. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators Finset TensorProduct Topology VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedArbitrarySewing

open ActualLeechHyperbolic (leechData)
open ActualChargedAdjoint (actualForm)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open LatticeHalfFockChargedTensorCoefficients (ActualGround ActualTensor)
open LatticeHalfFockCorrectedField (correctedField)
open LatticeHalfFockGradedTrace (actual_basis_apply oddWeight)
open LatticeHalfFockParityT (actualParity actualParity_on_actualGrade)
open Orbifold.NativeOddTwistedIntertwiner
  (Twisted TwistedEven TwistedOdd OddCarrier leechUnit paritySign)
open Orbifold.NativeFullMixedField (project)
open Orbifold.NativeFixedPairField (nu)
open Orbifold.NativeMixedPairField (mu)
open Orbifold.NativeOddUpperRightSkew (R rightField)
open OriginalFourMActualChart (Puncture)
open OriginalFourMVariableSupport (wordAt)
open NativeMixedWickChartTransport (MixedParity doubledOccupation sigma)
open NativeMixedUpperProductCusp (bJointTerm bSewnNumerator)
open NativeMixedComplexSewing (aJointTerm hhbb_actual_complex_sewing)
open NativeFourHHomogeneousExtension (occupation_monomials_have_marked_words)

open private BasisIndex ambientBasis basis_mem_grade coeffAt from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHHomogeneousExtension
open private sum_projectedBasis from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairField
open private project_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeFullMixedField
open private doubledCoefficient from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew
open private bSewnNumerator_differentiableOn from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedUpperProductCusp
open private b_lens_analytic sqrt_square from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedComplexSewing

local notation "ℒ" => leechData

private abbrev BSpace := paritySpace ℒ leechUnit (paritySign true)
private abbrev HHBBLinear :=
  TwistedEven →ₗ[ℂ] TwistedEven →ₗ[ℂ] TwistedOdd →ₗ[ℂ] TwistedOdd →ₗ[ℂ] ℂ

private def pairWithB : ActualTensor ℒ leechUnit →ₗ[ℂ] TwistedOdd →ₗ[ℂ] ℂ :=
  (actualForm ℒ leechUnit).flip.compl₂ BSpace.subtype

/-- Bilinearity in the two inputs of a literal doubled mode of the upper odd
right-skew field. The coefficient is zero at even doubled exponents. -/
private def oddRightCoeff (s : Bool) (e : ℤ) :
    Twisted ℒ leechUnit s →ₗ[ℂ] OddCarrier ℒ →ₗ[ℂ] Twisted ℒ leechUnit (!s) :=
  if Even e then 0 else R ℒ leechUnit s ((-e - 3) / 2)

private theorem oddRightCoeff_apply (s : Bool) (e : ℤ) (u : Twisted ℒ leechUnit s)
    (a : OddCarrier ℒ) :
    oddRightCoeff s e u a = (rightField ℒ leechUnit s u).coeff e a := by
  simp only [rightField, HVertexOperator.coeff_of_coeff, oddRightCoeff, doubledCoefficient]
  by_cases he : Even e
  · simp only [ite_eq_left he, LinearMap.zero_apply]
  · simp only [ite_eq_right he]

private def aLinear (differenceRoot zRoot : ℂ) (p : ℤ × ℤ) : HHBBLinear :=
  let inner := (coeffAt p.1).comp (nu false)
  let outer := ((coeffAt p.2).comp (correctedField ℒ leechUnit)).compl₁₂
    (LatticeInvolution.fixedSpace ℒ).subtype BSpace.subtype
  (differenceRoot ^ p.1 * zRoot ^ p.2) • inner.compr₂ (outer.compr₂ pairWithB)

private def bLinear (xRoot zRoot : ℂ) (p : ℤ × ℤ) : HHBBLinear :=
  let inner := (coeffAt p.1).comp (mu false)
  let outer := (oddRightCoeff false p.2).flip
  let product := inner.compr₂ (outer.compr₂ (pairWithB.comp BSpace.subtype))
  let swap : (TwistedOdd →ₗ[ℂ] TwistedEven →ₗ[ℂ] TwistedOdd →ₗ[ℂ] ℂ) →ₗ[ℂ]
      TwistedEven →ₗ[ℂ] TwistedOdd →ₗ[ℂ] TwistedOdd →ₗ[ℂ] ℂ :=
    LinearMap.lflip.toLinearMap
  (zRoot ^ p.1 * xRoot ^ p.2) • (swap.comp product).flip

private theorem aLinear_apply (differenceRoot zRoot : ℂ) (p : ℤ × ℤ)
    (u v : TwistedEven) (w b : TwistedOdd) :
    aLinear differenceRoot zRoot p u v w b = aJointTerm u v w b differenceRoot zRoot p :=
  mul_comm _ _

private theorem bLinear_apply (xRoot zRoot : ℂ) (p : ℤ × ℤ)
    (u v : TwistedEven) (w b : TwistedOdd) :
    bLinear xRoot zRoot p u v w b = bJointTerm false false v w u b xRoot zRoot p := by
  change (zRoot ^ p.1 * xRoot ^ p.2) *
      actualForm ℒ leechUnit b.val (oddRightCoeff false p.2 u ((mu false v).coeff p.1 w)).val = _
  rw [oddRightCoeff_apply]
  exact mul_comm _ _

private theorem project_basis_val (s : Bool) (i : BasisIndex) :
    (project s (ambientBasis i)).val =
      if oddWeight ℒ i.1 % 2 = (if s then 1 else 0) then ambientBasis i else 0 := by
  have hp := actualParity_on_actualGrade ℒ leechUnit _ ⟨ambientBasis i, basis_mem_grade i⟩
  change actualParity ℒ leechUnit (ambientBasis i) =
    (-1 : ℂ) ^ oddWeight ℒ i.1 • ambientBasis i at hp
  rw [project_val, hp]
  by_cases hi : Even (oddWeight ℒ i.1)
  · rw [hi.neg_one_pow, one_smul, Nat.even_iff.mp hi]
    cases s <;> norm_num [paritySign]
    rw [← add_smul]
    norm_num
  · have ho := Nat.not_even_iff_odd.mp hi
    rw [ho.neg_one_pow, Nat.odd_iff.mp ho]
    cases s <;> norm_num [paritySign]
    rw [← add_smul]
    norm_num

private abbrev component (s : Bool) (u : Twisted ℒ leechUnit s) (i : BasisIndex) :
    Twisted ℒ leechUnit s :=
  ambientBasis.repr u.val i • project s (ambientBasis i)

private theorem component_eq_zero (s : Bool) (u : Twisted ℒ leechUnit s) (i : BasisIndex)
    (hi : ¬ oddWeight ℒ i.1 % 2 = (if s then 1 else 0)) :
    component s u i = 0 := by
  apply Subtype.ext
  change ambientBasis.repr u.val i • (project s (ambientBasis i)).val = 0
  rw [project_basis_val, ite_eq_right hi, smul_zero]

private abbrev BasisQuad := BasisIndex × BasisIndex × BasisIndex × BasisIndex

private def basisTuples (u v : TwistedEven) (w b : TwistedOdd) : Finset BasisQuad :=
  (ambientBasis.repr u.val).support ×ˢ ((ambientBasis.repr v.val).support ×ˢ
    ((ambientBasis.repr w.val).support ×ˢ (ambientBasis.repr b.val).support))

private abbrev onComponents (u v : TwistedEven) (w b : TwistedOdd)
    (F : HHBBLinear) (i : BasisQuad) : ℂ :=
  F (component false u i.1) (component false v i.2.1)
    (component true w i.2.2.1) (component true b i.2.2.2)

private theorem expand (u v : TwistedEven) (w b : TwistedOdd) (F : HHBBLinear) :
    F u v w b = ∑ i ∈ basisTuples u v w b, onComponents u v w b F i := by
  classical
  conv_lhs =>
    rw [← sum_projectedBasis false u]
    simp only [map_sum, LinearMap.sum_apply]
    rw [← sum_projectedBasis false v]
    simp only [map_sum, LinearMap.sum_apply]
    rw [← sum_projectedBasis true w]
    simp only [map_sum, LinearMap.sum_apply]
    rw [← sum_projectedBasis true b]
    simp only [map_sum]
  simp only [basisTuples, Finset.sum_product]

/-- Root coordinates for the HHBB overlap, with the first entry the
nonzero root of the outer insertion and the second entry the physical ratio. -/
def hhbbRootDomain : Set (ℂ × ℂ) :=
  {q | q.1 ≠ 0 ∧ ‖q.2‖ < 1 ∧ (1 / 2 : ℝ) < q.2.re}

private theorem isOpen_hhbbRootDomain : IsOpen hhbbRootDomain :=
  (isOpen_ne_fun continuous_fst continuous_const).inter
    ((isOpen_lt continuous_snd.norm continuous_const).inter
      (isOpen_lt continuous_const (Complex.continuous_re.comp continuous_snd)))

/-- The canonical HHBB value is the sum of the literal upper B terms with
the principal square root of the ratio. -/
def hhbbCorrelation (u v : TwistedEven) (w b : TwistedOdd) (xRoot y : ℂ) : ℂ :=
  ∑' i, bJointTerm false false v w u b xRoot (xRoot * Complex.sqrt y) i

set_option maxHeartbeats 4000000 in
-- Elaborating the marked comparison and its analytic continuation in the same proof
-- requires reducing the actual state and mode types through several definitions.
private theorem component_sewing (u v : TwistedEven) (w b : TwistedOdd) (i : BasisQuad) :
    let u' := component false u i.1
    let v' := component false v i.2.1
    let w' := component true w i.2.2.1
    let b' := component true b i.2.2.2
    (∀ {xRoot y ξ : ℂ}, xRoot ≠ 0 → ‖y‖ < 1 → (1 / 2 : ℝ) < y.re →
      ξ ^ (2 : ℕ) = (1 - y) / y →
      HasSum (aJointTerm u' v' w' b' (xRoot * Complex.sqrt y * ξ) (xRoot * Complex.sqrt y))
        (-hhbbCorrelation u' v' w' b' xRoot y) ∧
      HasSum (bJointTerm false false v' w' u' b' xRoot (xRoot * Complex.sqrt y))
        (hhbbCorrelation u' v' w' b' xRoot y)) ∧
    AnalyticOnNhd ℂ (fun q : ℂ × ℂ => hhbbCorrelation u' v' w' b' q.1 q.2) hhbbRootDomain := by
  classical
  let u' := component false u i.1
  let v' := component false v i.2.1
  let w' := component true w i.2.2.1
  let b' := component true b i.2.2.2
  change (∀ {xRoot y ξ : ℂ}, xRoot ≠ 0 → ‖y‖ < 1 → (1 / 2 : ℝ) < y.re →
      ξ ^ (2 : ℕ) = (1 - y) / y →
      HasSum (aJointTerm u' v' w' b' (xRoot * Complex.sqrt y * ξ) (xRoot * Complex.sqrt y))
        (-hhbbCorrelation u' v' w' b' xRoot y) ∧
      HasSum (bJointTerm false false v' w' u' b' xRoot (xRoot * Complex.sqrt y))
        (hhbbCorrelation u' v' w' b' xRoot y)) ∧
    AnalyticOnNhd ℂ (fun q : ℂ × ℂ => hhbbCorrelation u' v' w' b' q.1 q.2) hhbbRootDomain
  let d : Puncture → BasisIndex
    | .P => i.1
    | .Q => i.2.1
    | .R => i.2.2.1
    | .S => i.2.2.2
  let odd : Puncture → Bool
    | .P => false
    | .Q => false
    | .R => true
    | .S => true
  by_cases h : ∀ t, oddWeight ℒ (d t).1 % 2 = (if odd t then 1 else 0)
  swap
  · obtain ⟨t, ht⟩ := not_forall.mp h
    have hzero (F : HHBBLinear) : F u' v' w' b' = 0 := by
      cases t with
      | P => simp [show u' = 0 from component_eq_zero false u i.1 ht]
      | Q => simp [show v' = 0 from component_eq_zero false v i.2.1 ht]
      | R => simp [show w' = 0 from component_eq_zero true w i.2.2.1 ht]
      | S => simp [show b' = 0 from component_eq_zero true b i.2.2.2 ht]
    have haZero (dr zr : ℂ) : aJointTerm u' v' w' b' dr zr = fun _ => 0 := by
      funext p
      rw [← aLinear_apply]
      exact hzero _
    have hbZero (xr zr : ℂ) :
        bJointTerm false false v' w' u' b' xr zr = fun _ => 0 := by
      funext p
      rw [← bLinear_apply]
      exact hzero _
    have hcZero (xr y : ℂ) : hhbbCorrelation u' v' w' b' xr y = 0 := by
      rw [hhbbCorrelation, hbZero, tsum_zero]
    constructor
    · intro xr y ξ _ _ _ _
      simp only [haZero, hbZero, hcZero, neg_zero]
      exact ⟨hasSum_zero, hasSum_zero⟩
    · have hc : (fun q : ℂ × ℂ => hhbbCorrelation u' v' w' b' q.1 q.2) = fun _ => 0 :=
        funext fun q => hcZero q.1 q.2
      rw [hc]
      exact analyticOnNhd_const
  obtain ⟨m, slot, colour, n, hmarks⟩ :=
    occupation_monomials_have_marked_words (fun t => (d t).1)
  let l := List.finRange m
  let W := wordAt ℒ slot colour n l
  have hweight (t : Puncture) :
      doubledOccupation slot n l t % 2 = ((if odd t then 1 else 0 : ℕ) : ℤ) := by
    rw [(hmarks t).2]
    exact_mod_cast h t
  have hpar : MixedParity slot n l := ⟨hweight .P, hweight .Q, hweight .R, hweight .S⟩
  let ground (s : Bool) (a : Twisted ℒ leechUnit s) (t : Puncture) :
      ActualGround ℒ leechUnit :=
    ambientBasis.repr a.val (d t) • Pi.single (d t).2 (1 : ℂ)
  have hword (s : Bool) (a : Twisted ℒ leechUnit s) (t : Puncture) (ht : odd t = s) :
      (component s a (d t)).val = W t ⊗ₜ[ℂ] ground s a t := by
    have hp := h t
    rw [ht] at hp
    rw [component, Submodule.coe_smul, project_basis_val, ite_eq_left hp,
      actual_basis_apply ℒ leechUnit (d t).1 (d t).2]
    change ambientBasis.repr a.val (d t) •
        (MvPolynomial.monomial (d t).1 (1 : ℂ) ⊗ₜ[ℂ] Pi.single (d t).2 (1 : ℂ)) =
      W t ⊗ₜ[ℂ] (ambientBasis.repr a.val (d t) • Pi.single (d t).2 (1 : ℂ))
    have hW : W t = MvPolynomial.monomial (d t).1 (1 : ℂ) := (hmarks t).1
    rw [TensorProduct.tmul_smul, hW]
  let p := ground false u .P
  let q := ground false v .Q
  let r := ground true w .R
  let dS := ground true b .S
  have hu : u'.val = W .P ⊗ₜ[ℂ] p := hword false u .P rfl
  have hv : v'.val = W .Q ⊗ₜ[ℂ] q := hword false v .Q rfl
  have hw : w'.val = W .R ⊗ₜ[ℂ] r := hword true w .R rfl
  have hb : b'.val = W .S ⊗ₜ[ℂ] dS := hword true b .S rfl
  let g (t : Puncture) := (doubledOccupation slot n l t).toNat
  let M := g .P
  let K := g .Q
  let L := g .R
  let N := g .S
  let s := sigma (M : ℤ) K L N
  let phase := Complex.I ^ ((L : ℤ) + N - M - 2 * (K : ℤ) - 3)
  let numerator := bSewnNumerator K L N (W .P) (W .Q) (W .R) (W .S) p q r dS
  let B (y : ℂ) := Complex.sqrt y ^ (-(6 + (K : ℤ) + L)) * phase * numerator y
  let scale (xRoot : ℂ) := (xRoot ^ (2 : ℕ)) ^ (-s)
  have hmarked {xRoot y ξ : ℂ} (hx : xRoot ≠ 0) (hy : ‖y‖ < 1)
      (hre : (1 / 2 : ℝ) < y.re) (hξ : ξ ^ (2 : ℕ) = (1 - y) / y) :
      HasSum (aJointTerm u' v' w' b' (xRoot * Complex.sqrt y * ξ) (xRoot * Complex.sqrt y))
        (-(scale xRoot * B y)) ∧
      HasSum (bJointTerm false false v' w' u' b' xRoot (xRoot * Complex.sqrt y))
        (scale xRoot * B y) :=
    (hhbb_actual_complex_sewing slot colour n l (List.nodup_finRange m) hpar
      u' v' w' b' p q r dS hu hv hw hb hx hy hre hξ).2.2.2.2
  constructor
  · intro xRoot y ξ hx hy hre hξ
    obtain ⟨ha, hb⟩ := hmarked hx hy hre hξ
    have heq : hhbbCorrelation u' v' w' b' xRoot y = scale xRoot * B y := hb.tsum_eq
    rw [heq]
    exact ⟨ha, hb⟩
  · intro z hz
    change z.1 ≠ 0 ∧ ‖z.2‖ < 1 ∧ (1 / 2 : ℝ) < z.2.re at hz
    have hroot : AnalyticAt ℂ (fun q : ℂ × ℂ => scale q.1) z :=
      ((analyticAt_fst (𝕜 := ℂ) (p := z)).pow 2).zpow (n := -s) (pow_ne_zero _ hz.1)
    have hB : AnalyticAt ℂ B z.2 := by
      apply analyticAt_neg.mp
      exact b_lens_analytic numerator phase (-(6 + (K : ℤ) + L)) hz.2.1 hz.2.2
        (bSewnNumerator_differentiableOn K L N (W .P) (W .Q) (W .R) (W .S) p q r dS)
    have hratio : AnalyticAt ℂ (fun q : ℂ × ℂ => B q.2) z :=
      hB.comp (f := fun q : ℂ × ℂ => q.2) analyticAt_snd
    refine (hroot.mul hratio).congr
      (Filter.Eventually.mono (isOpen_hhbbRootDomain.mem_nhds
        (show z ∈ hhbbRootDomain from hz)) fun t ht => ?_)
    change t.1 ≠ 0 ∧ ‖t.2‖ < 1 ∧ (1 / 2 : ℝ) < t.2.re at ht
    exact (hmarked ht.1 ht.2.1 ht.2.2 (sqrt_square ((1 - t.2) / t.2))).2.tsum_eq.symm

private abbrev componentValue (u v : TwistedEven) (w b : TwistedOdd)
    (xRoot y : ℂ) (i : BasisQuad) : ℂ :=
  hhbbCorrelation (component false u i.1) (component false v i.2.1)
    (component true w i.2.2.1) (component true b i.2.2.2) xRoot y

private theorem finite_b_hasSum (u v : TwistedEven) (w b : TwistedOdd)
    {xRoot y : ℂ} (hx : xRoot ≠ 0) (hy : ‖y‖ < 1) (hre : (1 / 2 : ℝ) < y.re) :
    HasSum (bJointTerm false false v w u b xRoot (xRoot * Complex.sqrt y))
      (∑ i ∈ basisTuples u v w b, componentValue u v w b xRoot y i) := by
  refine (hasSum_sum (s := basisTuples u v w b) fun i _ =>
    ((component_sewing u v w b i).1 hx hy hre (sqrt_square ((1 - y) / y))).2).congr_fun ?_
  intro p
  simpa only [onComponents, bLinear_apply] using
    expand u v w b (bLinear xRoot (xRoot * Complex.sqrt y) p)

/-- On the complex overlap the literal double-mode A and upper B sums for
arbitrary actual HHBB states are the negative and positive canonical
correlation, respectively. Either root of `(1 - y) / y` gives the A value. -/
theorem hhbb_actual_complex_sewing_of_states (u v : TwistedEven) (w b : TwistedOdd)
    {xRoot y ξ : ℂ} (hx : xRoot ≠ 0) (hy : ‖y‖ < 1) (hre : (1 / 2 : ℝ) < y.re)
    (hξ : ξ ^ (2 : ℕ) = (1 - y) / y) :
    let zRoot := xRoot * Complex.sqrt y
    let C := hhbbCorrelation u v w b xRoot y
    HasSum (aJointTerm u v w b (zRoot * ξ) zRoot) (-C) ∧
    HasSum (bJointTerm false false v w u b xRoot zRoot) C := by
  let zRoot := xRoot * Complex.sqrt y
  have hb := finite_b_hasSum u v w b hx hy hre
  have heq : hhbbCorrelation u v w b xRoot y =
      ∑ i ∈ basisTuples u v w b, componentValue u v w b xRoot y i := hb.tsum_eq
  have ha : HasSum (aJointTerm u v w b (zRoot * ξ) zRoot)
      (-(∑ i ∈ basisTuples u v w b, componentValue u v w b xRoot y i)) := by
    rw [← Finset.sum_neg_distrib]
    refine (hasSum_sum (s := basisTuples u v w b) fun i _ =>
      ((component_sewing u v w b i).1 hx hy hre hξ).1).congr_fun ?_
    intro p
    simpa only [zRoot, onComponents, aLinear_apply] using
      expand u v w b (aLinear (zRoot * ξ) zRoot p)
  change HasSum (aJointTerm u v w b (zRoot * ξ) zRoot)
      (-hhbbCorrelation u v w b xRoot y) ∧
    HasSum (bJointTerm false false v w u b xRoot zRoot) (hhbbCorrelation u v w b xRoot y)
  rw [heq]
  exact ⟨ha, hb⟩

/-- The canonical HHBB correlation is jointly analytic in the outer root
and the physical ratio on the complex overlap. -/
theorem hhbb_actual_correlation_analytic (u v : TwistedEven) (w b : TwistedOdd) :
    AnalyticOnNhd ℂ (fun q : ℂ × ℂ => hhbbCorrelation u v w b q.1 q.2) hhbbRootDomain := by
  intro z hz
  have hf : AnalyticAt ℂ (fun q : ℂ × ℂ =>
      ∑ i ∈ basisTuples u v w b, componentValue u v w b q.1 q.2 i) z :=
    Finset.analyticAt_fun_sum (basisTuples u v w b)
      (fun i _ => (component_sewing u v w b i).2 z hz)
  refine hf.congr (Filter.Eventually.mono (isOpen_hhbbRootDomain.mem_nhds hz) fun t ht => ?_)
  change t.1 ≠ 0 ∧ ‖t.2‖ < 1 ∧ (1 / 2 : ℝ) < t.2.re at ht
  exact (finite_b_hasSum u v w b ht.1 ht.2.1 ht.2.2).tsum_eq.symm

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedArbitrarySewing
