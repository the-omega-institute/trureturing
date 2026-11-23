/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldNativeBPZRadical
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldNativeBPZRadical
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native relative BPZ detects the ghost-one boundaries at every momentum. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldAllWeightDimension
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldNativeBPZLightCone
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeBPZDescent
import D5.S3.VertexAlgebra.SourceBPZ.OriginalSourceCoevaluation
import D5.S3.VertexAlgebra.TwistedGround.ActualOddGradeOrthogonality

/-! The radical on the actual ghost-one cycles is tested against the cycles
at the opposite plane momentum. At zero momentum the two original plane
currents give the pairing in the degree-one shell coordinates. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.NativeBPZ

open ActualLeechHyperbolic (leechData)
open ActualLeechOrbifoldMatter (Orbifold leechUnit leechPosDef)
open ActualLeechOrbifoldCriticalMatter (hyperbolicPlane)
open ActualLeechOrbifoldAllWeightDimension
  (FixedWeight TwistedWeight twistedWeight_eq)
open LatticeGeneratingFieldLocality (Charge)
open LatticeInvolution (fixedSpace plusPart)
open LatticePositiveEnergy (grade)
open LatticeHalfFockChargedTensorCoefficients (ActualTensor groundRank)
open LatticeHalfFockGradedTrace
  (OddMonomial actualAmbientBasis actualGrade
    actualTensorL0 actual_basis_eigenvalue oddWeight)
open LatticeHalfFockParityT (actualParity_on_actualGrade)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open LatticeLightConeCoordinates (NullFrame)
open SourceBPZ.OriginalSourceCoevaluation (coevaluation coevaluation_pairing)
open SourceBPZ.OriginalSourcePairing
  (sourcePairing sourcePairing_nondegenerate sourcePairing_symmetric)
open SourceBPZ.SourcePairingLaws (sourcePairing_theta)
open TwistedGround.ActualChargedAdjoint (actualForm actualForm_nondegenerate)
open TwistedGround.ActualOddGradeOrthogonality (actualForm_oddGrade_orthogonal)
open RelativeCohomology
  (NativeShell nativeQ GhostSpace coefficient primitive representative
    cycle_boundary_witness primitive_of_coefficient_zero primitive_degree
    representative_closed representative_degree)

open private pairing_plusPart_right_of_fixed_left
  from D5.S3.VertexAlgebra.Lattice.FixedGradedDuality
open private negative_support from D5.S3.VertexAlgebra.TwistedGround.MixedTranslation
open private mem_orbifoldWeight_iff untwistedWeight_eq_grade
  from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldAllWeightDimension
open private nativeShellEquiv assocQ_reassoc
  from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeCohomology
open private degree_shell from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeBracket
open private representative_one planeCurrent from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeZeroMomentum
open private opposite_plus_ne_zero from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldNativeBPZLightCone

private local instance : AddCommGroup ComplexState := TensorProduct.addCommGroup
private local instance (p : Charge hyperbolicPlane) : AddCommGroup (NativeShell p) :=
  Submodule.addCommGroup _
private local instance (p : Charge hyperbolicPlane) : AddCommGroup (relativeShell p) :=
  Submodule.addCommGroup _

/-- The fixed restriction detects every fixed vector via theta projection. -/
theorem fixed_sourcePairing_nondegenerate :
    ((sourcePairing leechData).compl₁₂ (fixedSpace leechData).subtype
      (fixedSpace leechData).subtype).Nondegenerate := by
  have hleft (x : fixedSpace leechData)
      (hx : ∀ y : fixedSpace leechData, sourcePairing leechData x.val y.val = 0) :
      x = 0 := by
    apply Subtype.ext
    apply (sourcePairing_nondegenerate leechData leechUnit).1
    intro y
    rw [← pairing_plusPart_right_of_fixed_left leechData (sourcePairing leechData)
      (sourcePairing_theta leechData) x.val x.property y]
    exact hx ⟨plusPart leechData y, FixedGradedDuality.plusPart_mem_fixedSpace leechData y⟩
  refine ⟨hleft, ?_⟩
  intro x hx
  apply hleft x
  intro y
  exact (sourcePairing_symmetric leechData x.val y.val).trans (hx y)

private abbrev TwistedTensor := ActualTensor leechData leechUnit
private abbrev NegativeTwisted := paritySpace leechData leechUnit (-1)
private abbrev twistedBasis := actualAmbientBasis leechData leechUnit

private theorem actualGrade_eigen (n : ℕ) (v : TwistedTensor) :
    v ∈ actualGrade leechData leechUnit n ↔
      actualTensorL0 leechData leechUnit v =
        ((leechData.rank : ℂ) / 16 + (n : ℂ) / 2) • v := by
  simp only [actualGrade, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

private theorem twistedBasis_grade
    (i : OddMonomial leechData ×
      LatticeTwistedGroundRealization.Half (groundRank leechData leechUnit)) :
    twistedBasis i ∈ actualGrade leechData leechUnit (oddWeight leechData i.1) :=
  (actualGrade_eigen _ _).mpr (actual_basis_eigenvalue leechData leechUnit i.1 i.2)

private theorem twisted_grade_orthogonal {m n : ℕ} {u v : TwistedTensor}
    (hu : u ∈ actualGrade leechData leechUnit m)
    (hv : v ∈ actualGrade leechData leechUnit n) (hmn : m ≠ n) :
    actualForm leechData leechUnit u v = 0 :=
  actualForm_oddGrade_orthogonal leechData leechUnit (m : ℤ) (n : ℤ) u v
    (by simpa only [Int.cast_natCast] using (actualGrade_eigen m u).mp hu)
    (by simpa only [Int.cast_natCast] using (actualGrade_eigen n v).mp hv)
    (by exact_mod_cast hmn)

/-- Negative parity occupies precisely the odd-degree coordinates relevant to
the restriction. Tests in even degrees vanish by energy orthogonality. -/
theorem negativeTwisted_actualForm_nondegenerate :
    ((actualForm leechData leechUnit).compl₁₂ NegativeTwisted.subtype
      NegativeTwisted.subtype).Nondegenerate := by
  classical
  have hleft (x : NegativeTwisted)
      (hx : ∀ y : NegativeTwisted, actualForm leechData leechUnit x.val y.val = 0) :
      x = 0 := by
    apply Subtype.ext
    apply (actualForm_nondegenerate leechData leechUnit).1
    have hzero : actualForm leechData leechUnit x.val = 0 := by
      apply twistedBasis.ext
      intro i
      change actualForm leechData leechUnit x.val (twistedBasis i) = 0
      by_cases hi : oddWeight leechData i.1 % 2 = 1
      · have hpar := actualParity_on_actualGrade leechData leechUnit _
          ⟨twistedBasis i, twistedBasis_grade i⟩
        rw [neg_one_pow_eq_pow_mod_two, hi, pow_one] at hpar
        have hmem : twistedBasis i ∈ NegativeTwisted := by
          simpa only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply,
            LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] using hpar
        exact hx ⟨twistedBasis i, hmem⟩
      · conv_lhs => rw [← twistedBasis.linearCombination_repr x.val]
        simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum,
          LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
        apply Finset.sum_eq_zero
        intro j hj
        have hjOdd := negative_support leechData leechUnit x j hj
        have hne : oddWeight leechData j.1 ≠ oddWeight leechData i.1 := by
          intro he
          exact hi (he ▸ hjOdd)
        rw [twisted_grade_orthogonal (twistedBasis_grade j) (twistedBasis_grade i) hne,
          smul_zero]
    intro y
    exact LinearMap.congr_fun hzero y
  refine ⟨hleft, ?_⟩
  intro x hx
  apply hleft x
  intro y
  exact ((TwistedGround.ActualPairingSymmetry.actualForm_symmetric leechData leechUnit).eq
    x.val y.val).trans (hx y)

private theorem fixed_weight_left_radical (n : ℤ) (x : FixedWeight n)
    (hx : ∀ y : FixedWeight n, sourcePairing leechData x.val y.val = 0) : x = 0 := by
  have hxGrade : x.val ∈ grade leechData n := by
    rw [← untwistedWeight_eq_grade n]
    exact x.property.2
  let u : ↥(grade leechData n ⊓ fixedSpace leechData) :=
    ⟨x.val, ⟨hxGrade, x.property.1⟩⟩
  have hu : u = 0 := (Module.forall_dual_apply_eq_zero_iff ℂ u).mp (by
    intro f
    let z := coevaluation leechData n f
    have hz : z.val ∈ ActualLeechOrbifoldAllWeightDimension.UntwistedWeight n := by
      rw [untwistedWeight_eq_grade n]
      exact z.property.1
    let y : FixedWeight n := ⟨z.val, ⟨z.property.2, hz⟩⟩
    calc
      f u = sourcePairing leechData z.val x.val :=
        (coevaluation_pairing leechData leechUnit leechPosDef n f u).symm
      _ = sourcePairing leechData x.val y.val := sourcePairing_symmetric leechData _ _
      _ = 0 := hx y)
  exact Subtype.ext (congrArg (fun y : ↥(grade leechData n ⊓ fixedSpace leechData) => y.val) hu)

private theorem twisted_weight_left_radical (n : ℤ) (x : TwistedWeight n)
    (hx : ∀ y : TwistedWeight n, actualForm leechData leechUnit x.val y.val = 0) :
    x = 0 := by
  classical
  by_cases hn : 2 ≤ n
  · let N := (2 * n - 3).toNat
    have hgrade : TwistedWeight n = actualGrade leechData leechUnit N := by
      rw [twistedWeight_eq, ite_eq_left hn]
    have hxGrade : x.val ∈ actualGrade leechData leechUnit N := by
      rw [← hgrade]
      exact x.property
    apply Subtype.ext
    apply (actualForm_nondegenerate leechData leechUnit).1
    have hzero : actualForm leechData leechUnit x.val = 0 := by
      apply twistedBasis.ext
      intro i
      change actualForm leechData leechUnit x.val (twistedBasis i) = 0
      by_cases hi : N = oddWeight leechData i.1
      · have hy : twistedBasis i ∈ TwistedWeight n := by
          rw [hgrade, hi]
          exact twistedBasis_grade i
        exact hx ⟨twistedBasis i, hy⟩
      · exact twisted_grade_orthogonal hxGrade (twistedBasis_grade i) hi
    intro y
    exact LinearMap.congr_fun hzero y
  · have hbot : x.val ∈ (⊥ : Submodule ℂ TwistedTensor) := by
      simpa only [twistedWeight_eq n, ite_eq_right hn] using x.property
    exact Subtype.ext ((Submodule.mem_bot ℂ).mp hbot)

/-- The BPZ restriction to each actual integer-weight orbifold eigenspace
has zero radical in both slots. -/
theorem orbifoldPairing_weight_nondegenerate (n : ℤ) :
    (orbifoldPairing.compl₁₂
      (ActualLeechOrbifoldAllWeightDimension.OrbifoldWeight n).subtype
      (ActualLeechOrbifoldAllWeightDimension.OrbifoldWeight n).subtype).Nondegenerate := by
  let W := ActualLeechOrbifoldAllWeightDimension.OrbifoldWeight n
  have hleft (x : W) (hx : ∀ y : W, orbifoldPairing x.val y.val = 0) : x = 0 := by
    have hxParts := (mem_orbifoldWeight_iff n x.val).mp x.property
    have hf := fixed_weight_left_radical n ⟨x.val.1.val, hxParts.1⟩ (by
      intro y
      let z : Orbifold := (⟨y.val, y.property.1⟩, 0)
      have hz : z ∈ W :=
        (mem_orbifoldWeight_iff n z).mpr ⟨y.property, (TwistedWeight n).zero_mem⟩
      simpa only [orbifoldPairing_apply, z, Submodule.coe_zero, map_zero, add_zero] using
        hx ⟨z, hz⟩)
    have ht := twisted_weight_left_radical n ⟨x.val.2.val, hxParts.2⟩ (by
      intro y
      let z : Orbifold := (0, ⟨y.val, y.property.1⟩)
      have hz : z ∈ W :=
        (mem_orbifoldWeight_iff n z).mpr ⟨(FixedWeight n).zero_mem, y.property⟩
      simpa only [orbifoldPairing_apply, z, Submodule.coe_zero,
        map_zero, LinearMap.zero_apply, zero_add] using hx ⟨z, hz⟩)
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext (congrArg (fun y : FixedWeight n => y.val) hf)
    · exact Subtype.ext (congrArg (fun y : TwistedWeight n => y.val) ht)
  refine ⟨hleft, ?_⟩
  intro x hx
  apply hleft x
  intro y
  exact (orbifoldPairing_symmetric x.val y.val).trans (hx y)

/-- Native boundaries are killed by the c₀ pairing against a relative cycle. -/
theorem relativePairing_boundary_cycle {p q : Charge hyperbolicPlane}
    (a : NativeShell p) (y : NativeShell q) (hy : nativeQ q y = 0) :
    relativePairing (nativeQ p a).val y.val = 0 := by
  rw [relativePairing_Q_skew a y, hy]
  simp only [Submodule.coe_zero, map_zero, neg_zero]

private theorem nativeQ_reassoc_symm (F : NullFrame hyperbolicPlane)
    (B : Module.Basis (Fin 0) ℂ F.K) (p : Charge hyperbolicPlane) (z : relativeShell p) :
    nativeQ p ((nativeShellEquiv p).symm z) =
      (nativeShellEquiv p).symm (relativeQ F B p z) := by
  apply Subtype.ext
  change Q (reassoc.symm z.val) = reassoc.symm (assocQ z.val)
  apply reassoc.injective
  rw [reassoc.apply_symm_apply, ← assocQ_reassoc, reassoc.apply_symm_apply]

private theorem orbifoldWeight_neg (p : Charge hyperbolicPlane) :
    RelativeCohomology.OrbifoldWeight (-p) = RelativeCohomology.OrbifoldWeight p := by
  simp only [RelativeCohomology.OrbifoldWeight, Pi.neg_apply, neg_mul_neg]

set_option maxHeartbeats 2500000 in
-- The proof compares the native shell and its reassociation through subtype coercions.
private theorem boundary_of_pairing_zero (F : NullFrame hyperbolicPlane)
    (B : Module.Basis (Fin 0) ℂ F.K) (p : Charge hyperbolicPlane) (hp : F.pPlus p ≠ 0)
    (x : NativeShell p) (hg : RelativeBracket.Degree 1 x.val) (hx : nativeQ p x = 0)
    (hrad : ∀ y : NativeShell (-p), RelativeBracket.Degree 1 y.val →
      nativeQ (-p) y = 0 → relativePairing x.val y.val = 0) :
    ∃ a : NativeShell p, RelativeBracket.Degree 0 a.val ∧ nativeQ p a = x := by
  let z := nativeShellEquiv p x
  have hz : relativeQ F B p z = 0 := by
    apply (nativeShellEquiv p).symm.map_eq_zero_iff.mp
    calc
      _ = nativeQ p ((nativeShellEquiv p).symm z) :=
        (nativeQ_reassoc_symm F B p z).symm
      _ = nativeQ p x := congrArg (nativeQ p) ((nativeShellEquiv p).symm_apply_apply x)
      _ = 0 := hx
  have hzDegree : z ∈ GhostSpace p 1 := (degree_shell p 1 z).mpr (by
    change RelativeBracket.Degree 1 ((nativeShellEquiv p).symm z).val
    simpa only [z, LinearEquiv.symm_apply_apply] using hg)
  let v := coefficient F B p hp z
  let a := (nativeShellEquiv p).symm (primitive F B p hp z)
  let r := (nativeShellEquiv p).symm (representative F B p hp v)
  have hboundary : nativeQ p a = x - r := by
    calc
      _ = (nativeShellEquiv p).symm (relativeQ F B p (primitive F B p hp z)) :=
        nativeQ_reassoc_symm F B p (primitive F B p hp z)
      _ = (nativeShellEquiv p).symm (z - representative F B p hp v) :=
        congrArg (nativeShellEquiv p).symm (cycle_boundary_witness F B p hp z hz)
      _ = (nativeShellEquiv p).symm z - r :=
        (nativeShellEquiv p).symm.toAddEquiv.map_sub z (representative F B p hp v)
      _ = x - r := congrArg (· - r) ((nativeShellEquiv p).symm_apply_apply x)
  have hvOpp (w : RelativeCohomology.OrbifoldWeight (-p)) : orbifoldPairing v.val w.val = 0 := by
    let hq := opposite_plus_ne_zero F p hp
    let t := representative F B (-p) hq w
    let s := (nativeShellEquiv (-p)).symm t
    have hs : nativeQ (-p) s = 0 := by
      calc
        _ = (nativeShellEquiv (-p)).symm (relativeQ F B (-p) t) :=
          nativeQ_reassoc_symm F B (-p) t
        _ = (nativeShellEquiv (-p)).symm 0 :=
          congrArg (nativeShellEquiv (-p)).symm (representative_closed F B (-p) hq w)
        _ = 0 := (nativeShellEquiv (-p)).symm.map_zero
    have hsDegree : RelativeBracket.Degree 1 s.val :=
      (degree_shell (-p) 1 _).mp (representative_degree F B (-p) hq w)
    have hb := relativePairing_boundary_cycle a s hs
    have he := congrArg (fun u : NativeShell p => relativePairing u.val s.val) hboundary
    change relativePairing (nativeQ p a).val s.val =
      relativePairing (x.val - r.val) s.val at he
    rw [hb, map_sub, LinearMap.sub_apply, hrad s hsDegree hs, zero_sub] at he
    have hpair := relativePairing_representative F B p hp v w
    change relativePairing r.val s.val = orbifoldPairing v.val w.val at hpair
    exact hpair.symm.trans (neg_eq_zero.mp he.symm)
  have hnondeg := orbifoldPairing_weight_nondegenerate (1 - p (0 : Fin 2) * p (1 : Fin 2))
  have hv : v = 0 := hnondeg.1 v (by
    intro w
    have hw : w.val ∈ RelativeCohomology.OrbifoldWeight (-p) := by
      rw [orbifoldWeight_neg p]
      exact w.property
    exact hvOpp ⟨w.val, hw⟩)
  refine ⟨a, ?_, ?_⟩
  · have ha := (degree_shell p (1 - 1) _).mp (primitive_degree F B p hp 1 z hzDegree)
    change RelativeBracket.Degree 0 (reassoc.symm (primitive F B p hp z).val)
    simpa only [sub_self] using ha
  · calc
      _ = (nativeShellEquiv p).symm (relativeQ F B p (primitive F B p hp z)) :=
        nativeQ_reassoc_symm F B p (primitive F B p hp z)
      _ = (nativeShellEquiv p).symm z :=
        congrArg (nativeShellEquiv p).symm (primitive_of_coefficient_zero F B p hp z hz hv)
      _ = x := (nativeShellEquiv p).symm_apply_apply x

/-- At every nonzero plane momentum, the left radical of native relative BPZ
on ghost-one cycles against the opposite-momentum ghost-one cycles is exactly
the image of the original differential from the ghost-zero relative shell. -/
theorem relativePairing_radical_iff_boundary (p : Charge hyperbolicPlane) (hp : p ≠ 0)
    (x : NativeShell p) (hg : RelativeBracket.Degree 1 x.val) (hx : nativeQ p x = 0) :
    (∀ y : NativeShell (-p), RelativeBracket.Degree 1 y.val →
      nativeQ (-p) y = 0 → relativePairing x.val y.val = 0) ↔
      ∃ a : NativeShell p, RelativeBracket.Degree 0 a.val ∧ nativeQ p a = x := by
  constructor
  · intro hrad
    rcases planeFrame_covers_nonzero p hp with h | h
    · exact boundary_of_pairing_zero planeFrame planeBasis p h x hg hx hrad
    · exact boundary_of_pairing_zero swappedPlaneFrame swappedPlaneBasis p h x hg hx hrad
  · rintro ⟨a, _, ha⟩ y _ hy
    rw [← ha]
    exact relativePairing_boundary_cycle a y hy

private theorem zeroMomentum_degreeOne_expansion (x : GhostSpace 0 1) :
    reassoc.symm x.val.val =
      RelativeZeroMomentum.degreeOneEquiv x 0 • RelativeZeroMomentum.u 0 +
      RelativeZeroMomentum.degreeOneEquiv x 1 • RelativeZeroMomentum.u 1 := by
  have h : RelativeZeroMomentum.representative
      (0, (RelativeZeroMomentum.degreeOneEquiv x, 0)) = reassoc.symm x.val.val :=
    congrArg (fun y : GhostSpace 0 1 => reassoc.symm y.val.val)
      (RelativeZeroMomentum.degreeOneEquiv.symm_apply_apply x)
  rw [← h, representative_one,
    Fin.sum_univ_two (fun i : Fin 2 => RelativeZeroMomentum.degreeOneEquiv x i • planeCurrent i)]
  simp only [RelativeZeroMomentum.u, TensorProduct.tmul_add, TensorProduct.add_tmul,
    TensorProduct.tmul_smul, TensorProduct.smul_tmul']

/-- The native pairing of actual degree-one zero-momentum states in their two
current coordinates. -/
theorem relativePairing_zeroMomentum_coordinates (x y : GhostSpace 0 1) :
    relativePairing (reassoc.symm x.val.val) (reassoc.symm y.val.val) =
      -(RelativeZeroMomentum.degreeOneEquiv x 0 * RelativeZeroMomentum.degreeOneEquiv y 1 +
        RelativeZeroMomentum.degreeOneEquiv x 1 * RelativeZeroMomentum.degreeOneEquiv y 0) := by
  rw [zeroMomentum_degreeOne_expansion x, zeroMomentum_degreeOne_expansion y]
  have h00 : hyperbolicPlane.G (0 : Fin 2) (0 : Fin 2) = 0 :=
    OrderedHyperbolicExtension.U_zero_zero
  have h01 : hyperbolicPlane.G (0 : Fin 2) (1 : Fin 2) = 1 :=
    OrderedHyperbolicExtension.U_zero_one
  have h10 : hyperbolicPlane.G (1 : Fin 2) (0 : Fin 2) = 1 :=
    OrderedHyperbolicExtension.U_one_zero
  have h11 : hyperbolicPlane.G (1 : Fin 2) (1 : Fin 2) = 0 :=
    OrderedHyperbolicExtension.U_one_one
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    relativePairing_cartan, h00, h01, h10, h11, Int.cast_zero, Int.cast_one, neg_zero,
    mul_zero, zero_add, add_zero, mul_neg, mul_one, neg_add]
  ring

private theorem nativeQ_zeroMomentum (x : NativeShell 0) : nativeQ 0 x = 0 := by
  obtain ⟨z, rfl⟩ := (nativeShellEquiv 0).symm.surjective x
  calc
    _ = (nativeShellEquiv 0).symm (relativeQ planeFrame planeBasis 0 z) :=
      nativeQ_reassoc_symm planeFrame planeBasis 0 z
    _ = (nativeShellEquiv 0).symm 0 :=
      congrArg (nativeShellEquiv 0).symm
        (DFunLike.congr_fun RelativeZeroMomentum.relativeQ_eq_zero z)
    _ = 0 := (nativeShellEquiv 0).symm.map_zero

set_option maxHeartbeats 2500000 in
-- The degree tests elaborate through both associations of the native shell.
/-- In the native ghost-one shell at zero momentum the radical consists of
boundaries. The original differential vanishes on this shell. -/
theorem relativePairing_radical_iff_boundary_zeroMomentum
    (x : NativeShell 0) (hg : RelativeBracket.Degree 1 x.val) :
    (∀ y : NativeShell 0, RelativeBracket.Degree 1 y.val →
      nativeQ 0 y = 0 → relativePairing x.val y.val = 0) ↔
      ∃ a : NativeShell 0, RelativeBracket.Degree 0 a.val ∧ nativeQ 0 a = x := by
  constructor
  · intro hrad
    let z : GhostSpace 0 1 := ⟨nativeShellEquiv 0 x, (degree_shell 0 1 _).mpr (by
      change RelativeBracket.Degree 1 (reassoc.symm (reassoc x.val))
      rwa [reassoc.symm_apply_apply])⟩
    have test (y : GhostSpace 0 1) :
        relativePairing (reassoc.symm z.val.val) (reassoc.symm y.val.val) = 0 := by
      let t := (nativeShellEquiv 0).symm y.val
      have ht : RelativeBracket.Degree 1 t.val :=
        (degree_shell 0 1 y.val).mp y.property
      change relativePairing (reassoc.symm (reassoc x.val)) t.val = 0
      rw [reassoc.symm_apply_apply]
      exact hrad t ht (nativeQ_zeroMomentum t)
    have h0 : RelativeZeroMomentum.degreeOneEquiv z 0 = 0 := by
      simpa only [relativePairing_zeroMomentum_coordinates, LinearEquiv.apply_symm_apply,
        Pi.single_eq_same, Pi.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide),
        mul_one, mul_zero, add_zero, neg_eq_zero] using
        test (RelativeZeroMomentum.degreeOneEquiv.symm (Pi.single (1 : Fin 2) 1))
    have h1 : RelativeZeroMomentum.degreeOneEquiv z 1 = 0 := by
      simpa only [relativePairing_zeroMomentum_coordinates, LinearEquiv.apply_symm_apply,
        Pi.single_eq_same, Pi.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide),
        mul_one, mul_zero, zero_add, neg_eq_zero] using
        test (RelativeZeroMomentum.degreeOneEquiv.symm (Pi.single (0 : Fin 2) 1))
    have hz : z = 0 := by
      apply RelativeZeroMomentum.degreeOneEquiv.injective
      rw [RelativeZeroMomentum.degreeOneEquiv.map_zero]
      funext i
      fin_cases i
      · exact h0
      · exact h1
    have hx : x = 0 := (nativeShellEquiv 0).map_eq_zero_iff.mp
      (congrArg (fun y : GhostSpace 0 1 => y.val) hz)
    refine ⟨0, ?_, (nativeQ_zeroMomentum 0).trans hx.symm⟩
    change RelativeBracket.N (0 : ComplexState) = ((0 : ℤ) : ℂ) • (0 : ComplexState)
    rw [RelativeBracket.N.map_zero, smul_zero]
  · rintro ⟨a, _, ha⟩ y _ hy
    rw [← ha]
    exact relativePairing_boundary_cycle a y hy

/-- In every original momentum sector, native relative BPZ against the opposite
sector detects exactly the ghost-one boundaries. The native shell has the
original momentum, antighost, and energy constraints of
`RelativeBracket.relative_iff`. -/
theorem relativePairing_radical_iff_boundary_all_momenta (p : Charge hyperbolicPlane)
    (x : NativeShell p) (hg : RelativeBracket.Degree 1 x.val) (hx : nativeQ p x = 0) :
    (∀ y : NativeShell (-p), RelativeBracket.Degree 1 y.val →
      nativeQ (-p) y = 0 → relativePairing x.val y.val = 0) ↔
      ∃ a : NativeShell p, RelativeBracket.Degree 0 a.val ∧ nativeQ p a = x := by
  by_cases hp : p = 0
  · subst p
    rw [show -(0 : Charge hyperbolicPlane) = 0 from neg_zero]
    exact relativePairing_radical_iff_boundary_zeroMomentum x hg
  · exact relativePairing_radical_iff_boundary p hp x hg hx

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.NativeBPZ
