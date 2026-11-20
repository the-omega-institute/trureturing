/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTPhysicalReal
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTPhysicalReal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positivity of the intrinsic contravariant form on the original nonzero shells. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTQuartetReal

/-! The native finite perturbation and the canonical positive form on the physical quotient. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTPhysicalReal

open OriginalOrbifoldCriticalMatter (Matter State Orbifold hyperbolicData)
open OriginalBRSTWeightPositive (orbifoldConjugation gradeConjugation
  physicalConjugationInFrame physicalHermitianInFrame physicalHermitianInFrame_positive
  physicalHermitianInFrame_conj_symm)
open OriginalOrbifoldBRSTChainReal (stateConjugation stateConjugation_N cycleConjugation
  cohomologyConjugation cohomologyConjugation_mk degreeOneConjugation
  degreeOneConjugation_involutive degreeOneSesquilinear)
open OriginalOrbifoldBRSTQuartetReal (stateConjugation_tmul stateConjugation_mem_fixedMomentum
  shellConjugation shellConjugation_shellH shellConjugation_delta)
open OriginalOrbifoldRealNullFrame (IsRealFrame exists_real_frame)
open OriginalOrbifoldBRSTDescent (relativeBoundaries RelativeCohomology)
open OriginalOrbifoldBRSTPhysicalLie (DegreeOne N)
open OriginalOrbifoldBRSTMomentum (physicalMomentum mem_physicalMomentum_iff)
open OriginalOrbifoldBRSTContravariant (contravariantBPZ)
open OriginalOrbifoldBRSTNoGhostPairing (physicalMomentumEquivOrbifoldGradeInFrame)
open OriginalOrbifoldBRSTPhysicalSpectrum (ghostOneCycleToRelative
  ghostOneCohomologyEquivPhysicalMomentum_apply_mk)
open OriginalOrbifoldRelativeMassShell (relativeMassShell)
open OriginalOrbifoldRelativeQuartet (Frame UCharge orbifoldGrade shellH inclusion groundTensor)
open LatticeLightConeCoordinates.NullFrame (pPlus)
open LatticePositiveEnergy (chargeEnergy)
open LatticeRelativeMassShell (massShellCutoff)
open D5.S3.Quantum.Fermionic.CountableOccupationFock (ket)
open OriginalOrbifoldBRSTGhostBilinear (kappa_ket)
open SourceBPZ.OriginalMatterHermitian (kappaCarrier_single kappaOsc)
open MvPolynomial (monomial)

open private ghostConjugation from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTChainReal
open private delta from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeQuartet
open private correctedTerm correctedCycle correctedCycle_sum correctedCycle_mk from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTNoGhostPairing

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

private abbrev shellGrade := massShellCutoff hyperbolicData

private theorem shellConjugation_inclusion (a : UCharge)
    (ha : chargeEnergy hyperbolicData a ≤ 1) (u : orbifoldGrade (shellGrade a)) :
    shellConjugation a (inclusion a ha u) =
      inclusion a ha (gradeConjugation (shellGrade a) u) := by
  apply Subtype.ext
  change stateConjugation (groundTensor a (u : Orbifold)) =
    groundTensor a (orbifoldConjugation (u : Orbifold))
  change stateConjugation (((u : Orbifold) ⊗ₜ[ℂ]
    Finsupp.single a (monomial 0 1)) ⊗ₜ[ℂ] ket {1}) = _
  rw [stateConjugation_tmul, kappaCarrier_single]
  have hg : ghostConjugation (ket {1}) = ket {1} := kappa_ket _
  rw [hg]
  simp only [kappaOsc, MvPolynomial.map_monomial, map_one]
  rfl

private theorem shellConjugation_correctedPower (F : Frame) (hF : IsRealFrame F)
    (a : UCharge) (r : ℕ) :
    Function.Commute (shellConjugation a) ((-(shellH F a * delta F a)) ^ r) := by
  have hK : Function.Commute (shellConjugation a) (-(shellH F a * delta F a)) := by
    intro x
    simp only [LinearMap.neg_apply, Module.End.mul_apply, map_neg]
    rw [shellConjugation_shellH F hF a (delta F a x), shellConjugation_delta F hF a x]
  induction r with
  | zero => intro x; simp only [pow_zero, Module.End.one_apply]
  | succ r ih =>
      intro x
      simp only [pow_succ, Module.End.mul_apply]
      rw [ih ((-(shellH F a * delta F a)) x), hK x]

/-- Conjugation carries the actual corrected representative to the corrected
representative of the transverse conjugate in the same frame and charge. -/
private theorem correctedCycle_equivariant (F : Frame) (hF : IsRealFrame F) (a : UCharge)
    (hp : F.pPlus a ≠ 0) (ha : chargeEnergy hyperbolicData a ≤ 1)
    (u : orbifoldGrade (shellGrade a)) :
    shellConjugation a (correctedCycle F a hp ha u : relativeMassShell a) =
      (correctedCycle F a hp ha (gradeConjugation (shellGrade a) u) : relativeMassShell a) := by
  simp only [correctedCycle_sum, map_sum]
  apply Finset.sum_congr rfl
  intro r _
  simp only [correctedTerm]
  rw [shellConjugation_correctedPower F hF a r (inclusion a ha u),
    shellConjugation_inclusion a ha u]

private theorem correctedRelative_equivariant (F : Frame) (hF : IsRealFrame F) (a : UCharge)
    (hp : F.pPlus a ≠ 0) (ha : chargeEnergy hyperbolicData a ≤ 1)
    (u : orbifoldGrade (shellGrade a)) :
    cycleConjugation (ghostOneCycleToRelative a (correctedCycle F a hp ha u)) =
      ghostOneCycleToRelative a (correctedCycle F a hp ha (gradeConjugation (shellGrade a) u)) :=
  Subtype.ext (Subtype.ext (congrArg (fun x : relativeMassShell a => (x : State))
    (correctedCycle_equivariant F hF a hp ha u)))

set_option backward.isDefEq.respectTransparency true

private theorem degreeOneConjugation_mem_physicalMomentum (a : UCharge) (x : DegreeOne)
    (hx : x ∈ physicalMomentum a) : degreeOneConjugation x ∈ physicalMomentum a := by
  refine Exists.elim ((mem_physicalMomentum_iff a x).mp hx) ?_
  intro z hz
  apply (mem_physicalMomentum_iff a (degreeOneConjugation x)).mpr
  refine ⟨cycleConjugation z, ?_, stateConjugation_mem_fixedMomentum a _ hz.2.1, ?_⟩
  · change relativeBoundaries.mkQ (cycleConjugation z) =
      cohomologyConjugation (x : RelativeCohomology)
    exact (cohomologyConjugation_mk z).symm.trans
      (congrArg (fun q : RelativeCohomology => cohomologyConjugation q) hz.1)
  · change N (stateConjugation (z.1 : State)) = stateConjugation (z.1 : State)
    exact (stateConjugation_N (z.1 : State)).symm.trans
      (congrArg (fun y : State => stateConjugation y) hz.2.2)

/-- The chain-induced conjugation on the original degree-one momentum space. -/
def physicalChainConjugation (a : UCharge) : physicalMomentum a →ₗ⋆[ℂ] physicalMomentum a :=
  degreeOneConjugation.restrict (degreeOneConjugation_mem_physicalMomentum a)

theorem physicalChainConjugation_involutive (a : UCharge) :
    Function.Involutive (physicalChainConjugation a) :=
  fun x => Subtype.ext (degreeOneConjugation_involutive (x : DegreeOne))

private theorem frameRepresentative_mk (F : Frame) (a : UCharge) (hp : F.pPlus a ≠ 0)
    (ha : chargeEnergy hyperbolicData a ≤ 1) (u : orbifoldGrade (shellGrade a)) :
    (((physicalMomentumEquivOrbifoldGradeInFrame F a hp ha).symm u).1 :
        RelativeCohomology) =
      relativeBoundaries.mkQ (ghostOneCycleToRelative a (correctedCycle F a hp ha u)) := by
  simp only [physicalMomentumEquivOrbifoldGradeInFrame, LinearEquiv.symm_trans_apply,
    LinearEquiv.symm_symm, correctedCycle_mk, ghostOneCohomologyEquivPhysicalMomentum_apply_mk]

/-- Intertwining on the original physical quotient, via the same native cycle on both sides. -/
theorem physicalChainConjugation_inFrame (F : Frame) (hF : IsRealFrame F) (a : UCharge)
    (hp : F.pPlus a ≠ 0) (ha : chargeEnergy hyperbolicData a ≤ 1)
    (u : orbifoldGrade (shellGrade a)) :
    physicalChainConjugation a ((physicalMomentumEquivOrbifoldGradeInFrame F a hp ha).symm u) =
      (physicalMomentumEquivOrbifoldGradeInFrame F a hp ha).symm
        (gradeConjugation (shellGrade a) u) := by
  let e := physicalMomentumEquivOrbifoldGradeInFrame F a hp ha
  let v := gradeConjugation (shellGrade a) u
  apply Subtype.ext
  apply Subtype.ext
  change cohomologyConjugation ((e.symm u).1 : RelativeCohomology) =
    ((e.symm v).1 : RelativeCohomology)
  let mk := relativeBoundaries.mkQ
  let c := ghostOneCycleToRelative a
  calc
    _ = cohomologyConjugation (mk (c (correctedCycle F a hp ha u))) :=
      congrArg (fun q : RelativeCohomology => cohomologyConjugation q)
        (frameRepresentative_mk F a hp ha u)
    _ = mk (cycleConjugation (c (correctedCycle F a hp ha u))) :=
      cohomologyConjugation_mk _
    _ = mk (c (correctedCycle F a hp ha v)) :=
      congrArg (fun z => mk z) (correctedRelative_equivariant F hF a hp ha u)
    _ = _ := (frameRepresentative_mk F a hp ha v).symm

theorem physicalChainConjugation_eq_inFrame (F : Frame) (hF : IsRealFrame F) (a : UCharge)
    (hp : F.pPlus a ≠ 0) (ha : chargeEnergy hyperbolicData a ≤ 1) :
    physicalChainConjugation a = physicalConjugationInFrame F a hp ha := by
  apply LinearMap.ext
  intro x
  let e := physicalMomentumEquivOrbifoldGradeInFrame F a hp ha
  change physicalChainConjugation a x = e.symm (gradeConjugation (shellGrade a) (e x))
  exact (congrArg (fun y : physicalMomentum a => physicalChainConjugation a y)
    (e.symm_apply_apply x).symm).trans (physicalChainConjugation_inFrame F hF a hp ha (e x))

/-- The canonical form uses the native chain conjugation and the native
contravariant BPZ form on degree-one cohomology. -/
def canonicalPhysicalHermitian (a : UCharge) :
    physicalMomentum a →ₗ⋆[ℂ] physicalMomentum a →ₗ[ℂ] ℂ :=
  (degreeOneSesquilinear.comp (physicalMomentum a).subtype).compl₂ (physicalMomentum a).subtype

theorem canonicalPhysicalHermitian_eq_inFrame (F : Frame) (hF : IsRealFrame F) (a : UCharge)
    (hp : F.pPlus a ≠ 0) (ha : chargeEnergy hyperbolicData a ≤ 1) :
    canonicalPhysicalHermitian a = physicalHermitianInFrame F a hp ha := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change contravariantBPZ (physicalChainConjugation a x).val y.val =
    contravariantBPZ (physicalConjugationInFrame F a hp ha x).val y.val
  exact congrArg (fun k : physicalMomentum a →ₗ⋆[ℂ] physicalMomentum a =>
    contravariantBPZ (k x).val y.val) (physicalChainConjugation_eq_inFrame F hF a hp ha)

/-- A real normalized frame identifies the intrinsic quotient form with the
known positive transverse form at every nonzero on-shell charge. -/
theorem canonicalPhysicalHermitian_exists_real_frame (a : UCharge) (ha0 : a ≠ 0)
    (ha : chargeEnergy hyperbolicData a ≤ 1) :
    ∃ (F : Frame) (hp : F.pPlus a ≠ 0), IsRealFrame F ∧
      canonicalPhysicalHermitian a = physicalHermitianInFrame F a hp ha := by
  refine Exists.elim (exists_real_frame a ha0) ?_
  intro F hF
  exact ⟨F, hF.2, hF.1, canonicalPhysicalHermitian_eq_inFrame F hF.1 a hF.2 ha⟩

theorem canonicalPhysicalHermitian_conj_symm (a : UCharge) (ha0 : a ≠ 0)
    (ha : chargeEnergy hyperbolicData a ≤ 1) (x y : physicalMomentum a) :
    star (canonicalPhysicalHermitian a x y) = canonicalPhysicalHermitian a y x := by
  refine Exists.elim (exists_real_frame a ha0) ?_
  intro F hF
  have hEq := canonicalPhysicalHermitian_eq_inFrame F hF.1 a hF.2 ha
  calc
    _ = star (physicalHermitianInFrame F a hF.2 ha x y) :=
      congrArg (fun H => star (H x y)) hEq
    _ = physicalHermitianInFrame F a hF.2 ha y x :=
      physicalHermitianInFrame_conj_symm F a hF.2 ha x y
    _ = _ := congrArg (fun H => H y x) hEq.symm

theorem canonicalPhysicalHermitian_positive (a : UCharge) (ha0 : a ≠ 0)
    (ha : chargeEnergy hyperbolicData a ≤ 1) (x : physicalMomentum a) (hx : x ≠ 0) :
    (canonicalPhysicalHermitian a x x).im = 0 ∧ 0 < (canonicalPhysicalHermitian a x x).re := by
  refine Exists.elim (exists_real_frame a ha0) ?_
  intro F hF
  have hxx : canonicalPhysicalHermitian a x x = physicalHermitianInFrame F a hF.2 ha x x :=
    congrArg (fun H => H x x) (canonicalPhysicalHermitian_eq_inFrame F hF.1 a hF.2 ha)
  have hpos := physicalHermitianInFrame_positive F a hF.2 ha x hx
  exact ⟨(congrArg Complex.im hxx).trans hpos.1,
    hpos.2.trans_eq (congrArg Complex.re hxx.symm)⟩

#print axioms correctedCycle_equivariant
#print axioms correctedRelative_equivariant
#print axioms physicalChainConjugation_eq_inFrame
#print axioms canonicalPhysicalHermitian_eq_inFrame
#print axioms canonicalPhysicalHermitian_exists_real_frame
#print axioms canonicalPhysicalHermitian_conj_symm
#print axioms canonicalPhysicalHermitian_positive

end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTPhysicalReal
