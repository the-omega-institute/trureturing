/- GID: D5/S3/VertexAlgebra/RelativePairing/RealPhysicalNoGhost
   generality: G
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   Literature status: integration of the original algebraic no-ghost chain;
   parameter packaging and applications claim no independent mathematical novelty.
   Source admission is independent of the kernel conclusions. -/

import D5.S3.VertexAlgebra.RelativePairing.NativePhysicalNoGhost
import D5.S3.VertexAlgebra.TransverseMetric.RealAdaptedFrame

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.RelativePairing.RealPhysicalNoGhost

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge
  OriginalQQuartetSource OriginalQPhysicalPairing OriginalQEnergyInclusionPairing
  NativePhysicalRealization NativeTransverseCoordinates TransverseMetric.RealAdaptedFrame
  LatticeBcGhostHermitianForm LatticeOscillatorFockForm LatticeOscillatorFockMetric

noncomputable section

structure AdmissibleFrame (D : LatticeData) (beta : Charge D) where
  frame : Matrix (Fin D.rank) (Fin D.rank) ℂ
  inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ
  leftFrame : inverse * frame = 1
  rightFrame : frame * inverse = 1
  direction : Fin D.rank → ℂ
  xAxis : Fin D.rank
  yAxis : Fin D.rank
  null : gramPair D direction direction = 0
  nonzero : chosenP D beta direction ≠ 0
  distinct : xAxis ≠ yAxis
  xRow : frame xAxis = direction
  yRow : frame yAxis = adaptedPartner D beta direction
  xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0
  yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0

def admissibleOfNative (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (beta : Charge D) (native : NativeFrame D H beta) : AdmissibleFrame D beta where
  frame := native.rows.map Complex.ofReal
  inverse := native.inverseRows.map Complex.ofReal
  leftFrame := native.leftComplexInverse
  rightFrame := native.rightComplexInverse
  direction := embed D native.direction
  xAxis := native.xAxis
  yAxis := native.yAxis
  null := native.null
  nonzero := native.chosenNonzero
  distinct := native.distinct
  xRow := by
    change embed D (native.rows native.xAxis) = embed D native.direction
    rw [native.xRow]
  yRow := native.yRow
  xDual := native.xComplexDual
  yDual := native.yComplexDual

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (leftGram : H * gramComplex D = 1) (rightGram : gramComplex D * H = 1)
  (beta : Charge D) (level : ℤ) (critical : D.rank = 26)
  (shell : chosenH D beta + (level : ℂ) - 1 = 0)

def frameForm (choice : AdmissibleFrame D beta) : physicalImage D H beta level →ₗ⋆[ℂ]
    physicalImage D H beta level →ₗ[ℂ] ℂ :=
  imageForm D H beta level choice.frame choice.inverse leftGram rightGram
    choice.leftFrame choice.rightFrame choice.direction choice.xAxis choice.yAxis critical
    choice.null choice.nonzero choice.distinct choice.xRow choice.yRow choice.xDual
    choice.yDual shell

theorem imageRepresentative_surjective :
    Function.Surjective (imageRepresentative D H beta level) := by
  intro state
  obtain ⟨quotient, equality⟩ := state.property
  induction quotient using Submodule.Quotient.induction_on with
  | _ representative =>
    refine ⟨representative, ?_⟩
    apply Subtype.ext
    exact equality

theorem frameForm_recovery (choice : AdmissibleFrame D beta)
    (first second : physicalCycles D H beta level) :
    frameForm D H leftGram rightGram beta level critical shell choice
      (imageRepresentative D H beta level first) (imageRepresentative D H beta level second) =
    F D (physicalState D H beta level first) (C D 0 (physicalState D H beta level second)) :=
  imageForm_recovery D H beta level choice.frame choice.inverse leftGram rightGram
    choice.leftFrame choice.rightFrame choice.direction choice.xAxis choice.yAxis critical
    choice.null choice.nonzero choice.distinct choice.xRow choice.yRow choice.xDual
    choice.yDual shell
    first second

theorem imageForm_frame_independent (firstFrame secondFrame : AdmissibleFrame D beta) :
    frameForm D H leftGram rightGram beta level critical shell firstFrame =
      frameForm D H leftGram rightGram beta level critical shell secondFrame := by
  apply LinearMap.ext
  intro first
  apply LinearMap.ext
  intro second
  obtain ⟨firstRepresentative, firstEquality⟩ := imageRepresentative_surjective D H beta level first
  obtain ⟨secondRepresentative, secondEquality⟩ :=
    imageRepresentative_surjective D H beta level second
  rw [← firstEquality, ← secondEquality,
    frameForm_recovery D H leftGram rightGram beta level critical shell firstFrame,
    frameForm_recovery D H leftGram rightGram beta level critical shell secondFrame]

variable (chargeNonzero : beta ≠ 0)
  (lorentzian : QuadraticForms.ActualSignature.signature (gramReal D).toQuadraticForm' =
    (D.rank : ℤ) - 2)

def constructedFrame : NativeFrame D H beta :=
  Classical.choice (exists_native_frame D H leftGram rightGram (by omega)
    beta chargeNonzero lorentzian)

def canonicalForm : physicalImage D H beta level →ₗ⋆[ℂ]
    physicalImage D H beta level →ₗ[ℂ] ℂ :=
  frameForm D H leftGram rightGram beta level critical shell
    (admissibleOfNative D H beta
      (constructedFrame D H leftGram rightGram beta critical chargeNonzero lorentzian))

local notation "intrinsicForm" => canonicalForm D H leftGram rightGram beta level critical shell
  chargeNonzero lorentzian

theorem canonicalForm_eq (choice : AdmissibleFrame D beta) :
    intrinsicForm = frameForm D H leftGram rightGram beta level critical shell choice :=
  imageForm_frame_independent D H leftGram rightGram beta level critical shell _ choice

theorem canonicalForm_recovery (first second : physicalCycles D H beta level) :
    intrinsicForm (imageRepresentative D H beta level first)
      (imageRepresentative D H beta level second) =
    F D (physicalState D H beta level first) (C D 0 (physicalState D H beta level second)) :=
  frameForm_recovery D H leftGram rightGram beta level critical shell _ first second

def canonicalExtraction : physicalImage D H beta level →ₗ[ℂ]
    TransverseDownIndex D
      (constructedFrame D H leftGram rightGram beta critical chargeNonzero lorentzian).xAxis
      (constructedFrame D H leftGram rightGram beta critical chargeNonzero lorentzian).yAxis
      level →₀ ℂ :=
  let choice := admissibleOfNative D H beta
    (constructedFrame D H leftGram rightGram beta critical chargeNonzero lorentzian)
  imageProjection D H choice.frame choice.inverse leftGram rightGram
    choice.leftFrame choice.rightFrame
    beta choice.direction choice.xAxis choice.yAxis level critical choice.null choice.nonzero
    choice.distinct choice.xRow choice.yRow choice.xDual choice.yDual shell

def canonicalOscillator : physicalImage D H beta level → Oscillator D :=
  let native := constructedFrame D H leftGram rightGram beta critical chargeNonzero lorentzian
  fun state => transverseDownOscillator D (native.rows.map Complex.ofReal)
    native.xAxis native.yAxis level
    (canonicalExtraction D H leftGram rightGram beta level critical shell
      chargeNonzero lorentzian state)

theorem canonicalForm_projection (first second : physicalImage D H beta level) :
    intrinsicForm first second = -fockForm D
      (canonicalOscillator D H leftGram rightGram beta level critical shell
        chargeNonzero lorentzian first)
      (canonicalOscillator D H leftGram rightGram beta level critical shell
        chargeNonzero lorentzian second) := by
  let native := constructedFrame D H leftGram rightGram beta critical chargeNonzero lorentzian
  let choice := admissibleOfNative D H beta native
  exact NativePhysicalNoGhost.imageForm_projection D H choice.frame choice.inverse
    leftGram rightGram choice.leftFrame choice.rightFrame beta choice.direction
    choice.xAxis choice.yAxis level critical choice.null choice.nonzero choice.distinct
    choice.xRow choice.yRow choice.xDual choice.yDual shell
    native.starFixed first second

theorem canonicalForm_noGhost :
    (∀ state : physicalImage D H beta level, state ≠ 0 →
      0 < (-intrinsicForm state state).re ∧ (-intrinsicForm state state).im = 0) ∧
    (∀ state : physicalImage D H beta level,
      (∀ other, intrinsicForm state other = 0) ↔ state = 0) ∧
    (∀ state : physicalImage D H beta level,
      (∀ other, intrinsicForm other state = 0) ↔ state = 0) := by
  let native := constructedFrame D H leftGram rightGram beta critical chargeNonzero lorentzian
  let choice := admissibleOfNative D H beta native
  exact NativePhysicalNoGhost.imageForm_noGhost D H choice.frame choice.inverse leftGram rightGram
    choice.leftFrame choice.rightFrame beta choice.direction choice.xAxis choice.yAxis level
    critical choice.null choice.nonzero choice.distinct choice.xRow choice.yRow
    choice.xDual choice.yDual shell
    native.starFixed lorentzian

theorem canonicalForm_radicals_bot :
    LinearMap.ker intrinsicForm = ⊥ ∧
      (⨅ other : physicalImage D H beta level, LinearMap.ker (intrinsicForm other)) = ⊥ := by
  have noGhost := canonicalForm_noGhost D H leftGram rightGram beta level critical shell
    chargeNonzero lorentzian
  constructor
  · apply (Submodule.eq_bot_iff _).mpr
    intro state member
    apply (noGhost.2.1 state).mp
    intro other
    exact LinearMap.congr_fun (show intrinsicForm state = 0 from member) other
  · apply (Submodule.eq_bot_iff _).mpr
    intro state member
    apply (noGhost.2.2 state).mp
    intro other
    exact (Submodule.mem_iInf _).mp member other

theorem original_imageForm_noGhost : ∀ choice : AdmissibleFrame D beta,
    (∀ first second : physicalCycles D H beta level,
      frameForm D H leftGram rightGram beta level critical shell choice
        (imageRepresentative D H beta level first) (imageRepresentative D H beta level second) =
      F D (physicalState D H beta level first) (C D 0 (physicalState D H beta level second))) ∧
    (∀ first second : physicalImage D H beta level,
      frameForm D H leftGram rightGram beta level critical shell choice first second = -fockForm D
        (canonicalOscillator D H leftGram rightGram beta level critical shell
          chargeNonzero lorentzian first)
        (canonicalOscillator D H leftGram rightGram beta level critical shell
          chargeNonzero lorentzian second)) ∧
    (∀ state : physicalImage D H beta level, state ≠ 0 →
      0 < (-frameForm D H leftGram rightGram beta level critical shell choice state state).re ∧
      (-frameForm D H leftGram rightGram beta level critical shell choice state state).im = 0) ∧
    LinearMap.ker (frameForm D H leftGram rightGram beta level critical shell choice) = ⊥ ∧
    (⨅ other : physicalImage D H beta level,
      LinearMap.ker (frameForm D H leftGram rightGram beta level critical shell choice other)) = ⊥ := by
  intro choice
  rw [← canonicalForm_eq D H leftGram rightGram beta level critical shell
    chargeNonzero lorentzian choice]
  exact ⟨canonicalForm_recovery D H leftGram rightGram beta level critical shell
      chargeNonzero lorentzian,
    canonicalForm_projection D H leftGram rightGram beta level critical shell
      chargeNonzero lorentzian,
    (canonicalForm_noGhost D H leftGram rightGram beta level critical shell
      chargeNonzero lorentzian).1,
    canonicalForm_radicals_bot D H leftGram rightGram beta level critical shell
      chargeNonzero lorentzian⟩

#print axioms imageForm_frame_independent
#print axioms canonicalForm_eq
#print axioms canonicalForm_recovery
#print axioms canonicalForm_projection
#print axioms canonicalForm_noGhost
#print axioms canonicalForm_radicals_bot
#print axioms original_imageForm_noGhost

end
end D5.S3.VertexAlgebra.RelativePairing.RealPhysicalNoGhost
