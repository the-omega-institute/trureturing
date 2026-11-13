import D5.S3.Geometry.AffineBallRigidity
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The exact nested-ball telescope with an actual extreme-point observation. -/

noncomputable section
open Set Metric
universe e v f

namespace Reg.D5.S3.Geometry.AffineBallRigidity

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  E : Type e
  V : Type v
  [eadd : NormedAddCommGroup E]
  [espace : NormedSpace ℝ E]
  [efinite : FiniteDimensional ℝ E]
  [vadd : NormedAddCommGroup V]
  [vspace : NormedSpace ℝ V]
  body : Set V
  c : V
  d : V
  A : E →L[ℝ] V
  B : E →L[ℝ] V

attribute [instance] Inputs.eadd Inputs.espace Inputs.efinite Inputs.vadd Inputs.vspace

abbrev signature : Signature where
  Params := Inputs.{e,v}
  State P := P.E
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{e,v} :=
  realize signature (fun _ P x => P.c + P.A x ∈ P.body.extremePoints ℝ)
    (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature.{e,v}
  Law O := ∀ P : Inputs.{e,v},
    Function.Injective P.A → Function.Injective P.B →
    (fun x => P.c + P.A x) '' closedBall 0 1 ⊆
      (fun x => P.d + P.B x) '' closedBall 0 1 →
    (fun x => P.d + P.B x) '' closedBall 0 1 ⊆ P.body →
    (∀ x, ‖x‖ = 1 → O.readout () P x) →
    (fun x => P.c + P.A x) '' closedBall 0 1 =
      (fun x => P.d + P.B x) '' closedBall 0 1

abbrev sourceScope : Prop := type_of%
  (@_root_.D5.S3.Geometry.AffineBallRigidity.eq_of_subset_of_extreme_sphere.{e,v})

theorem source_bridge : sourceScope.{e,v} ↔ arena.{e,v}.Law actual.{e,v} := by
  constructor
  · intro h P
    exact @h P.E P.V P.eadd P.espace P.efinite P.vadd P.vspace P.body P.c P.d P.A P.B
  · intro h E V eadd espace efinite vadd vspace K c d A B
    exact h (@Inputs.mk E V eadd espace efinite vadd vspace K c d A B)

theorem actual_positive : arena.{e,v}.Law actual.{e,v} :=
  source_bridge.mp
    (@_root_.D5.S3.Geometry.AffineBallRigidity.eq_of_subset_of_extreme_sphere.{e,v})

structure CenterInputs where
  E : Type e
  V : Type v
  F : Type f
  [eadd : NormedAddCommGroup E]
  [espace : NormedSpace ℝ E]
  [efinite : FiniteDimensional ℝ E]
  [vadd : NormedAddCommGroup V]
  [vspace : NormedSpace ℝ V]
  [fadd : NormedAddCommGroup F]
  [fspace : NormedSpace ℝ F]
  c : V
  d : V
  A : E →L[ℝ] V
  B : F →L[ℝ] V

attribute [instance] CenterInputs.eadd CenterInputs.espace CenterInputs.efinite
  CenterInputs.vadd CenterInputs.vspace CenterInputs.fadd CenterInputs.fspace

abbrev centerSignature : Signature where
  Params := CenterInputs.{e,v,f}
  State P := P.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := P.V
  Anchor := Empty
  finiteAnchor := inferInstance

def centerActual : Realization centerSignature.{e,v,f} :=
  realize centerSignature (fun _ _ x => x) (fun a => nomatch a)

abbrev centerArena : Arena where
  signature := centerSignature.{e,v,f}
  Law O := ∀ P : CenterInputs.{e,v,f},
    (fun x => P.c + P.A x) '' closedBall 0 1 =
      (fun x => P.d + P.B x) '' closedBall 0 1 → O.readout () P P.c = P.d

abbrev centerSourceScope : Prop := type_of%
  (@_root_.D5.S3.Geometry.AffineBallRigidity.center_eq_of_ball_eq.{e,v,f})

theorem center_source_bridge : centerSourceScope.{e,v,f} ↔
    centerArena.{e,v,f}.Law centerActual.{e,v,f} := by
  constructor
  · intro h P
    exact @h P.E P.V P.eadd P.espace P.efinite P.vadd P.vspace
      P.F P.fadd P.fspace P.c P.d P.A P.B
  · intro h E V eadd espace efinite vadd vspace F fadd fspace c d A B
    exact h (@CenterInputs.mk E V F eadd espace efinite vadd vspace fadd fspace c d A B)

theorem center_actual_positive : centerArena.{e,v,f}.Law centerActual.{e,v,f} :=
  center_source_bridge.mp
    (@_root_.D5.S3.Geometry.AffineBallRigidity.center_eq_of_ball_eq.{e,v,f})

end Reg.D5.S3.Geometry.AffineBallRigidity
