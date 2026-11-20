import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.AURICOmega.CapCausalOrder
import Reg.Support.SingleDependentReadout

/-! The audit of the cap correspondence observes the hyperboloid point `deSitterPoint n a` as a
function of the centre and radius `(n, a)`, in the bijection clause. -/

noncomputable section
open scoped InnerProductSpace Quaternion
open _root_.D5.S3.Quantum.AURICOmega.CapCausalOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

namespace Reg.D5.S3.Quantum.AURICOmega.CapCausalOrder

/-- No parameter; the state is a centre and a radius, the output a point of `ℝ × ℍ`. -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => unitary ℍ[ℝ] × ℝ) (fun _ => ℝ × ℍ[ℝ])

def actual : Realization signature :=
  realize signature (fun _ _ na => deSitterPoint na.1 na.2) (fun e => nomatch e)

/-- The constant map to the origin of `ℝ × ℍ`. -/
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0, 0)) (fun e => nomatch e)

/-- The complete statement of `cap_causal_order` with the point map of the bijection clause
replaced by the readout. -/
abbrev arena : Arena where
  signature := signature
  Law R := Set.BijOn (fun na : unitary ℍ[ℝ] × ℝ => R.readout () () na)
        {na | na.2 ∈ Set.Ioo 0 Real.pi} {ξ | ‖ξ.2‖ ^ 2 - ξ.1 ^ 2 = 1} ∧
    (∀ n n' : unitary ℍ[ℝ], ∀ a a' : ℝ, a ∈ Set.Ioo 0 Real.pi → a' ∈ Set.Ioo 0 Real.pi →
      (cap n a = cap n' a' ↔ n = n' ∧ a = a')) ∧
    ∀ n n' : unitary ℍ[ℝ], ∀ a a' : ℝ, a ∈ Set.Ioo 0 Real.pi → a' ∈ Set.Ioo 0 Real.pi →
      (cap n a ⊆ cap n' a' ↔
        (deSitterPoint n a).1 ≤ (deSitterPoint n' a').1 ∧
          ‖(deSitterPoint n' a').2 - (deSitterPoint n a).2‖ ^ 2 ≤
            ((deSitterPoint n' a').1 - (deSitterPoint n a).1) ^ 2)

private theorem half_pi_mem : Real.pi / 2 ∈ Set.Ioo 0 Real.pi :=
  ⟨by positivity, by linarith [Real.pi_pos]⟩

/-- The origin of `ℝ × ℍ` does not lie on the hyperboloid. -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h1 := h.1.mapsTo (x := ((1 : unitary ℍ[ℝ]), Real.pi / 2)) half_pi_mem
  simp [rejected, realize] at h1

/-- The radii `π / 2` and `π / 4` at the centre `1` give the time coordinates `0` and `-1`. -/
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), ((1 : unitary ℍ[ℝ]), Real.pi / 2), ((1 : unitary ℍ[ℝ]), Real.pi / 4), ?_⟩
  intro he
  have h1 := congrArg Prod.fst he
  change -(Real.cos (Real.pi / 2) / Real.sin (Real.pi / 2)) =
    -(Real.cos (Real.pi / 4) / Real.sin (Real.pi / 4)) at h1
  have hs : Real.sqrt 2 / 2 ≠ 0 := by positivity
  rw [Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_pi_div_four, Real.sin_pi_div_four,
    div_self hs] at h1
  norm_num at h1

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @cap_causal_order

def family : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cap_causal_order, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    cap_causal_order (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.AURICOmega.CapCausalOrder.cap_causal_order_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.CapCausalOrder.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ na => deSitterPoint na.1 na.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.CapCausalOrder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn", "fn", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.AURICOmega.CapCausalOrder
