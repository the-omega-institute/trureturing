import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.FourVectorSignSumBound
import Reg.Support.DependentFamily

open _root_.D5.S3.Geometry.FourVectorSignSumBound
open _root_.D5.S3.Combinatorics.IsingUniquenessSets (sgn)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Reg.D5.S3.Geometry.FourVectorSignSumBound
universe u
abbrev Vec := EuclideanSpace ℝ (Fin 3)

abbrev signature : Signature where
  Params := Unit
  State _ := Fin 4 → Vec
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => maxNorm x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ x : Fin 4 → Vec, (∑ i, ‖x i‖) ≤ (Real.sqrt 13 / 2) * R.readout () () x

theorem positive : arena.Law actual := four_vector_inequality
theorem negative : ¬ arena.Law rejected := by
  intro h
  have hh := h (fun _ => 0)
  have hp : 0 < Real.sqrt 13 := Real.sqrt_pos.mpr (by norm_num)
  simp only [norm_zero, Finset.sum_const_zero] at hh
  change 0 ≤ (Real.sqrt 13 / 2) * (-1) at hh
  nlinarith

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun _ => !₂[1,0,0]), ?_⟩
  have hz : maxNorm (fun _ : Fin 4 => (0 : Vec)) = 0 := by
    simp [maxNorm, signedSum]
  have hp := signedSum_le_max (fun _ : Fin 4 => (!₂[1,0,0] : Vec)) (fun _ => true)
  intro he
  have hm : maxNorm (fun _ : Fin 4 => (!₂[1,0,0] : Vec)) = 0 := by
    simpa [actual, realize, hz] using he.symm
  rw [hm] at hp
  have hs : signedSum (fun _ : Fin 4 => (!₂[1,0,0] : Vec)) (fun _ => true) =
      !₂[4,0,0] := by ext j; fin_cases j <;> norm_num [signedSum, sgn, Fin.sum_univ_succ]
  rw [hs] at hp
  have hn := norm_eq_zero.mp (le_antisymm hp (norm_nonneg _))
  have hc := congrArg (fun a : Vec => a 0) hn
  norm_num at hc

def evidence : Registration arena
    (type_of% (@_root_.D5.S3.Geometry.FourVectorSignSumBound.four_vector_inequality)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, negative⟩,
    fun i => nomatch i⟩
  dependence := dependence

abbrev orderSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def orderActual : Realization orderSignature :=
  realize orderSignature (fun _ _ a b => a ≤ b) (fun e => nomatch e)
def orderRejected : Realization orderSignature :=
  realize orderSignature (fun _ _ _ _ => False) (fun e => nomatch e)
@[reducible] def orderArena : Arena where
  signature := orderSignature
  Law R := ∀ x : Fin 4 → Vec,
    R.readout () () (∑ i, ‖x i‖) ((Real.sqrt 13 / 2) * maxNorm x)

theorem orderPositive : orderArena.Law orderActual := four_vector_inequality

theorem orderNegative : ¬ orderArena.Law orderRejected := by
  intro h
  exact h (fun _ => 0)

theorem orderDependence : ObservationalDependence orderSignature orderActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  change ((0 : ℝ) ≤ 0) = ((1 : ℝ) ≤ 0) at he
  have hz : (0 : ℝ) ≤ 0 := le_rfl
  have hn : (1 : ℝ) ≤ 0 := he ▸ hz
  norm_num at hn

def orderEvidence : Registration orderArena
    (type_of% (@_root_.D5.S3.Geometry.FourVectorSignSumBound.four_vector_inequality)) where
  actual := orderActual
  bridge := Iff.rfl
  variation := ⟨orderPositive, orderRejected, orderNegative⟩
  sensitivity := ⟨fun i => ⟨orderRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, orderNegative⟩,
    fun i => nomatch i⟩
  dependence := orderDependence

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Geometry.FourVectorSignSumBound.four_vector_inequality)
    (type_of% (realize orderSignature (fun _ _ a b => a ≤ b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Geometry.FourVectorSignSumBound.four_vector_inequality
    "Reg.D5.S3.Geometry.FourVectorSignSumBound/Reg.D5.S3.Geometry.FourVectorSignSumBound.arena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Geometry.FourVectorSignSumBound.orderEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨orderArena⟩,
  objectArena := .source ⟨orderArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source orderArena ⟨orderEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize orderSignature (fun _ _ a b => a ≤ b) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Geometry.FourVectorSignSumBound, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "fn", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms registration

/-- The comparison observation retains the complete source law, including trivial spaces. -/
@[reducible] def signedArena : Arena where
  signature := orderSignature
  Law R := ∀ {E : Type u} [n : NormedAddCommGroup E] [h : InnerProductSpace ℝ E]
    (x : Fin 4 → E) (ε : Fin 4 → Bool),
    R.readout () () (‖signedSum x ε‖) (maxNorm x)

theorem signedPositive : signedArena.{u}.Law orderActual := @signedSum_le_max.{u}

theorem signedNegative : ¬ signedArena.{u}.Law orderRejected := by
  intro h
  exact h (E := EuclideanSpace ℝ (ULift.{u} Unit)) (fun _ => 0) (fun _ => true)

/-- Dependence concerns the comparison function on real states, not each source space. -/
def signedEvidence : Registration signedArena.{u}
    (type_of% (@_root_.D5.S3.Geometry.FourVectorSignSumBound.signedSum_le_max.{u})) where
  actual := orderActual
  bridge := Iff.rfl
  variation := ⟨signedPositive, orderRejected, signedNegative⟩
  sensitivity := ⟨fun i => ⟨orderRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, signedNegative⟩,
    fun i => nomatch i⟩
  dependence := orderDependence

noncomputable def signedRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Geometry.FourVectorSignSumBound.signedSum_le_max.{u})
    (type_of% (realize orderSignature (fun _ _ a b => a ≤ b) (fun e => nomatch e))) Unit Unit := {
  unitName := Lean.Name.str (Lean.Name.str `D5.S3.Geometry.FourVectorSignSumBound.signedSum_le_max
    "Reg.D5.S3.Geometry.FourVectorSignSumBound/Reg.D5.S3.Geometry.FourVectorSignSumBound.signedArena/[anonymous]") "__information_unit",
  realizationName := `Reg.D5.S3.Geometry.FourVectorSignSumBound.signedEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨signedArena.{u}⟩,
  objectArena := .source ⟨signedArena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source signedArena.{u} ⟨signedEvidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize orderSignature (fun _ _ a b => a ≤ b) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Geometry.FourVectorSignSumBound, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms signedRegistration

end Reg.D5.S3.Geometry.FourVectorSignSumBound
