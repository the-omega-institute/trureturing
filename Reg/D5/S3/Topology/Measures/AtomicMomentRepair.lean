import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Topology.Measures.AtomicMomentRepair
import Reg.Support.SingleDependentReadout

/-! Escape registration for the absolute correction budget. -/

open Set Filter LeanInformationAudit
open _root_.D5.S3.Topology.Measures.AtomicMomentRepair
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators Topology

namespace Reg.D5.S3.Topology.Measures.AtomicMomentRepair

noncomputable section

abbrev signature := _root_.Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ cost budget => cost < budget) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have heq := congrFun h 1
  have h01 : (0 : ℝ) < 1 := zero_lt_one
  have h11 : (1 : ℝ) < 1 := Eq.mp heq h01
  exact (lt_irrefl _) h11

abbrev repairArena : Arena where
  signature := signature
  Law R := ∀ (moment : ℝ → Fin 5 → ℝ),
    ContinuousWithinAt moment (Ioc 0 1) 0 →
    ∀ (basisNode : Fin 5 → Ioc (0 : ℝ) 1)
      (basis : Module.Basis (Fin 5) ℝ (Fin 5 → ℝ)),
    (∀ j, basis j = moment (basisNode j)) →
    ∀ (weight : ℝ) {ε : ℝ}, 0 < ε →
    ∃ (x : Ioc (0 : ℝ) 1) (correction : Fin 5 → ℝ),
      weight • moment x + (∑ j, correction j • moment (basisNode j)) =
        weight • moment 0 ∧ R.readout () () (∑ j, |correction j|) ε

private theorem repair_rejected : ¬ repairArena.Law rejected := by
  intro h
  let cutoff (i : Fin 5) : ℝ := ((i.val : ℝ) + 1) / 5
  have hLower (i : Fin 5) : (1 : ℝ) / 5 ≤ cutoff i := by
    have hi : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _
    dsimp [cutoff]
    linarith
  let node (i : Fin 5) : Ioc (0 : ℝ) 1 :=
    ⟨cutoff i, lt_of_lt_of_le (by norm_num) (hLower i), by
      have hiNat : i.val ≤ 4 := Nat.le_of_lt_succ i.isLt
      have hi : (i.val : ℝ) ≤ 4 := by exact_mod_cast hiNat
      dsimp [cutoff]
      linarith⟩
  have hInjective : Function.Injective cutoff := by
    intro i j hij
    have hc : (i.val : ℝ) = (j.val : ℝ) := by
      dsimp [cutoff] at hij
      linarith
    exact Fin.ext (by exact_mod_cast hc)
  let moment (x : ℝ) (i : Fin 5) : ℝ := if cutoff i = x then 1 else 0
  have hNear : ∀ᶠ x in 𝓝 (0 : ℝ), x < (1 : ℝ) / 5 := Iio_mem_nhds (by norm_num)
  have hContinuous : ContinuousAt moment 0 := by
    refine (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : Fin 5 → ℝ)) 0).congr ?_
    filter_upwards [hNear] with x hx
    funext i
    simp [moment, ne_of_gt (lt_of_lt_of_le hx (hLower i))]
  have hBasis (j : Fin 5) : Pi.basisFun ℝ (Fin 5) j = moment (node j) := by
    funext i
    simp [Pi.basisFun_apply, Pi.single_apply, moment, node, hInjective.eq_iff]
  obtain ⟨_, _, _, bad⟩ := h moment hContinuous.continuousWithinAt node
    (Pi.basisFun ℝ (Fin 5)) hBasis (-1) (ε := 1) zero_lt_one
  exact bad

def repairFamily : Registration repairArena (type_of% @exists_exact_moment_repair) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_exact_moment_repair, rejected, repair_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    repairArena.Law actual rejected repair_rejected
  dependence := dependence

def repairAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_exact_moment_repair) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.Topology.Measures.AtomicMomentRepair.exists_exact_moment_repair
    "__information_unit"
  realizationName := `Reg.D5.S3.Topology.Measures.AtomicMomentRepair.repairFamily
  realizationSource := none
  generated := false
  arena := .source ⟨repairArena⟩
  objectArena := .source ⟨repairArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source repairArena ⟨repairFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ cost budget => cost < budget) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Topology.Measures.AtomicMomentRepair
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Topology.Measures.AtomicMomentRepair
