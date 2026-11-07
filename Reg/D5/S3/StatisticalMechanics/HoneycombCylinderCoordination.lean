import D5.S3.StatisticalMechanics.HoneycombCylinderCoordination
import D5.S3.StatisticalMechanics.TeaCoordinationSequence
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! The entire coordination sequence is observed at each cylinder width. The horizontal radii
in the source graph metric are TeaCoordinationSequence.residual at (p,q) = (0,0) and (0,1). -/

namespace Reg.D5.S3.StatisticalMechanics.HoneycombCylinderCoordination

open _root_.D5.S3.StatisticalMechanics.HoneycombCylinderCoordination
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => c n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n m => c n m + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 1 ≤ n →
    (1-X)^2 * (PowerSeries.mk fun m => (R.readout () () n m : ℤ)) =
      (1-X)*(1+2*X-C ((n : ℤ)-2)*X^(2*n)-C ((n : ℤ)-1)*X^(2*n+1)) +
        3*X^2*(1-X^(2*n-2))

private theorem initial_values : c 1 0 = 1 ∧ c 1 2 = 4 ∧ c 2 2 = 6 := by
  have h₁₀ := congrArg PowerSeries.constantCoeff (result 1 (by omega))
  have h₁₁ := congrArg (PowerSeries.coeff 1) (result 1 (by omega))
  have h₁₂ := congrArg (PowerSeries.coeff 2) (result 1 (by omega))
  have h₂₀ := congrArg PowerSeries.constantCoeff (result 2 (by omega))
  have h₂₁ := congrArg (PowerSeries.coeff 1) (result 2 (by omega))
  have h₂₂ := congrArg (PowerSeries.coeff 2) (result 2 (by omega))
  norm_num at h₁₀ h₂₀
  norm_num [PowerSeries.coeff_mul, PowerSeries.coeff_mk, PowerSeries.coeff_X,
    Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, pow_two] at h₁₁ h₁₂ h₂₁ h₂₂
  omega

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := congrArg PowerSeries.constantCoeff (h 1 (by omega))
  have ha := initial_values.1
  norm_num [rejected, realize] at hb
  omega

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    change c 1 ≠ c 2
    intro h
    have he := congrFun h 2
    rw [initial_values.2.1, initial_values.2.2] at he
    omega

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.HoneycombCylinderCoordination.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.HoneycombCylinderCoordination.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => c n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.HoneycombCylinderCoordination
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "arg", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

namespace PlaneGeodesic
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Vertex) (fun _ => ℕ)
def actual : Realization signature := realize signature (fun _ _ v => potential v) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ v, ∃ p : honeycombGraph.Walk (false, 0, 0) v,
    p.length = R.readout () () v
private theorem bad : ¬ arena.Law rejected := by
  intro h
  obtain ⟨p, hp⟩ := h (true, 0, 0)
  have he := SimpleGraph.Walk.eq_of_length_eq_zero hp
  have hc := congrArg Prod.fst he
  exact Bool.false_ne_true hc
def family : Registration arena (type_of% @geodesic) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨geodesic, rejected, bad⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected bad
  dependence := by
    intro role
    refine ⟨(), (false, 0, 0), (true, 0, 0), ?_⟩
    norm_num [actual, realize, potential, _root_.D5.S3.StatisticalMechanics.TeaCoordinationSequence.residual]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@geodesic) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.HoneycombCylinderCoordination.PlaneGeodesic.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.HoneycombCylinderCoordination.PlaneGeodesic.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => potential v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.HoneycombCylinderCoordination
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PlaneGeodesic

namespace PlaneDistance
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Vertex) (fun _ => ℕ)
def actual : Realization signature := realize signature
  (fun _ _ v => honeycombGraph.dist (false, 0, 0) v) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ v => potential v + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ v, R.readout () () v = potential v
private theorem bad : ¬ arena.Law rejected := by
  intro h
  have h0 := h (false, 0, 0)
  change potential (false, 0, 0) + 1 = potential (false, 0, 0) at h0
  omega
def family : Registration arena (type_of% @plane_distance) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨plane_distance, rejected, bad⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected bad
  dependence := by
    intro role
    refine ⟨(), (false, 0, 0), (true, 0, 0), ?_⟩
    change honeycombGraph.dist (false, 0, 0) (false, 0, 0) ≠
      honeycombGraph.dist (false, 0, 0) (true, 0, 0)
    rw [plane_distance, plane_distance]
    norm_num [potential, _root_.D5.S3.StatisticalMechanics.TeaCoordinationSequence.residual]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@plane_distance) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.HoneycombCylinderCoordination.PlaneDistance.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.HoneycombCylinderCoordination.PlaneDistance.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => honeycombGraph.dist (false, 0, 0) v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.HoneycombCylinderCoordination
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PlaneDistance

namespace AFiberCount
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℤ) (fun _ => ℕ)
def actual : Realization signature := realize signature (fun _ p s => Nat.card (AFiber s p)) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ p s => Nat.card (AFiber s p) + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (s : ℤ) (k : ℕ) (hk : 0 < k), R.readout () k s =
      (if -(k : ℤ) < s ∧ s < k then 2 else 0) +
      (if s = k then k+1 else 0) + (if s = -(k : ℤ) then k+1 else 0)
private theorem bad : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 1 (by omega)
  have ha := a_fiber_card 0 1 (by omega)
  change Nat.card (AFiber 0 1) + 1 = _ at hb
  norm_num at ha hb
  omega
def family : Registration arena (type_of% @a_fiber_card) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨a_fiber_card, rejected, bad⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected bad
  dependence := by
    intro role
    refine ⟨1, 0, 2, ?_⟩
    change Nat.card (AFiber 0 1) ≠ Nat.card (AFiber 2 1)
    rw [a_fiber_card _ _ (by omega), a_fiber_card _ _ (by omega)]
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@a_fiber_card) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.HoneycombCylinderCoordination.AFiberCount.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.HoneycombCylinderCoordination.AFiberCount.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p s => Nat.card (AFiber s p)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.HoneycombCylinderCoordination
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end AFiberCount

namespace BFiberCount
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℕ) (fun _ => ℤ) (fun _ => ℕ)
def actual : Realization signature := realize signature (fun _ p s => Nat.card (BFiber s p)) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ p s => Nat.card (BFiber s p) + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (s : ℤ) (k : ℕ), R.readout () k s =
      (if -(k : ℤ) ≤ s ∧ s < k then 2 else 0) +
      (if s = k then k+1 else 0) + (if s = -(k : ℤ)-1 then k+2 else 0)
private theorem bad : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 0
  have ha := b_fiber_card 0 0
  change Nat.card (BFiber 0 0) + 1 = _ at hb
  norm_num at ha hb
  omega
def family : Registration arena (type_of% @b_fiber_card) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨b_fiber_card, rejected, bad⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected bad
  dependence := by
    intro role
    refine ⟨0, 0, 1, ?_⟩
    change Nat.card (BFiber 0 0) ≠ Nat.card (BFiber 1 0)
    rw [b_fiber_card, b_fiber_card]
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@b_fiber_card) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.HoneycombCylinderCoordination.BFiberCount.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.HoneycombCylinderCoordination.BFiberCount.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p s => Nat.card (BFiber s p)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.HoneycombCylinderCoordination
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end BFiberCount

namespace IntervalSum
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _U : ℤ, Σ _a : ℤ, ℤ) (fun _ => ℤ) (fun _ => ℕ)
def actual : Realization signature := realize signature
  (fun _ p L => ∑ s ∈ Finset.Icc L p.1, if p.2.1 ≤ s ∧ s ≤ p.2.2 then (2 : ℕ) else 0)
  (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ L U a b : ℤ, R.readout () ⟨U, a, b⟩ L =
    2 * (min U b + 1 - max L a).toNat
private theorem bad : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 0 0 0
  norm_num [rejected, realize] at hb
def family : Registration arena (type_of% @interval_sum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨interval_sum, rejected, bad⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected bad
  dependence := by
    intro role
    refine ⟨⟨0, 0, 0⟩, 0, 1, ?_⟩
    change (∑ s ∈ Finset.Icc (0 : ℤ) 0, if (0 : ℤ) ≤ s ∧ s ≤ 0 then (2 : ℕ) else 0) ≠
      (∑ s ∈ Finset.Icc (1 : ℤ) 0, if (0 : ℤ) ≤ s ∧ s ≤ 0 then (2 : ℕ) else 0)
    rw [interval_sum, interval_sum]
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@interval_sum) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.HoneycombCylinderCoordination.IntervalSum.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.HoneycombCylinderCoordination.IntervalSum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p L => ∑ s ∈ Finset.Icc L p.1, if p.2.1 ≤ s ∧ s ≤ p.2.2 then (2 : ℕ) else 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.HoneycombCylinderCoordination
    definition := none
    coordinates := #[1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end IntervalSum

end
end Reg.D5.S3.StatisticalMechanics.HoneycombCylinderCoordination
