import D5.S3.StatisticalMechanics.KisrhombilleFaceCoordination
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! The infinite coordination readout, with Tea hexagon counts reused by the source proof. -/

namespace Reg.D5.S3.StatisticalMechanics.KisrhombilleFaceCoordination

open _root_.D5.S3.StatisticalMechanics.KisrhombilleFaceCoordination
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => a n + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := (1 - X^2)^2 * (PowerSeries.mk fun n => (R.readout () () n : ℤ)) =
    1 + 6*X + 22*X^2 + 6*X^3 + X^4

private theorem initial_values : a 0 = 1 ∧ a 1 = 6 := by
  have h0 := congrArg PowerSeries.constantCoeff result
  have h1 := congrArg (PowerSeries.coeff 1) result
  norm_num at h0
  norm_num [PowerSeries.coeff_mul, PowerSeries.coeff_mk, PowerSeries.coeff_X,
    Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, pow_two] at h1
  omega

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := congrArg PowerSeries.constantCoeff h
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
    refine ⟨(), 0, 1, ?_⟩
    change a 0 ≠ a 1
    rw [initial_values.1, initial_values.2]
    omega

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.KisrhombilleFaceCoordination.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.KisrhombilleFaceCoordination.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.KisrhombilleFaceCoordination
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "arg", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

namespace PolygonMembership

abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature
  (ℕ × ℕ × ℕ × ℕ × ℤ × ℤ) (fun _ => ℤ × ℤ) (fun _ => Prop)
def actual : Realization signature := realize signature
  (fun _ p z => z ∈ polygon p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)
  (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (A B l r : ℕ) (i0 j0 : ℤ),
    l ≤ A+1 → l ≤ B+1 → r ≤ A+1 → r ≤ B+1 → ∀ p : ℤ × ℤ,
    R.readout () (A,B,l,r,i0,j0) p ↔
      i0 ≤ p.1 ∧ p.1 ≤ i0+A ∧ j0 ≤ p.2 ∧ p.2 ≤ j0+B ∧
      (l:ℤ) ≤ p.1+p.2-i0-j0 ∧ p.1+p.2-i0-j0+r ≤ (A:ℤ)+B
private theorem bad : ¬ arena.Law rejected := by
  intro h
  exact (h 0 0 0 0 0 0 (by omega) (by omega) (by omega) (by omega) (0,0)).mpr
    (by norm_num)
def family : Registration arena (type_of% @polygon_mem) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@polygon_mem, rejected, bad⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ bad
  dependence := by
    intro role
    refine ⟨(0,0,0,0,0,0), (0,0), (1,0), ?_⟩
    change ((0,0) ∈ polygon 0 0 0 0 0 0) ≠ ((1,0) ∈ polygon 0 0 0 0 0 0)
    have h0 := polygon_mem 0 0 0 0 0 0 (by omega) (by omega) (by omega) (by omega) (0,0)
    have h1 := polygon_mem 0 0 0 0 0 0 (by omega) (by omega) (by omega) (by omega) (1,0)
    norm_num at h0 h1
    intro he
    exact h1 (Eq.mp he h0)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@polygon_mem) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.KisrhombilleFaceCoordination.PolygonMembership.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.KisrhombilleFaceCoordination.PolygonMembership.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p z => z ∈ polygon p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.KisrhombilleFaceCoordination
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 10
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PolygonMembership

namespace PolygonCount

abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature
  (ℕ × ℕ × ℕ × ℤ × ℤ) (fun _ => ℕ) (fun _ => ℕ)
def actual : Realization signature := realize signature
  (fun _ p A => (polygon A p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2).card) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ p A => (polygon A p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2).card + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (A B l r : ℕ) (i0 j0 : ℤ),
    l ≤ A+1 → l ≤ B+1 → r ≤ A+1 → r ≤ B+1 → l+r ≤ A+B+1 →
    2*(R.readout () (B,l,r,i0,j0) A : ℤ) =
      2*(A+1)*(B+1)-(l:ℤ)*(l+1)-(r:ℤ)*(r+1)
private theorem bad : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 0 0 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega)
  have hc := polygon_card 0 0 0 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega)
  change 2*((polygon 0 0 0 0 0 0).card + 1 : ℤ) = _ at hb
  norm_num at hb hc
  omega
def family : Registration arena (type_of% @polygon_card) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@polygon_card, rejected, bad⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ bad
  dependence := by
    intro role
    refine ⟨(0,0,0,0,0), 0, 1, ?_⟩
    change (polygon 0 0 0 0 0 0).card ≠ (polygon 1 0 0 0 0 0).card
    have h0 := polygon_card 0 0 0 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega)
    have h1 := polygon_card 1 0 0 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega)
    norm_num at h0 h1
    omega

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@polygon_card) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.KisrhombilleFaceCoordination.PolygonCount.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.KisrhombilleFaceCoordination.PolygonCount.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p A => (polygon A p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2).card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.KisrhombilleFaceCoordination
    definition := none
    coordinates := #[1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "fn", "fn", "fn", "fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PolygonCount

namespace FiniteShells

abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => Simplex) (fun _ => ℕ)
def actual : Realization signature := realize signature (fun _ _ s => distance s) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, {s : Simplex | R.readout () () s = n}.Finite
private theorem bad : ¬ arena.Law rejected := by
  intro h
  have hf : (Set.univ : Set Simplex).Finite := by simpa [rejected, realize] using h 0
  exact Set.infinite_univ hf
def family : Registration arena (type_of% @shell_finite) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨shell_finite, rejected, bad⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ bad
  dependence := by
    intro role
    refine ⟨(), root, (0,0,0), ?_⟩
    change distance root ≠ distance (0,0,0)
    have ha : graph.Adj root (0,0,0) := by simp [graph, support, root, Prod.ext_iff]
    have hd := graph.dist_eq_one_iff_adj.mpr ha
    change graph.dist root root ≠ graph.dist root (0,0,0)
    rw [graph.dist_self, hd]
    omega

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@shell_finite) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.KisrhombilleFaceCoordination.FiniteShells.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.KisrhombilleFaceCoordination.FiniteShells.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => distance s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.KisrhombilleFaceCoordination
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FiniteShells

end
end Reg.D5.S3.StatisticalMechanics.KisrhombilleFaceCoordination
