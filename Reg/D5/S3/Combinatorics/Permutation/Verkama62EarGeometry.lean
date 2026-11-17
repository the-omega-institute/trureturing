import Reg.D5.S3.Combinatorics.Permutation.Verkama62Local

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Permutation.Verkama62EarGeometry
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Permutation.Verkama62Local
open Reg.D5.S3.Combinatorics.Permutation.Verkama62Count (sampleDouble)

def samplePair : PairEar pattern {0,1,2,4} where
  u := 3
  v := 5
  x := 4
  y := 1
  hx := by decide
  hy := by decide
  hu := by decide
  hv := by decide
  hxy := by decide
  huv := by decide
  hvu := by decide
  edge_u := by norm_num [valueGraph,pattern]
  edge_v := by norm_num [valueGraph,pattern]
  unique_u := by intro i hi hne; fin_cases i <;> norm_num [valueGraph,pattern] at *
  unique_v := by intro i hi hne; fin_cases i <;> norm_num [valueGraph,pattern] at *

theorem base_run : EarRun pattern {0,1,2,4} :=
  EarRun.square 0 1 2 4 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem full_run : EarRun pattern Finset.univ := by
  have h := base_run.double sampleDouble
  convert h using 1 <;> decide

theorem graph_connected : (valueGraph pattern).Connected := by
  have edge (u v : Fin 6) (h : (valueGraph pattern).Adj u v) := h.reachable
  have e02 : (valueGraph pattern).Adj 0 2 := by norm_num [valueGraph,pattern]
  have e21 : (valueGraph pattern).Adj 2 1 := by norm_num [valueGraph,pattern]
  have e04 : (valueGraph pattern).Adj 0 4 := by norm_num [valueGraph,pattern]
  have e43 : (valueGraph pattern).Adj 4 3 := by norm_num [valueGraph,pattern]
  have e35 : (valueGraph pattern).Adj 3 5 := by norm_num [valueGraph,pattern]
  have reach (v : Fin 6) : (valueGraph pattern).Reachable 0 v := by
    fin_cases v
    · exact .refl _
    · exact e02.reachable.trans e21.reachable
    · exact e02.reachable
    · exact e04.reachable.trans e43.reachable
    · exact e04.reachable
    · exact e04.reachable.trans (e43.reachable.trans e35.reachable)
  exact ⟨fun a b => (reach a).symm.trans (reach b)⟩

theorem graph_deleted (v : Fin 6) : ((valueGraph pattern).induce {v}ᶜ).Connected := by
  have h := full_run.robust (pattern.symm v)
  have heq : pattern '' (((Finset.univ : Finset (Fin 6)).erase (pattern.symm v)) : Set _) = {v}ᶜ := by
    ext u
    constructor
    · rintro ⟨i, hi, rfl⟩
      change pattern i ≠ v
      intro hv
      exact (Finset.mem_erase.mp hi).1 (pattern.injective (hv.trans (pattern.apply_symm_apply v).symm))
    · intro hv
      change u ≠ v at hv
      refine ⟨pattern.symm u, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, pattern.apply_symm_apply u⟩
      intro he
      exact hv (pattern.symm.injective he)
  rwa [heq] at h

namespace Pair
abbrev signature : Signature where
  Params := ℕ
  State n := Fin n
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Fin n
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ w => w) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ w => ⟨0, lt_of_le_of_lt (Nat.zero_le _) w.isLt⟩) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {π : Equiv.Perm (Fin n)} {S : Finset (Fin n)}
    (e : PairEar π S), 3 ≤ S.card →
    (∀ w ∈ S, ((valueGraph π).induce (π '' ((S.erase w : Finset _) : Set _))).Connected) →
    ∀ z : Fin n, z.val = 0 → z ∈ S →
      ∃ d : Double π S, d.u = R.readout () n e.u ∧ d.v = e.v
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨d,hu,hv⟩ := @h 6 pattern {0,1,2,4} samplePair (by decide)
    (fun w _ => base_run.robust w) 0 rfl (by decide)
  change d.u = 0 at hu
  have hy := d.old_left d.y d.hy d.hxy.symm
  rw [hu] at hy
  exact (Fin.not_lt_zero _ ) hy

def family : Registration arena (type_of% (@PairEar.to_double)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@PairEar.to_double, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i; refine ⟨2,0,1,?_⟩
    change (0 : Fin 2) ≠ 1
    decide
noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@PairEar.to_double) (Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Permutation.Verkama62Local.PairEar.to_double.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Permutation.Verkama62EarGeometry.Pair.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ w => w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Permutation.Verkama62EarGeometry
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #[]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Pair
namespace Extension
abbrev signature : Signature where
  Params := Σ n : ℕ, Equiv.Perm (Fin n)
  State p := Finset (Fin p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p S => Nonempty (Double p.2 S)) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (π : Equiv.Perm (Fin n)) (S : Finset (Fin n)),
    3 ≤ S.card →
    (∀ w ∈ S, ((valueGraph π).induce (π '' ((S.erase w : Finset _) : Set _))).Connected) →
    ∀ z b : Fin n, z.val = 0 → (π b).val = 0 → z ≠ b → z ∈ S → b ∈ S →
    S ≠ Finset.univ → (valueGraph π).Connected →
    (∀ v, ((valueGraph π).induce {v}ᶜ).Connected) →
      (∃ u ∉ S, 2 ≤ (neighbours π S u).card) ∨ R.readout () ⟨n,π⟩ S
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := @h 6 pattern {0,1,2,4} (by decide) (fun w _ => base_run.robust w)
    0 2 rfl rfl (by decide) (by decide) (by decide) (by decide) graph_connected graph_deleted
  have hsmall (u : Fin 6) (hu : u ∉ ({0,1,2,4} : Finset (Fin 6))) :
      (neighbours pattern {0,1,2,4} u).card ≤ 1 := by
    fin_cases u <;> first | exact (hu (by decide)).elim | decide
  rcases he with ⟨u,hu,hd⟩ | he
  · have := hsmall u hu
    omega
  · exact he

def family : Registration arena (type_of% (@anchored_extension)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@anchored_extension, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    refine ⟨⟨6,pattern⟩, {0,1,2,4}, ∅, ?_⟩
    intro h
    obtain ⟨d⟩ := Eq.mp h (show Nonempty (Double pattern {0,1,2,4}) from ⟨sampleDouble⟩)
    exact Finset.notMem_empty d.x d.hx
noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@anchored_extension) (Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Permutation.Verkama62Local.anchored_extension.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Permutation.Verkama62EarGeometry.Extension.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p S => Nonempty (Double p.2 S)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Permutation.Verkama62EarGeometry
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Extension
end Reg.D5.S3.Combinatorics.Permutation.Verkama62EarGeometry
