import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-!
Source-bound audit of the literal strip's necessary pair-colour zone data.
The typed evidence compiles; source-telescope reconstruction remains unresolved:
https://github.com/the-omega-institute/trureturing/issues/29434.
This mirror does not establish a `declared_validated` audit.
-/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233196Strip (beta)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Fin n × Fin 6 → Fin 8) (fun n => Fin n × Fin 6 → Fin 4)

def actual : Realization signature :=
  realize signature (fun _ _ f p => beta (f p)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (hn : 2 ≤ n) (f : Fin n × Fin 6 → Fin 8), Legal f →
    let c := R.readout () n f
    let z : Fin n := ⟨0,by omega⟩
    (∀ i j, c (i,j) = (c (i,0) ^^^ c (z,0)) ^^^ c (z,j)) ∧
    (∀ j : Fin 5, c (z,j.castSucc) ^^^ c (z,j.succ) ≠ 0) ∧
    (∀ (i : ℕ) (hi : i + 1 < n),
      c (⟨i,by omega⟩,0) ^^^ c (⟨i+1,hi⟩,0) ≠ 0 ∧
      ∀ j : Fin 5, c (z,j.castSucc) ^^^ c (z,j.succ) ≠
        c (⟨i,by omega⟩,0) ^^^ c (⟨i+1,hi⟩,0)) ∧
    (∀ k : Fin 4, ∃ p, p.1.val ≤ 1 ∧ c p = k) ∧
    (∀ d : Fin 3, ∃ p, p.1.val ≤ 1 ∧ (f p).val = d.val + 1) ∧
    ((Finset.univ.filter (fun v : Fin 4 => v ≠ 0 ∧ ∀ j : Fin 5,
      c (z,j.castSucc) ^^^ c (z,j.succ) ≠ v)).card =
      if ∀ j : Fin 5, c (z,j.castSucc) ^^^ c (z,j.succ) = c (z,0) ^^^ c (z,1)
      then 2 else 1)

private def sample : Fin 2 × Fin 6 → Fin 8 := fun p =>
  (![![0,1,0,6,7,2],![3,5,4,2,4,6]] : Fin 2 → Fin 6 → Fin 8) p.1 p.2

private theorem sample_legal : Legal sample := by
  simp [Legal, sample, Fin.forall_fin_succ, Fin.exists_fin_succ]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 2 (by omega) sample sample_legal).2.1 (0 : Fin 5)
  change (0 : Fin 4) ^^^ 0 ≠ 0 at hh
  exact hh (by decide)

def family : Registration arena (type_of% @pair_rectangle) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pair_rectangle, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨1, (fun _ => 0), (fun _ => 1), ?_⟩
    intro h
    have hh := congrFun h ((0 : Fin 1),(0 : Fin 6))
    change (0 : Fin 4) = 1 at hh
    exact (by decide : (0 : Fin 4) ≠ 1) hh

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@pair_rectangle) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f p => beta (f p)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "value"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233166KingStrip
