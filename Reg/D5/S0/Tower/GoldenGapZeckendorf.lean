import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Tower.GoldenGapZeckendorf
import Reg.Support.DependentFamily

open _root_.D5.S0.Conventions
open _root_.D5.S0.Tower.GoldenGapZeckendorf
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S0.Tower.GoldenGapZeckendorf

noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State Q := Fin (Nat.fib (Q + 2))
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ (Q : ℕ) (j : Fin (Nat.fib (Q + 2))) => wdigits (Nat.fib (Q + 3) + j.val))
    (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => []) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ Q : ℕ, ∀ j : Fin (Nat.fib (Q + 2)),
    R.readout () Q j = (Q + 3) :: wdigits j.val

theorem rejected_law : ¬ arena.Law rejected := by
  intro hr
  have hh := hr 0 ⟨0, by norm_num [Nat.fib]⟩
  change [] = 3 :: wdigits 0 at hh
  simp at hh

def registration : Registration arena
    (∀ Q : ℕ, ∀ j : Fin (Nat.fib (Q + 2)),
      wdigits (Nat.fib (Q + 3) + j.val) = (Q + 3) :: wdigits j.val) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨wdigits_fib_add, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj; exact False.elim (hj (@Subsingleton.elim Unit _ j i))
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(1 : ℕ), ⟨0, by norm_num [Nat.fib]⟩, ⟨1, by norm_num [Nat.fib]⟩, ?_⟩
    change wdigits 3 ≠ wdigits 4
    intro he
    have hd := congrArg (fun l : List ℕ => (l.map Nat.fib).sum) he
    rw [decode_wdigits, decode_wdigits] at hd
    omega

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S0.Tower.GoldenGapZeckendorf.wdigits_fib_add) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ (Q : ℕ) (j : Fin (Nat.fib (Q + 2))) => wdigits (Nat.fib (Q + 3) + j.val))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S0") "Tower") "GoldenGapZeckendorf") "wdigits_fib_add") "Reg.D5.S0.Tower.GoldenGapZeckendorf/Reg.D5.S0.Tower.GoldenGapZeckendorf.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S0.Tower.GoldenGapZeckendorf.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ (Q : ℕ) (j : Fin (Nat.fib (Q + 2))) => wdigits (Nat.fib (Q + 3) + j.val))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S0.Tower.GoldenGapZeckendorf, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S0.Tower.GoldenGapZeckendorf, declaration := `D5.S0.Tower.GoldenGapZeckendorf.wdigits_fib_add, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S0.Tower.GoldenGapZeckendorf, declaration := `Reg.D5.S0.Tower.GoldenGapZeckendorf.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S0.Tower.GoldenGapZeckendorf, declaration := `Reg.D5.S0.Tower.GoldenGapZeckendorf.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S0.Tower.GoldenGapZeckendorf, declaration := `Reg.D5.S0.Tower.GoldenGapZeckendorf.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S0.Tower.GoldenGapZeckendorf, declaration := `Reg.D5.S0.Tower.GoldenGapZeckendorf.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S0.Tower.GoldenGapZeckendorf.registration_1.canonicalArenaFact, `Reg.D5.S0.Tower.GoldenGapZeckendorf.registration_1.canonicalObjectArenaFact, `Reg.D5.S0.Tower.GoldenGapZeckendorf.registration_1.sourceBridgeFact, `Reg.D5.S0.Tower.GoldenGapZeckendorf.registration_1.observationFact0, `Reg.D5.S0.Tower.GoldenGapZeckendorf.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S0.Tower.GoldenGapZeckendorf.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S0.Tower.GoldenGapZeckendorf.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S0.Tower.GoldenGapZeckendorf.registration_1.anchorEnumeration }


#print axioms registration

end
end Reg.D5.S0.Tower.GoldenGapZeckendorf


noncomputable def Reg.D5.S0.Tower.GoldenGapZeckendorf.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S0.Tower.GoldenGapZeckendorf.arena
noncomputable def Reg.D5.S0.Tower.GoldenGapZeckendorf.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Tower\",\"GoldenGapZeckendorf\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Tower\",\"GoldenGapZeckendorf\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S0.Tower.GoldenGapZeckendorf, declaration := `Reg.D5.S0.Tower.GoldenGapZeckendorf.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S0.Tower.GoldenGapZeckendorf, declaration := `Reg.D5.S0.Tower.GoldenGapZeckendorf.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S0.Tower.GoldenGapZeckendorf.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S0.Tower.GoldenGapZeckendorf.arena
noncomputable def Reg.D5.S0.Tower.GoldenGapZeckendorf.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Tower\",\"GoldenGapZeckendorf\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Tower\",\"GoldenGapZeckendorf\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S0.Tower.GoldenGapZeckendorf, declaration := `Reg.D5.S0.Tower.GoldenGapZeckendorf.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S0.Tower.GoldenGapZeckendorf, declaration := `Reg.D5.S0.Tower.GoldenGapZeckendorf.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S0.Tower.GoldenGapZeckendorf.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S0.Tower.GoldenGapZeckendorf.arena) (Reg.D5.S0.Tower.GoldenGapZeckendorf.registration).actual

noncomputable def Reg.D5.S0.Tower.GoldenGapZeckendorf.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S0\",\"Tower\",\"GoldenGapZeckendorf\",\"wdigits_fib_add\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Tower\",\"GoldenGapZeckendorf\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S0.Tower.GoldenGapZeckendorf, declaration := `D5.S0.Tower.GoldenGapZeckendorf.wdigits_fib_add, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S0.Tower.GoldenGapZeckendorf, declaration := `Reg.D5.S0.Tower.GoldenGapZeckendorf.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S0.Tower.GoldenGapZeckendorf.registration).bridge

noncomputable def Reg.D5.S0.Tower.GoldenGapZeckendorf.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S0.Tower.GoldenGapZeckendorf.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S0.Tower.GoldenGapZeckendorf.registration_1.observation0 : (Q : Nat) →
  (j :
      Fin
        (Nat.fib
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) Q
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))) →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
      Reg.D5.S0.Tower.GoldenGapZeckendorf.signature PUnit.unit.{1} Q :=
  fun (Q : Nat)
    (j :
      Fin
        (Nat.fib
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) Q
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S0.Tower.GoldenGapZeckendorf.signature Reg.D5.S0.Tower.GoldenGapZeckendorf.actual PUnit.unit.{1} Q j

noncomputable def Reg.D5.S0.Tower.GoldenGapZeckendorf.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S0\",\"Tower\",\"GoldenGapZeckendorf\",\"wdigits_fib_add\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Tower\",\"GoldenGapZeckendorf\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S0.Tower.GoldenGapZeckendorf, declaration := `D5.S0.Tower.GoldenGapZeckendorf.wdigits_fib_add, part := .type, path := [.body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S0.Tower.GoldenGapZeckendorf, declaration := `Reg.D5.S0.Tower.GoldenGapZeckendorf.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S0.Tower.GoldenGapZeckendorf.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S0.Tower.GoldenGapZeckendorf.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S0.Tower.GoldenGapZeckendorf.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Tower\",\"GoldenGapZeckendorf\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S0.Tower.GoldenGapZeckendorf.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Tower\",\"GoldenGapZeckendorf\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S0\",\"Tower\",\"GoldenGapZeckendorf\",\"wdigits_fib_add\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S0.Tower.GoldenGapZeckendorf, declaration := `Reg.D5.S0.Tower.GoldenGapZeckendorf.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S0.Tower.GoldenGapZeckendorf, declaration := `D5.S0.Tower.GoldenGapZeckendorf.wdigits_fib_add, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S0.Tower.GoldenGapZeckendorf.registration).actual (Reg.D5.S0.Tower.GoldenGapZeckendorf.registration).variation.2.choose (Reg.D5.S0.Tower.GoldenGapZeckendorf.registration).variation.1 (Reg.D5.S0.Tower.GoldenGapZeckendorf.registration).variation.2.choose_spec

noncomputable def Reg.D5.S0.Tower.GoldenGapZeckendorf.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Tower\",\"GoldenGapZeckendorf\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Tower\",\"GoldenGapZeckendorf\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S0.Tower.GoldenGapZeckendorf, declaration := `Reg.D5.S0.Tower.GoldenGapZeckendorf.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S0.Tower.GoldenGapZeckendorf, declaration := `Reg.D5.S0.Tower.GoldenGapZeckendorf.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
