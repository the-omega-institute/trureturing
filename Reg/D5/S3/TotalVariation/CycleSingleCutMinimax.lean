import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.TotalVariation.CycleSingleCutMinimax
import Reg.Support.DependentFamily

open _root_.D5.S3.TotalVariation.CycleSingleCutMinimax
open _root_.D5.S3.TotalVariation.Pinsker
open _root_.D5.S3.TotalVariation.Metric
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable
namespace Reg.D5.S3.TotalVariation.CycleSingleCutMinimax
universe u

abbrev signature : Signature where
  Params := Type u
  State B := B → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ B := B → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ μ => μ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => 0) (fun e => nomatch e)

/-- Vary the prescribed marginal in the first single-cut conclusion while retaining
the complete source telescope and every other conclusion. -/
def arena : Arena where
  signature := signature
  Law r := ∀ {B : Type u} [Fintype B]
    (n : ℕ) (μ : B → ℝ) (g : Equiv.Perm B)
    (_hμ : Probability μ) (_hinv : ∀ x, μ (g x) = μ x),
    (∀ k : Fin (n + 1), Joint (r.readout () B μ) (cutLaw μ g k) ∧
      ∀ i, error μ g (cutLaw μ g k) i = if i = k then moved μ g else 0) ∧
    (∀ π : Fin (n + 1) → ℝ, Probability π → Joint μ (mixture μ g π) ∧
      ∀ i, error μ g (mixture μ g π) i = moved μ g * π i) ∧
    (∀ P : (Fin (n + 1) → B) → ℝ, Joint μ P → ∀ i, error μ g P i =
      ∑ y, if y (next i) ≠ transport g i (y i) then P y else 0) ∧
    (∀ P : (Fin (n + 1) → B) → ℝ, Joint μ P → moved μ g ≤ ∑ i, error μ g P i) ∧
    (∀ ε : Fin (n + 1) → ℝ, (∀ i, 0 ≤ ε i) →
      ((∃ P, Joint μ P ∧ ∀ i, error μ g P i ≤ ε i) ↔ moved μ g ≤ ∑ i, ε i)) ∧
    IsLeast {t | ∃ P : (Fin (n + 1) → B) → ℝ, Joint μ P ∧ worst μ g P = t}
      (moved μ g / (n + 1)) ∧
    ((∃ P : (Fin (n + 1) → B) → ℝ, Joint μ P ∧ ∀ i, error μ g P i ≤ 0) ↔ moved μ g = 0) ∧
    (∀ ε : Fin (n + 1) → ℝ, (∀ i, 0 ≤ ε i) → moved μ g ≤ ∑ i, ε i →
      0 < moved μ g →
      Probability (fun i => ε i / ∑ j, ε j) ∧
      Joint μ (mixture μ g (fun i => ε i / ∑ j, ε j)) ∧
      (∀ i, error μ g (mixture μ g (fun i => ε i / ∑ j, ε j)) i ≤ ε i) ∧
      (∀ i, ε i = 0 → ε i / (∑ j, ε j) = 0)) ∧
    (∀ A : Set (((Fin (n + 1) → B) → ℝ)), Convex ℝ A →
      (∀ k, cutLaw μ g k ∈ A) →
      (∀ π, Probability π → mixture μ g π ∈ A) ∧
      (∀ ε : Fin (n + 1) → ℝ, (∀ i, 0 ≤ ε i) →
        ((∃ P ∈ A, Joint μ P ∧ ∀ i, error μ g P i ≤ ε i) ↔ moved μ g ≤ ∑ i, ε i)) ∧
      IsLeast {t | ∃ P ∈ A, Joint μ P ∧ worst μ g P = t} (moved μ g / (n + 1))) ∧
    RestrictedCounterexample

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let V := ULift.{u} Unit
  let μ : V → ℝ := fun _ => 1
  let g : Equiv.Perm V := Equiv.refl V
  have hμ : Probability μ := ⟨fun _ => by norm_num [μ], by simp [μ, V]⟩
  have hz := congrFun (((h 2 μ g hμ (fun _ => rfl)).1 (0 : Fin 3)).1.2 0) ⟨()⟩
  have hp := congrFun (((cycle_single_cut_minimax 2 μ g hμ (fun _ => rfl)).1
    (0 : Fin 3)).1.2 0) ⟨()⟩
  have he : (0 : ℝ) = 1 := by
    simpa [rejected, realize, μ] using hz.symm.trans hp
  norm_num at he

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨ULift.{u} Unit, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have he := congrFun h ⟨()⟩
  norm_num [actual, realize] at he

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.TotalVariation.CycleSingleCutMinimax.cycle_single_cut_minimax.{u},
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.TotalVariation.CycleSingleCutMinimax.cycle_single_cut_minimax.{u}) (type_of% (realize.{u + 1, u, 0, u, 0} signature.{u} (fun _ _ μ => μ) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "TotalVariation") "CycleSingleCutMinimax") "cycle_single_cut_minimax") "Reg.D5.S3.TotalVariation.CycleSingleCutMinimax/Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u})⟩,
  objectArena := .source ⟨(arena.{u})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u}) ⟨(registration.{u})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u + 1, u, 0, u, 0} signature.{u} (fun _ _ μ => μ) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.TotalVariation.CycleSingleCutMinimax, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "fn", "arg", "fn", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.TotalVariation.CycleSingleCutMinimax, declaration := `D5.S3.TotalVariation.CycleSingleCutMinimax.cycle_single_cut_minimax, part := .type, path := [], levels := [.param `u] },
    { owner := `Reg.D5.S3.TotalVariation.CycleSingleCutMinimax, declaration := `Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.TotalVariation.CycleSingleCutMinimax, declaration := `Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.TotalVariation.CycleSingleCutMinimax, declaration := `Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.TotalVariation.CycleSingleCutMinimax, declaration := `Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u] }], facts := [`Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration_1.canonicalArenaFact, `Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration_1.sourceBridgeFact, `Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration_1.observationFact0, `Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration_1.anchorEnumeration }


#print axioms registration
end Reg.D5.S3.TotalVariation.CycleSingleCutMinimax


noncomputable def Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration_1.canonicalArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u + 1, u, 0, u, 0} :=
  Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.arena.{u}
noncomputable def Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration_1.canonicalArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"TotalVariation\",\"CycleSingleCutMinimax\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"TotalVariation\",\"CycleSingleCutMinimax\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.TotalVariation.CycleSingleCutMinimax, declaration := `Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.TotalVariation.CycleSingleCutMinimax, declaration := `Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence
noncomputable def Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration_1.canonicalObjectArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u + 1, u, 0, u, 0} :=
  Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.arena.{u}
noncomputable def Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration_1.canonicalObjectArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"TotalVariation\",\"CycleSingleCutMinimax\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"TotalVariation\",\"CycleSingleCutMinimax\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.TotalVariation.CycleSingleCutMinimax, declaration := `Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.TotalVariation.CycleSingleCutMinimax, declaration := `Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence


noncomputable def Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration_1.sourceLaw.{u} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u + 1, u, 0, u, 0}
  Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.arena.{u}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{u + 1, u, 0, u, 0}
    Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.arena.{u}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u + 1, u, 0, u, 0}
      Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.arena.{u}
      Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.actual.{u})
    Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration.{u})

noncomputable def Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration_1.sourceBridgeFact.{u} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"TotalVariation\",\"CycleSingleCutMinimax\",\"cycle_single_cut_minimax\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"TotalVariation\",\"CycleSingleCutMinimax\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.TotalVariation.CycleSingleCutMinimax, declaration := `D5.S3.TotalVariation.CycleSingleCutMinimax.cycle_single_cut_minimax, part := .type, path := [], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.TotalVariation.CycleSingleCutMinimax, declaration := `Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{u + 1, u, 0, u, 0}
  Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.arena.{u}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u + 1, u, 0, u, 0}
    Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.arena.{u} Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.actual.{u})
  Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration.{u})

noncomputable def Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration_1.observation0.{u} : {B : Type u} →
  [inst : Fintype.{u} B] →
    (n : Nat) →
      (μ : B → Real) →
        (g : Equiv.Perm.{u + 1} B) →
          (hμ : @D5.S3.TotalVariation.CycleSingleCutMinimax.Probability.{u} B inst μ) →
            (hinv :
                ∀ (x : B),
                  @Eq.{1} Real
                    (μ
                      (@DFunLike.coe.{u + 1, u + 1, u + 1} (Equiv.Perm.{u + 1} B) B (fun (x : B) => B)
                        (@EquivLike.toFunLike.{u + 1, u + 1, u + 1} (Equiv.Perm.{u + 1} B) B B
                          (@Equiv.instEquivLike.{u + 1, u + 1} B B))
                        g x))
                    (μ x)) →
              (k :
                  Fin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u + 1, u, 0, u, 0}
                  Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.signature.{u} PUnit.unit.{1} B :=
  fun {B : Type u} [Fintype.{u} B] (n : Nat) (μ : B → Real) (g : Equiv.Perm.{u + 1} B)
    (hμ : @D5.S3.TotalVariation.CycleSingleCutMinimax.Probability.{u} B inst μ)
    (hinv :
      ∀ (x : B),
        @Eq.{1} Real
          (μ
            (@DFunLike.coe.{u + 1, u + 1, u + 1} (Equiv.Perm.{u + 1} B) B (fun (x : B) => B)
              (@EquivLike.toFunLike.{u + 1, u + 1, u + 1} (Equiv.Perm.{u + 1} B) B B
                (@Equiv.instEquivLike.{u + 1, u + 1} B B))
              g x))
          (μ x))
    (k :
      Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u + 1, u, 0, u, 0}
    Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.signature.{u}
    Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.actual.{u} PUnit.unit.{1} B μ

noncomputable def Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration_1.observationFact0.{u} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"TotalVariation\",\"CycleSingleCutMinimax\",\"cycle_single_cut_minimax\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"body\",\"function\",\"argument\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"TotalVariation\",\"CycleSingleCutMinimax\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.TotalVariation.CycleSingleCutMinimax, declaration := `D5.S3.TotalVariation.CycleSingleCutMinimax.cycle_single_cut_minimax, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .function, .argument, .body, .function, .argument, .function, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.TotalVariation.CycleSingleCutMinimax, declaration := `Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration_1.observation0, part := .value, path := [], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration_1.varyingLawInput.{u} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration_1.canonicalArenaOperand.{u})
noncomputable def Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration_1.varyingLaw.{u}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"TotalVariation\",\"CycleSingleCutMinimax\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"

noncomputable def Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration_1.statementExclusion.{u} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"TotalVariation\",\"CycleSingleCutMinimax\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"TotalVariation\",\"CycleSingleCutMinimax\",\"cycle_single_cut_minimax\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.TotalVariation.CycleSingleCutMinimax, declaration := `Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u)] }
  statementLocation := { owner := `D5.S3.TotalVariation.CycleSingleCutMinimax, declaration := `D5.S3.TotalVariation.CycleSingleCutMinimax.cycle_single_cut_minimax, part := .type, path := [], levels := [(.param `u)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration.{u}).actual (Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration.{u}).variation.2.choose (Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration.{u}).variation.1 (Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration.{u}).variation.2.choose_spec

noncomputable def Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration_1.descriptorFact.{u} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"TotalVariation\",\"CycleSingleCutMinimax\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"TotalVariation\",\"CycleSingleCutMinimax\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.TotalVariation.CycleSingleCutMinimax, declaration := `Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.TotalVariation.CycleSingleCutMinimax, declaration := `Reg.D5.S3.TotalVariation.CycleSingleCutMinimax.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))
