import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.Attractors.PeriodicPrefixAttractors
import Reg.Support.DependentFamily
import Reg.D5.S1.Words.Attractors.FiniteWordAttractors

open _root_.D5.S1.Words.Attractors
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u
namespace Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits
open _root_.D5.S1.Words.Powers
open _root_.Reg.D5.S1.Words.Attractors.FiniteWordAttractors.HelperAudits
noncomputable section

namespace Endpoints
abbrev signature : Signature where
  Params := Σ _k : Nat, Nat → Nat
  State := fun _ => Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Finset Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p n => (Finset.Icc (n+1-p.1) n).image (fun j => p.2 j-1)) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => ∅) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α : Type u} (k : Nat) (hk : 2 ≤ k)
    (w : Nat → List α) (U : Nat → Nat)
    (hlen : ∀ m, (w m).length = m)
    (hprefix : ∀ m n, m ≤ n → w m = (w n).take m)
    (hU0 : U 0 = 1) (hU : StrictMono U)
    (hgaps : Monotone fun n => U (n + 1) - U n)
    (hperiod : ∀ n, List.HasPeriod (w (U (n + 1) - 1)) (U n))
    (hsuffix : ∀ n, k ≤ n → w (U (n - k)) <:+ w (U n)),
let B := fun n => U (n + 1) - 1
    let Δ := fun n => B n - U n
    let P := fun n => U n + if n < k then 0 else Δ (n - k)
    let Γ := fun n => (Finset.Icc (n + 1 - k) n).image fun j => U j - 1
    ∀ n, P n ≤ B n ∧ ∀ m, P n ≤ m → m ≤ B n → IsAttractor (w m) (R.readout () ⟨k,U⟩ n)

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let w : Nat → List (ULift.{u} Nat) := fun m => List.replicate m ⟨0⟩
  let U : Nat → Nat := fun n => n+1
  have hpref : ∀ m n, m ≤ n → w m = (w n).take m := by
    intro m n hmn
    simp [w, List.take_replicate, Nat.min_eq_left hmn]
  have hper : ∀ n, List.HasPeriod (w (U (n+1)-1)) (U n) := by
    intro n
    apply List.hasPeriod_of_length_le
    simp [w,U]
  have hsuf : ∀ n, 2 ≤ n → w (U (n-2)) <:+ w (U n) := by
    intro n hn
    refine ⟨List.replicate (U n - U (n-2)) ⟨0⟩, ?_⟩
    dsimp [w]
    rw [← List.replicate_add]
    congr 1
    dsimp [U]
    omega
  have hh := h 2 (by omega) w U (by intro m; simp [w]) hpref rfl
    (by intro a b hab; dsimp [U]; omega)
    (by intro a b hab; dsimp [U]; omega) hper hsuf
  have hhit := (hh 0).2 1 (by decide) (by decide)
  exact no_empty_attractor _ (by simp [w]) hhit

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@nested_word_endpoint_attractors, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    exact ⟨⟨2,fun n => n+1⟩,0,1,by cases i; decide⟩

noncomputable def registration_1.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Attractors.nested_word_endpoint_attractors.{u_1}) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ p n => (Finset.Icc.{0} (n+1-p.1) n).image (fun j => p.2 j-1)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Attractors") "nested_word_endpoint_attractors") "Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors/Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1})⟩,
  objectArena := .source ⟨(arena.{u_1})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1}) ⟨(registration.{u_1})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ p n => (Finset.Icc.{0} (n+1-p.1) n).image (fun j => p.2 j-1)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Attractors.PeriodicPrefixAttractors, definition := none, coordinates := #[1, 4], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "body", "arg"], stateBinder := 16, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Attractors.PeriodicPrefixAttractors, declaration := `D5.S1.Words.Attractors.nested_word_endpoint_attractors, part := .type, path := [], levels := [.param `u_1] },
    { owner := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors, declaration := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors, declaration := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors, declaration := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors, declaration := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1] }], facts := [`Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration_1.canonicalArenaFact, `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration_1.canonicalObjectArenaFact, `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration_1.sourceBridgeFact, `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration_1.observationFact0, `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration_1.anchorEnumeration }



end Endpoints

namespace Scan
abbrev signature : Signature where
  Params := Σ _α : Type u, Nat
  State := fun p => List p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ p => List p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p W => W.drop p.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ W => W) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α : Type u} (w : Nat → List α) (U b : Nat → Nat)
    (hlen : ∀ m, (w m).length = m)
    (hprefix : ∀ m n, m ≤ n → w m = (w n).take m)
    (hU : StrictMono U) (hpos : ∀ n, 0 < U n)
    (hperiod : ∀ n, List.HasPeriod (w (U (n + 1) - 1)) (U n))
    (count t N r : Nat) (X W : List α)
    (hcount : 0 < count)
    (hX : X <+: w (U (t + 1) - 1))
    (hR : X.length < U (t + 1) - 1) (hr : r ≤ X.length)
    (hstack : W = descendingBlocks w U b count t ++ X)
    (hsize : W.length = N + r)
    (htop : U (t + count) - 1 < W.length),
∃ h p, t ≤ h ∧ h < t + count ∧ U h ≤ p ∧ p ≤ N ∧
      p - U h + (U (h + 1) - 1) ≤ W.length ∧
      (W.drop (p - U h)).take (U (h + 1) - 1) = w (U (h + 1) - 1) ∧
      R.readout () ⟨α,p⟩ W <+: w (U (h + 1) - 1)

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro hh
  let w : Nat → List (ULift.{u} Nat) := fun m => List.replicate m ⟨0⟩
  let U : Nat → Nat := fun n => n+1
  have hpref : ∀ m n, m ≤ n → w m = (w n).take m := by
    intro m n hmn
    simp [w,List.take_replicate,Nat.min_eq_left hmn]
  have hper : ∀ n, List.HasPeriod (w (U (n+1)-1)) (U n) := by
    intro n
    apply List.hasPeriod_of_length_le
    simp [w,U]
  obtain ⟨h,p,hlo,hhi,hrest⟩ := hh w U (fun _ => 2)
    (by intro m; simp [w]) hpref
    (by intro a b hab; dsimp [U]; omega) (by intro n; dsimp [U]; omega) hper
    1 0 2 0 [] ([⟨0⟩,⟨0⟩] : List (ULift.{u} Nat)) (by omega) (by exact List.nil_prefix)
    (by decide) (by decide) (by rfl) (by rfl) (by decide)
  have heq : h = 0 := by omega
  subst h
  have hlen := hrest.2.2.2.2.length_le
  change 2 ≤ 1 at hlen
  omega

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@periodic_residual_scan, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    exact ⟨⟨ULift.{u} Nat,0⟩,[],[⟨0⟩],by cases i; decide⟩

noncomputable def registration_2.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Attractors.periodic_residual_scan.{u_1}) (type_of% (realize.{u_1 + 1, u_1, 0, u_1, 0} signature.{u_1} (fun _ p W => W.drop p.2) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Attractors") "periodic_residual_scan") "Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors/Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1})⟩,
  objectArena := .source ⟨(arena.{u_1})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1}) ⟨(registration.{u_1})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u_1 + 1, u_1, 0, u_1, 0} signature.{u_1} (fun _ p W => W.drop p.2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Attractors.PeriodicPrefixAttractors, definition := none, coordinates := #[0, 23], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg"], stateBinder := 14, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Attractors.PeriodicPrefixAttractors, declaration := `D5.S1.Words.Attractors.periodic_residual_scan, part := .type, path := [], levels := [.param `u_1] },
    { owner := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors, declaration := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors, declaration := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors, declaration := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors, declaration := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1] }], facts := [`Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration_2.canonicalArenaFact, `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration_2.canonicalObjectArenaFact, `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration_2.sourceBridgeFact, `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration_2.observationFact0, `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration_2.anchorEnumeration }



end Scan

end
end Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits


noncomputable def Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration_2.canonicalArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, u_1, 0} :=
  Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.arena.{u_1}
noncomputable def Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration_2.canonicalArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"PeriodicPrefixAttractors\",\"HelperAudits\",\"Scan\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"PeriodicPrefixAttractors\",\"HelperAudits\",\"Scan\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors, declaration := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors, declaration := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence
noncomputable def Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration_2.canonicalObjectArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, u_1, 0} :=
  Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.arena.{u_1}
noncomputable def Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration_2.canonicalObjectArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"PeriodicPrefixAttractors\",\"HelperAudits\",\"Scan\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"PeriodicPrefixAttractors\",\"HelperAudits\",\"Scan\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors, declaration := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors, declaration := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence

noncomputable def Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration_1.canonicalArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.arena.{u_1}
noncomputable def Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration_1.canonicalArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"PeriodicPrefixAttractors\",\"HelperAudits\",\"Endpoints\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"PeriodicPrefixAttractors\",\"HelperAudits\",\"Endpoints\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors, declaration := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors, declaration := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence
noncomputable def Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration_1.canonicalObjectArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.arena.{u_1}
noncomputable def Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration_1.canonicalObjectArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"PeriodicPrefixAttractors\",\"HelperAudits\",\"Endpoints\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"PeriodicPrefixAttractors\",\"HelperAudits\",\"Endpoints\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors, declaration := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors, declaration := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence


noncomputable def Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration_2.sourceLaw.{u_1} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_1 + 1, u_1, 0, u_1, 0}
  Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.arena.{u_1}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{u_1 + 1, u_1, 0, u_1, 0}
    Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.arena.{u_1}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_1 + 1, u_1, 0, u_1, 0}
      Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.arena.{u_1}
      Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.actual.{u_1})
    Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration.{u_1})

noncomputable def Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration_2.sourceBridgeFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Attractors\",\"periodic_residual_scan\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"PeriodicPrefixAttractors\",\"HelperAudits\",\"Scan\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S1.Words.Attractors.PeriodicPrefixAttractors, declaration := `D5.S1.Words.Attractors.periodic_residual_scan, part := .type, path := [], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors, declaration := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration_2.sourceLaw, part := .value, path := [], levels := [(.param `u_1)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{u_1 + 1, u_1, 0, u_1, 0}
  Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.arena.{u_1}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_1 + 1, u_1, 0, u_1, 0}
    Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.arena.{u_1}
    Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.actual.{u_1})
  Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration.{u_1})

noncomputable def Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration_2.observation0.{u_1} : {α : Type u_1} →
  (w : Nat → List.{u_1} α) →
    (U b : Nat → Nat) →
      (hlen : ∀ (m : Nat), @Eq.{1} Nat (@List.length.{u_1} α (w m)) m) →
        (hprefix :
            ∀ (m n : Nat),
              @LE.le.{0} Nat instLENat m n → @Eq.{u_1 + 1} (List.{u_1} α) (w m) (@List.take.{u_1} α m (w n))) →
          (hU : @StrictMono.{0, 0} Nat Nat Nat.instPreorder Nat.instPreorder U) →
            (hpos :
                ∀ (n : Nat),
                  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (U n)) →
              (hperiod :
                  ∀ (n : Nat),
                    @List.HasPeriod.{u_1} α
                      (w
                        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                          (U
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (U n)) →
                (count t N r : Nat) →
                  (X W : List.{u_1} α) →
                    (hcount :
                        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) count) →
                      (hX :
                          @List.IsPrefix.{u_1} α X
                            (w
                              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                (U
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
                        (hR :
                            @LT.lt.{0} Nat instLTNat (@List.length.{u_1} α X)
                              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                (U
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                          (hr : @LE.le.{0} Nat instLENat r (@List.length.{u_1} α X)) →
                            (hstack :
                                @Eq.{u_1 + 1} (List.{u_1} α) W
                                  (@HAppend.hAppend.{u_1, u_1, u_1} (List.{u_1} α) (List.{u_1} α) (List.{u_1} α)
                                    (@instHAppendOfAppend.{u_1} (List.{u_1} α) (@List.instAppend.{u_1} α))
                                    (@D5.S1.Words.Attractors.descendingBlocks.{u_1} α w U b count t) X)) →
                              (hsize :
                                  @Eq.{1} Nat (@List.length.{u_1} α W)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N r)) →
                                (htop :
                                    @LT.lt.{0} Nat instLTNat
                                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                        (U (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t count))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                      (@List.length.{u_1} α W)) →
                                  (h p : Nat) →
                                    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u_1 + 1,
                                        u_1, 0, u_1, 0}
                                      Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.signature.{u_1}
                                      PUnit.unit.{1}
                                      (@Sigma.mk.{u_1 + 1, 0} (Type u_1) (fun (_α : Type u_1) => Nat) α p) :=
  fun {α : Type u_1} (w : Nat → List.{u_1} α) (U b : Nat → Nat)
    (hlen : ∀ (m : Nat), @Eq.{1} Nat (@List.length.{u_1} α (w m)) m)
    (hprefix :
      ∀ (m n : Nat), @LE.le.{0} Nat instLENat m n → @Eq.{u_1 + 1} (List.{u_1} α) (w m) (@List.take.{u_1} α m (w n)))
    (hU : @StrictMono.{0, 0} Nat Nat Nat.instPreorder Nat.instPreorder U)
    (hpos : ∀ (n : Nat), @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (U n))
    (hperiod :
      ∀ (n : Nat),
        @List.HasPeriod.{u_1} α
          (w
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (U
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (U n))
    (count t N r : Nat) (X W : List.{u_1} α)
    (hcount : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) count)
    (hX :
      @List.IsPrefix.{u_1} α X
        (w
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (U
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (hR :
      @LT.lt.{0} Nat instLTNat (@List.length.{u_1} α X)
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (U
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (hr : @LE.le.{0} Nat instLENat r (@List.length.{u_1} α X))
    (hstack :
      @Eq.{u_1 + 1} (List.{u_1} α) W
        (@HAppend.hAppend.{u_1, u_1, u_1} (List.{u_1} α) (List.{u_1} α) (List.{u_1} α)
          (@instHAppendOfAppend.{u_1} (List.{u_1} α) (@List.instAppend.{u_1} α))
          (@D5.S1.Words.Attractors.descendingBlocks.{u_1} α w U b count t) X))
    (hsize : @Eq.{1} Nat (@List.length.{u_1} α W) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N r))
    (htop :
      @LT.lt.{0} Nat instLTNat
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (U (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t count))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@List.length.{u_1} α W))
    (h p : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u_1 + 1, u_1, 0, u_1, 0}
    Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.signature.{u_1}
    Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.actual.{u_1} PUnit.unit.{1}
    (@Sigma.mk.{u_1 + 1, 0} (Type u_1) (fun (_α : Type u_1) => Nat) α p) W

noncomputable def Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration_2.observationFact0.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Attractors\",\"periodic_residual_scan\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"PeriodicPrefixAttractors\",\"HelperAudits\",\"Scan\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S1.Words.Attractors.PeriodicPrefixAttractors, declaration := `D5.S1.Words.Attractors.periodic_residual_scan, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .body, .argument, .body, .argument, .argument, .argument, .argument, .argument, .argument, .function, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors, declaration := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration_2.observation0, part := .value, path := [], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration_2.varyingLawInput.{u_1} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration_2.canonicalArenaOperand.{u_1})
noncomputable def Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration_2.varyingLaw.{u_1}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"PeriodicPrefixAttractors\",\"HelperAudits\",\"Scan\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"

noncomputable def Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration_2.statementExclusion.{u_1} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"PeriodicPrefixAttractors\",\"HelperAudits\",\"Scan\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Attractors\",\"periodic_residual_scan\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors, declaration := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration_2.varyingLaw, part := .value, path := [], levels := [(.param `u_1)] }
  statementLocation := { owner := `D5.S1.Words.Attractors.PeriodicPrefixAttractors, declaration := `D5.S1.Words.Attractors.periodic_residual_scan, part := .type, path := [], levels := [(.param `u_1)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration.{u_1}).actual (Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration.{u_1}).variation.2.choose (Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration.{u_1}).variation.1 (Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration.{u_1}).variation.2.choose_spec

noncomputable def Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration_2.descriptorFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"PeriodicPrefixAttractors\",\"HelperAudits\",\"Scan\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"PeriodicPrefixAttractors\",\"HelperAudits\",\"Scan\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors, declaration := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors, declaration := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Scan.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration_1.sourceLaw.{u_1} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.arena.{u_1}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.arena.{u_1}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.arena.{u_1}
      Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.actual)
    Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration.{u_1})

noncomputable def Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration_1.sourceBridgeFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Attractors\",\"nested_word_endpoint_attractors\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"PeriodicPrefixAttractors\",\"HelperAudits\",\"Endpoints\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S1.Words.Attractors.PeriodicPrefixAttractors, declaration := `D5.S1.Words.Attractors.nested_word_endpoint_attractors, part := .type, path := [], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors, declaration := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.arena.{u_1}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.arena.{u_1}
    Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.actual)
  Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration.{u_1})

noncomputable def Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration_1.observation0.{u_1} : {α : Type u_1} →
  (k : Nat) →
    (hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k) →
      (w : Nat → List.{u_1} α) →
        (U : Nat → Nat) →
          (hlen : ∀ (m : Nat), @Eq.{1} Nat (@List.length.{u_1} α (w m)) m) →
            (hprefix :
                ∀ (m n : Nat),
                  @LE.le.{0} Nat instLENat m n → @Eq.{u_1 + 1} (List.{u_1} α) (w m) (@List.take.{u_1} α m (w n))) →
              (hU0 :
                  @Eq.{1} Nat (U (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                (hU : @StrictMono.{0, 0} Nat Nat Nat.instPreorder Nat.instPreorder U) →
                  (hgaps :
                      @Monotone.{0, 0} Nat Nat Nat.instPreorder Nat.instPreorder fun (n : Nat) =>
                        @HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                          (U
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (U n)) →
                    (hperiod :
                        ∀ (n : Nat),
                          @List.HasPeriod.{u_1} α
                            (w
                              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                (U
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                            (U n)) →
                      (hsuffix :
                          ∀ (n : Nat),
                            @LE.le.{0} Nat instLENat k n →
                              @List.IsSuffix.{u_1} α
                                (w (U (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n k)))
                                (w (U n))) →
                        have B : (n : Nat) → Nat := fun (n : Nat) =>
                          @HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                            (U
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)));
                        have Δ : (n : Nat) → Nat := fun (n : Nat) =>
                          @HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (B n) (U n);
                        have P : (n : Nat) → Nat := fun (n : Nat) =>
                          @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (U n)
                            (@ite.{1} Nat (@LT.lt.{0} Nat instLTNat n k) (Nat.decLt n k)
                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                              (Δ (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n k)));
                        (n m : Nat) →
                          @LE.le.{0} Nat instLENat (P n) m →
                            @LE.le.{0} Nat instLENat m (B n) →
                              D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                                Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.signature
                                PUnit.unit.{1} (@Sigma.mk.{0, 0} Nat (fun (_k : Nat) => Nat → Nat) k U) :=
  fun {α : Type u_1} (k : Nat)
    (hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)
    (w : Nat → List.{u_1} α) (U : Nat → Nat) (hlen : ∀ (m : Nat), @Eq.{1} Nat (@List.length.{u_1} α (w m)) m)
    (hprefix :
      ∀ (m n : Nat), @LE.le.{0} Nat instLENat m n → @Eq.{u_1 + 1} (List.{u_1} α) (w m) (@List.take.{u_1} α m (w n)))
    (hU0 :
      @Eq.{1} Nat (U (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (hU : @StrictMono.{0, 0} Nat Nat Nat.instPreorder Nat.instPreorder U)
    (hgaps :
      @Monotone.{0, 0} Nat Nat Nat.instPreorder Nat.instPreorder fun (n : Nat) =>
        @HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (U
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (U n))
    (hperiod :
      ∀ (n : Nat),
        @List.HasPeriod.{u_1} α
          (w
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (U
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (U n))
    (hsuffix :
      ∀ (n : Nat),
        @LE.le.{0} Nat instLENat k n →
          @List.IsSuffix.{u_1} α (w (U (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n k)))
            (w (U n))) =>
  have B : (n : Nat) → Nat := fun (n : Nat) =>
    @HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
      (U
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)));
  have Δ : (n : Nat) → Nat := fun (n : Nat) =>
    @HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (B n) (U n);
  have P : (n : Nat) → Nat := fun (n : Nat) =>
    @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (U n)
      (@ite.{1} Nat (@LT.lt.{0} Nat instLTNat n k) (Nat.decLt n k)
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Δ (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n k)));
  have Γ : (n : Nat) → Finset.{0} Nat := fun (n : Nat) =>
    @Finset.image.{0, 0} Nat Nat instDecidableEqNat
      (fun (j : Nat) =>
        @HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (U j)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          k)
        n);
  fun (n m : Nat) (a : @LE.le.{0} Nat instLENat (P n) m) (a_1 : @LE.le.{0} Nat instLENat m (B n)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.signature
    Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat (fun (_k : Nat) => Nat → Nat) k U) n

noncomputable def Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration_1.observationFact0.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Attractors\",\"nested_word_endpoint_attractors\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"letBody\",\"letBody\",\"letBody\",\"letBody\",\"body\",\"argument\",\"body\",\"body\",\"body\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"PeriodicPrefixAttractors\",\"HelperAudits\",\"Endpoints\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S1.Words.Attractors.PeriodicPrefixAttractors, declaration := `D5.S1.Words.Attractors.nested_word_endpoint_attractors, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .letBody, .letBody, .letBody, .letBody, .body, .argument, .body, .body, .body, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors, declaration := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration_1.varyingLawInput.{u_1} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration_1.canonicalArenaOperand.{u_1})
noncomputable def Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration_1.varyingLaw.{u_1}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"PeriodicPrefixAttractors\",\"HelperAudits\",\"Endpoints\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"

noncomputable def Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration_1.statementExclusion.{u_1} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"PeriodicPrefixAttractors\",\"HelperAudits\",\"Endpoints\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Attractors\",\"nested_word_endpoint_attractors\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors, declaration := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1)] }
  statementLocation := { owner := `D5.S1.Words.Attractors.PeriodicPrefixAttractors, declaration := `D5.S1.Words.Attractors.nested_word_endpoint_attractors, part := .type, path := [], levels := [(.param `u_1)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration.{u_1}).actual (Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration.{u_1}).variation.2.choose (Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration.{u_1}).variation.1 (Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration.{u_1}).variation.2.choose_spec

noncomputable def Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"PeriodicPrefixAttractors\",\"HelperAudits\",\"Endpoints\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"PeriodicPrefixAttractors\",\"HelperAudits\",\"Endpoints\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors, declaration := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors, declaration := `Reg.D5.S1.Words.Attractors.PeriodicPrefixAttractors.HelperAudits.Endpoints.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))
