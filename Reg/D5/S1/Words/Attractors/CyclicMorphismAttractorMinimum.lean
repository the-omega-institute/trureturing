import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import Reg.Support.SourceSelection
import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum
import Reg.Support.DependentFamily
import Reg.D5.S1.Words.Attractors.FiniteWordAttractors

open _root_.D5.S1.Words.Attractors
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum
noncomputable section

abbrev signature : Signature where
  Params := Σ k : Nat, Fin k → Nat
  State := fun p => List (Fin p.1)
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ w => gamma w)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k : Nat} (hk : 2 ≤ k) (c : Fin k → Nat),
    1 ≤ c ⟨0, by omega⟩ → 1 ≤ c ⟨k - 1, by omega⟩ → CyclicMaximal c →
    ∀ m : Nat, 0 < m →
      (∀ i : Nat, i ≤ k - 2 → cyclicLength (by omega) c i ≤ m →
        m < cyclicLength (by omega) c (i + 1) →
          R.readout 0 ⟨k, c⟩ (cyclicPrefix (k := k) (by omega) c m) = i + 1) ∧
      (cyclicLength (by omega) c (k - 1) ≤ m →
        R.readout 1 ⟨k, c⟩ (cyclicPrefix (k := k) (by omega) c m) = k)

def rejected : Realization signature := realize signature (fun _ _ _ => 0)
  (fun e => nomatch e)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let c : Fin 2 → Nat := fun _ => 1
  have hcyc : CyclicMaximal c := by
    intro r
    have hd : List.ofFn (cyclicDigit c) = [1, 0] := by decide
    rw [hd, ← List.rotate_mod]
    have hr : r % 2 = 0 ∨ r % 2 = 1 := by have := Nat.mod_lt r (by omega : 0 < 2); omega
    simp only [List.length_cons, List.length_nil] at *
    rcases hr with hr | hr
    · rw [hr]; decide
    · rw [hr]; decide
  have hh := (h (by omega : 2 ≤ 2) c (by decide) (by decide) hcyc 1 (by omega)).1
    0 (by omega) (by decide) (by decide)
  norm_num [rejected, realize] at hh

def rejectedAt (i : Fin 2) : Realization signature :=
  realize signature (fun j _ w => if j = i then 0 else gamma w) (fun e => nomatch e)

theorem rejectedAt_law (i : Fin 2) : ¬ arena.Law (rejectedAt i) := by
  intro h
  let c : Fin 2 → Nat := fun _ => 1
  have hcyc : CyclicMaximal c := by
    intro r
    have hd : List.ofFn (cyclicDigit c) = [1, 0] := by decide
    rw [hd, ← List.rotate_mod]
    have hr : r % 2 = 0 ∨ r % 2 = 1 := by have := Nat.mod_lt r (by omega : 0 < 2); omega
    simp only [List.length_cons, List.length_nil] at *
    rcases hr with hr | hr
    · rw [hr]; decide
    · rw [hr]; decide
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with hi | hi
  · subst i
    have hh := (h (by omega : 2 ≤ 2) c (by decide) (by decide) hcyc 1 (by omega)).1
      0 (by omega) (by decide) (by decide)
    norm_num [rejectedAt, realize] at hh
  · subst i
    have hh := (h (by omega : 2 ≤ 2) c (by decide) (by decide) hcyc 2 (by omega)).2
      (by decide)
    norm_num [rejectedAt, realize] at hh

def registration : Registration arena
    (∀ {k : Nat} (hk : 2 ≤ k) (c : Fin k → Nat),
      1 ≤ c ⟨0, by omega⟩ → 1 ≤ c ⟨k - 1, by omega⟩ → CyclicMaximal c →
        CyclicAttractorMinimum (by omega) c) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by intro k hk c h0 hl hc; exact result hk c h0 hl hc, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedAt i, ?_, rfl, rejectedAt_law i⟩
      intro j h
      simp [rejectedAt, actual, realize, h]
    · intro e; exact nomatch e
  dependence := by
    intro i
    let z : Fin 2 := 0
    have hnil : IsAttractor ([] : List (Fin 2)) ∅ := by
      refine ⟨by simp, ?_⟩
      intro a l hl ha; simp only [List.length_nil] at ha; omega
    have hg0 : gamma ([] : List (Fin 2)) = 0 := by
      have h := (attractor_minimum ([] : List (Fin 2))).2.1 ∅ hnil
      simpa using h
    have hs : IsAttractor [z] {0} := by
      refine ⟨by simp, ?_⟩
      intro a l hl ha
      simp only [List.length_singleton] at ha
      have ha0 : a = 0 := by omega
      have hl1 : l = 1 := by omega
      subst a; subst l
      exact ⟨0, 0, by simp, by simp, le_rfl, by omega, rfl⟩
    have hg1 : gamma [z] = 1 := by
      have lo := (attractor_minimum [z]).2.2
      have hi := (attractor_minimum [z]).2.1 {0} hs
      simp only [List.toFinset_cons, List.toFinset_nil] at lo
      simp at lo hi
      omega
    refine ⟨⟨2, fun _ => 1⟩, [], [z], ?_⟩
    simp only [actual, realize, hg0, hg1]
    decide

def selection : _root_.Reg.Support.SourceSelection where
  owner := `D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum
  coordinates := #[0, 2]
  readouts := #[
    {path := #["body", "body", "body", "body", "body", "body", "body", "body",
      "fn", "arg", "body", "body", "body", "body", "fn", "arg"],
      stateOperand := some #["arg"]},
    {path := #["body", "body", "body", "body", "body", "body", "body", "body",
      "arg", "body", "fn", "arg"], stateOperand := some #["arg"]}]


noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Attractors.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ w => gamma.{0} w) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Attractors") "result") "Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum/Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ w => gamma.{0} w) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, definition := none, coordinates := #[0, 2], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "body", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }, { path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `D5.S1.Words.Attractors.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1.canonicalArenaFact, `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1.canonicalObjectArenaFact, `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1.sourceBridgeFact, `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1.observationFact0, `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1.observationFact1, `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1.anchorEnumeration }


#print axioms registration
end
end Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum


universe u
namespace Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits
open TrureTuring.Raney
open _root_.D5.S1.Words.Powers
open _root_.Reg.D5.S1.Words.Attractors.FiniteWordAttractors.HelperAudits
noncomputable section

namespace Fractional
abbrev signature : Signature where
  Params := Nat
  State := fun k => List (Fin k)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ k => List (Fin k)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ w => w.dropLast) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ w => w) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k : Nat} (hk : 2 ≤ k) (c : Fin k → Nat)
    (h0 : 1 ≤ c ⟨0, by omega⟩) (hlast : 1 ≤ c ⟨k - 1, by omega⟩)
    (hcyc : CyclicMaximal c) (n : Nat),
R.readout () k (cyclicWord (by omega) c (n + 1)) <+:
      wordPower (c ⟨0, by omega⟩ + 1) (cyclicWord (by omega) c n)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc : CyclicMaximal (fun _ : Fin 2 => 1) := by
    intro r
    have hd : List.ofFn (cyclicDigit (fun _ : Fin 2 => 1)) = [1,0] := by decide
    rw [hd, ← List.rotate_mod]
    have hr : r % 2 = 0 ∨ r % 2 = 1 := by have := Nat.mod_lt r (by omega : 0 < 2); omega
    simp only [List.length_cons,List.length_nil] at *
    rcases hr with hr | hr <;> rw [hr] <;> decide
  have hh := h (by omega : 2 ≤ 2) (fun _ => 1) (by decide) (by decide) hc 0
  change ([0,1] : List (Fin 2)) <+: [0,0] at hh
  have := hh.getElem (by decide : 1 < ([0,1] : List (Fin 2)).length)
  simp at this

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cyclic_fractional_prefix, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    exact ⟨2, [], [0,0], by cases i; decide⟩

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Attractors.cyclic_fractional_prefix) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ w => w.dropLast) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Attractors") "cyclic_fractional_prefix") "Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum/Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ w => w.dropLast) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `D5.S1.Words.Attractors.cyclic_fractional_prefix, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration_2.canonicalArenaFact, `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration_2.canonicalObjectArenaFact, `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration_2.sourceBridgeFact, `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration_2.observationFact0, `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration_2.anchorEnumeration }



end Fractional

namespace Structure
abbrev signature : Signature where
  Params := Σ k : Nat, {c : Fin k → Nat // 2 ≤ k}
  State := fun _ => Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p n => cyclicLength (by have := p.2.property; omega) p.2.val n) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k : Nat} (hk : 2 ≤ k) (c : Fin k → Nat)
    (h0 : 1 ≤ c ⟨0, by omega⟩) (hlast : 1 ≤ c ⟨k - 1, by omega⟩),
(∀ (n : Nat) (a : Fin k),
      morphismPower (cyclicMorphism (by omega) c) n [a] =
        cyclicInterior (by omega) c n a ++
          [⟨(a.val + n) % k, Nat.mod_lt _ (by omega)⟩]) ∧
    (∀ n, cyclicWord (by omega) c n <+: cyclicWord (by omega) c (n + 1)) ∧
    (∀ n, cyclicLength (by omega) c n < cyclicLength (by omega) c (n + 1)) ∧
    (∀ n, n + 1 ≤ R.readout () ⟨k,⟨c,hk⟩⟩ n) ∧
    (Monotone fun n => cyclicLength (by omega) c (n + 1) - cyclicLength (by omega) c n) ∧
    (∀ (m n : Nat), m ≤ cyclicLength (by omega) c n →
      cyclicPrefix (by omega) c m = (cyclicWord (by omega) c n).take m)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h (by omega : 2 ≤ 2) (fun _ => 1) (by decide) (by decide)).2.2.2.1 0
  change 0+1 ≤ 0 at hh
  exact Nat.not_succ_le_zero 0 hh

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cyclic_iterate_structure, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    exact ⟨⟨2,⟨fun _ => 1,by omega⟩⟩,0,1,by cases i; decide⟩

noncomputable def registration_3 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Attractors.cyclic_iterate_structure) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ p n => cyclicLength (by have := p.2.property; omega) p.2.val n) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Attractors") "cyclic_iterate_structure") "Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum/Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ p n => cyclicLength (by have := p.2.property; omega) p.2.val n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, definition := none, coordinates := #[0, 1, 2], readouts := #[{ path := #["body", "body", "body", "body", "body", "arg", "arg", "arg", "fn", "arg", "body", "arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `D5.S1.Words.Attractors.cyclic_iterate_structure, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration_3.canonicalArenaFact, `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration_3.canonicalObjectArenaFact, `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration_3.sourceBridgeFact, `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration_3.descriptorFact] },
  exclusion := some `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration_3.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration_3.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration_3.anchorEnumeration }



end Structure

namespace Recurrence
abbrev signature : Signature where
  Params := Σ k : Nat, {c : Fin k → Nat // 2 ≤ k}
  State := fun _ => Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ p => List (Fin p.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p n => cyclicWord (by have := p.2.property; omega) p.2.val n) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => []) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k : Nat} (hk : 2 ≤ k) (c : Fin k → Nat)
    (h0 : 1 ≤ c ⟨0, by omega⟩) (hlast : 1 ≤ c ⟨k - 1, by omega⟩),
(∀ (n : Nat) (hn : n < k), R.readout () ⟨k,⟨c,hk⟩⟩ n =
      cyclicBlockProduct (by omega) c n n hn.le ++ [⟨n, hn⟩]) ∧
    (∀ (n : Nat), k ≤ n → cyclicWord (by omega) c n =
      cyclicBlockProduct (by omega) c n k le_rfl)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h (by omega : 2 ≤ 2) (fun _ => 1) (by decide) (by decide)).1 0 (by omega)
  change ([] : List (Fin 2)) = [0] at hh
  simp at hh

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cyclic_word_recurrence, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    exact ⟨⟨2,⟨fun _ => 1,by omega⟩⟩,0,1,by cases i; decide⟩

noncomputable def registration_4 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S1.Words.Attractors.cyclic_word_recurrence) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ p n => cyclicWord (by have := p.2.property; omega) p.2.val n) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S1") "Words") "Attractors") "cyclic_word_recurrence") "Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum/Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ p n => cyclicWord (by have := p.2.property; omega) p.2.val n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, definition := none, coordinates := #[0, 1, 2], readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "arg", "body", "body", "fn", "arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `D5.S1.Words.Attractors.cyclic_word_recurrence, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration_4.canonicalArenaFact, `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration_4.canonicalObjectArenaFact, `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration_4.sourceBridgeFact, `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration_4.descriptorFact] },
  exclusion := some `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration_4.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration_4.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration_4.anchorEnumeration }



end Recurrence

end
end Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits


noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.arena
noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.arena
noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration_3.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.arena
noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration_3.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"HelperAudits\",\"Structure\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"HelperAudits\",\"Structure\",\"registration_3\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration_3.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration_3.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.arena
noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration_3.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"HelperAudits\",\"Structure\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"HelperAudits\",\"Structure\",\"registration_3\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration_3.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration_2.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.arena
noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration_2.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"HelperAudits\",\"Fractional\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"HelperAudits\",\"Fractional\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration_2.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.arena
noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration_2.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"HelperAudits\",\"Fractional\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"HelperAudits\",\"Fractional\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration_4.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.arena
noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration_4.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"HelperAudits\",\"Recurrence\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"HelperAudits\",\"Recurrence\",\"registration_4\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration_4.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration_4.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.arena
noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration_4.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"HelperAudits\",\"Recurrence\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"HelperAudits\",\"Recurrence\",\"registration_4\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration_4.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.arena) (Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration).actual

noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Attractors\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `D5.S1.Words.Attractors.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration).bridge

noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) where
  values := [(fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => i)
  (@Fin.mk (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 0)
    (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (Nat.le_refl (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))), (fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => i)
  (@Fin.mk (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
    (Nat.le_refl (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1.observation0 : {k : Nat} →
  (hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k) →
    (c : Fin k → Nat) →
      (h0 :
          @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (c
              (@Fin.mk k (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@Decidable.byContradiction
                  (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                  (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                  fun
                    (a :
                      Not (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)) =>
                  @D5.S1.Words.Attractors.cyclic_iterate_structure._proof_1 k hk a)))) →
        (hlast :
            @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (c
                (@Fin.mk k
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@Decidable.byContradiction
                    (@LT.lt.{0} Nat instLTNat
                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      k)
                    (Nat.decLt
                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      k)
                    fun
                      (a :
                        Not
                          (@LT.lt.{0} Nat instLTNat
                            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            k)) =>
                    @D5.S1.Words.Attractors.cyclic_iterate_structure._proof_2 k hk c a)))) →
          (hcyc : @D5.S1.Words.Attractors.CyclicMaximal k c) →
            (m : Nat) →
              @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m →
                (i : Nat) →
                  @LE.le.{0} Nat instLENat i
                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
                    @LE.le.{0} Nat instLENat
                        (@D5.S1.Words.Attractors.cyclicLength k
                          (@Decidable.byContradiction
                            (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                            (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                            fun
                              (a :
                                Not
                                  (@LT.lt.{0} Nat instLTNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)) =>
                            @D5.S1.Words.Attractors.cyclic_iterate_structure._proof_3 k hk c a)
                          c i)
                        m →
                      @LT.lt.{0} Nat instLTNat m
                          (@D5.S1.Words.Attractors.cyclicLength k
                            (@Decidable.byContradiction
                              (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                              (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                              fun
                                (a :
                                  Not
                                    (@LT.lt.{0} Nat instLTNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)) =>
                              @D5.S1.Words.Attractors.cyclic_iterate_structure._proof_3 k hk c a)
                            c
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                          Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.signature
                          ((fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => i)
                            (@Fin.mk (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 0)
                              (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                (Nat.le_refl (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                          (@Sigma.mk.{0, 0} Nat (fun (k : Nat) => Fin k → Nat) k c) :=
  fun {k : Nat} (hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)
    (c : Fin k → Nat)
    (h0 :
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (c
          (@Fin.mk k (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@Decidable.byContradiction
              (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
              (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
              fun
                (a : Not (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)) =>
              @D5.S1.Words.Attractors.cyclic_iterate_structure._proof_1 k hk a))))
    (hlast :
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (c
          (@Fin.mk k
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@Decidable.byContradiction
              (@LT.lt.{0} Nat instLTNat
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                k)
              (Nat.decLt
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                k)
              fun
                (a :
                  Not
                    (@LT.lt.{0} Nat instLTNat
                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      k)) =>
              @D5.S1.Words.Attractors.cyclic_iterate_structure._proof_2 k hk c a))))
    (hcyc : @D5.S1.Words.Attractors.CyclicMaximal k c) (m : Nat)
    (a : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m) (i : Nat)
    (a_1 :
      @LE.le.{0} Nat instLENat i
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (a_2 :
      @LE.le.{0} Nat instLENat
        (@D5.S1.Words.Attractors.cyclicLength k
          (@Decidable.byContradiction
            (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
            (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
            fun (a : Not (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)) =>
            @D5.S1.Words.Attractors.cyclic_iterate_structure._proof_3 k hk c a)
          c i)
        m)
    (a_3 :
      @LT.lt.{0} Nat instLTNat m
        (@D5.S1.Words.Attractors.cyclicLength k
          (@Decidable.byContradiction
            (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
            (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
            fun (a : Not (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)) =>
            @D5.S1.Words.Attractors.cyclic_iterate_structure._proof_3 k hk c a)
          c
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.signature
    Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.actual
    ((fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => i)
      (@Fin.mk (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 0)
        (@Nat.le_of_lt (nat_lit 1) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (Nat.le_refl (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    (@Sigma.mk.{0, 0} Nat (fun (k : Nat) => Fin k → Nat) k c)
    (@D5.S1.Words.Attractors.cyclicPrefix k
      (@Decidable.byContradiction
        (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
        (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
        fun (a : Not (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)) =>
        @D5.S1.Words.Attractors.cyclic_iterate_structure._proof_3 k hk c a)
      c m)

noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Attractors\",\"result\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `D5.S1.Words.Attractors.result, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .function, .argument, .body, .body, .body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1.observation1 : {k : Nat} →
  (hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k) →
    (c : Fin k → Nat) →
      (h0 :
          @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (c
              (@Fin.mk k (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@Decidable.byContradiction
                  (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                  (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                  fun
                    (a :
                      Not (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)) =>
                  @D5.S1.Words.Attractors.cyclic_iterate_structure._proof_1 k hk a)))) →
        (hlast :
            @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (c
                (@Fin.mk k
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@Decidable.byContradiction
                    (@LT.lt.{0} Nat instLTNat
                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      k)
                    (Nat.decLt
                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      k)
                    fun
                      (a :
                        Not
                          (@LT.lt.{0} Nat instLTNat
                            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            k)) =>
                    @D5.S1.Words.Attractors.cyclic_iterate_structure._proof_2 k hk c a)))) →
          (hcyc : @D5.S1.Words.Attractors.CyclicMaximal k c) →
            (m : Nat) →
              @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m →
                @LE.le.{0} Nat instLENat
                    (@D5.S1.Words.Attractors.cyclicLength k
                      (@Decidable.byContradiction
                        (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                        (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                        fun
                          (a :
                            Not
                              (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                k)) =>
                        @D5.S1.Words.Attractors.cyclic_iterate_structure._proof_3 k hk c a)
                      c
                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    m →
                  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                    Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.signature
                    ((fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => i)
                      (@Fin.mk (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
                        (Nat.le_refl (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                    (@Sigma.mk.{0, 0} Nat (fun (k : Nat) => Fin k → Nat) k c) :=
  fun {k : Nat} (hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)
    (c : Fin k → Nat)
    (h0 :
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (c
          (@Fin.mk k (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@Decidable.byContradiction
              (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
              (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
              fun
                (a : Not (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)) =>
              @D5.S1.Words.Attractors.cyclic_iterate_structure._proof_1 k hk a))))
    (hlast :
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (c
          (@Fin.mk k
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@Decidable.byContradiction
              (@LT.lt.{0} Nat instLTNat
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                k)
              (Nat.decLt
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                k)
              fun
                (a :
                  Not
                    (@LT.lt.{0} Nat instLTNat
                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      k)) =>
              @D5.S1.Words.Attractors.cyclic_iterate_structure._proof_2 k hk c a))))
    (hcyc : @D5.S1.Words.Attractors.CyclicMaximal k c) (m : Nat)
    (a : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m)
    (a_1 :
      @LE.le.{0} Nat instLENat
        (@D5.S1.Words.Attractors.cyclicLength k
          (@Decidable.byContradiction
            (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
            (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
            fun (a : Not (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)) =>
            @D5.S1.Words.Attractors.cyclic_iterate_structure._proof_3 k hk c a)
          c
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        m) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.signature
    Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.actual
    ((fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => i)
      (@Fin.mk (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (nat_lit 1)
        (Nat.le_refl (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@Sigma.mk.{0, 0} Nat (fun (k : Nat) => Fin k → Nat) k c)
    (@D5.S1.Words.Attractors.cyclicPrefix k
      (@Decidable.byContradiction
        (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
        (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
        fun (a : Not (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)) =>
        @D5.S1.Words.Attractors.cyclic_iterate_structure._proof_3 k hk c a)
      c m)

noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1.observationFact1 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Attractors\",\"result\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"registration_1\",\"observation1\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `D5.S1.Words.Attractors.result, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .argument, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1.observation1, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Attractors\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `D5.S1.Words.Attractors.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration).actual (Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration).variation.2.choose (Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration).variation.1 (Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration_3.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.arena) (Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration).actual

noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration_3.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Attractors\",\"cyclic_iterate_structure\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"HelperAudits\",\"Structure\",\"registration_3\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `D5.S1.Words.Attractors.cyclic_iterate_structure, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration_3.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration).bridge

noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration_3.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration_3.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration_3.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration_3.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration_3.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"HelperAudits\",\"Structure\",\"registration_3\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration_3.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"HelperAudits\",\"Structure\",\"registration_3\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Attractors\",\"cyclic_iterate_structure\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration_3.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `D5.S1.Words.Attractors.cyclic_iterate_structure, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration).actual (Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration).variation.2.choose (Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration).variation.1 (Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration_3.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"HelperAudits\",\"Structure\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"HelperAudits\",\"Structure\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Structure.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration_2.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.arena) (Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration).actual

noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration_2.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Attractors\",\"cyclic_fractional_prefix\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"HelperAudits\",\"Fractional\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `D5.S1.Words.Attractors.cyclic_fractional_prefix, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration_2.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration).bridge

noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration_2.observation0 : {k : Nat} →
  (hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k) →
    (c : Fin k → Nat) →
      (h0 :
          @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (c
              (@Fin.mk k (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@Decidable.byContradiction
                  (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                  (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
                  fun
                    (a :
                      Not (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)) =>
                  @D5.S1.Words.Attractors.cyclic_iterate_structure._proof_1 k hk a)))) →
        (hlast :
            @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (c
                (@Fin.mk k
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@Decidable.byContradiction
                    (@LT.lt.{0} Nat instLTNat
                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      k)
                    (Nat.decLt
                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      k)
                    fun
                      (a :
                        Not
                          (@LT.lt.{0} Nat instLTNat
                            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            k)) =>
                    @D5.S1.Words.Attractors.cyclic_iterate_structure._proof_2 k hk c a)))) →
          (hcyc : @D5.S1.Words.Attractors.CyclicMaximal k c) →
            (n : Nat) →
              D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.signature
                PUnit.unit.{1} k :=
  fun {k : Nat} (hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)
    (c : Fin k → Nat)
    (h0 :
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (c
          (@Fin.mk k (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@Decidable.byContradiction
              (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
              (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
              fun
                (a : Not (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)) =>
              @D5.S1.Words.Attractors.cyclic_iterate_structure._proof_1 k hk a))))
    (hlast :
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (c
          (@Fin.mk k
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@Decidable.byContradiction
              (@LT.lt.{0} Nat instLTNat
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                k)
              (Nat.decLt
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                k)
              fun
                (a :
                  Not
                    (@LT.lt.{0} Nat instLTNat
                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      k)) =>
              @D5.S1.Words.Attractors.cyclic_iterate_structure._proof_2 k hk c a))))
    (hcyc : @D5.S1.Words.Attractors.CyclicMaximal k c) (n : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.signature
    Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.actual PUnit.unit.{1} k
    (@D5.S1.Words.Attractors.cyclicWord k
      (@Decidable.byContradiction
        (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
        (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
        fun (a : Not (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)) =>
        @D5.S1.Words.Attractors.cyclic_iterate_structure._proof_3 k hk c a)
      c
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))

noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration_2.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Attractors\",\"cyclic_fractional_prefix\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"HelperAudits\",\"Fractional\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `D5.S1.Words.Attractors.cyclic_fractional_prefix, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration_2.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration_2.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration_2.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration_2.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"HelperAudits\",\"Fractional\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration_2.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"HelperAudits\",\"Fractional\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Attractors\",\"cyclic_fractional_prefix\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration_2.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `D5.S1.Words.Attractors.cyclic_fractional_prefix, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration).actual (Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration).variation.2.choose (Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration).variation.1 (Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration_2.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"HelperAudits\",\"Fractional\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"HelperAudits\",\"Fractional\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Fractional.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration_4.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.arena) (Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration).actual

noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration_4.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Attractors\",\"cyclic_word_recurrence\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"HelperAudits\",\"Recurrence\",\"registration_4\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `D5.S1.Words.Attractors.cyclic_word_recurrence, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration_4.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration).bridge

noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration_4.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration_4.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration_4.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration_4.canonicalArenaOperand)
noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration_4.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"HelperAudits\",\"Recurrence\",\"registration_4\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration_4.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"HelperAudits\",\"Recurrence\",\"registration_4\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S1\",\"Words\",\"Attractors\",\"cyclic_word_recurrence\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration_4.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `D5.S1.Words.Attractors.cyclic_word_recurrence, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration).actual (Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration).variation.2.choose (Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration).variation.1 (Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration).variation.2.choose_spec

noncomputable def Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration_4.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"HelperAudits\",\"Recurrence\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Attractors\",\"CyclicMorphismAttractorMinimum\",\"HelperAudits\",\"Recurrence\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum, declaration := `Reg.D5.S1.Words.Attractors.CyclicMorphismAttractorMinimum.HelperAudits.Recurrence.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
