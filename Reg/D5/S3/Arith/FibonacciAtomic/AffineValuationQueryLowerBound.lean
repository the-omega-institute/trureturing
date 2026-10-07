import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound
import Reg.Support.DependentFamily

set_option autoImplicit false
open _root_.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound
open _root_.D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound

abbrev signature : Signature where
  Params := (p : ℕ) × (e : ℕ) × (d : ℕ) ×
    PassiveProtocol (AffineQuery p e d) (fun _ => ℕ)
  State k := Point k.1 k.2.1 k.2.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ k x =>
      (runPassiveProtocol (affineReadout k.1 k.2.1 k.2.2.1) k.2.2.2 x).length)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (p e d : ℕ) (hp : p.Prime) (he : 1 ≤ e) (hd : 1 ≤ d),
    (∀ T : PassiveProtocol (AffineQuery p e d) (fun _ => ℕ),
      Function.Injective (runPassiveProtocol (affineReadout p e d) T) →
      ∃ x : Point p e d, d * e * (p - 1) ≤ R.readout () ⟨p, e, d, T⟩ x) ∧
    (∀ (policy : List (Sigma (fun _ : AffineQuery p e d => ℕ)) →
        Sum (AffineQuery p e d) (Point p e d))
      (trace : Point p e d → List (Sigma (fun _ : AffineQuery p e d => ℕ)))
      (fuel : Point p e d → ℕ),
      (∀ x, _root_.D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization.execute
        (affineReadout p e d) policy (fuel x) [] x = some (trace x, x)) →
      ∃ x : Point p e d, d * e * (p - 1) ≤ (trace x).length)

def binaryTree : PassiveProtocol (AffineQuery 2 1 1) (fun _ => ℕ) :=
  .query ((fun _ => 1), 0) (fun _ => .stop)

theorem binary_identifies :
    Function.Injective (runPassiveProtocol (affineReadout 2 1 1) binaryTree) := by
  decide

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨x, bad⟩ := (h 2 1 1 (by norm_num) (by decide) (by decide)).1
    binaryTree binary_identifies
  norm_num [rejected, realize] at bad

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨affine_valuation_query_lower_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    let T : PassiveProtocol (AffineQuery 2 1 1) (fun _ => ℕ) :=
      .query ((fun _ => 1), 0) (fun r => if r = 1 then .stop else binaryTree)
    refine ⟨⟨2, 1, 1, T⟩, (0 : Point 2 1 1), (1 : Point 2 1 1), ?_⟩
    have zeroResponse : affineReadout 2 1 1 ((fun _ => 1), 0)
        (0 : Point 2 1 1) = 1 := by
      norm_num [affineReadout, affineValue,
        _root_.D5.S3.Observer.Budget.ResidueLeafOptimality.residueReadout,
        Fin.sum_univ_one, Finset.range_add_one, ZMod.val_one_eq_one_mod]
    have oneResponse : affineReadout 2 1 1 ((fun _ => 1), 0)
        (1 : Point 2 1 1) = 0 := by
      norm_num [affineReadout, affineValue,
        _root_.D5.S3.Observer.Budget.ResidueLeafOptimality.residueReadout,
        Fin.sum_univ_one, Finset.range_add_one, ZMod.val_one_eq_one_mod]
    change (runPassiveProtocol (affineReadout 2 1 1) T 0).length ≠
      (runPassiveProtocol (affineReadout 2 1 1) T 1).length
    simp [T, binaryTree, runPassiveProtocol, zeroResponse, oneResponse]

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.affine_valuation_query_lower_bound) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ k x =>
      (runPassiveProtocol.{0, 0, 0} (affineReadout k.1 k.2.1 k.2.2.1) k.2.2.2 x).length)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "FibonacciAtomic") "AffineValuationQueryLowerBound") "affine_valuation_query_lower_bound") "Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound/Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration,
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
    (fun _ k x =>
      (runPassiveProtocol.{0, 0, 0} (affineReadout k.1 k.2.1 k.2.2.1) k.2.2.2 x).length)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound, definition := none, coordinates := #[0, 1, 2, 6], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "body", "body", "arg", "body", "arg"], stateBinder := 8, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound, declaration := `D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.affine_valuation_query_lower_bound, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration_1.observationFact0, `Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound


noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.arena
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"AffineValuationQueryLowerBound\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"AffineValuationQueryLowerBound\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.arena
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"AffineValuationQueryLowerBound\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"AffineValuationQueryLowerBound\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.arena) (Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration).actual

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"AffineValuationQueryLowerBound\",\"affine_valuation_query_lower_bound\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"AffineValuationQueryLowerBound\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound, declaration := `D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.affine_valuation_query_lower_bound, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration).bridge

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration_1.observation0 : (p e d : Nat) →
  (hp : Nat.Prime p) →
    (he : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) e) →
      (hd : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) d) →
        (T :
            D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound.PassiveProtocol.{0, 0}
              (D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.AffineQuery p e d)
              fun (x : D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.AffineQuery p e d) => Nat) →
          @Function.Injective.{1, 1} (D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.Point p e d)
              (List.{0}
                (@Sigma.{0, 0} (D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.AffineQuery p e d)
                  fun (experiment : D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.AffineQuery p e d) =>
                  Nat))
              (@D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound.runPassiveProtocol.{0, 0, 0}
                (D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.AffineQuery p e d)
                (fun (experiment : D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.AffineQuery p e d) => Nat)
                (D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.Point p e d)
                (D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.affineReadout p e d) T) →
            (x : D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.Point p e d) →
              D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.signature PUnit.unit.{1}
                (@Sigma.mk.{0, 0} Nat
                  (fun (p : Nat) =>
                    @Sigma.{0, 0} Nat fun (e : Nat) =>
                      @Sigma.{0, 0} Nat fun (d : Nat) =>
                        D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound.PassiveProtocol.{0, 0}
                          (D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.AffineQuery p e d)
                          fun (x : D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.AffineQuery p e d) => Nat)
                  p
                  (@Sigma.mk.{0, 0} Nat
                    (fun (e : Nat) =>
                      @Sigma.{0, 0} Nat fun (d : Nat) =>
                        D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound.PassiveProtocol.{0, 0}
                          (D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.AffineQuery p e d)
                          fun (x : D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.AffineQuery p e d) => Nat)
                    e
                    (@Sigma.mk.{0, 0} Nat
                      (fun (d : Nat) =>
                        D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound.PassiveProtocol.{0, 0}
                          (D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.AffineQuery p e d)
                          fun (x : D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.AffineQuery p e d) => Nat)
                      d T))) :=
  fun (p e d : Nat) (hp : Nat.Prime p)
    (he : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) e)
    (hd : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) d)
    (T :
      D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound.PassiveProtocol.{0, 0}
        (D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.AffineQuery p e d)
        fun (x : D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.AffineQuery p e d) => Nat)
    (a :
      @Function.Injective.{1, 1} (D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.Point p e d)
        (List.{0}
          (@Sigma.{0, 0} (D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.AffineQuery p e d)
            fun (experiment : D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.AffineQuery p e d) => Nat))
        (@D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound.runPassiveProtocol.{0, 0, 0}
          (D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.AffineQuery p e d)
          (fun (experiment : D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.AffineQuery p e d) => Nat)
          (D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.Point p e d)
          (D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.affineReadout p e d) T))
    (x : D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.Point p e d) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.signature
    Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat
      (fun (p : Nat) =>
        @Sigma.{0, 0} Nat fun (e : Nat) =>
          @Sigma.{0, 0} Nat fun (d : Nat) =>
            D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound.PassiveProtocol.{0, 0}
              (D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.AffineQuery p e d)
              fun (x : D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.AffineQuery p e d) => Nat)
      p
      (@Sigma.mk.{0, 0} Nat
        (fun (e : Nat) =>
          @Sigma.{0, 0} Nat fun (d : Nat) =>
            D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound.PassiveProtocol.{0, 0}
              (D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.AffineQuery p e d)
              fun (x : D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.AffineQuery p e d) => Nat)
        e
        (@Sigma.mk.{0, 0} Nat
          (fun (d : Nat) =>
            D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound.PassiveProtocol.{0, 0}
              (D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.AffineQuery p e d)
              fun (x : D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.AffineQuery p e d) => Nat)
          d T)))
    x

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"AffineValuationQueryLowerBound\",\"affine_valuation_query_lower_bound\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"body\",\"body\",\"argument\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"AffineValuationQueryLowerBound\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound, declaration := `D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.affine_valuation_query_lower_bound, part := .type, path := [.body, .body, .body, .body, .body, .body, .function, .argument, .body, .body, .argument, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"AffineValuationQueryLowerBound\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"AffineValuationQueryLowerBound\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"AffineValuationQueryLowerBound\",\"affine_valuation_query_lower_bound\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound, declaration := `D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.affine_valuation_query_lower_bound, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration).actual (Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration).variation.2.choose (Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration).variation.1 (Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"AffineValuationQueryLowerBound\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"AffineValuationQueryLowerBound\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.AffineValuationQueryLowerBound.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
