import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.SamplingQuotient
import Reg.Support.DependentFamily

open Matrix
open _root_.D5.S3.Arith.FibonacciAtomic.TimeSampling
open _root_.D5.S3.Arith.FibonacciAtomic.SamplingQuotient
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient

@[reducible] def signature : Signature where
  Params := Σ _n : ℕ, Σ m : ℕ, Fin m → ℕ
  State p := ZMod p.1 × ZMod p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin p.2.1 → ZMod p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x i => readout p.1 (p.2.2 i) x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (n m : ℕ) (hn : 0 < n) (hm : 2 ≤ m)
    (t : Fin m → ℕ) (ht : StrictMono t),
    let M (N : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod N) := !![0, 1; 1, 1]
    let S (N : ℕ) : ZMod N × ZMod N → ZMod N × ZMod N :=
      fun x => (x.2, x.1 + x.2)
    let i0 : Fin m := ⟨0, by omega⟩
    let s := t i0
    let g := (Finset.univ.erase i0).gcd (fun i => t i - s)
    let O := R.readout () ⟨n, m, t⟩
    (∀ x j, readout n (s + (j + 2) * g) x =
      (M n ^ g).trace * readout n (s + (j + 1) * g) x -
        (-1 : ZMod n) ^ g * readout n (s + j * g) x) ∧
    (∀ z, (O z = 0 ↔ readout n s z = 0 ∧ readout n (s + g) z = 0) ∧
      (O z = 0 ↔ ((S n)^[s] z).2 = 0 ∧
        (Nat.fib g : ZMod n) * ((S n)^[s] z).1 = 0)) ∧
    (∀ x y, O x = O y ↔
      ∀ j : ℕ, readout n (s + j * g) x = readout n (s + j * g) y) ∧
    (∀ Φ : (Fin m → ZMod n) → (Fin m → ZMod n),
      (∀ x, O (S n x) = Φ (O x)) → ∀ z, O z = 0 → O (S n z) = 0) ∧
    Function.Injective (fun x => (readout n s x, readout n (s + 1) x)) ∧
    (!![(Nat.fib s : ZMod n), Nat.fib (s + 1);
      Nat.fib (s + 1), Nat.fib (s + 2)] : Matrix (Fin 2) (Fin 2) (ZMod n)).det =
        (-1 : ZMod n) ^ (s + 1) ∧
    ((∃ z, z ≠ 0 ∧ O z = 0) →
      ¬ ∃ Φ : (Fin m → ZMod n) → (Fin m → ZMod n),
        ∀ x, O (S n x) = Φ (O x)) ∧
    (M 3 ^ 4 = (2 : ZMod 3) • (1 : Matrix (Fin 2) (Fin 2) (ZMod 3))) ∧
    (∀ (j : ℕ) (x : ZMod 3 × ZMod 3), readout 3 (4 * j) x = 2 ^ j * x.2) ∧
    (∀ (j : ℕ) (x : ZMod 3 × ZMod 3),
      readout 3 (8 * j) x = x.2 ∧ readout 3 (8 * j + 4) x = 2 * x.2) ∧
    (∀ j : ℕ, readout 3 (4 * j) (0, 0) = readout 3 (4 * j) (1, 0)) ∧
    readout 3 1 (0, 0) = 0 ∧ readout 3 1 (1, 0) = 1 ∧
    (0 : ZMod 3) ≠ 1 ∧
    (let O4 := fun x : ZMod 3 × ZMod 3 => ![readout 3 0 x, readout 3 4 x]
     (∃ Ψ : (Fin 2 → ZMod 3) → (Fin 2 → ZMod 3),
       ∀ x, O4 ((S 3)^[4] x) = Ψ (O4 x)) ∧
     (¬ ∃ Φ : (Fin 2 → ZMod 3) → (Fin 2 → ZMod 3),
       ∀ x, O4 (S 3 x) = Φ (O4 x)) ∧
     ¬ ((∃ Ψ : (Fin 2 → ZMod 3) → (Fin 2 → ZMod 3),
          ∀ x, O4 ((S 3)^[4] x) = Ψ (O4 x)) →
        ∃ Φ : (Fin 2 → ZMod 3) → (Fin 2 → ZMod 3),
          ∀ x, O4 (S 3 x) = Φ (O4 x)))

theorem actual_law : arena.Law actual := sampling_quotient

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ht : StrictMono (fun i : Fin 2 => i.val) := fun _ _ h => h
  have bad := ((h 2 2 (by omega) (by omega) (fun i => i.val) ht).2.1
    (1, 0)).1.mp rfl
  have hb := bad.2
  have he : Finset.univ.erase (0 : Fin 2) = {1} := by decide
  norm_num [readout, he] at hb

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨2, 2, fun j => j.val⟩, (0, 0), (1, 0), ?_⟩
    cases i
    decide

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.sampling_quotient) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ p x i => readout p.1 (p.2.2 i) x) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "FibonacciAtomic") "SamplingQuotient") "sampling_quotient") "Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient/Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration,
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
    (fun _ p x i => readout p.1 (p.2.2 i) x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.FibonacciAtomic.SamplingQuotient, definition := none, coordinates := #[0, 1, 4], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "value"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.FibonacciAtomic.SamplingQuotient, declaration := `D5.S3.Arith.FibonacciAtomic.SamplingQuotient.sampling_quotient, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration_1.observationFact0, `Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient


noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.arena
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"SamplingQuotient\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"SamplingQuotient\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.arena
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"SamplingQuotient\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"SamplingQuotient\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.arena Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.actual)
    Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration)

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"SamplingQuotient\",\"sampling_quotient\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"SamplingQuotient\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.SamplingQuotient, declaration := `D5.S3.Arith.FibonacciAtomic.SamplingQuotient.sampling_quotient, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.arena Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.actual)
  Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration)

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration_1.observation0 : (n m : Nat) →
  (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) →
    (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m) →
      (t : Fin m → Nat) →
        (ht :
            @StrictMono.{0, 0} (Fin m) Nat (@PartialOrder.toPreorder.{0} (Fin m) (@Fin.instPartialOrder m))
              Nat.instPreorder t) →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
              Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.signature
              (@Sigma.mk.{0, 0} Nat (fun (_n : Nat) => @Sigma.{0, 0} Nat fun (m : Nat) => Fin m → Nat) n
                (@Sigma.mk.{0, 0} Nat (fun (m : Nat) => Fin m → Nat) m t)) →
            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.signature PUnit.unit.{1}
              (@Sigma.mk.{0, 0} Nat (fun (_n : Nat) => @Sigma.{0, 0} Nat fun (m : Nat) => Fin m → Nat) n
                (@Sigma.mk.{0, 0} Nat (fun (m : Nat) => Fin m → Nat) m t)) :=
  fun (n m : Nat) (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
    (hm : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m) (t : Fin m → Nat)
    (ht :
      @StrictMono.{0, 0} (Fin m) Nat (@PartialOrder.toPreorder.{0} (Fin m) (@Fin.instPartialOrder m)) Nat.instPreorder
        t) =>
  have M :
    (N : Nat) →
      Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod N) :=
    fun (N : Nat) =>
    @DFunLike.coe.{1, 1, 1}
      (Equiv.{1, 1}
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
          Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod N)
        (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod N)))
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
        Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod N)
      (fun
          (x :
            Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
              Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod N) =>
        Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod N))
      (@EquivLike.toFunLike.{1, 1, 1}
        (Equiv.{1, 1}
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
            Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod N)
          (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod N)))
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
          Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod N)
        (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod N))
        (@Equiv.instEquivLike.{1, 1}
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
            Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod N)
          (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod N))))
      (@Matrix.of.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod N))
      (@Matrix.vecCons.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod N)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@Matrix.vecCons.{0} (ZMod N) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@OfNat.ofNat.{0} (ZMod N) (nat_lit 0)
            (@Zero.toOfNat0.{0} (ZMod N)
              (@MulZeroClass.toZero.{0} (ZMod N)
                (@instMulZeroClassOfSemiring.{0} (ZMod N)
                  (@CommSemiring.toSemiring.{0} (ZMod N) (@CommRing.toCommSemiring.{0} (ZMod N) (ZMod.commRing N)))))))
          (@Matrix.vecCons.{0} (ZMod N) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@OfNat.ofNat.{0} (ZMod N) (nat_lit 1)
              (@One.toOfNat1.{0} (ZMod N)
                (@AddMonoidWithOne.toOne.{0} (ZMod N)
                  (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod N)
                    (@Ring.toAddGroupWithOne.{0} (ZMod N) (@CommRing.toRing.{0} (ZMod N) (ZMod.commRing N)))))))
            (@Matrix.vecEmpty.{0} (ZMod N))))
        (@Matrix.vecCons.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod N)
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@Matrix.vecCons.{0} (ZMod N) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@OfNat.ofNat.{0} (ZMod N) (nat_lit 1)
              (@One.toOfNat1.{0} (ZMod N)
                (@AddMonoidWithOne.toOne.{0} (ZMod N)
                  (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod N)
                    (@Ring.toAddGroupWithOne.{0} (ZMod N) (@CommRing.toRing.{0} (ZMod N) (ZMod.commRing N)))))))
            (@Matrix.vecCons.{0} (ZMod N) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat.{0} (ZMod N) (nat_lit 1)
                (@One.toOfNat1.{0} (ZMod N)
                  (@AddMonoidWithOne.toOne.{0} (ZMod N)
                    (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod N)
                      (@Ring.toAddGroupWithOne.{0} (ZMod N) (@CommRing.toRing.{0} (ZMod N) (ZMod.commRing N)))))))
              (@Matrix.vecEmpty.{0} (ZMod N))))
          (@Matrix.vecEmpty.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod N))));
  have S : (N : Nat) → Prod.{0, 0} (ZMod N) (ZMod N) → Prod.{0, 0} (ZMod N) (ZMod N) :=
    fun (N : Nat) (x : Prod.{0, 0} (ZMod N) (ZMod N)) =>
    @Prod.mk.{0, 0} (ZMod N) (ZMod N) (@Prod.snd.{0, 0} (ZMod N) (ZMod N) x)
      (@HAdd.hAdd.{0, 0, 0} (ZMod N) (ZMod N) (ZMod N)
        (@instHAdd.{0} (ZMod N)
          (@Distrib.toAdd.{0} (ZMod N)
            (@instDistribOfSemiring.{0} (ZMod N)
              (@CommSemiring.toSemiring.{0} (ZMod N) (@CommRing.toCommSemiring.{0} (ZMod N) (ZMod.commRing N))))))
        (@Prod.fst.{0, 0} (ZMod N) (ZMod N) x) (@Prod.snd.{0, 0} (ZMod N) (ZMod N) x));
  have i0 : Fin m :=
    @Fin.mk m (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@Decidable.byContradiction
        (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m)
        (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m)
        fun (a : Not (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m)) =>
        D5.S3.Arith.FibonacciAtomic.SamplingQuotient.sampling_quotient._proof_1 n m hm a);
  have s : Nat := t i0;
  have g : Nat :=
    @Finset.gcd.{0, 0} Nat (Fin m) Nat.instCommMonoidWithZero
      (@instNormalizedGCDMonoidOfStrongNormalizedGCDMonoid.{0} Nat Nat.instCommMonoidWithZero
        instStrongNormalizedGCDMonoidNat)
      (@Finset.erase.{0} (Fin m) (instDecidableEqFin m) (@Finset.univ.{0} (Fin m) (Fin.fintype m)) i0)
      fun (i : Fin m) => @HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (t i) s;
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.signature Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.actual
    PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat (fun (_n : Nat) => @Sigma.{0, 0} Nat fun (m : Nat) => Fin m → Nat) n
      (@Sigma.mk.{0, 0} Nat (fun (m : Nat) => Fin m → Nat) m t))

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"SamplingQuotient\",\"sampling_quotient\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"letBody\",\"letBody\",\"letBody\",\"letBody\",\"letBody\",\"letValue\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"SamplingQuotient\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.SamplingQuotient, declaration := `D5.S3.Arith.FibonacciAtomic.SamplingQuotient.sampling_quotient, part := .type, path := [.body, .body, .body, .body, .body, .body, .letBody, .letBody, .letBody, .letBody, .letBody, .letValue], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"SamplingQuotient\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"SamplingQuotient\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"SamplingQuotient\",\"sampling_quotient\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.FibonacciAtomic.SamplingQuotient, declaration := `D5.S3.Arith.FibonacciAtomic.SamplingQuotient.sampling_quotient, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration).actual (Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration).variation.2.choose (Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration).variation.1 (Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"SamplingQuotient\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"SamplingQuotient\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.SamplingQuotient.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
