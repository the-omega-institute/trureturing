import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.RecordCapacity
import Reg.Support.DependentFamily
import Mathlib.Tactic.NormNum

open _root_.D5.S3.Arith.FibonacciAtomic.RecordCapacity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix

namespace Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity
universe u

abbrev signature : Signature where
  Params := Σ d : ℕ, Σ _p : ℕ, (Fin d → ℕ)
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ t r => t.2.1 ^ (r * Fintype.card (Defect t.2.1 t.2.2)))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law T := (∀ {d p : ℕ} (_hp : p.Prime)
    (B : Matrix (Fin d) (Fin d) ℤ)
    (U V : (Matrix (Fin d) (Fin d) ℤ)ˣ) (s : Fin d → ℕ)
    (_hSmith : U.val * B * V.val = diagonal (fun i => (s i : ℤ)))
    {R : ℕ → Type u} [∀ r, Fintype (R r)]
    (η : ∀ r, State d p (r + 1) → R r) (ρ : ∀ r, R (r + 1) → R r)
    (_hjoint : ∀ r, Function.Injective (fun x => (action B p (r + 1) x, η r x)))
    (_haut : ∀ r x, ρ r (η (r + 1) x) = η r (reduce p (r + 1) x)),
    (∀ r, Function.Injective (fun x => η r (defectInput V p (r + 1) s x)) ∧
      T.readout () ⟨d, p, s⟩ (r + 1) ≤ Fintype.card (R r)) ∧
    (∀ r, Function.Injective (fun x =>
      (action B p (r + 1) x, canonicalRecord V p (r + 1) s x)) ∧
      Nat.card (Defect p s → ZMod (p ^ (r + 1))) =
        p ^ ((r + 1) * Fintype.card (Defect p s))) ∧
    (∀ r x, reduce p (r + 1) (canonicalRecord V p (r + 2) s x) =
      canonicalRecord V p (r + 1) s (reduce p (r + 1) x))) ∧
    (∀ (q : ℕ) (hq : q.Prime), ScalarRecordExamples.{u} q hq) ∧
    ThreeNodeRecordExamples.{u}

theorem actual_law : arena.{u}.Law actual := by
  exact @autonomous_record_capacity

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hbad := h.1 (d := 0) (p := 2) (by decide) 0 1 1 (fun i => Fin.elim0 i)
    (by ext i; exact Fin.elim0 i) (R := fun _ => ULift.{u} (ZMod 1))
    (fun _ _ => 0) (fun _ _ => 0)
    (fun _ _ _ _ => Subsingleton.elim _ _) (fun _ _ => rfl)
  have hb := (hbad.1 0).2
  norm_num [rejected, realize] at hb

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨1, 2, fun _ => 2⟩, 1, 2, ?_⟩
    norm_num [actual, realize, Defect]

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.FibonacciAtomic.RecordCapacity.autonomous_record_capacity.{u}) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ t r => t.2.1 ^ (r * Fintype.card.{0} (Defect t.2.1 t.2.2)))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "FibonacciAtomic") "RecordCapacity") "autonomous_record_capacity") "Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity/Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u})⟩,
  objectArena := .source ⟨(arena.{u})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u}) ⟨(registration.{u})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ t r => t.2.1 ^ (r * Fintype.card.{0} (Defect t.2.1 t.2.2)))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.FibonacciAtomic.RecordCapacity, definition := none, coordinates := #[0, 1, 6], readouts := #[{ path := #["fn", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg", "fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.FibonacciAtomic.RecordCapacity, declaration := `D5.S3.Arith.FibonacciAtomic.RecordCapacity.autonomous_record_capacity, part := .type, path := [], levels := [.param `u] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u] }], facts := [`Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration_1.observationFact0, `Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity


noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration_1.canonicalArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.arena.{u}
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration_1.canonicalArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"RecordCapacity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"RecordCapacity\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration_1.canonicalObjectArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.arena.{u}
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration_1.canonicalObjectArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"RecordCapacity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"RecordCapacity\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence


noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration_1.sourceLaw.{u} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.arena.{u}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.arena.{u}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.arena.{u} Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.actual)
    Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration.{u})

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration_1.sourceBridgeFact.{u} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"RecordCapacity\",\"autonomous_record_capacity\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"RecordCapacity\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.RecordCapacity, declaration := `D5.S3.Arith.FibonacciAtomic.RecordCapacity.autonomous_record_capacity, part := .type, path := [], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.arena.{u}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.arena.{u} Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.actual)
  Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration.{u})

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration_1.observation0.{u} : {d p : Nat} →
  (hp : Nat.Prime p) →
    (B : Matrix.{0, 0, 0} (Fin d) (Fin d) Int) →
      (U V :
          @Units.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Int)
            (@Semiring.toMonoid.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Int)
              (@Matrix.semiring.{0, 0} (Fin d) Int Int.instSemiring (Fin.fintype d) (instDecidableEqFin d)))) →
        (s : Fin d → Nat) →
          (hSmith :
              @Eq.{1} (Matrix.{0, 0, 0} (Fin d) (Fin d) Int)
                (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Int) (Matrix.{0, 0, 0} (Fin d) (Fin d) Int)
                  (Matrix.{0, 0, 0} (Fin d) (Fin d) Int)
                  (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin d) (Fin d) (Fin d) Int
                    (Fin.fintype d) Int.instMul Int.instAddCommMonoid)
                  (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Int) (Matrix.{0, 0, 0} (Fin d) (Fin d) Int)
                    (Matrix.{0, 0, 0} (Fin d) (Fin d) Int)
                    (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin d) (Fin d) (Fin d) Int
                      (Fin.fintype d) Int.instMul Int.instAddCommMonoid)
                    (@Units.val.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Int)
                      (@Semiring.toMonoid.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Int)
                        (@Matrix.semiring.{0, 0} (Fin d) Int Int.instSemiring (Fin.fintype d) (instDecidableEqFin d)))
                      U)
                    B)
                  (@Units.val.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Int)
                    (@Semiring.toMonoid.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Int)
                      (@Matrix.semiring.{0, 0} (Fin d) Int Int.instSemiring (Fin.fintype d) (instDecidableEqFin d)))
                    V))
                (@Matrix.diagonal.{0, 0} (Fin d) Int (instDecidableEqFin d)
                  (@MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring))
                  fun (i : Fin d) => @Nat.cast.{0} Int instNatCastInt (s i))) →
            {R : Nat → Type u} →
              [(r : Nat) → Fintype.{u} (R r)] →
                (η :
                    (r : Nat) →
                      D5.S3.Arith.FibonacciAtomic.RecordCapacity.State d p
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                        R r) →
                  (ρ :
                      (r : Nat) →
                        R
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                          R r) →
                    (hjoint :
                        ∀ (r : Nat),
                          @Function.Injective.{1, max (u + 1) 1}
                            (D5.S3.Arith.FibonacciAtomic.RecordCapacity.State d p
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                            (Prod.{0, u}
                              (D5.S3.Arith.FibonacciAtomic.RecordCapacity.State d p
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                              (R r))
                            fun
                              (x :
                                D5.S3.Arith.FibonacciAtomic.RecordCapacity.State d p
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                            @Prod.mk.{0, u}
                              (D5.S3.Arith.FibonacciAtomic.RecordCapacity.State d p
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                              (R r)
                              (@DFunLike.coe.{1, 1, 1}
                                (@AddMonoidHom.{0, 0}
                                  (D5.S3.Arith.FibonacciAtomic.RecordCapacity.State d p
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                  (D5.S3.Arith.FibonacciAtomic.RecordCapacity.State d p
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                  (@AddZeroClass.toAddZero.{0}
                                    (D5.S3.Arith.FibonacciAtomic.RecordCapacity.State d p
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                    (@Pi.addZeroClass.{0, 0} (Fin d)
                                      (fun (a : Fin d) =>
                                        ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                      fun (i : Fin d) =>
                                      @AddMonoid.toAddZeroClass.{0}
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                        (@AddMonoidWithOne.toAddMonoid.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                          (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                            (ZMod
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                            (@Ring.toAddGroupWithOne.{0}
                                              (ZMod
                                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                  (@instHPow.{0, 0} Nat Nat
                                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                  p
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                              (@CommRing.toRing.{0}
                                                (ZMod
                                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                    (@instHPow.{0, 0} Nat Nat
                                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                    p
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                                (ZMod.commRing
                                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                    (@instHPow.{0, 0} Nat Nat
                                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                    p
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                        (instOfNatNat (nat_lit 1))))))))))))
                                  (@AddZeroClass.toAddZero.{0}
                                    (D5.S3.Arith.FibonacciAtomic.RecordCapacity.State d p
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                    (@Pi.addZeroClass.{0, 0} (Fin d)
                                      (fun (a : Fin d) =>
                                        ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                      fun (i : Fin d) =>
                                      @AddMonoid.toAddZeroClass.{0}
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                        (@AddMonoidWithOne.toAddMonoid.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                          (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                            (ZMod
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                            (@Ring.toAddGroupWithOne.{0}
                                              (ZMod
                                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                  (@instHPow.{0, 0} Nat Nat
                                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                  p
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                              (@CommRing.toRing.{0}
                                                (ZMod
                                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                    (@instHPow.{0, 0} Nat Nat
                                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                    p
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                                (ZMod.commRing
                                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                    (@instHPow.{0, 0} Nat Nat
                                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                    p
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                        (instOfNatNat (nat_lit 1)))))))))))))
                                (D5.S3.Arith.FibonacciAtomic.RecordCapacity.State d p
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                (fun
                                    (x :
                                      D5.S3.Arith.FibonacciAtomic.RecordCapacity.State d p
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                  D5.S3.Arith.FibonacciAtomic.RecordCapacity.State d p
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                (@AddMonoidHom.instFunLike.{0, 0}
                                  (D5.S3.Arith.FibonacciAtomic.RecordCapacity.State d p
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                  (D5.S3.Arith.FibonacciAtomic.RecordCapacity.State d p
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                  (@AddZeroClass.toAddZero.{0}
                                    (D5.S3.Arith.FibonacciAtomic.RecordCapacity.State d p
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                    (@Pi.addZeroClass.{0, 0} (Fin d)
                                      (fun (a : Fin d) =>
                                        ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                      fun (i : Fin d) =>
                                      @AddMonoid.toAddZeroClass.{0}
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                        (@AddMonoidWithOne.toAddMonoid.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                          (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                            (ZMod
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                            (@Ring.toAddGroupWithOne.{0}
                                              (ZMod
                                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                  (@instHPow.{0, 0} Nat Nat
                                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                  p
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                              (@CommRing.toRing.{0}
                                                (ZMod
                                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                    (@instHPow.{0, 0} Nat Nat
                                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                    p
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                                (ZMod.commRing
                                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                    (@instHPow.{0, 0} Nat Nat
                                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                    p
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                        (instOfNatNat (nat_lit 1))))))))))))
                                  (@AddZeroClass.toAddZero.{0}
                                    (D5.S3.Arith.FibonacciAtomic.RecordCapacity.State d p
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                    (@Pi.addZeroClass.{0, 0} (Fin d)
                                      (fun (a : Fin d) =>
                                        ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                      fun (i : Fin d) =>
                                      @AddMonoid.toAddZeroClass.{0}
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                        (@AddMonoidWithOne.toAddMonoid.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                          (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                            (ZMod
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                            (@Ring.toAddGroupWithOne.{0}
                                              (ZMod
                                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                  (@instHPow.{0, 0} Nat Nat
                                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                  p
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                              (@CommRing.toRing.{0}
                                                (ZMod
                                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                    (@instHPow.{0, 0} Nat Nat
                                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                    p
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                                (ZMod.commRing
                                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                    (@instHPow.{0, 0} Nat Nat
                                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                    p
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                        (instOfNatNat (nat_lit 1)))))))))))))
                                (@D5.S3.Arith.FibonacciAtomic.RecordCapacity.action d B p
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                x)
                              (η r x)) →
                      (haut :
                          ∀ (r : Nat)
                            (x :
                              D5.S3.Arith.FibonacciAtomic.RecordCapacity.State d p
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
                            @Eq.{u + 1} (R r)
                              (ρ r
                                (η
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                  x))
                              (η r
                                (@DFunLike.coe.{1, 1, 1}
                                  (@AddMonoidHom.{0, 0}
                                    (Fin d →
                                      ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                    (Fin d →
                                      ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                    (@AddZeroClass.toAddZero.{0}
                                      (Fin d →
                                        ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                      (@Pi.addZeroClass.{0, 0} (Fin d)
                                        (fun (a : Fin d) =>
                                          ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                        fun (i : Fin d) =>
                                        @AddMonoid.toAddZeroClass.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                          (@AddMonoidWithOne.toAddMonoid.{0}
                                            (ZMod
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                            (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                              (ZMod
                                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                  (@instHPow.{0, 0} Nat Nat
                                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                  p
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                              (@Ring.toAddGroupWithOne.{0}
                                                (ZMod
                                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                    (@instHPow.{0, 0} Nat Nat
                                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                    p
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                                (@CommRing.toRing.{0}
                                                  (ZMod
                                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                      (@instHPow.{0, 0} Nat Nat
                                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                      p
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          r
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                                  (ZMod.commRing
                                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                      (@instHPow.{0, 0} Nat Nat
                                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                      p
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          r
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                          (instOfNatNat (nat_lit 1))))))))))))
                                    (@AddZeroClass.toAddZero.{0}
                                      (Fin d →
                                        ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                      (@Pi.addZeroClass.{0, 0} (Fin d)
                                        (fun (a : Fin d) =>
                                          ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                        fun (i : Fin d) =>
                                        @AddMonoid.toAddZeroClass.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                          (@AddMonoidWithOne.toAddMonoid.{0}
                                            (ZMod
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                            (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                              (ZMod
                                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                  (@instHPow.{0, 0} Nat Nat
                                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                  p
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                              (@Ring.toAddGroupWithOne.{0}
                                                (ZMod
                                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                    (@instHPow.{0, 0} Nat Nat
                                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                    p
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                                (@CommRing.toRing.{0}
                                                  (ZMod
                                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                      (@instHPow.{0, 0} Nat Nat
                                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                      p
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                                  (ZMod.commRing
                                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                      (@instHPow.{0, 0} Nat Nat
                                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                      p
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                          (instOfNatNat (nat_lit 1)))))))))))))
                                  (Fin d →
                                    ZMod
                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                        (@instHPow.{0, 0} Nat Nat
                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                        p
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                  (fun
                                      (x :
                                        Fin d →
                                          ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) =>
                                    Fin d →
                                      ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                  (@AddMonoidHom.instFunLike.{0, 0}
                                    (Fin d →
                                      ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                    (Fin d →
                                      ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                    (@AddZeroClass.toAddZero.{0}
                                      (Fin d →
                                        ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                      (@Pi.addZeroClass.{0, 0} (Fin d)
                                        (fun (a : Fin d) =>
                                          ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                        fun (i : Fin d) =>
                                        @AddMonoid.toAddZeroClass.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                          (@AddMonoidWithOne.toAddMonoid.{0}
                                            (ZMod
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                            (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                              (ZMod
                                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                  (@instHPow.{0, 0} Nat Nat
                                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                  p
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                              (@Ring.toAddGroupWithOne.{0}
                                                (ZMod
                                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                    (@instHPow.{0, 0} Nat Nat
                                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                    p
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                                (@CommRing.toRing.{0}
                                                  (ZMod
                                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                      (@instHPow.{0, 0} Nat Nat
                                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                      p
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          r
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                                  (ZMod.commRing
                                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                      (@instHPow.{0, 0} Nat Nat
                                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                      p
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          r
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                          (instOfNatNat (nat_lit 1))))))))))))
                                    (@AddZeroClass.toAddZero.{0}
                                      (Fin d →
                                        ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                      (@Pi.addZeroClass.{0, 0} (Fin d)
                                        (fun (a : Fin d) =>
                                          ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                        fun (i : Fin d) =>
                                        @AddMonoid.toAddZeroClass.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                          (@AddMonoidWithOne.toAddMonoid.{0}
                                            (ZMod
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                            (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                              (ZMod
                                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                  (@instHPow.{0, 0} Nat Nat
                                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                  p
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                              (@Ring.toAddGroupWithOne.{0}
                                                (ZMod
                                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                    (@instHPow.{0, 0} Nat Nat
                                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                    p
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                                (@CommRing.toRing.{0}
                                                  (ZMod
                                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                      (@instHPow.{0, 0} Nat Nat
                                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                      p
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                                  (ZMod.commRing
                                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                      (@instHPow.{0, 0} Nat Nat
                                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                      p
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                          (instOfNatNat (nat_lit 1)))))))))))))
                                  (@D5.S3.Arith.FibonacciAtomic.RecordCapacity.reduce.{0} (Fin d) p
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                  x))) →
                        (r : Nat) →
                          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                            Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.signature PUnit.unit.{1}
                            (@Sigma.mk.{0, 0} Nat (fun (d : Nat) => @Sigma.{0, 0} Nat fun (_p : Nat) => Fin d → Nat) d
                              (@Sigma.mk.{0, 0} Nat (fun (_p : Nat) => Fin d → Nat) p s)) :=
  fun {d p : Nat} (hp : Nat.Prime p) (B : Matrix.{0, 0, 0} (Fin d) (Fin d) Int)
    (U V :
      @Units.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Int)
        (@Semiring.toMonoid.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Int)
          (@Matrix.semiring.{0, 0} (Fin d) Int Int.instSemiring (Fin.fintype d) (instDecidableEqFin d))))
    (s : Fin d → Nat)
    (hSmith :
      @Eq.{1} (Matrix.{0, 0, 0} (Fin d) (Fin d) Int)
        (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Int) (Matrix.{0, 0, 0} (Fin d) (Fin d) Int)
          (Matrix.{0, 0, 0} (Fin d) (Fin d) Int)
          (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin d) (Fin d) (Fin d) Int (Fin.fintype d)
            Int.instMul Int.instAddCommMonoid)
          (@HMul.hMul.{0, 0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Int) (Matrix.{0, 0, 0} (Fin d) (Fin d) Int)
            (Matrix.{0, 0, 0} (Fin d) (Fin d) Int)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin d) (Fin d) (Fin d) Int (Fin.fintype d)
              Int.instMul Int.instAddCommMonoid)
            (@Units.val.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Int)
              (@Semiring.toMonoid.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Int)
                (@Matrix.semiring.{0, 0} (Fin d) Int Int.instSemiring (Fin.fintype d) (instDecidableEqFin d)))
              U)
            B)
          (@Units.val.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Int)
            (@Semiring.toMonoid.{0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Int)
              (@Matrix.semiring.{0, 0} (Fin d) Int Int.instSemiring (Fin.fintype d) (instDecidableEqFin d)))
            V))
        (@Matrix.diagonal.{0, 0} (Fin d) Int (instDecidableEqFin d)
          (@MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring)) fun (i : Fin d) =>
          @Nat.cast.{0} Int instNatCastInt (s i)))
    {R : Nat → Type u} [(r : Nat) → Fintype.{u} (R r)]
    (η :
      (r : Nat) →
        D5.S3.Arith.FibonacciAtomic.RecordCapacity.State d p
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
          R r)
    (ρ :
      (r : Nat) →
        R
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
          R r)
    (hjoint :
      ∀ (r : Nat),
        @Function.Injective.{1, max (u + 1) 1}
          (D5.S3.Arith.FibonacciAtomic.RecordCapacity.State d p
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (Prod.{0, u}
            (D5.S3.Arith.FibonacciAtomic.RecordCapacity.State d p
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (R r))
          fun
            (x :
              D5.S3.Arith.FibonacciAtomic.RecordCapacity.State d p
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
          @Prod.mk.{0, u}
            (D5.S3.Arith.FibonacciAtomic.RecordCapacity.State d p
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (R r)
            (@DFunLike.coe.{1, 1, 1}
              (@AddMonoidHom.{0, 0}
                (D5.S3.Arith.FibonacciAtomic.RecordCapacity.State d p
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (D5.S3.Arith.FibonacciAtomic.RecordCapacity.State d p
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@AddZeroClass.toAddZero.{0}
                  (D5.S3.Arith.FibonacciAtomic.RecordCapacity.State d p
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@Pi.addZeroClass.{0, 0} (Fin d)
                    (fun (a : Fin d) =>
                      ZMod
                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    fun (i : Fin d) =>
                    @AddMonoid.toAddZeroClass.{0}
                      (ZMod
                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                      (@AddMonoidWithOne.toAddMonoid.{0}
                        (ZMod
                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                        (@AddGroupWithOne.toAddMonoidWithOne.{0}
                          (ZMod
                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                          (@Ring.toAddGroupWithOne.{0}
                            (ZMod
                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                p
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                            (@CommRing.toRing.{0}
                              (ZMod
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat
                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                  p
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                              (ZMod.commRing
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat
                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                  p
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))))
                (@AddZeroClass.toAddZero.{0}
                  (D5.S3.Arith.FibonacciAtomic.RecordCapacity.State d p
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@Pi.addZeroClass.{0, 0} (Fin d)
                    (fun (a : Fin d) =>
                      ZMod
                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    fun (i : Fin d) =>
                    @AddMonoid.toAddZeroClass.{0}
                      (ZMod
                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                      (@AddMonoidWithOne.toAddMonoid.{0}
                        (ZMod
                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                        (@AddGroupWithOne.toAddMonoidWithOne.{0}
                          (ZMod
                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                          (@Ring.toAddGroupWithOne.{0}
                            (ZMod
                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                p
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                            (@CommRing.toRing.{0}
                              (ZMod
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat
                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                  p
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                              (ZMod.commRing
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat
                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                  p
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))))))
              (D5.S3.Arith.FibonacciAtomic.RecordCapacity.State d p
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (fun
                  (x :
                    D5.S3.Arith.FibonacciAtomic.RecordCapacity.State d p
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                D5.S3.Arith.FibonacciAtomic.RecordCapacity.State d p
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@AddMonoidHom.instFunLike.{0, 0}
                (D5.S3.Arith.FibonacciAtomic.RecordCapacity.State d p
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (D5.S3.Arith.FibonacciAtomic.RecordCapacity.State d p
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@AddZeroClass.toAddZero.{0}
                  (D5.S3.Arith.FibonacciAtomic.RecordCapacity.State d p
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@Pi.addZeroClass.{0, 0} (Fin d)
                    (fun (a : Fin d) =>
                      ZMod
                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    fun (i : Fin d) =>
                    @AddMonoid.toAddZeroClass.{0}
                      (ZMod
                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                      (@AddMonoidWithOne.toAddMonoid.{0}
                        (ZMod
                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                        (@AddGroupWithOne.toAddMonoidWithOne.{0}
                          (ZMod
                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                          (@Ring.toAddGroupWithOne.{0}
                            (ZMod
                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                p
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                            (@CommRing.toRing.{0}
                              (ZMod
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat
                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                  p
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                              (ZMod.commRing
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat
                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                  p
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))))
                (@AddZeroClass.toAddZero.{0}
                  (D5.S3.Arith.FibonacciAtomic.RecordCapacity.State d p
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@Pi.addZeroClass.{0, 0} (Fin d)
                    (fun (a : Fin d) =>
                      ZMod
                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    fun (i : Fin d) =>
                    @AddMonoid.toAddZeroClass.{0}
                      (ZMod
                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                      (@AddMonoidWithOne.toAddMonoid.{0}
                        (ZMod
                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                        (@AddGroupWithOne.toAddMonoidWithOne.{0}
                          (ZMod
                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                          (@Ring.toAddGroupWithOne.{0}
                            (ZMod
                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                p
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                            (@CommRing.toRing.{0}
                              (ZMod
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat
                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                  p
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                              (ZMod.commRing
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat
                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                  p
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))))))
              (@D5.S3.Arith.FibonacciAtomic.RecordCapacity.action d B p
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              x)
            (η r x))
    (haut :
      ∀ (r : Nat)
        (x :
          D5.S3.Arith.FibonacciAtomic.RecordCapacity.State d p
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
        @Eq.{u + 1} (R r)
          (ρ r
            (η
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              x))
          (η r
            (@DFunLike.coe.{1, 1, 1}
              (@AddMonoidHom.{0, 0}
                (Fin d →
                  ZMod
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (Fin d →
                  ZMod
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (@AddZeroClass.toAddZero.{0}
                  (Fin d →
                    ZMod
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (@Pi.addZeroClass.{0, 0} (Fin d)
                    (fun (a : Fin d) =>
                      ZMod
                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    fun (i : Fin d) =>
                    @AddMonoid.toAddZeroClass.{0}
                      (ZMod
                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                      (@AddMonoidWithOne.toAddMonoid.{0}
                        (ZMod
                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                        (@AddGroupWithOne.toAddMonoidWithOne.{0}
                          (ZMod
                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                          (@Ring.toAddGroupWithOne.{0}
                            (ZMod
                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                p
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                            (@CommRing.toRing.{0}
                              (ZMod
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat
                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                  p
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                              (ZMod.commRing
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat
                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                  p
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))))
                (@AddZeroClass.toAddZero.{0}
                  (Fin d →
                    ZMod
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (@Pi.addZeroClass.{0, 0} (Fin d)
                    (fun (a : Fin d) =>
                      ZMod
                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    fun (i : Fin d) =>
                    @AddMonoid.toAddZeroClass.{0}
                      (ZMod
                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                      (@AddMonoidWithOne.toAddMonoid.{0}
                        (ZMod
                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                        (@AddGroupWithOne.toAddMonoidWithOne.{0}
                          (ZMod
                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                          (@Ring.toAddGroupWithOne.{0}
                            (ZMod
                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                p
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                            (@CommRing.toRing.{0}
                              (ZMod
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat
                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                  p
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                              (ZMod.commRing
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat
                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                  p
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))))))
              (Fin d →
                ZMod
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (fun
                  (x :
                    Fin d →
                      ZMod
                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) =>
                Fin d →
                  ZMod
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (@AddMonoidHom.instFunLike.{0, 0}
                (Fin d →
                  ZMod
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (Fin d →
                  ZMod
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (@AddZeroClass.toAddZero.{0}
                  (Fin d →
                    ZMod
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (@Pi.addZeroClass.{0, 0} (Fin d)
                    (fun (a : Fin d) =>
                      ZMod
                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    fun (i : Fin d) =>
                    @AddMonoid.toAddZeroClass.{0}
                      (ZMod
                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                      (@AddMonoidWithOne.toAddMonoid.{0}
                        (ZMod
                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                        (@AddGroupWithOne.toAddMonoidWithOne.{0}
                          (ZMod
                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                          (@Ring.toAddGroupWithOne.{0}
                            (ZMod
                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                p
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                            (@CommRing.toRing.{0}
                              (ZMod
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat
                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                  p
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                              (ZMod.commRing
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat
                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                  p
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))))
                (@AddZeroClass.toAddZero.{0}
                  (Fin d →
                    ZMod
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (@Pi.addZeroClass.{0, 0} (Fin d)
                    (fun (a : Fin d) =>
                      ZMod
                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    fun (i : Fin d) =>
                    @AddMonoid.toAddZeroClass.{0}
                      (ZMod
                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                      (@AddMonoidWithOne.toAddMonoid.{0}
                        (ZMod
                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                        (@AddGroupWithOne.toAddMonoidWithOne.{0}
                          (ZMod
                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                          (@Ring.toAddGroupWithOne.{0}
                            (ZMod
                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                p
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                            (@CommRing.toRing.{0}
                              (ZMod
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat
                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                  p
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                              (ZMod.commRing
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat
                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                  p
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))))))
              (@D5.S3.Arith.FibonacciAtomic.RecordCapacity.reduce.{0} (Fin d) p
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              x)))
    (r : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.signature Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.actual
    PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat (fun (d : Nat) => @Sigma.{0, 0} Nat fun (_p : Nat) => Fin d → Nat) d
      (@Sigma.mk.{0, 0} Nat (fun (_p : Nat) => Fin d → Nat) p s))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration_1.observationFact0.{u} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"RecordCapacity\",\"autonomous_record_capacity\"],\"part\":\"type\",\"path\":[\"function\",\"argument\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"body\",\"argument\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"RecordCapacity\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.RecordCapacity, declaration := `D5.S3.Arith.FibonacciAtomic.RecordCapacity.autonomous_record_capacity, part := .type, path := [.function, .argument, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .function, .argument, .body, .argument, .function, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration_1.observation0, part := .value, path := [], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration_1.varyingLawInput.{u} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration_1.canonicalArenaOperand.{u})
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration_1.varyingLaw.{u}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"RecordCapacity\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration_1.statementExclusion.{u} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"RecordCapacity\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"RecordCapacity\",\"autonomous_record_capacity\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u)] }
  statementLocation := { owner := `D5.S3.Arith.FibonacciAtomic.RecordCapacity, declaration := `D5.S3.Arith.FibonacciAtomic.RecordCapacity.autonomous_record_capacity, part := .type, path := [], levels := [(.param `u)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration.{u}).actual (Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration.{u}).variation.2.choose (Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration.{u}).variation.1 (Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration.{u}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"RecordCapacity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"RecordCapacity\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.RecordCapacity.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))
