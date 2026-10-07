import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset Filter Asymptotics
open scoped BigOperators Topology

namespace Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ m => delta m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r :=
    (∀ m a b : ℕ, 2 ≤ m → 0 < a → 0 < b → Nat.ModEq m.factorial a b →
      delta m ≤ smallWeight m a / smallWeight m b ∧
        smallWeight m a / smallWeight m b ≤ (delta m)⁻¹) ∧
    (∀ m : ℕ, 4 ≤ m →
      (∑ p ∈ Ioc 0 m with p.Prime,
        ((p : ℝ)⁻¹) ^ (m.factorial.factorization p + 1)) ≤
          (Real.sqrt m)⁻¹ + (Real.sqrt m - 1)⁻¹) ∧
    (fun m : ℕ => r.readout () () m - 1) =O[atTop]
      (fun m : ℕ => (Real.sqrt m)⁻¹)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ho := h.2.2
  change (fun _ : ℕ => (0 : ℝ) - 1) =O[atTop] (fun m : ℕ => (Real.sqrt m)⁻¹) at ho
  have hi : Tendsto (fun m : ℕ => (Real.sqrt m)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hc : (0 : ℝ) - 1 = 0 := tendsto_nhds_unique tendsto_const_nhds (ho.trans_tendsto hi)
  norm_num at hc

def registration : Registration arena (
(∀ m a b : ℕ, 2 ≤ m → 0 < a → 0 < b → Nat.ModEq m.factorial a b →
      delta m ≤ smallWeight m a / smallWeight m b ∧
        smallWeight m a / smallWeight m b ≤ (delta m)⁻¹) ∧
    (∀ m : ℕ, 4 ≤ m →
      (∑ p ∈ Ioc 0 m with p.Prime,
        ((p : ℝ)⁻¹) ^ (m.factorial.factorization p + 1)) ≤
          (Real.sqrt m)⁻¹ + (Real.sqrt m - 1)⁻¹) ∧
    (fun m : ℕ => delta m - 1) =O[atTop] (fun m : ℕ => (Real.sqrt m)⁻¹)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 0, 2, ?_⟩
    change delta 0 ≠ delta 2
    have hprimes : (Ioc 0 2).filter Nat.Prime = {2} := by decide
    norm_num [delta, hprimes]

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ m => delta m) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "FibonacciAtomic") "ModularDivisorWeightTransfer") "result") "Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer/Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ m => delta m) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer, definition := none, coordinates := #[], readouts := #[{ path := #["arg", "arg", "fn", "arg", "body", "fn", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer, declaration := `D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.observationFact0, `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.anchorEnumeration }


#print axioms registration

end
end Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer


noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.arena
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightTransfer\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightTransfer\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.arena
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightTransfer\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightTransfer\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.arena
    (And
      (∀ (m a b : Nat),
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m →
          @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) a →
            @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b →
              Nat.ModEq (Nat.factorial m) a b →
                And
                  (@LE.le.{0} Real Real.instLE (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.delta m)
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.smallWeight m a)
                      (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.smallWeight m b)))
                  (@LE.le.{0} Real Real.instLE
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.smallWeight m a)
                      (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.smallWeight m b))
                    (@Inv.inv.{0} Real Real.instInv
                      (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.delta m))))
      (And
        (∀ (m : Nat),
          @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m →
            @LE.le.{0} Real Real.instLE
              (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid
                (@Finset.filter.{0} Nat (fun (p : Nat) => Nat.Prime p) Nat.decidablePrime
                  (@Finset.Ioc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m))
                fun (p : Nat) =>
                @HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                  (@Inv.inv.{0} Real Real.instInv (@Nat.cast.{0} Real Real.instNatCast p))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@DFunLike.coe.{1, 1, 1}
                      (@Finsupp.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) Nat
                      (fun (x : Nat) => Nat)
                      (@Finsupp.instFunLike.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                      (Nat.factorization (Nat.factorial m)) p)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast m)))
                (@Inv.inv.{0} Real Real.instInv
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast m))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))))
        (@Asymptotics.IsBigO.{0, 0, 0} Nat Real Real Real.norm Real.norm (@Filter.atTop.{0} Nat Nat.instPreorder)
          (fun (m : Nat) =>
            @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.delta m)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
          fun (m : Nat) => @Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast m)))))
    Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration)

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightTransfer\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightTransfer\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer, declaration := `D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.arena
  (And
    (∀ (m a b : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m →
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) a →
          @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b →
            Nat.ModEq (Nat.factorial m) a b →
              And
                (@LE.le.{0} Real Real.instLE (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.delta m)
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.smallWeight m a)
                    (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.smallWeight m b)))
                (@LE.le.{0} Real Real.instLE
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.smallWeight m a)
                    (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.smallWeight m b))
                  (@Inv.inv.{0} Real Real.instInv (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.delta m))))
    (And
      (∀ (m : Nat),
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) m →
          @LE.le.{0} Real Real.instLE
            (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid
              (@Finset.filter.{0} Nat (fun (p : Nat) => Nat.Prime p) Nat.decidablePrime
                (@Finset.Ioc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m))
              fun (p : Nat) =>
              @HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                (@Inv.inv.{0} Real Real.instInv (@Nat.cast.{0} Real Real.instNatCast p))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@DFunLike.coe.{1, 1, 1} (@Finsupp.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                    Nat (fun (x : Nat) => Nat)
                    (@Finsupp.instFunLike.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                    (Nat.factorization (Nat.factorial m)) p)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast m)))
              (@Inv.inv.{0} Real Real.instInv
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast m))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))))
      (@Asymptotics.IsBigO.{0, 0, 0} Nat Real Real Real.norm Real.norm (@Filter.atTop.{0} Nat Nat.instPreorder)
        (fun (m : Nat) =>
          @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.delta m)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
        fun (m : Nat) => @Inv.inv.{0} Real Real.instInv (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast m)))))
  Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration)

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.observation0 : (m : Nat) →
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
      Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.signature PUnit.unit.{1} →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
      Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (m : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.signature
    Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.actual PUnit.unit.{1} PUnit.unit.{1}

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightTransfer\",\"result\"],\"part\":\"type\",\"path\":[\"argument\",\"argument\",\"function\",\"argument\",\"body\",\"function\",\"argument\",\"function\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightTransfer\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer, declaration := `D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.result, part := .type, path := [.argument, .argument, .function, .argument, .body, .function, .argument, .function], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightTransfer\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightTransfer\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightTransfer\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer, declaration := `D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration).actual (Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration).variation.2.choose (Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration).variation.1 (Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightTransfer\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightTransfer\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightTransfer.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
