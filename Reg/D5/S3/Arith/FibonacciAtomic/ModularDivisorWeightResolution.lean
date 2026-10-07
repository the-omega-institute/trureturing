import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution
open _root_.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset Filter Real
open scoped BigOperators Topology

namespace Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution
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
  realize signature (fun _ _ n => normalizedWeight n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
noncomputable def observedValues (r : Realization signature) (C : ℝ) (m : ℕ) : Set ℝ :=
  {v | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
    (a : ℝ) ≤ (m.factorial : ℝ)^C ∧ (b : ℝ) ≤ (m.factorial : ℝ)^C ∧
    Nat.ModEq m.factorial a b ∧ v = r.readout () () a / r.readout () () b}
noncomputable def observedExtreme (r : Realization signature) (C : ℝ) (m : ℕ) : ℝ :=
  sSup (observedValues r C m)

abbrev arena : Arena where
  signature := signature
  Law r :=
    ∀ C : ℝ, 1 < C →
    (∀ m : ℕ, (observedValues r C m).Finite ∧ (1 : ℝ) ∈ observedValues r C m ∧
          observedExtreme r C m ∈ observedValues r C m ∧ 1 ≤ observedExtreme r C m) ∧
        (∀ᶠ m : ℕ in atTop,
          0 < lowerNumber C m ∧
          (lowerNumber C m : ℝ) ≤ (m.factorial : ℝ)^C ∧
          (m.factorial : ℝ) ≤ (m.factorial : ℝ)^C ∧
          Nat.ModEq m.factorial (lowerNumber C m) m.factorial ∧
          Nat.Coprime m.factorial (primeBlock m (lowerCutoff C m)) ∧
          r.readout () () (lowerNumber C m) / r.readout () () m.factorial =
            ∏ p ∈ blockSet m (lowerCutoff C m), (1 + (p : ℝ)⁻¹)) ∧
        Tendsto (fun m : ℕ => (observedExtreme r C m - 1) *
          (log m / log (log m))) atTop (𝓝 1) ∧
        Tendsto (fun m : ℕ =>
          (r.readout () () (lowerNumber C m) / r.readout () () m.factorial - 1) *
          (log m / log (log m))) atTop (𝓝 1) ∧
        Tendsto (fun m : ℕ =>
          (r.readout () () (lowerNumber C m) - r.readout () () m.factorial) /
          (exp eulerMascheroniConstant * log (log m))) atTop (𝓝 1) ∧
        Tendsto (fun m : ℕ =>
          r.readout () () (lowerNumber C m) - r.readout () () m.factorial) atTop atTop

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hone := (h 2 (by norm_num)).1 0 |>.2.1
  obtain ⟨a, b, ha, hb, haH, hbH, hab, heq⟩ := hone
  norm_num [rejected, realize] at heq

def registration : Registration arena (
    ∀ C : ℝ, 1 < C →
    (∀ m : ℕ, (pairValues C m).Finite ∧ (1 : ℝ) ∈ pairValues C m ∧
          extremeRatio C m ∈ pairValues C m ∧ 1 ≤ extremeRatio C m) ∧
        (∀ᶠ m : ℕ in atTop,
          0 < lowerNumber C m ∧
          (lowerNumber C m : ℝ) ≤ (m.factorial : ℝ)^C ∧
          (m.factorial : ℝ) ≤ (m.factorial : ℝ)^C ∧
          Nat.ModEq m.factorial (lowerNumber C m) m.factorial ∧
          Nat.Coprime m.factorial (primeBlock m (lowerCutoff C m)) ∧
          normalizedWeight (lowerNumber C m) / normalizedWeight m.factorial =
            ∏ p ∈ blockSet m (lowerCutoff C m), (1 + (p : ℝ)⁻¹)) ∧
        Tendsto (fun m : ℕ => (extremeRatio C m - 1) *
          (log m / log (log m))) atTop (𝓝 1) ∧
        Tendsto (fun m : ℕ =>
          (normalizedWeight (lowerNumber C m) / normalizedWeight m.factorial - 1) *
          (log m / log (log m))) atTop (𝓝 1) ∧
        Tendsto (fun m : ℕ =>
          (normalizedWeight (lowerNumber C m) - normalizedWeight m.factorial) /
          (exp eulerMascheroniConstant * log (log m))) atTop (𝓝 1) ∧
        Tendsto (fun m : ℕ =>
          normalizedWeight (lowerNumber C m) - normalizedWeight m.factorial) atTop atTop) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fun C hC => result C hC, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    change normalizedWeight 1 ≠ normalizedWeight 2
    have h2 : ArithmeticFunction.sigma 1 2 = 3 := by
      simpa using ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) Nat.prime_two
    norm_num [normalizedWeight, ArithmeticFunction.sigma_one, h2]

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => normalizedWeight n) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "FibonacciAtomic") "ModularDivisorWeightResolution") "result") "Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution/Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => normalizedWeight n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "arg", "fn", "arg", "fn", "arg", "body", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution, declaration := `D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration_1.observationFact0, `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration_1.anchorEnumeration }


#print axioms registration
end
end Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution


noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.arena
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightResolution\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightResolution\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.arena
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightResolution\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightResolution\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.arena
    (∀ (C : Real),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) C →
        And
          (∀ (m : Nat),
            And (@Set.Finite.{0} Real (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.pairValues C m))
              (And
                (@Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                  (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.pairValues C m)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                (And
                  (@Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                    (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.pairValues C m)
                    (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.extremeRatio C m))
                  (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.extremeRatio C m)))))
          (And
            (@Filter.Eventually.{0} Nat
              (fun (m : Nat) =>
                And
                  (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.lowerNumber C m))
                  (And
                    (@LE.le.{0} Real Real.instLE
                      (@Nat.cast.{0} Real Real.instNatCast
                        (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.lowerNumber C m))
                      (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                        (@Nat.cast.{0} Real Real.instNatCast (Nat.factorial m)) C))
                    (And
                      (@LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (Nat.factorial m))
                        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                          (@Nat.cast.{0} Real Real.instNatCast (Nat.factorial m)) C))
                      (And
                        (Nat.ModEq (Nat.factorial m)
                          (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.lowerNumber C m)
                          (Nat.factorial m))
                        (And
                          (Nat.Coprime (Nat.factorial m)
                            (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.primeBlock m
                              (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.lowerCutoff C m)))
                          (@Eq.{1} Real
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                              (D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.normalizedWeight
                                (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.lowerNumber C m))
                              (D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.normalizedWeight
                                (Nat.factorial m)))
                            (@Finset.prod.{0, 0} Nat Real Real.instCommMonoid
                              (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.blockSet m
                                (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.lowerCutoff C m))
                              fun (p : Nat) =>
                              @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                (@Inv.inv.{0} Real Real.instInv (@Nat.cast.{0} Real Real.instNatCast p)))))))))
              (@Filter.atTop.{0} Nat Nat.instPreorder))
            (And
              (@Filter.Tendsto.{0, 0} Nat Real
                (fun (m : Nat) =>
                  @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.extremeRatio C m)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (Real.log (@Nat.cast.{0} Real Real.instNatCast m))
                      (Real.log (Real.log (@Nat.cast.{0} Real Real.instNatCast m)))))
                (@Filter.atTop.{0} Nat Nat.instPreorder)
                (@nhds.{0} Real
                  (@UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
              (And
                (@Filter.Tendsto.{0, 0} Nat Real
                  (fun (m : Nat) =>
                    @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.normalizedWeight
                            (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.lowerNumber C m))
                          (D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.normalizedWeight (Nat.factorial m)))
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (Real.log (@Nat.cast.{0} Real Real.instNatCast m))
                        (Real.log (Real.log (@Nat.cast.{0} Real Real.instNatCast m)))))
                  (@Filter.atTop.{0} Nat Nat.instPreorder)
                  (@nhds.{0} Real
                    (@UniformSpace.toTopologicalSpace.{0} Real
                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
                (And
                  (@Filter.Tendsto.{0, 0} Nat Real
                    (fun (m : Nat) =>
                      @HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                          (D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.normalizedWeight
                            (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.lowerNumber C m))
                          (D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.normalizedWeight (Nat.factorial m)))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (Real.exp Real.eulerMascheroniConstant)
                          (Real.log (Real.log (@Nat.cast.{0} Real Real.instNatCast m)))))
                    (@Filter.atTop.{0} Nat Nat.instPreorder)
                    (@nhds.{0} Real
                      (@UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
                  (@Filter.Tendsto.{0, 0} Nat Real
                    (fun (m : Nat) =>
                      @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                        (D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.normalizedWeight
                          (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.lowerNumber C m))
                        (D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.normalizedWeight (Nat.factorial m)))
                    (@Filter.atTop.{0} Nat Nat.instPreorder) (@Filter.atTop.{0} Real Real.instPreorder)))))))
    Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration)

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightResolution\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightResolution\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution, declaration := `D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.arena
  (∀ (C : Real),
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) C →
      And
        (∀ (m : Nat),
          And (@Set.Finite.{0} Real (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.pairValues C m))
            (And
              (@Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.pairValues C m)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
              (And
                (@Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
                  (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.pairValues C m)
                  (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.extremeRatio C m))
                (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.extremeRatio C m)))))
        (And
          (@Filter.Eventually.{0} Nat
            (fun (m : Nat) =>
              And
                (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.lowerNumber C m))
                (And
                  (@LE.le.{0} Real Real.instLE
                    (@Nat.cast.{0} Real Real.instNatCast
                      (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.lowerNumber C m))
                    (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                      (@Nat.cast.{0} Real Real.instNatCast (Nat.factorial m)) C))
                  (And
                    (@LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (Nat.factorial m))
                      (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                        (@Nat.cast.{0} Real Real.instNatCast (Nat.factorial m)) C))
                    (And
                      (Nat.ModEq (Nat.factorial m)
                        (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.lowerNumber C m) (Nat.factorial m))
                      (And
                        (Nat.Coprime (Nat.factorial m)
                          (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.primeBlock m
                            (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.lowerCutoff C m)))
                        (@Eq.{1} Real
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                            (D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.normalizedWeight
                              (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.lowerNumber C m))
                            (D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.normalizedWeight
                              (Nat.factorial m)))
                          (@Finset.prod.{0, 0} Nat Real Real.instCommMonoid
                            (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.blockSet m
                              (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.lowerCutoff C m))
                            fun (p : Nat) =>
                            @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                              (@Inv.inv.{0} Real Real.instInv (@Nat.cast.{0} Real Real.instNatCast p)))))))))
            (@Filter.atTop.{0} Nat Nat.instPreorder))
          (And
            (@Filter.Tendsto.{0, 0} Nat Real
              (fun (m : Nat) =>
                @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.extremeRatio C m)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (Real.log (@Nat.cast.{0} Real Real.instNatCast m))
                    (Real.log (Real.log (@Nat.cast.{0} Real Real.instNatCast m)))))
              (@Filter.atTop.{0} Nat Nat.instPreorder)
              (@nhds.{0} Real
                (@UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
            (And
              (@Filter.Tendsto.{0, 0} Nat Real
                (fun (m : Nat) =>
                  @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.normalizedWeight
                          (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.lowerNumber C m))
                        (D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.normalizedWeight (Nat.factorial m)))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (Real.log (@Nat.cast.{0} Real Real.instNatCast m))
                      (Real.log (Real.log (@Nat.cast.{0} Real Real.instNatCast m)))))
                (@Filter.atTop.{0} Nat Nat.instPreorder)
                (@nhds.{0} Real
                  (@UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
              (And
                (@Filter.Tendsto.{0, 0} Nat Real
                  (fun (m : Nat) =>
                    @HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                        (D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.normalizedWeight
                          (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.lowerNumber C m))
                        (D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.normalizedWeight (Nat.factorial m)))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (Real.exp Real.eulerMascheroniConstant)
                        (Real.log (Real.log (@Nat.cast.{0} Real Real.instNatCast m)))))
                  (@Filter.atTop.{0} Nat Nat.instPreorder)
                  (@nhds.{0} Real
                    (@UniformSpace.toTopologicalSpace.{0} Real
                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
                (@Filter.Tendsto.{0, 0} Nat Real
                  (fun (m : Nat) =>
                    @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.normalizedWeight
                        (D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.lowerNumber C m))
                      (D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.normalizedWeight (Nat.factorial m)))
                  (@Filter.atTop.{0} Nat Nat.instPreorder) (@Filter.atTop.{0} Real Real.instPreorder)))))))
  Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration)

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration_1.observation0 : (C : Real) →
  (hC : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) C) →
    (m : Nat) →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
          Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.signature PUnit.unit.{1} →
        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
          Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (C : Real)
    (hC : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) C)
    (m : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.signature
    Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.actual PUnit.unit.{1} PUnit.unit.{1}

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightResolution\",\"result\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"argument\",\"function\",\"argument\",\"function\",\"argument\",\"body\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"function\",\"argument\",\"function\",\"argument\",\"function\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightResolution\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution, declaration := `D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.result, part := .type, path := [.body, .body, .argument, .function, .argument, .function, .argument, .body, .argument, .argument, .argument, .argument, .argument, .function, .argument, .function, .argument, .function], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightResolution\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightResolution\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightResolution\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution, declaration := `D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration).actual (Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration).variation.2.choose (Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration).variation.1 (Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightResolution\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"ModularDivisorWeightResolution\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
