import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset Filter Real
open scoped BigOperators Topology

namespace Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer
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

noncomputable def observedError (r : Realization signature) (C : ℝ) (m : ℕ) : ℝ := sSup
  {v : ℝ | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
    (a : ℝ) ≤ exp (C * m * log m) ∧ (b : ℝ) ≤ exp (C * m * log m) ∧
    Nat.ModEq m.factorial a b ∧ v = |r.readout () () a / r.readout () () b - 1|}

abbrev arena : Arena where
  signature := signature
  Law r :=
    (∀ m n : ℕ, 2 ≤ m → 0 < n → ∀ X : ℝ, (m : ℝ) ≤ X →
      1 ≤ highWeight m n ∧ highWeight m n ≤
        primeProduct X / primeProduct m * exp (log n / ((X - 1) * log X))) ∧
    (∀ C : ℝ, 0 < C → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      ∀ a b : ℕ, 0 < a → 0 < b →
        (a : ℝ) ≤ exp (C * m * log m) → (b : ℝ) ≤ exp (C * m * log m) →
        Nat.ModEq m.factorial a b →
        |r.readout () () a / r.readout () () b - 1| < ε) ∧
    (∀ C : ℝ, 0 < C → Tendsto (fun m : ℕ => observedError r C m) atTop (𝓝 0))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h.2.1 1 (by norm_num) (1/2) (by norm_num)
  obtain ⟨m, hm, hbound⟩ := (he.and (eventually_ge_atTop (2 : ℕ))).exists
  have hs : (1 : ℝ) ≤ exp (1 * m * log m) := by
    apply one_le_exp_iff.mpr
    have hlog : 0 ≤ log (m : ℝ) := log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
    positivity
  have hf := hm 1 1 (by norm_num) (by norm_num) (by simpa using hs) (by simpa using hs) (Nat.ModEq.refl 1)
  norm_num [rejected, realize] at hf

def registration : Registration arena (
    (∀ m n : ℕ, 2 ≤ m → 0 < n → ∀ X : ℝ, (m : ℝ) ≤ X →
      1 ≤ highWeight m n ∧ highWeight m n ≤
        primeProduct X / primeProduct m * exp (log n / ((X - 1) * log X))) ∧
    (∀ C : ℝ, 0 < C → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      ∀ a b : ℕ, 0 < a → 0 < b →
        (a : ℝ) ≤ exp (C * m * log m) → (b : ℝ) ≤ exp (C * m * log m) →
        Nat.ModEq m.factorial a b →
        |normalizedWeight a / normalizedWeight b - 1| < ε) ∧
    (∀ C : ℝ, 0 < C → Tendsto (fun m : ℕ => uniformError C m) atTop (𝓝 0))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    change normalizedWeight 1 ≠ normalizedWeight 2
    have h2 : ArithmeticFunction.sigma 1 2 = 3 := by
      simpa using ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) Nat.prime_two
    norm_num [normalizedWeight, ArithmeticFunction.sigma_one, h2]

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => normalizedWeight n) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "FibonacciAtomic") "UniformDivisorWeightTransfer") "result") "Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer/Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration,
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
  sourceSelection := some { owner := `D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer, definition := none, coordinates := #[], readouts := #[{ path := #["arg", "fn", "arg", "body", "body", "body", "body", "fn", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg", "fn", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer, declaration := `D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration_1.observationFact0, `Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration_1.anchorEnumeration }


#print axioms registration

end
end Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer


noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.arena
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"UniformDivisorWeightTransfer\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"UniformDivisorWeightTransfer\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.arena
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"UniformDivisorWeightTransfer\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"UniformDivisorWeightTransfer\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.arena
    (And
      (∀ (m n : Nat),
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m →
          @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
            ∀ (X : Real),
              @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast m) X →
                And
                  (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.highWeight m n))
                  (@LE.le.{0} Real Real.instLE (D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.highWeight m n)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.primeProduct X)
                        (D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.primeProduct
                          (@Nat.cast.{0} Real Real.instNatCast m)))
                      (Real.exp
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (Real.log (@Nat.cast.{0} Real Real.instNatCast n))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) X
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                            (Real.log X)))))))
      (And
        (∀ (C : Real),
          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
            ∀ (ε : Real),
              @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  ε →
                @Filter.Eventually.{0} Nat
                  (fun (m : Nat) =>
                    ∀ (a b : Nat),
                      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) a →
                        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b →
                          @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast a)
                              (Real.exp
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                                    (@Nat.cast.{0} Real Real.instNatCast m))
                                  (Real.log (@Nat.cast.{0} Real Real.instNatCast m)))) →
                            @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast b)
                                (Real.exp
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                                      (@Nat.cast.{0} Real Real.instNatCast m))
                                    (Real.log (@Nat.cast.{0} Real Real.instNatCast m)))) →
                              Nat.ModEq (Nat.factorial m) a b →
                                @LT.lt.{0} Real Real.instLT
                                  (@abs.{0} Real Real.lattice Real.instAddGroup
                                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                        (D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.normalizedWeight a)
                                        (D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.normalizedWeight b))
                                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
                                  ε)
                  (@Filter.atTop.{0} Nat Nat.instPreorder))
        (∀ (C : Real),
          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
            @Filter.Tendsto.{0, 0} Nat Real
              (fun (m : Nat) => D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.uniformError C m)
              (@Filter.atTop.{0} Nat Nat.instPreorder)
              (@nhds.{0} Real
                (@UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))))
    Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration)

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"UniformDivisorWeightTransfer\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"UniformDivisorWeightTransfer\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer, declaration := `D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.arena
  (And
    (∀ (m n : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m →
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
          ∀ (X : Real),
            @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast m) X →
              And
                (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.highWeight m n))
                (@LE.le.{0} Real Real.instLE (D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.highWeight m n)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.primeProduct X)
                      (D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.primeProduct
                        (@Nat.cast.{0} Real Real.instNatCast m)))
                    (Real.exp
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (Real.log (@Nat.cast.{0} Real Real.instNatCast n))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) X
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                          (Real.log X)))))))
    (And
      (∀ (C : Real),
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
          ∀ (ε : Real),
            @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
              @Filter.Eventually.{0} Nat
                (fun (m : Nat) =>
                  ∀ (a b : Nat),
                    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) a →
                      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b →
                        @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast a)
                            (Real.exp
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                                  (@Nat.cast.{0} Real Real.instNatCast m))
                                (Real.log (@Nat.cast.{0} Real Real.instNatCast m)))) →
                          @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast b)
                              (Real.exp
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                                    (@Nat.cast.{0} Real Real.instNatCast m))
                                  (Real.log (@Nat.cast.{0} Real Real.instNatCast m)))) →
                            Nat.ModEq (Nat.factorial m) a b →
                              @LT.lt.{0} Real Real.instLT
                                (@abs.{0} Real Real.lattice Real.instAddGroup
                                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                      (D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.normalizedWeight a)
                                      (D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.normalizedWeight b))
                                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
                                ε)
                (@Filter.atTop.{0} Nat Nat.instPreorder))
      (∀ (C : Real),
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
          @Filter.Tendsto.{0, 0} Nat Real
            (fun (m : Nat) => D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.uniformError C m)
            (@Filter.atTop.{0} Nat Nat.instPreorder)
            (@nhds.{0} Real
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))))
  Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration)

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration_1.observation0 : (C : Real) →
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
    (ε : Real) →
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
        (m a b : Nat) →
          @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) a →
            @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b →
              @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast a)
                  (Real.exp
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                        (@Nat.cast.{0} Real Real.instNatCast m))
                      (Real.log (@Nat.cast.{0} Real Real.instNatCast m)))) →
                @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast b)
                    (Real.exp
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                          (@Nat.cast.{0} Real Real.instNatCast m))
                        (Real.log (@Nat.cast.{0} Real Real.instNatCast m)))) →
                  Nat.ModEq (Nat.factorial m) a b →
                    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
                        Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.signature PUnit.unit.{1} →
                      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                        Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.signature PUnit.unit.{1}
                        PUnit.unit.{1} :=
  fun (C : Real)
    (a : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C)
    (ε : Real)
    (a_1 : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
    (m a_2 b : Nat) (a_3 : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) a_2)
    (a_4 : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b)
    (a_5 :
      @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast a_2)
        (Real.exp
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
              (@Nat.cast.{0} Real Real.instNatCast m))
            (Real.log (@Nat.cast.{0} Real Real.instNatCast m)))))
    (a_6 :
      @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast b)
        (Real.exp
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
              (@Nat.cast.{0} Real Real.instNatCast m))
            (Real.log (@Nat.cast.{0} Real Real.instNatCast m)))))
    (a_7 : Nat.ModEq (Nat.factorial m) a_2 b) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.signature
    Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.actual PUnit.unit.{1} PUnit.unit.{1}

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"UniformDivisorWeightTransfer\",\"result\"],\"part\":\"type\",\"path\":[\"argument\",\"function\",\"argument\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"argument\",\"function\",\"argument\",\"function\",\"argument\",\"function\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"UniformDivisorWeightTransfer\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer, declaration := `D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.result, part := .type, path := [.argument, .function, .argument, .body, .body, .body, .body, .function, .argument, .body, .body, .body, .body, .body, .body, .body, .body, .function, .argument, .argument, .function, .argument, .function, .argument, .function], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"UniformDivisorWeightTransfer\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"UniformDivisorWeightTransfer\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"UniformDivisorWeightTransfer\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer, declaration := `D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration).actual (Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration).variation.2.choose (Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration).variation.1 (Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"UniformDivisorWeightTransfer\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"UniformDivisorWeightTransfer\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
