import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare

open _root_.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialCoefficients
open _root_.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := ℕ
  State := fun _ => ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature
    (fun _ r x => (fibonacciRecurrencePolynomial (2 * r + 1)).eval x)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℤ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law a :=
    (∀ (r : ℕ), 119 ≤ r → ∀ (x : ℤ), 2 < x →
      128 * (6 : ℤ) ^ r < x ^ 2 - 4 →
      ¬ IsSquare (a.readout () r x)) ∧
    (∀ (r n : ℕ), 119 ≤ r → Odd n → 2 * r + 1 ≤ n →
      0 < Nat.fib ((2 * r + 1) * n) / Nat.fib n ∧
      ¬ IsSquare (Nat.fib ((2 * r + 1) * n) / Nat.fib n)) ∧
    (∀ (q k : ℕ), q.Prime → 239 ≤ q → 1 ≤ k →
      0 < Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k) ∧
      ¬ IsSquare (Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k)))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let x0 : ℤ := 128 * 6 ^ 119 + 5
  have hpow : 0 ≤ (6 : ℤ) ^ 119 := pow_nonneg (by norm_num) _
  have hx : 2 < x0 := by
    dsimp [x0]
    nlinarith
  have hsize : 128 * (6 : ℤ) ^ 119 < x0 ^ 2 - 4 := by
    dsimp [x0]
    nlinarith [sq_nonneg ((6 : ℤ) ^ 119)]
  have hbad := h.1 119 (by decide) x0 hx hsize
  change ¬ IsSquare (0 : ℤ) at hbad
  exact hbad ⟨0, by norm_num⟩

noncomputable def registration : Registration arena
    ((∀ (r : ℕ), 119 ≤ r → ∀ (x : ℤ), 2 < x →
      128 * (6 : ℤ) ^ r < x ^ 2 - 4 →
      ¬ IsSquare ((fibonacciRecurrencePolynomial (2 * r + 1)).eval x)) ∧
    (∀ (r n : ℕ), 119 ≤ r → Odd n → 2 * r + 1 ≤ n →
      0 < Nat.fib ((2 * r + 1) * n) / Nat.fib n ∧
      ¬ IsSquare (Nat.fib ((2 * r + 1) * n) / Nat.fib n)) ∧
    (∀ (q k : ℕ), q.Prime → 239 ≤ q → 1 ≤ k →
      0 < Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k) ∧
      ¬ IsSquare (Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k)))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fibonacci_recurrence_polynomial_nonsquare, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨1, (0 : ℤ), (1 : ℤ), ?_⟩
    change (fibonacciRecurrencePolynomial (2 * 1 + 1)).eval (0 : ℤ) ≠
      (fibonacciRecurrencePolynomial (2 * 1 + 1)).eval (1 : ℤ)
    norm_num [fibonacciRecurrencePolynomial]

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.fibonacci_recurrence_polynomial_nonsquare) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ r x => (fibonacciRecurrencePolynomial (2 * r + 1)).eval x)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Primes") "FibonacciRecurrencePolynomialNonsquare") "fibonacci_recurrence_polynomial_nonsquare") "Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare/Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration,
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
    (fun _ r x => (fibonacciRecurrencePolynomial (2 * r + 1)).eval x)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare, definition := none, coordinates := #[0], readouts := #[{ path := #["fn", "arg", "body", "body", "body", "body", "body", "arg", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare, declaration := `D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.fibonacci_recurrence_polynomial_nonsquare, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration_1.observationFact0, `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration_1.anchorEnumeration }


end Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare


noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.arena
noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRecurrencePolynomialNonsquare\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRecurrencePolynomialNonsquare\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.arena
noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRecurrencePolynomialNonsquare\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRecurrencePolynomialNonsquare\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.arena
    (And
      (∀ (r : Nat),
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 119) (instOfNatNat (nat_lit 119))) r →
          ∀ (x : Int),
            @LT.lt.{0} Int Int.instLTInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) x →
              @LT.lt.{0} Int Int.instLTInt
                  (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                    (@OfNat.ofNat.{0} Int (nat_lit 128) (@instOfNat (nat_lit 128)))
                    (@HPow.hPow.{0, 0, 0} Int Nat Int
                      (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                      (@OfNat.ofNat.{0} Int (nat_lit 6) (@instOfNat (nat_lit 6))) r))
                  (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
                    (@HPow.hPow.{0, 0, 0} Int Nat Int
                      (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid))) x
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4)))) →
                Not
                  (@IsSquare.{0} Int Int.instMul
                    (@Polynomial.eval.{0} Int Int.instSemiring x
                      (D5.S3.Arith.Primes.FibonacciRecurrencePolynomialCoefficients.fibonacciRecurrencePolynomial
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
      (And
        (∀ (r n : Nat),
          @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 119) (instOfNatNat (nat_lit 119))) r →
            @Odd.{0} Nat Nat.instSemiring n →
              @LE.le.{0} Nat instLENat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  n →
                And
                  (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                      (Nat.fib
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          n))
                      (Nat.fib n)))
                  (Not
                    (@IsSquare.{0} Nat instMulNat
                      (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                        (Nat.fib
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            n))
                        (Nat.fib n)))))
        (∀ (q k : Nat),
          Nat.Prime q →
            @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 239) (instOfNatNat (nat_lit 239))) q →
              @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k →
                And
                  (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                      (Nat.fib
                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                      (Nat.fib
                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q
                          k))))
                  (Not
                    (@IsSquare.{0} Nat instMulNat
                      (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                        (Nat.fib
                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                        (Nat.fib
                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q
                            k))))))))
    Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration)

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRecurrencePolynomialNonsquare\",\"fibonacci_recurrence_polynomial_nonsquare\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRecurrencePolynomialNonsquare\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare, declaration := `D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.fibonacci_recurrence_polynomial_nonsquare, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.arena
  (And
    (∀ (r : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 119) (instOfNatNat (nat_lit 119))) r →
        ∀ (x : Int),
          @LT.lt.{0} Int Int.instLTInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) x →
            @LT.lt.{0} Int Int.instLTInt
                (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
                  (@OfNat.ofNat.{0} Int (nat_lit 128) (@instOfNat (nat_lit 128)))
                  (@HPow.hPow.{0, 0, 0} Int Nat Int
                    (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                    (@OfNat.ofNat.{0} Int (nat_lit 6) (@instOfNat (nat_lit 6))) r))
                (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
                  (@HPow.hPow.{0, 0, 0} Int Nat Int
                    (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid))) x
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4)))) →
              Not
                (@IsSquare.{0} Int Int.instMul
                  (@Polynomial.eval.{0} Int Int.instSemiring x
                    (D5.S3.Arith.Primes.FibonacciRecurrencePolynomialCoefficients.fibonacciRecurrencePolynomial
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
    (And
      (∀ (r n : Nat),
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 119) (instOfNatNat (nat_lit 119))) r →
          @Odd.{0} Nat Nat.instSemiring n →
            @LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                n →
              And
                (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                    (Nat.fib
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        n))
                    (Nat.fib n)))
                (Not
                  (@IsSquare.{0} Nat instMulNat
                    (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                      (Nat.fib
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          n))
                      (Nat.fib n)))))
      (∀ (q k : Nat),
        Nat.Prime q →
          @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 239) (instOfNatNat (nat_lit 239))) q →
            @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k →
              And
                (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                    (Nat.fib
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    (Nat.fib
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q k))))
                (Not
                  (@IsSquare.{0} Nat instMulNat
                    (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                      (Nat.fib
                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                      (Nat.fib
                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q
                          k))))))))
  Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration)

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration_1.observation0 : (r : Nat) →
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 119) (instOfNatNat (nat_lit 119))) r →
    (x : Int) →
      @LT.lt.{0} Int Int.instLTInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) x →
        @LT.lt.{0} Int Int.instLTInt
            (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
              (@OfNat.ofNat.{0} Int (nat_lit 128) (@instOfNat (nat_lit 128)))
              (@HPow.hPow.{0, 0, 0} Int Nat Int
                (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                (@OfNat.ofNat.{0} Int (nat_lit 6) (@instOfNat (nat_lit 6))) r))
            (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
              (@HPow.hPow.{0, 0, 0} Int Nat Int
                (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid))) x
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4)))) →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
            Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.signature PUnit.unit.{1} r :=
  fun (r : Nat) (a : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 119) (instOfNatNat (nat_lit 119))) r)
    (x : Int) (a_1 : @LT.lt.{0} Int Int.instLTInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) x)
    (a_2 :
      @LT.lt.{0} Int Int.instLTInt
        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
          (@OfNat.ofNat.{0} Int (nat_lit 128) (@instOfNat (nat_lit 128)))
          (@HPow.hPow.{0, 0, 0} Int Nat Int
            (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
            (@OfNat.ofNat.{0} Int (nat_lit 6) (@instOfNat (nat_lit 6))) r))
        (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
          (@HPow.hPow.{0, 0, 0} Int Nat Int
            (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid))) x
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4))))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.signature
    Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.actual PUnit.unit.{1} r x

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRecurrencePolynomialNonsquare\",\"fibonacci_recurrence_polynomial_nonsquare\"],\"part\":\"type\",\"path\":[\"function\",\"argument\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRecurrencePolynomialNonsquare\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare, declaration := `D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.fibonacci_recurrence_polynomial_nonsquare, part := .type, path := [.function, .argument, .body, .body, .body, .body, .body, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRecurrencePolynomialNonsquare\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRecurrencePolynomialNonsquare\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRecurrencePolynomialNonsquare\",\"fibonacci_recurrence_polynomial_nonsquare\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare, declaration := `D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.fibonacci_recurrence_polynomial_nonsquare, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration).actual (Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration).variation.2.choose (Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration).variation.1 (Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRecurrencePolynomialNonsquare\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRecurrencePolynomialNonsquare\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
