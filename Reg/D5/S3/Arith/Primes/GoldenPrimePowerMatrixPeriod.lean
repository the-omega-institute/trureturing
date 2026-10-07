import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod

open scoped Matrix
open _root_.D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open _root_.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ p a =>
      let τ := orderOf
        (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p))
      let h := padicValNat p (Nat.fib (fibonacciRank p))
      τ * p ^ (a - h))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature
    (fun _ p a =>
      let τ := orderOf
        (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p))
      let h := padicValNat p (Nat.fib (fibonacciRank p))
      τ * p ^ (a - h) + 1)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (p a : ℕ) (_hp : p.Prime) (_hpFive : 5 < p) (_ha : 1 ≤ a),
    let τ := orderOf
      (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p))
    let h := padicValNat p (Nat.fib (fibonacciRank p))
    0 < h ∧
      padicValNat p (Nat.fib τ) = h ∧
      padicValNat p (Nat.fib τ) = padicValNat p (Nat.fib (τ - 1) - 1) ∧
      Even τ ∧
      (Nat.fib (τ - 1) - 1) * (Nat.fib (τ - 1) + 1) =
        Nat.fib τ * (Nat.fib τ - Nat.fib (τ - 1)) ∧
      (¬ p ∣ Nat.fib (τ - 1) + 1 ∧
        ¬ p ∣ Nat.fib τ - Nat.fib (τ - 1)) ∧
      (∃ u v : ℕ,
        Nat.fib (τ - 1) = 1 + p ^ h * u ∧
        Nat.fib τ = p ^ h * v ∧ ¬ p ∣ v ∧
        ∃ A : Matrix (Fin 2) (Fin 2) ℕ,
          A = !![u + v, v; v, u] ∧
          (∀ q : ℕ,
            (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod q)) ^ τ =
              1 + ((p ^ h : ℕ) : ZMod q) •
                A.map (Nat.castRingHom (ZMod q))) ∧
          A.map (Nat.castRingHom (ZMod p)) ≠ 0) ∧
      (∀ m : ℕ, 0 < m →
        ((!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod (p ^ a))) ^
            (τ * m) = 1 ↔ a ≤ h + padicValNat p m)) ∧
      (∀ n : ℕ,
        (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod (p ^ a))) ^ n = 1 →
          τ ∣ n) ∧
      orderOf
        (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod (p ^ a))) =
        r.readout () p a

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let τ7 := orderOf
    (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod 7))
  let h7 := padicValNat 7 (Nat.fib (fibonacciRank 7))
  have hgood := (golden_matrix_prime_power_period 7 1
    (by decide) (by decide) (by decide)).2.2.2.2.2.2.2.2.2
  have hbad := (h 7 1 (by decide) (by decide) (by decide)).2.2.2.2.2.2.2.2.2
  change orderOf
      (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod (7 ^ 1))) =
    τ7 * 7 ^ (1 - h7) at hgood
  change orderOf
      (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod (7 ^ 1))) =
    τ7 * 7 ^ (1 - h7) + 1 at hbad
  omega

def registration : Registration arena
    (∀ (p a : ℕ) (_hp : p.Prime) (_hpFive : 5 < p) (_ha : 1 ≤ a),
      let τ := orderOf
        (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p))
      let h := padicValNat p (Nat.fib (fibonacciRank p))
      0 < h ∧
        padicValNat p (Nat.fib τ) = h ∧
        padicValNat p (Nat.fib τ) = padicValNat p (Nat.fib (τ - 1) - 1) ∧
        Even τ ∧
        (Nat.fib (τ - 1) - 1) * (Nat.fib (τ - 1) + 1) =
          Nat.fib τ * (Nat.fib τ - Nat.fib (τ - 1)) ∧
        (¬ p ∣ Nat.fib (τ - 1) + 1 ∧
          ¬ p ∣ Nat.fib τ - Nat.fib (τ - 1)) ∧
        (∃ u v : ℕ,
          Nat.fib (τ - 1) = 1 + p ^ h * u ∧
          Nat.fib τ = p ^ h * v ∧ ¬ p ∣ v ∧
          ∃ A : Matrix (Fin 2) (Fin 2) ℕ,
            A = !![u + v, v; v, u] ∧
            (∀ q : ℕ,
              (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod q)) ^ τ =
                1 + ((p ^ h : ℕ) : ZMod q) •
                  A.map (Nat.castRingHom (ZMod q))) ∧
            A.map (Nat.castRingHom (ZMod p)) ≠ 0) ∧
        (∀ m : ℕ, 0 < m →
          ((!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod (p ^ a))) ^
              (τ * m) = 1 ↔ a ≤ h + padicValNat p m)) ∧
        (∀ n : ℕ,
          (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod (p ^ a))) ^ n = 1 →
            τ ∣ n) ∧
        orderOf
          (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod (p ^ a))) =
          τ * p ^ (a - h)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨golden_matrix_prime_power_period, rejected, rejected_law⟩
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
    let h7 := padicValNat 7 (Nat.fib (fibonacciRank 7))
    let τ7 := orderOf
      (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod 7))
    have hunit : IsUnit
        (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod 7)) := by
      rw [Matrix.isUnit_iff_isUnit_det]
      simp [Matrix.det_fin_two_of]
    have htpos : 0 < τ7 := hunit.isOfFinOrder.orderOf_pos
    refine ⟨7, h7 + 1, h7 + 2, ?_⟩
    change τ7 * 7 ^ (h7 + 1 - h7) ≠ τ7 * 7 ^ (h7 + 2 - h7)
    have hfirst : h7 + 1 - h7 = 1 := by omega
    have hsecond : h7 + 2 - h7 = 2 := by omega
    rw [hfirst, hsecond]
    intro heq
    norm_num at heq
    omega

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.golden_matrix_prime_power_period) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ p a =>
      let τ := orderOf.{0}
        (!![1, 1; 1, 0] : Matrix.{0, 0, 0} (Fin 2) (Fin 2) (ZMod p))
      let h := padicValNat p (Nat.fib (fibonacciRank p))
      τ * p ^ (a - h))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Primes") "GoldenPrimePowerMatrixPeriod") "golden_matrix_prime_power_period") "Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod/Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration,
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
    (fun _ p a =>
      let τ := orderOf.{0}
        (!![1, 1; 1, 0] : Matrix.{0, 0, 0} (Fin 2) (Fin 2) (ZMod p))
      let h := padicValNat p (Nat.fib (fibonacciRank p))
      τ * p ^ (a - h))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod, declaration := `D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.golden_matrix_prime_power_period, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod, declaration := `Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod, declaration := `Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod, declaration := `Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod, declaration := `Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration_1.observationFact0, `Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration_1.anchorEnumeration }


end
end Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod


noncomputable def Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.arena
noncomputable def Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenPrimePowerMatrixPeriod\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenPrimePowerMatrixPeriod\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod, declaration := `Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod, declaration := `Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.arena
noncomputable def Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenPrimePowerMatrixPeriod\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenPrimePowerMatrixPeriod\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod, declaration := `Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod, declaration := `Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.arena
    (∀ (p a : _) (_hp : _) (_hpFive : _) (_ha : _),
      have τ : _ :=
        @orderOf.{0}
          (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod p))
          (@Semiring.toMonoid.{0}
            (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod p))
            (@Matrix.semiring.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod p)
              (@CommSemiring.toSemiring.{0} (ZMod p) (@CommRing.toCommSemiring.{0} (ZMod p) (ZMod.commRing p)))
              (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
          (@DFunLike.coe.{1, 1, 1}
            (Equiv.{1, 1}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod p)
              (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod p)))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
              Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod p)
            (fun
                (x :
                  Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                    Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod p) =>
              Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod p))
            (@EquivLike.toFunLike.{1, 1, 1}
              (Equiv.{1, 1}
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                  Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod p)
                (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod p)))
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod p)
              (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod p))
              (@Equiv.instEquivLike.{1, 1}
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                  Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod p)
                (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod p))))
            (@Matrix.of.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod p))
            (@Matrix.vecCons.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod p)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Matrix.vecCons.{0} (ZMod p) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@OfNat.ofNat.{0} (ZMod p) (nat_lit 1)
                  (@One.toOfNat1.{0} (ZMod p)
                    (@AddMonoidWithOne.toOne.{0} (ZMod p)
                      (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod p)
                        (@Ring.toAddGroupWithOne.{0} (ZMod p) (@CommRing.toRing.{0} (ZMod p) (ZMod.commRing p)))))))
                (@Matrix.vecCons.{0} (ZMod p) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@OfNat.ofNat.{0} (ZMod p) (nat_lit 1)
                    (@One.toOfNat1.{0} (ZMod p)
                      (@AddMonoidWithOne.toOne.{0} (ZMod p)
                        (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod p)
                          (@Ring.toAddGroupWithOne.{0} (ZMod p) (@CommRing.toRing.{0} (ZMod p) (ZMod.commRing p)))))))
                  (@Matrix.vecEmpty.{0} (ZMod p))))
              (@Matrix.vecCons.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod p)
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@Matrix.vecCons.{0} (ZMod p) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@OfNat.ofNat.{0} (ZMod p) (nat_lit 1)
                    (@One.toOfNat1.{0} (ZMod p)
                      (@AddMonoidWithOne.toOne.{0} (ZMod p)
                        (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod p)
                          (@Ring.toAddGroupWithOne.{0} (ZMod p) (@CommRing.toRing.{0} (ZMod p) (ZMod.commRing p)))))))
                  (@Matrix.vecCons.{0} (ZMod p) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@OfNat.ofNat.{0} (ZMod p) (nat_lit 0)
                      (@Zero.toOfNat0.{0} (ZMod p)
                        (@MulZeroClass.toZero.{0} (ZMod p)
                          (@instMulZeroClassOfSemiring.{0} (ZMod p)
                            (@CommSemiring.toSemiring.{0} (ZMod p)
                              (@CommRing.toCommSemiring.{0} (ZMod p) (ZMod.commRing p)))))))
                    (@Matrix.vecEmpty.{0} (ZMod p))))
                (@Matrix.vecEmpty.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod p)))));
      have h : _ := padicValNat p (Nat.fib (D5.S3.Arith.Primes.FiniteFibonacciRankClosure.fibonacciRank p));
      And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) h)
        (And (@Eq.{1} Nat (padicValNat p (Nat.fib τ)) h)
          (And
            (@Eq.{1} Nat (padicValNat p (Nat.fib τ))
              (padicValNat p
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                  (Nat.fib
                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) τ
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (And (@Even.{0} Nat instAddNat τ)
              (And
                (@Eq.{1} Nat
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                      (Nat.fib
                        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) τ
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (Nat.fib
                        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) τ
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (Nat.fib τ)
                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (Nat.fib τ)
                      (Nat.fib
                        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) τ
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
                (And
                  (And
                    (Not
                      (@Dvd.dvd.{0} Nat Nat.instDvd p
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (Nat.fib
                            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) τ
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    (Not
                      (@Dvd.dvd.{0} Nat Nat.instDvd p
                        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (Nat.fib τ)
                          (Nat.fib
                            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) τ
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
                  (And
                    (@Exists.{1} Nat fun (u : Nat) =>
                      @Exists.{1} Nat fun (v : Nat) =>
                        And
                          (@Eq.{1} Nat
                            (Nat.fib
                              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) τ
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat
                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                  p h)
                                u)))
                          (And
                            (@Eq.{1} Nat (Nat.fib τ)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat
                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                  p h)
                                v))
                            (And (Not (@Dvd.dvd.{0} Nat Nat.instDvd p v))
                              (@Exists.{1}
                                (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Nat)
                                fun
                                  (A :
                                    Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Nat) =>
                                And
                                  (@Eq.{1}
                                    (Matrix.{0, 0, 0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Nat)
                                    A
                                    (@DFunLike.coe.{1, 1, 1}
                                      (Equiv.{1, 1}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                          Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Nat)
                                        (Matrix.{0, 0, 0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Nat))
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                        Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Nat)
                                      (fun
                                          (x :
                                            Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                              Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                                Nat) =>
                                        Matrix.{0, 0, 0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Nat)
                                      (@EquivLike.toFunLike.{1, 1, 1}
                                        (Equiv.{1, 1}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                            Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Nat)
                                          (Matrix.{0, 0, 0}
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Nat))
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                          Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Nat)
                                        (Matrix.{0, 0, 0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Nat)
                                        (@Equiv.instEquivLike.{1, 1}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                            Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Nat)
                                          (Matrix.{0, 0, 0}
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Nat)))
                                      (@Matrix.of.{0, 0, 0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Nat)
                                      (@Matrix.vecCons.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Nat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                        (@Matrix.vecCons.{0} Nat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) u v)
                                          (@Matrix.vecCons.{0} Nat
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) v
                                            (@Matrix.vecEmpty.{0} Nat)))
                                        (@Matrix.vecCons.{0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Nat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                          (@Matrix.vecCons.{0} Nat
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) v
                                            (@Matrix.vecCons.{0} Nat
                                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) u
                                              (@Matrix.vecEmpty.{0} Nat)))
                                          (@Matrix.vecEmpty.{0}
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                              Nat))))))
                                  (And
                                    (∀ (q : Nat),
                                      @Eq.{1}
                                        (Matrix.{0, 0, 0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod q))
                                        (@HPow.hPow.{0, 0, 0}
                                          (Matrix.{0, 0, 0}
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                            (ZMod q))
                                          Nat
                                          (Matrix.{0, 0, 0}
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                            (ZMod q))
                                          (@instHPow.{0, 0}
                                            (Matrix.{0, 0, 0}
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (ZMod q))
                                            Nat
                                            (@NPow.toPow.{0}
                                              (Matrix.{0, 0, 0}
                                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                (ZMod q))
                                              (@Monoid.toNPow.{0}
                                                (Matrix.{0, 0, 0}
                                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                  (ZMod q))
                                                (@Semiring.toMonoid.{0}
                                                  (Matrix.{0, 0, 0}
                                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                    (ZMod q))
                                                  (@Matrix.semiring.{0, 0}
                                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                    (ZMod q)
                                                    (@CommSemiring.toSemiring.{0} (ZMod q)
                                                      (@CommRing.toCommSemiring.{0} (ZMod q) (ZMod.commRing q)))
                                                    (Fin.fintype
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                    (instDecidableEqFin
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                        (instOfNatNat (nat_lit 2)))))))))
                                          (@DFunLike.coe.{1, 1, 1}
                                            (Equiv.{1, 1}
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                                Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                                  ZMod q)
                                              (Matrix.{0, 0, 0}
                                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                (ZMod q)))
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                              Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                                ZMod q)
                                            (fun
                                                (x :
                                                  Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                                    Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                                      ZMod q) =>
                                              Matrix.{0, 0, 0}
                                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                (ZMod q))
                                            (@EquivLike.toFunLike.{1, 1, 1}
                                              (Equiv.{1, 1}
                                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                                  Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                                    ZMod q)
                                                (Matrix.{0, 0, 0}
                                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                  (ZMod q)))
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                                Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                                  ZMod q)
                                              (Matrix.{0, 0, 0}
                                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                (ZMod q))
                                              (@Equiv.instEquivLike.{1, 1}
                                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                                  Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                                    ZMod q)
                                                (Matrix.{0, 0, 0}
                                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                  (ZMod q))))
                                            (@Matrix.of.{0, 0, 0}
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (ZMod q))
                                            (@Matrix.vecCons.{0}
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                                ZMod q)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                              (@Matrix.vecCons.{0} (ZMod q)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                                (@OfNat.ofNat.{0} (ZMod q) (nat_lit 1)
                                                  (@One.toOfNat1.{0} (ZMod q)
                                                    (@AddMonoidWithOne.toOne.{0} (ZMod q)
                                                      (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod q)
                                                        (@Ring.toAddGroupWithOne.{0} (ZMod q)
                                                          (@CommRing.toRing.{0} (ZMod q) (ZMod.commRing q)))))))
                                                (@Matrix.vecCons.{0} (ZMod q)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                                  (@OfNat.ofNat.{0} (ZMod q) (nat_lit 1)
                                                    (@One.toOfNat1.{0} (ZMod q)
                                                      (@AddMonoidWithOne.toOne.{0} (ZMod q)
                                                        (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod q)
                                                          (@Ring.toAddGroupWithOne.{0} (ZMod q)
                                                            (@CommRing.toRing.{0} (ZMod q) (ZMod.commRing q)))))))
                                                  (@Matrix.vecEmpty.{0} (ZMod q))))
                                              (@Matrix.vecCons.{0}
                                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                                  ZMod q)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                                (@Matrix.vecCons.{0} (ZMod q)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                                  (@OfNat.ofNat.{0} (ZMod q) (nat_lit 1)
                                                    (@One.toOfNat1.{0} (ZMod q)
                                                      (@AddMonoidWithOne.toOne.{0} (ZMod q)
                                                        (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod q)
                                                          (@Ring.toAddGroupWithOne.{0} (ZMod q)
                                                            (@CommRing.toRing.{0} (ZMod q) (ZMod.commRing q)))))))
                                                  (@Matrix.vecCons.{0} (ZMod q)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                                    (@OfNat.ofNat.{0} (ZMod q) (nat_lit 0)
                                                      (@Zero.toOfNat0.{0} (ZMod q)
                                                        (@MulZeroClass.toZero.{0} (ZMod q)
                                                          (@instMulZeroClassOfSemiring.{0} (ZMod q)
                                                            (@CommSemiring.toSemiring.{0} (ZMod q)
                                                              (@CommRing.toCommSemiring.{0} (ZMod q)
                                                                (ZMod.commRing q)))))))
                                                    (@Matrix.vecEmpty.{0} (ZMod q))))
                                                (@Matrix.vecEmpty.{0}
                                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                                    ZMod q)))))
                                          τ)
                                        (@HAdd.hAdd.{0, 0, 0}
                                          (Matrix.{0, 0, 0}
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                            (ZMod q))
                                          (Matrix.{0, 0, 0}
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                            (ZMod q))
                                          (Matrix.{0, 0, 0}
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                            (ZMod q))
                                          (@instHAdd.{0}
                                            (Matrix.{0, 0, 0}
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (ZMod q))
                                            (@Matrix.add.{0, 0, 0}
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (ZMod q)
                                              (@Distrib.toAdd.{0} (ZMod q)
                                                (@instDistribOfSemiring.{0} (ZMod q)
                                                  (@CommSemiring.toSemiring.{0} (ZMod q)
                                                    (@CommRing.toCommSemiring.{0} (ZMod q) (ZMod.commRing q)))))))
                                          (@OfNat.ofNat.{0}
                                            (Matrix.{0, 0, 0}
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (ZMod q))
                                            (nat_lit 1)
                                            (@One.toOfNat1.{0}
                                              (Matrix.{0, 0, 0}
                                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                (ZMod q))
                                              (@Matrix.one.{0, 0}
                                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                (ZMod q)
                                                (instDecidableEqFin
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                (@MulZeroClass.toZero.{0} (ZMod q)
                                                  (@instMulZeroClassOfSemiring.{0} (ZMod q)
                                                    (@CommSemiring.toSemiring.{0} (ZMod q)
                                                      (@CommRing.toCommSemiring.{0} (ZMod q) (ZMod.commRing q)))))
                                                (@AddMonoidWithOne.toOne.{0} (ZMod q)
                                                  (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod q)
                                                    (@Ring.toAddGroupWithOne.{0} (ZMod q)
                                                      (@CommRing.toRing.{0} (ZMod q) (ZMod.commRing q))))))))
                                          (@HSMul.hSMul.{0, 0, 0} (ZMod q)
                                            (Matrix.{0, 0, 0}
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (ZMod q))
                                            (Matrix.{0, 0, 0}
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (ZMod q))
                                            (@instHSMul.{0, 0} (ZMod q)
                                              (Matrix.{0, 0, 0}
                                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                (ZMod q))
                                              (@Matrix.smul.{0, 0, 0, 0}
                                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                (ZMod q) (ZMod q)
                                                (@instSMulOfMul.{0} (ZMod q)
                                                  (@Distrib.toMul.{0} (ZMod q)
                                                    (@instDistribOfSemiring.{0} (ZMod q)
                                                      (@CommSemiring.toSemiring.{0} (ZMod q)
                                                        (@CommRing.toCommSemiring.{0} (ZMod q) (ZMod.commRing q))))))))
                                            (@Nat.cast.{0} (ZMod q)
                                              (@AddMonoidWithOne.toNatCast.{0} (ZMod q)
                                                (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod q)
                                                  (@Ring.toAddGroupWithOne.{0} (ZMod q)
                                                    (@CommRing.toRing.{0} (ZMod q) (ZMod.commRing q)))))
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p h))
                                            (@Matrix.map.{0, 0, 0, 0}
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Nat
                                              (ZMod q) A
                                              (@DFunLike.coe.{1, 1, 1}
                                                (@RingHom.{0, 0} Nat (ZMod q) Nat.instNonAssocSemiring
                                                  (@Semiring.toNonAssocSemiring.{0} (ZMod q)
                                                    (@CommSemiring.toSemiring.{0} (ZMod q)
                                                      (@CommRing.toCommSemiring.{0} (ZMod q) (ZMod.commRing q)))))
                                                Nat (fun (x : Nat) => ZMod q)
                                                (@RingHom.instFunLike.{0, 0} Nat (ZMod q) Nat.instNonAssocSemiring
                                                  (@Semiring.toNonAssocSemiring.{0} (ZMod q)
                                                    (@CommSemiring.toSemiring.{0} (ZMod q)
                                                      (@CommRing.toCommSemiring.{0} (ZMod q) (ZMod.commRing q)))))
                                                (@Nat.castRingHom.{0} (ZMod q)
                                                  (@Semiring.toNonAssocSemiring.{0} (ZMod q)
                                                    (@CommSemiring.toSemiring.{0} (ZMod q)
                                                      (@CommRing.toCommSemiring.{0} (ZMod q) (ZMod.commRing q))))))))))
                                    (@Ne.{1}
                                      (Matrix.{0, 0, 0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod p))
                                      (@Matrix.map.{0, 0, 0, 0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Nat (ZMod p)
                                        A
                                        (@DFunLike.coe.{1, 1, 1}
                                          (@RingHom.{0, 0} Nat (ZMod p) Nat.instNonAssocSemiring
                                            (@Semiring.toNonAssocSemiring.{0} (ZMod p)
                                              (@CommSemiring.toSemiring.{0} (ZMod p)
                                                (@CommRing.toCommSemiring.{0} (ZMod p) (ZMod.commRing p)))))
                                          Nat (fun (x : Nat) => ZMod p)
                                          (@RingHom.instFunLike.{0, 0} Nat (ZMod p) Nat.instNonAssocSemiring
                                            (@Semiring.toNonAssocSemiring.{0} (ZMod p)
                                              (@CommSemiring.toSemiring.{0} (ZMod p)
                                                (@CommRing.toCommSemiring.{0} (ZMod p) (ZMod.commRing p)))))
                                          (@Nat.castRingHom.{0} (ZMod p)
                                            (@Semiring.toNonAssocSemiring.{0} (ZMod p)
                                              (@CommSemiring.toSemiring.{0} (ZMod p)
                                                (@CommRing.toCommSemiring.{0} (ZMod p) (ZMod.commRing p)))))))
                                      (@OfNat.ofNat.{0}
                                        (Matrix.{0, 0, 0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod p))
                                        (nat_lit 0)
                                        (@Zero.toOfNat0.{0}
                                          (Matrix.{0, 0, 0}
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                            (ZMod p))
                                          (@Matrix.zero.{0, 0, 0}
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod p)
                                            (@MulZeroClass.toZero.{0} (ZMod p)
                                              (@instMulZeroClassOfSemiring.{0} (ZMod p)
                                                (@CommSemiring.toSemiring.{0} (ZMod p)
                                                  (@CommRing.toCommSemiring.{0} (ZMod p) (ZMod.commRing p))))))))))))))
                    (And
                      (∀ (m : Nat),
                        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m →
                          Iff
                            (@Eq.{1}
                              (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (ZMod
                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                    (@instHPow.{0, 0} Nat Nat
                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                    p a)))
                              (@HPow.hPow.{0, 0, 0}
                                (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (ZMod
                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                      (@instHPow.{0, 0} Nat Nat
                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                      p a)))
                                Nat
                                (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (ZMod
                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                      (@instHPow.{0, 0} Nat Nat
                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                      p a)))
                                (@instHPow.{0, 0}
                                  (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (ZMod
                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                        (@instHPow.{0, 0} Nat Nat
                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                        p a)))
                                  Nat
                                  (@NPow.toPow.{0}
                                    (Matrix.{0, 0, 0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a)))
                                    (@Monoid.toNPow.{0}
                                      (Matrix.{0, 0, 0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a)))
                                      (@Semiring.toMonoid.{0}
                                        (Matrix.{0, 0, 0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a)))
                                        (@Matrix.semiring.{0, 0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))
                                          (@CommSemiring.toSemiring.{0}
                                            (ZMod
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p a))
                                            (@CommRing.toCommSemiring.{0}
                                              (ZMod
                                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                  (@instHPow.{0, 0} Nat Nat
                                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                  p a))
                                              (ZMod.commRing
                                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                  (@instHPow.{0, 0} Nat Nat
                                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                  p a))))
                                          (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                          (instDecidableEqFin
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                                (@DFunLike.coe.{1, 1, 1}
                                  (Equiv.{1, 1}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                      Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                        ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))
                                    (Matrix.{0, 0, 0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a))))
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                    Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                      ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a))
                                  (fun
                                      (x :
                                        Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                          Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                            ZMod
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p a)) =>
                                    Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a)))
                                  (@EquivLike.toFunLike.{1, 1, 1}
                                    (Equiv.{1, 1}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                        Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                          ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))
                                      (Matrix.{0, 0, 0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))))
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                      Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                        ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))
                                    (Matrix.{0, 0, 0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a)))
                                    (@Equiv.instEquivLike.{1, 1}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                        Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                          ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))
                                      (Matrix.{0, 0, 0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a)))))
                                  (@Matrix.of.{0, 0, 0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (ZMod
                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                        (@instHPow.{0, 0} Nat Nat
                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                        p a)))
                                  (@Matrix.vecCons.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                      ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                    (@Matrix.vecCons.{0}
                                      (ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                      (@OfNat.ofNat.{0}
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))
                                        (nat_lit 1)
                                        (@One.toOfNat1.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))
                                          (@AddMonoidWithOne.toOne.{0}
                                            (ZMod
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p a))
                                            (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                              (ZMod
                                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                  (@instHPow.{0, 0} Nat Nat
                                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                  p a))
                                              (@Ring.toAddGroupWithOne.{0}
                                                (ZMod
                                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                    (@instHPow.{0, 0} Nat Nat
                                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                    p a))
                                                (@CommRing.toRing.{0}
                                                  (ZMod
                                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                      (@instHPow.{0, 0} Nat Nat
                                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                      p a))
                                                  (ZMod.commRing
                                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                      (@instHPow.{0, 0} Nat Nat
                                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                      p a))))))))
                                      (@Matrix.vecCons.{0}
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                        (@OfNat.ofNat.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))
                                          (nat_lit 1)
                                          (@One.toOfNat1.{0}
                                            (ZMod
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p a))
                                            (@AddMonoidWithOne.toOne.{0}
                                              (ZMod
                                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                  (@instHPow.{0, 0} Nat Nat
                                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                  p a))
                                              (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                                (ZMod
                                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                    (@instHPow.{0, 0} Nat Nat
                                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                    p a))
                                                (@Ring.toAddGroupWithOne.{0}
                                                  (ZMod
                                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                      (@instHPow.{0, 0} Nat Nat
                                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                      p a))
                                                  (@CommRing.toRing.{0}
                                                    (ZMod
                                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                        (@instHPow.{0, 0} Nat Nat
                                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                        p a))
                                                    (ZMod.commRing
                                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                        (@instHPow.{0, 0} Nat Nat
                                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                        p a))))))))
                                        (@Matrix.vecEmpty.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a)))))
                                    (@Matrix.vecCons.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                        ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                      (@Matrix.vecCons.{0}
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                        (@OfNat.ofNat.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))
                                          (nat_lit 1)
                                          (@One.toOfNat1.{0}
                                            (ZMod
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p a))
                                            (@AddMonoidWithOne.toOne.{0}
                                              (ZMod
                                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                  (@instHPow.{0, 0} Nat Nat
                                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                  p a))
                                              (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                                (ZMod
                                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                    (@instHPow.{0, 0} Nat Nat
                                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                    p a))
                                                (@Ring.toAddGroupWithOne.{0}
                                                  (ZMod
                                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                      (@instHPow.{0, 0} Nat Nat
                                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                      p a))
                                                  (@CommRing.toRing.{0}
                                                    (ZMod
                                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                        (@instHPow.{0, 0} Nat Nat
                                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                        p a))
                                                    (ZMod.commRing
                                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                        (@instHPow.{0, 0} Nat Nat
                                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                        p a))))))))
                                        (@Matrix.vecCons.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                          (@OfNat.ofNat.{0}
                                            (ZMod
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p a))
                                            (nat_lit 0)
                                            (@Zero.toOfNat0.{0}
                                              (ZMod
                                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                  (@instHPow.{0, 0} Nat Nat
                                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                  p a))
                                              (@MulZeroClass.toZero.{0}
                                                (ZMod
                                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                    (@instHPow.{0, 0} Nat Nat
                                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                    p a))
                                                (@instMulZeroClassOfSemiring.{0}
                                                  (ZMod
                                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                      (@instHPow.{0, 0} Nat Nat
                                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                      p a))
                                                  (@CommSemiring.toSemiring.{0}
                                                    (ZMod
                                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                        (@instHPow.{0, 0} Nat Nat
                                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                        p a))
                                                    (@CommRing.toCommSemiring.{0}
                                                      (ZMod
                                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                          (@instHPow.{0, 0} Nat Nat
                                                            (@NPow.toPow.{0} Nat
                                                              (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                          p a))
                                                      (ZMod.commRing
                                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                          (@instHPow.{0, 0} Nat Nat
                                                            (@NPow.toPow.{0} Nat
                                                              (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                          p a))))))))
                                          (@Matrix.vecEmpty.{0}
                                            (ZMod
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p a)))))
                                      (@Matrix.vecEmpty.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                          ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))))))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) τ m))
                              (@OfNat.ofNat.{0}
                                (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (ZMod
                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                      (@instHPow.{0, 0} Nat Nat
                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                      p a)))
                                (nat_lit 1)
                                (@One.toOfNat1.{0}
                                  (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (ZMod
                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                        (@instHPow.{0, 0} Nat Nat
                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                        p a)))
                                  (@Matrix.one.{0, 0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (ZMod
                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                        (@instHPow.{0, 0} Nat Nat
                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                        p a))
                                    (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (@MulZeroClass.toZero.{0}
                                      (ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a))
                                      (@instMulZeroClassOfSemiring.{0}
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))
                                        (@CommSemiring.toSemiring.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))
                                          (@CommRing.toCommSemiring.{0}
                                            (ZMod
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p a))
                                            (ZMod.commRing
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p a))))))
                                    (@AddMonoidWithOne.toOne.{0}
                                      (ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a))
                                      (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))
                                        (@Ring.toAddGroupWithOne.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))
                                          (@CommRing.toRing.{0}
                                            (ZMod
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p a))
                                            (ZMod.commRing
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p a))))))))))
                            (@LE.le.{0} Nat instLENat a
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h (padicValNat p m))))
                      (And
                        (∀ (n : Nat),
                          @Eq.{1}
                              (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (ZMod
                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                    (@instHPow.{0, 0} Nat Nat
                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                    p a)))
                              (@HPow.hPow.{0, 0, 0}
                                (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (ZMod
                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                      (@instHPow.{0, 0} Nat Nat
                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                      p a)))
                                Nat
                                (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (ZMod
                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                      (@instHPow.{0, 0} Nat Nat
                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                      p a)))
                                (@instHPow.{0, 0}
                                  (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (ZMod
                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                        (@instHPow.{0, 0} Nat Nat
                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                        p a)))
                                  Nat
                                  (@NPow.toPow.{0}
                                    (Matrix.{0, 0, 0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a)))
                                    (@Monoid.toNPow.{0}
                                      (Matrix.{0, 0, 0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a)))
                                      (@Semiring.toMonoid.{0}
                                        (Matrix.{0, 0, 0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a)))
                                        (@Matrix.semiring.{0, 0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))
                                          (@CommSemiring.toSemiring.{0}
                                            (ZMod
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p a))
                                            (@CommRing.toCommSemiring.{0}
                                              (ZMod
                                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                  (@instHPow.{0, 0} Nat Nat
                                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                  p a))
                                              (ZMod.commRing
                                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                  (@instHPow.{0, 0} Nat Nat
                                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                  p a))))
                                          (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                          (instDecidableEqFin
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                                (@DFunLike.coe.{1, 1, 1}
                                  (Equiv.{1, 1}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                      Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                        ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))
                                    (Matrix.{0, 0, 0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a))))
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                    Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                      ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a))
                                  (fun
                                      (x :
                                        Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                          Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                            ZMod
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p a)) =>
                                    Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a)))
                                  (@EquivLike.toFunLike.{1, 1, 1}
                                    (Equiv.{1, 1}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                        Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                          ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))
                                      (Matrix.{0, 0, 0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))))
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                      Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                        ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))
                                    (Matrix.{0, 0, 0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a)))
                                    (@Equiv.instEquivLike.{1, 1}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                        Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                          ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))
                                      (Matrix.{0, 0, 0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a)))))
                                  (@Matrix.of.{0, 0, 0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (ZMod
                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                        (@instHPow.{0, 0} Nat Nat
                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                        p a)))
                                  (@Matrix.vecCons.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                      ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                    (@Matrix.vecCons.{0}
                                      (ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                      (@OfNat.ofNat.{0}
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))
                                        (nat_lit 1)
                                        (@One.toOfNat1.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))
                                          (@AddMonoidWithOne.toOne.{0}
                                            (ZMod
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p a))
                                            (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                              (ZMod
                                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                  (@instHPow.{0, 0} Nat Nat
                                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                  p a))
                                              (@Ring.toAddGroupWithOne.{0}
                                                (ZMod
                                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                    (@instHPow.{0, 0} Nat Nat
                                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                    p a))
                                                (@CommRing.toRing.{0}
                                                  (ZMod
                                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                      (@instHPow.{0, 0} Nat Nat
                                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                      p a))
                                                  (ZMod.commRing
                                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                      (@instHPow.{0, 0} Nat Nat
                                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                      p a))))))))
                                      (@Matrix.vecCons.{0}
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                        (@OfNat.ofNat.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))
                                          (nat_lit 1)
                                          (@One.toOfNat1.{0}
                                            (ZMod
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p a))
                                            (@AddMonoidWithOne.toOne.{0}
                                              (ZMod
                                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                  (@instHPow.{0, 0} Nat Nat
                                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                  p a))
                                              (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                                (ZMod
                                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                    (@instHPow.{0, 0} Nat Nat
                                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                    p a))
                                                (@Ring.toAddGroupWithOne.{0}
                                                  (ZMod
                                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                      (@instHPow.{0, 0} Nat Nat
                                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                      p a))
                                                  (@CommRing.toRing.{0}
                                                    (ZMod
                                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                        (@instHPow.{0, 0} Nat Nat
                                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                        p a))
                                                    (ZMod.commRing
                                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                        (@instHPow.{0, 0} Nat Nat
                                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                        p a))))))))
                                        (@Matrix.vecEmpty.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a)))))
                                    (@Matrix.vecCons.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                        ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                      (@Matrix.vecCons.{0}
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                        (@OfNat.ofNat.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))
                                          (nat_lit 1)
                                          (@One.toOfNat1.{0}
                                            (ZMod
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p a))
                                            (@AddMonoidWithOne.toOne.{0}
                                              (ZMod
                                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                  (@instHPow.{0, 0} Nat Nat
                                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                  p a))
                                              (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                                (ZMod
                                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                    (@instHPow.{0, 0} Nat Nat
                                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                    p a))
                                                (@Ring.toAddGroupWithOne.{0}
                                                  (ZMod
                                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                      (@instHPow.{0, 0} Nat Nat
                                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                      p a))
                                                  (@CommRing.toRing.{0}
                                                    (ZMod
                                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                        (@instHPow.{0, 0} Nat Nat
                                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                        p a))
                                                    (ZMod.commRing
                                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                        (@instHPow.{0, 0} Nat Nat
                                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                        p a))))))))
                                        (@Matrix.vecCons.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                          (@OfNat.ofNat.{0}
                                            (ZMod
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p a))
                                            (nat_lit 0)
                                            (@Zero.toOfNat0.{0}
                                              (ZMod
                                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                  (@instHPow.{0, 0} Nat Nat
                                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                  p a))
                                              (@MulZeroClass.toZero.{0}
                                                (ZMod
                                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                    (@instHPow.{0, 0} Nat Nat
                                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                    p a))
                                                (@instMulZeroClassOfSemiring.{0}
                                                  (ZMod
                                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                      (@instHPow.{0, 0} Nat Nat
                                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                      p a))
                                                  (@CommSemiring.toSemiring.{0}
                                                    (ZMod
                                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                        (@instHPow.{0, 0} Nat Nat
                                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                        p a))
                                                    (@CommRing.toCommSemiring.{0}
                                                      (ZMod
                                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                          (@instHPow.{0, 0} Nat Nat
                                                            (@NPow.toPow.{0} Nat
                                                              (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                          p a))
                                                      (ZMod.commRing
                                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                          (@instHPow.{0, 0} Nat Nat
                                                            (@NPow.toPow.{0} Nat
                                                              (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                          p a))))))))
                                          (@Matrix.vecEmpty.{0}
                                            (ZMod
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p a)))))
                                      (@Matrix.vecEmpty.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                          ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))))))
                                n)
                              (@OfNat.ofNat.{0}
                                (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (ZMod
                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                      (@instHPow.{0, 0} Nat Nat
                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                      p a)))
                                (nat_lit 1)
                                (@One.toOfNat1.{0}
                                  (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (ZMod
                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                        (@instHPow.{0, 0} Nat Nat
                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                        p a)))
                                  (@Matrix.one.{0, 0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (ZMod
                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                        (@instHPow.{0, 0} Nat Nat
                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                        p a))
                                    (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (@MulZeroClass.toZero.{0}
                                      (ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a))
                                      (@instMulZeroClassOfSemiring.{0}
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))
                                        (@CommSemiring.toSemiring.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))
                                          (@CommRing.toCommSemiring.{0}
                                            (ZMod
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p a))
                                            (ZMod.commRing
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p a))))))
                                    (@AddMonoidWithOne.toOne.{0}
                                      (ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a))
                                      (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))
                                        (@Ring.toAddGroupWithOne.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))
                                          (@CommRing.toRing.{0}
                                            (ZMod
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p a))
                                            (ZMod.commRing
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p a))))))))) →
                            @Dvd.dvd.{0} Nat Nat.instDvd τ n)
                        (@Eq.{1} Nat
                          (@orderOf.{0}
                            (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (ZMod
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat
                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                  p a)))
                            (@Semiring.toMonoid.{0}
                              (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (ZMod
                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                    (@instHPow.{0, 0} Nat Nat
                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                    p a)))
                              (@Matrix.semiring.{0, 0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (ZMod
                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} _ _)) _
                                    _))
                                _ _ _))
                            _)
                          _))))))))))
    _)

noncomputable def Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenPrimePowerMatrixPeriod\",\"golden_matrix_prime_power_period\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenPrimePowerMatrixPeriod\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod, declaration := `D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.golden_matrix_prime_power_period, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod, declaration := `Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.arena
  (∀ (p a : _) (_hp : _) (_hpFive : _) (_ha : _),
    have τ : _ :=
      @orderOf.{0}
        (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod p))
        (@Semiring.toMonoid.{0}
          (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod p))
          (@Matrix.semiring.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod p)
            (@CommSemiring.toSemiring.{0} (ZMod p) (@CommRing.toCommSemiring.{0} (ZMod p) (ZMod.commRing p)))
            (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
        (@DFunLike.coe.{1, 1, 1}
          (Equiv.{1, 1}
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
              Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod p)
            (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod p)))
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
            Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod p)
          (fun
              (x :
                Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                  Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod p) =>
            Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod p))
          (@EquivLike.toFunLike.{1, 1, 1}
            (Equiv.{1, 1}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod p)
              (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod p)))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
              Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod p)
            (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod p))
            (@Equiv.instEquivLike.{1, 1}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod p)
              (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod p))))
          (@Matrix.of.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod p))
          (@Matrix.vecCons.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod p)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Matrix.vecCons.{0} (ZMod p) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@OfNat.ofNat.{0} (ZMod p) (nat_lit 1)
                (@One.toOfNat1.{0} (ZMod p)
                  (@AddMonoidWithOne.toOne.{0} (ZMod p)
                    (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod p)
                      (@Ring.toAddGroupWithOne.{0} (ZMod p) (@CommRing.toRing.{0} (ZMod p) (ZMod.commRing p)))))))
              (@Matrix.vecCons.{0} (ZMod p) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat.{0} (ZMod p) (nat_lit 1)
                  (@One.toOfNat1.{0} (ZMod p)
                    (@AddMonoidWithOne.toOne.{0} (ZMod p)
                      (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod p)
                        (@Ring.toAddGroupWithOne.{0} (ZMod p) (@CommRing.toRing.{0} (ZMod p) (ZMod.commRing p)))))))
                (@Matrix.vecEmpty.{0} (ZMod p))))
            (@Matrix.vecCons.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod p)
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@Matrix.vecCons.{0} (ZMod p) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@OfNat.ofNat.{0} (ZMod p) (nat_lit 1)
                  (@One.toOfNat1.{0} (ZMod p)
                    (@AddMonoidWithOne.toOne.{0} (ZMod p)
                      (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod p)
                        (@Ring.toAddGroupWithOne.{0} (ZMod p) (@CommRing.toRing.{0} (ZMod p) (ZMod.commRing p)))))))
                (@Matrix.vecCons.{0} (ZMod p) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@OfNat.ofNat.{0} (ZMod p) (nat_lit 0)
                    (@Zero.toOfNat0.{0} (ZMod p)
                      (@MulZeroClass.toZero.{0} (ZMod p)
                        (@instMulZeroClassOfSemiring.{0} (ZMod p)
                          (@CommSemiring.toSemiring.{0} (ZMod p)
                            (@CommRing.toCommSemiring.{0} (ZMod p) (ZMod.commRing p)))))))
                  (@Matrix.vecEmpty.{0} (ZMod p))))
              (@Matrix.vecEmpty.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod p)))));
    have h : _ := padicValNat p (Nat.fib (D5.S3.Arith.Primes.FiniteFibonacciRankClosure.fibonacciRank p));
    And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) h)
      (And (@Eq.{1} Nat (padicValNat p (Nat.fib τ)) h)
        (And
          (@Eq.{1} Nat (padicValNat p (Nat.fib τ))
            (padicValNat p
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                (Nat.fib
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) τ
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (And (@Even.{0} Nat instAddNat τ)
            (And
              (@Eq.{1} Nat
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                    (Nat.fib
                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) τ
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (Nat.fib
                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) τ
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (Nat.fib τ)
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (Nat.fib τ)
                    (Nat.fib
                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) τ
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
              (And
                (And
                  (Not
                    (@Dvd.dvd.{0} Nat Nat.instDvd p
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (Nat.fib
                          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) τ
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (Not
                    (@Dvd.dvd.{0} Nat Nat.instDvd p
                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (Nat.fib τ)
                        (Nat.fib
                          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) τ
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
                (And
                  (@Exists.{1} Nat fun (u : Nat) =>
                    @Exists.{1} Nat fun (v : Nat) =>
                      And
                        (@Eq.{1} Nat
                          (Nat.fib
                            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) τ
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                p h)
                              u)))
                        (And
                          (@Eq.{1} Nat (Nat.fib τ)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                p h)
                              v))
                          (And (Not (@Dvd.dvd.{0} Nat Nat.instDvd p v))
                            (@Exists.{1}
                              (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Nat)
                              fun
                                (A :
                                  Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Nat) =>
                              And
                                (@Eq.{1}
                                  (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Nat)
                                  A
                                  (@DFunLike.coe.{1, 1, 1}
                                    (Equiv.{1, 1}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                        Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Nat)
                                      (Matrix.{0, 0, 0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Nat))
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                      Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Nat)
                                    (fun
                                        (x :
                                          Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                            Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Nat) =>
                                      Matrix.{0, 0, 0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Nat)
                                    (@EquivLike.toFunLike.{1, 1, 1}
                                      (Equiv.{1, 1}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                          Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Nat)
                                        (Matrix.{0, 0, 0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Nat))
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                        Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Nat)
                                      (Matrix.{0, 0, 0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Nat)
                                      (@Equiv.instEquivLike.{1, 1}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                          Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Nat)
                                        (Matrix.{0, 0, 0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Nat)))
                                    (@Matrix.of.{0, 0, 0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Nat)
                                    (@Matrix.vecCons.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Nat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                      (@Matrix.vecCons.{0} Nat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) u v)
                                        (@Matrix.vecCons.{0} Nat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) v
                                          (@Matrix.vecEmpty.{0} Nat)))
                                      (@Matrix.vecCons.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Nat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                        (@Matrix.vecCons.{0} Nat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) v
                                          (@Matrix.vecCons.{0} Nat
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) u
                                            (@Matrix.vecEmpty.{0} Nat)))
                                        (@Matrix.vecEmpty.{0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Nat))))))
                                (And
                                  (∀ (q : Nat),
                                    @Eq.{1}
                                      (Matrix.{0, 0, 0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod q))
                                      (@HPow.hPow.{0, 0, 0}
                                        (Matrix.{0, 0, 0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod q))
                                        Nat
                                        (Matrix.{0, 0, 0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod q))
                                        (@instHPow.{0, 0}
                                          (Matrix.{0, 0, 0}
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                            (ZMod q))
                                          Nat
                                          (@NPow.toPow.{0}
                                            (Matrix.{0, 0, 0}
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (ZMod q))
                                            (@Monoid.toNPow.{0}
                                              (Matrix.{0, 0, 0}
                                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                (ZMod q))
                                              (@Semiring.toMonoid.{0}
                                                (Matrix.{0, 0, 0}
                                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                  (ZMod q))
                                                (@Matrix.semiring.{0, 0}
                                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                  (ZMod q)
                                                  (@CommSemiring.toSemiring.{0} (ZMod q)
                                                    (@CommRing.toCommSemiring.{0} (ZMod q) (ZMod.commRing q)))
                                                  (Fin.fintype
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                  (instDecidableEqFin
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                                        (@DFunLike.coe.{1, 1, 1}
                                          (Equiv.{1, 1}
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                              Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                                ZMod q)
                                            (Matrix.{0, 0, 0}
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (ZMod q)))
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                            Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod q)
                                          (fun
                                              (x :
                                                Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                                  Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                                    ZMod q) =>
                                            Matrix.{0, 0, 0}
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (ZMod q))
                                          (@EquivLike.toFunLike.{1, 1, 1}
                                            (Equiv.{1, 1}
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                                Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                                  ZMod q)
                                              (Matrix.{0, 0, 0}
                                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                (ZMod q)))
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                              Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                                ZMod q)
                                            (Matrix.{0, 0, 0}
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (ZMod q))
                                            (@Equiv.instEquivLike.{1, 1}
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                                Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                                  ZMod q)
                                              (Matrix.{0, 0, 0}
                                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                (ZMod q))))
                                          (@Matrix.of.{0, 0, 0}
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                            (ZMod q))
                                          (@Matrix.vecCons.{0}
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod q)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                            (@Matrix.vecCons.{0} (ZMod q)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                              (@OfNat.ofNat.{0} (ZMod q) (nat_lit 1)
                                                (@One.toOfNat1.{0} (ZMod q)
                                                  (@AddMonoidWithOne.toOne.{0} (ZMod q)
                                                    (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod q)
                                                      (@Ring.toAddGroupWithOne.{0} (ZMod q)
                                                        (@CommRing.toRing.{0} (ZMod q) (ZMod.commRing q)))))))
                                              (@Matrix.vecCons.{0} (ZMod q)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                                (@OfNat.ofNat.{0} (ZMod q) (nat_lit 1)
                                                  (@One.toOfNat1.{0} (ZMod q)
                                                    (@AddMonoidWithOne.toOne.{0} (ZMod q)
                                                      (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod q)
                                                        (@Ring.toAddGroupWithOne.{0} (ZMod q)
                                                          (@CommRing.toRing.{0} (ZMod q) (ZMod.commRing q)))))))
                                                (@Matrix.vecEmpty.{0} (ZMod q))))
                                            (@Matrix.vecCons.{0}
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                                ZMod q)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                              (@Matrix.vecCons.{0} (ZMod q)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                                (@OfNat.ofNat.{0} (ZMod q) (nat_lit 1)
                                                  (@One.toOfNat1.{0} (ZMod q)
                                                    (@AddMonoidWithOne.toOne.{0} (ZMod q)
                                                      (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod q)
                                                        (@Ring.toAddGroupWithOne.{0} (ZMod q)
                                                          (@CommRing.toRing.{0} (ZMod q) (ZMod.commRing q)))))))
                                                (@Matrix.vecCons.{0} (ZMod q)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                                  (@OfNat.ofNat.{0} (ZMod q) (nat_lit 0)
                                                    (@Zero.toOfNat0.{0} (ZMod q)
                                                      (@MulZeroClass.toZero.{0} (ZMod q)
                                                        (@instMulZeroClassOfSemiring.{0} (ZMod q)
                                                          (@CommSemiring.toSemiring.{0} (ZMod q)
                                                            (@CommRing.toCommSemiring.{0} (ZMod q)
                                                              (ZMod.commRing q)))))))
                                                  (@Matrix.vecEmpty.{0} (ZMod q))))
                                              (@Matrix.vecEmpty.{0}
                                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                                  ZMod q)))))
                                        τ)
                                      (@HAdd.hAdd.{0, 0, 0}
                                        (Matrix.{0, 0, 0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod q))
                                        (Matrix.{0, 0, 0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod q))
                                        (Matrix.{0, 0, 0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod q))
                                        (@instHAdd.{0}
                                          (Matrix.{0, 0, 0}
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                            (ZMod q))
                                          (@Matrix.add.{0, 0, 0}
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod q)
                                            (@Distrib.toAdd.{0} (ZMod q)
                                              (@instDistribOfSemiring.{0} (ZMod q)
                                                (@CommSemiring.toSemiring.{0} (ZMod q)
                                                  (@CommRing.toCommSemiring.{0} (ZMod q) (ZMod.commRing q)))))))
                                        (@OfNat.ofNat.{0}
                                          (Matrix.{0, 0, 0}
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                            (ZMod q))
                                          (nat_lit 1)
                                          (@One.toOfNat1.{0}
                                            (Matrix.{0, 0, 0}
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (ZMod q))
                                            (@Matrix.one.{0, 0}
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (ZMod q)
                                              (instDecidableEqFin
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (@MulZeroClass.toZero.{0} (ZMod q)
                                                (@instMulZeroClassOfSemiring.{0} (ZMod q)
                                                  (@CommSemiring.toSemiring.{0} (ZMod q)
                                                    (@CommRing.toCommSemiring.{0} (ZMod q) (ZMod.commRing q)))))
                                              (@AddMonoidWithOne.toOne.{0} (ZMod q)
                                                (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod q)
                                                  (@Ring.toAddGroupWithOne.{0} (ZMod q)
                                                    (@CommRing.toRing.{0} (ZMod q) (ZMod.commRing q))))))))
                                        (@HSMul.hSMul.{0, 0, 0} (ZMod q)
                                          (Matrix.{0, 0, 0}
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                            (ZMod q))
                                          (Matrix.{0, 0, 0}
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                            (ZMod q))
                                          (@instHSMul.{0, 0} (ZMod q)
                                            (Matrix.{0, 0, 0}
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (ZMod q))
                                            (@Matrix.smul.{0, 0, 0, 0}
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (ZMod q) (ZMod q)
                                              (@instSMulOfMul.{0} (ZMod q)
                                                (@Distrib.toMul.{0} (ZMod q)
                                                  (@instDistribOfSemiring.{0} (ZMod q)
                                                    (@CommSemiring.toSemiring.{0} (ZMod q)
                                                      (@CommRing.toCommSemiring.{0} (ZMod q) (ZMod.commRing q))))))))
                                          (@Nat.cast.{0} (ZMod q)
                                            (@AddMonoidWithOne.toNatCast.{0} (ZMod q)
                                              (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod q)
                                                (@Ring.toAddGroupWithOne.{0} (ZMod q)
                                                  (@CommRing.toRing.{0} (ZMod q) (ZMod.commRing q)))))
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p h))
                                          (@Matrix.map.{0, 0, 0, 0}
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Nat
                                            (ZMod q) A
                                            (@DFunLike.coe.{1, 1, 1}
                                              (@RingHom.{0, 0} Nat (ZMod q) Nat.instNonAssocSemiring
                                                (@Semiring.toNonAssocSemiring.{0} (ZMod q)
                                                  (@CommSemiring.toSemiring.{0} (ZMod q)
                                                    (@CommRing.toCommSemiring.{0} (ZMod q) (ZMod.commRing q)))))
                                              Nat (fun (x : Nat) => ZMod q)
                                              (@RingHom.instFunLike.{0, 0} Nat (ZMod q) Nat.instNonAssocSemiring
                                                (@Semiring.toNonAssocSemiring.{0} (ZMod q)
                                                  (@CommSemiring.toSemiring.{0} (ZMod q)
                                                    (@CommRing.toCommSemiring.{0} (ZMod q) (ZMod.commRing q)))))
                                              (@Nat.castRingHom.{0} (ZMod q)
                                                (@Semiring.toNonAssocSemiring.{0} (ZMod q)
                                                  (@CommSemiring.toSemiring.{0} (ZMod q)
                                                    (@CommRing.toCommSemiring.{0} (ZMod q) (ZMod.commRing q))))))))))
                                  (@Ne.{1}
                                    (Matrix.{0, 0, 0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod p))
                                    (@Matrix.map.{0, 0, 0, 0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Nat (ZMod p) A
                                      (@DFunLike.coe.{1, 1, 1}
                                        (@RingHom.{0, 0} Nat (ZMod p) Nat.instNonAssocSemiring
                                          (@Semiring.toNonAssocSemiring.{0} (ZMod p)
                                            (@CommSemiring.toSemiring.{0} (ZMod p)
                                              (@CommRing.toCommSemiring.{0} (ZMod p) (ZMod.commRing p)))))
                                        Nat (fun (x : Nat) => ZMod p)
                                        (@RingHom.instFunLike.{0, 0} Nat (ZMod p) Nat.instNonAssocSemiring
                                          (@Semiring.toNonAssocSemiring.{0} (ZMod p)
                                            (@CommSemiring.toSemiring.{0} (ZMod p)
                                              (@CommRing.toCommSemiring.{0} (ZMod p) (ZMod.commRing p)))))
                                        (@Nat.castRingHom.{0} (ZMod p)
                                          (@Semiring.toNonAssocSemiring.{0} (ZMod p)
                                            (@CommSemiring.toSemiring.{0} (ZMod p)
                                              (@CommRing.toCommSemiring.{0} (ZMod p) (ZMod.commRing p)))))))
                                    (@OfNat.ofNat.{0}
                                      (Matrix.{0, 0, 0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod p))
                                      (nat_lit 0)
                                      (@Zero.toOfNat0.{0}
                                        (Matrix.{0, 0, 0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod p))
                                        (@Matrix.zero.{0, 0, 0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod p)
                                          (@MulZeroClass.toZero.{0} (ZMod p)
                                            (@instMulZeroClassOfSemiring.{0} (ZMod p)
                                              (@CommSemiring.toSemiring.{0} (ZMod p)
                                                (@CommRing.toCommSemiring.{0} (ZMod p) (ZMod.commRing p))))))))))))))
                  (And
                    (∀ (m : Nat),
                      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m →
                        Iff
                          (@Eq.{1}
                            (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (ZMod
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat
                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                  p a)))
                            (@HPow.hPow.{0, 0, 0}
                              (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (ZMod
                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                    (@instHPow.{0, 0} Nat Nat
                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                    p a)))
                              Nat
                              (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (ZMod
                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                    (@instHPow.{0, 0} Nat Nat
                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                    p a)))
                              (@instHPow.{0, 0}
                                (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (ZMod
                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                      (@instHPow.{0, 0} Nat Nat
                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                      p a)))
                                Nat
                                (@NPow.toPow.{0}
                                  (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (ZMod
                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                        (@instHPow.{0, 0} Nat Nat
                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                        p a)))
                                  (@Monoid.toNPow.{0}
                                    (Matrix.{0, 0, 0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a)))
                                    (@Semiring.toMonoid.{0}
                                      (Matrix.{0, 0, 0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a)))
                                      (@Matrix.semiring.{0, 0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))
                                        (@CommSemiring.toSemiring.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))
                                          (@CommRing.toCommSemiring.{0}
                                            (ZMod
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p a))
                                            (ZMod.commRing
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p a))))
                                        (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (instDecidableEqFin
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                              (@DFunLike.coe.{1, 1, 1}
                                (Equiv.{1, 1}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                    Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                      ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a))
                                  (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (ZMod
                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                        (@instHPow.{0, 0} Nat Nat
                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                        p a))))
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                  Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                    ZMod
                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                        (@instHPow.{0, 0} Nat Nat
                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                        p a))
                                (fun
                                    (x :
                                      Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                        Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                          ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a)) =>
                                  Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (ZMod
                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                        (@instHPow.{0, 0} Nat Nat
                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                        p a)))
                                (@EquivLike.toFunLike.{1, 1, 1}
                                  (Equiv.{1, 1}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                      Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                        ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))
                                    (Matrix.{0, 0, 0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a))))
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                    Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                      ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a))
                                  (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (ZMod
                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                        (@instHPow.{0, 0} Nat Nat
                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                        p a)))
                                  (@Equiv.instEquivLike.{1, 1}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                      Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                        ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))
                                    (Matrix.{0, 0, 0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a)))))
                                (@Matrix.of.{0, 0, 0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (ZMod
                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                      (@instHPow.{0, 0} Nat Nat
                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                      p a)))
                                (@Matrix.vecCons.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                    ZMod
                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                        (@instHPow.{0, 0} Nat Nat
                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                        p a))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Matrix.vecCons.{0}
                                    (ZMod
                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                        (@instHPow.{0, 0} Nat Nat
                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                        p a))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                    (@OfNat.ofNat.{0}
                                      (ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a))
                                      (nat_lit 1)
                                      (@One.toOfNat1.{0}
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))
                                        (@AddMonoidWithOne.toOne.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))
                                          (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                            (ZMod
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p a))
                                            (@Ring.toAddGroupWithOne.{0}
                                              (ZMod
                                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                  (@instHPow.{0, 0} Nat Nat
                                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                  p a))
                                              (@CommRing.toRing.{0}
                                                (ZMod
                                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                    (@instHPow.{0, 0} Nat Nat
                                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                    p a))
                                                (ZMod.commRing
                                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                    (@instHPow.{0, 0} Nat Nat
                                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                    p a))))))))
                                    (@Matrix.vecCons.{0}
                                      (ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                      (@OfNat.ofNat.{0}
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))
                                        (nat_lit 1)
                                        (@One.toOfNat1.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))
                                          (@AddMonoidWithOne.toOne.{0}
                                            (ZMod
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p a))
                                            (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                              (ZMod
                                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                  (@instHPow.{0, 0} Nat Nat
                                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                  p a))
                                              (@Ring.toAddGroupWithOne.{0}
                                                (ZMod
                                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                    (@instHPow.{0, 0} Nat Nat
                                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                    p a))
                                                (@CommRing.toRing.{0}
                                                  (ZMod
                                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                      (@instHPow.{0, 0} Nat Nat
                                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                      p a))
                                                  (ZMod.commRing
                                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                      (@instHPow.{0, 0} Nat Nat
                                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                      p a))))))))
                                      (@Matrix.vecEmpty.{0}
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a)))))
                                  (@Matrix.vecCons.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                      ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                    (@Matrix.vecCons.{0}
                                      (ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                      (@OfNat.ofNat.{0}
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))
                                        (nat_lit 1)
                                        (@One.toOfNat1.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))
                                          (@AddMonoidWithOne.toOne.{0}
                                            (ZMod
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p a))
                                            (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                              (ZMod
                                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                  (@instHPow.{0, 0} Nat Nat
                                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                  p a))
                                              (@Ring.toAddGroupWithOne.{0}
                                                (ZMod
                                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                    (@instHPow.{0, 0} Nat Nat
                                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                    p a))
                                                (@CommRing.toRing.{0}
                                                  (ZMod
                                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                      (@instHPow.{0, 0} Nat Nat
                                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                      p a))
                                                  (ZMod.commRing
                                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                      (@instHPow.{0, 0} Nat Nat
                                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                      p a))))))))
                                      (@Matrix.vecCons.{0}
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                        (@OfNat.ofNat.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))
                                          (nat_lit 0)
                                          (@Zero.toOfNat0.{0}
                                            (ZMod
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p a))
                                            (@MulZeroClass.toZero.{0}
                                              (ZMod
                                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                  (@instHPow.{0, 0} Nat Nat
                                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                  p a))
                                              (@instMulZeroClassOfSemiring.{0}
                                                (ZMod
                                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                    (@instHPow.{0, 0} Nat Nat
                                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                    p a))
                                                (@CommSemiring.toSemiring.{0}
                                                  (ZMod
                                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                      (@instHPow.{0, 0} Nat Nat
                                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                      p a))
                                                  (@CommRing.toCommSemiring.{0}
                                                    (ZMod
                                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                        (@instHPow.{0, 0} Nat Nat
                                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                        p a))
                                                    (ZMod.commRing
                                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                        (@instHPow.{0, 0} Nat Nat
                                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                        p a))))))))
                                        (@Matrix.vecEmpty.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a)))))
                                    (@Matrix.vecEmpty.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                        ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))))))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) τ m))
                            (@OfNat.ofNat.{0}
                              (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (ZMod
                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                    (@instHPow.{0, 0} Nat Nat
                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                    p a)))
                              (nat_lit 1)
                              (@One.toOfNat1.{0}
                                (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (ZMod
                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                      (@instHPow.{0, 0} Nat Nat
                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                      p a)))
                                (@Matrix.one.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (ZMod
                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                      (@instHPow.{0, 0} Nat Nat
                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                      p a))
                                  (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (@MulZeroClass.toZero.{0}
                                    (ZMod
                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                        (@instHPow.{0, 0} Nat Nat
                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                        p a))
                                    (@instMulZeroClassOfSemiring.{0}
                                      (ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a))
                                      (@CommSemiring.toSemiring.{0}
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))
                                        (@CommRing.toCommSemiring.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))
                                          (ZMod.commRing
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))))))
                                  (@AddMonoidWithOne.toOne.{0}
                                    (ZMod
                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                        (@instHPow.{0, 0} Nat Nat
                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                        p a))
                                    (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                      (ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a))
                                      (@Ring.toAddGroupWithOne.{0}
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))
                                        (@CommRing.toRing.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))
                                          (ZMod.commRing
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))))))))))
                          (@LE.le.{0} Nat instLENat a
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h (padicValNat p m))))
                    (And
                      (∀ (n : Nat),
                        @Eq.{1}
                            (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (ZMod
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat
                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                  p a)))
                            (@HPow.hPow.{0, 0, 0}
                              (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (ZMod
                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                    (@instHPow.{0, 0} Nat Nat
                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                    p a)))
                              Nat
                              (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (ZMod
                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                    (@instHPow.{0, 0} Nat Nat
                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                    p a)))
                              (@instHPow.{0, 0}
                                (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (ZMod
                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                      (@instHPow.{0, 0} Nat Nat
                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                      p a)))
                                Nat
                                (@NPow.toPow.{0}
                                  (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (ZMod
                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                        (@instHPow.{0, 0} Nat Nat
                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                        p a)))
                                  (@Monoid.toNPow.{0}
                                    (Matrix.{0, 0, 0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a)))
                                    (@Semiring.toMonoid.{0}
                                      (Matrix.{0, 0, 0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a)))
                                      (@Matrix.semiring.{0, 0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))
                                        (@CommSemiring.toSemiring.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))
                                          (@CommRing.toCommSemiring.{0}
                                            (ZMod
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p a))
                                            (ZMod.commRing
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p a))))
                                        (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (instDecidableEqFin
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                              (@DFunLike.coe.{1, 1, 1}
                                (Equiv.{1, 1}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                    Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                      ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a))
                                  (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (ZMod
                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                        (@instHPow.{0, 0} Nat Nat
                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                        p a))))
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                  Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                    ZMod
                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                        (@instHPow.{0, 0} Nat Nat
                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                        p a))
                                (fun
                                    (x :
                                      Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                        Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                          ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a)) =>
                                  Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (ZMod
                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                        (@instHPow.{0, 0} Nat Nat
                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                        p a)))
                                (@EquivLike.toFunLike.{1, 1, 1}
                                  (Equiv.{1, 1}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                      Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                        ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))
                                    (Matrix.{0, 0, 0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a))))
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                    Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                      ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a))
                                  (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (ZMod
                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                        (@instHPow.{0, 0} Nat Nat
                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                        p a)))
                                  (@Equiv.instEquivLike.{1, 1}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                      Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                        ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))
                                    (Matrix.{0, 0, 0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a)))))
                                (@Matrix.of.{0, 0, 0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (ZMod
                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                      (@instHPow.{0, 0} Nat Nat
                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                      p a)))
                                (@Matrix.vecCons.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                    ZMod
                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                        (@instHPow.{0, 0} Nat Nat
                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                        p a))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Matrix.vecCons.{0}
                                    (ZMod
                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                        (@instHPow.{0, 0} Nat Nat
                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                        p a))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                    (@OfNat.ofNat.{0}
                                      (ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a))
                                      (nat_lit 1)
                                      (@One.toOfNat1.{0}
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))
                                        (@AddMonoidWithOne.toOne.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))
                                          (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                            (ZMod
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p a))
                                            (@Ring.toAddGroupWithOne.{0}
                                              (ZMod
                                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                  (@instHPow.{0, 0} Nat Nat
                                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                  p a))
                                              (@CommRing.toRing.{0}
                                                (ZMod
                                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                    (@instHPow.{0, 0} Nat Nat
                                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                    p a))
                                                (ZMod.commRing
                                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                    (@instHPow.{0, 0} Nat Nat
                                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                    p a))))))))
                                    (@Matrix.vecCons.{0}
                                      (ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                      (@OfNat.ofNat.{0}
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))
                                        (nat_lit 1)
                                        (@One.toOfNat1.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))
                                          (@AddMonoidWithOne.toOne.{0}
                                            (ZMod
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p a))
                                            (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                              (ZMod
                                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                  (@instHPow.{0, 0} Nat Nat
                                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                  p a))
                                              (@Ring.toAddGroupWithOne.{0}
                                                (ZMod
                                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                    (@instHPow.{0, 0} Nat Nat
                                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                    p a))
                                                (@CommRing.toRing.{0}
                                                  (ZMod
                                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                      (@instHPow.{0, 0} Nat Nat
                                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                      p a))
                                                  (ZMod.commRing
                                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                      (@instHPow.{0, 0} Nat Nat
                                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                      p a))))))))
                                      (@Matrix.vecEmpty.{0}
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a)))))
                                  (@Matrix.vecCons.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                      ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                    (@Matrix.vecCons.{0}
                                      (ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                      (@OfNat.ofNat.{0}
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))
                                        (nat_lit 1)
                                        (@One.toOfNat1.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))
                                          (@AddMonoidWithOne.toOne.{0}
                                            (ZMod
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p a))
                                            (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                              (ZMod
                                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                  (@instHPow.{0, 0} Nat Nat
                                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                  p a))
                                              (@Ring.toAddGroupWithOne.{0}
                                                (ZMod
                                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                    (@instHPow.{0, 0} Nat Nat
                                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                    p a))
                                                (@CommRing.toRing.{0}
                                                  (ZMod
                                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                      (@instHPow.{0, 0} Nat Nat
                                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                      p a))
                                                  (ZMod.commRing
                                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                      (@instHPow.{0, 0} Nat Nat
                                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                      p a))))))))
                                      (@Matrix.vecCons.{0}
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                        (@OfNat.ofNat.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))
                                          (nat_lit 0)
                                          (@Zero.toOfNat0.{0}
                                            (ZMod
                                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                (@instHPow.{0, 0} Nat Nat
                                                  (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                p a))
                                            (@MulZeroClass.toZero.{0}
                                              (ZMod
                                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                  (@instHPow.{0, 0} Nat Nat
                                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                  p a))
                                              (@instMulZeroClassOfSemiring.{0}
                                                (ZMod
                                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                    (@instHPow.{0, 0} Nat Nat
                                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                    p a))
                                                (@CommSemiring.toSemiring.{0}
                                                  (ZMod
                                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                      (@instHPow.{0, 0} Nat Nat
                                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                      p a))
                                                  (@CommRing.toCommSemiring.{0}
                                                    (ZMod
                                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                        (@instHPow.{0, 0} Nat Nat
                                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                        p a))
                                                    (ZMod.commRing
                                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                                        (@instHPow.{0, 0} Nat Nat
                                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                                        p a))))))))
                                        (@Matrix.vecEmpty.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a)))))
                                    (@Matrix.vecEmpty.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                                        ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))))))
                              n)
                            (@OfNat.ofNat.{0}
                              (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (ZMod
                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                    (@instHPow.{0, 0} Nat Nat
                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                    p a)))
                              (nat_lit 1)
                              (@One.toOfNat1.{0}
                                (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (ZMod
                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                      (@instHPow.{0, 0} Nat Nat
                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                      p a)))
                                (@Matrix.one.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (ZMod
                                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                      (@instHPow.{0, 0} Nat Nat
                                        (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                      p a))
                                  (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (@MulZeroClass.toZero.{0}
                                    (ZMod
                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                        (@instHPow.{0, 0} Nat Nat
                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                        p a))
                                    (@instMulZeroClassOfSemiring.{0}
                                      (ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a))
                                      (@CommSemiring.toSemiring.{0}
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))
                                        (@CommRing.toCommSemiring.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))
                                          (ZMod.commRing
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))))))
                                  (@AddMonoidWithOne.toOne.{0}
                                    (ZMod
                                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                        (@instHPow.{0, 0} Nat Nat
                                          (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                        p a))
                                    (@AddGroupWithOne.toAddMonoidWithOne.{0}
                                      (ZMod
                                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                          (@instHPow.{0, 0} Nat Nat
                                            (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                          p a))
                                      (@Ring.toAddGroupWithOne.{0}
                                        (ZMod
                                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                            (@instHPow.{0, 0} Nat Nat
                                              (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                            p a))
                                        (@CommRing.toRing.{0}
                                          (ZMod
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))
                                          (ZMod.commRing
                                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                              (@instHPow.{0, 0} Nat Nat
                                                (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                              p a))))))))) →
                          @Dvd.dvd.{0} Nat Nat.instDvd τ n)
                      (@Eq.{1} Nat
                        (@orderOf.{0}
                          (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (ZMod
                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                p a)))
                          (@Semiring.toMonoid.{0}
                            (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (ZMod
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat
                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                  p a)))
                            (@Matrix.semiring.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (ZMod
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} _ _))) _ _))
                              _ _ _))
                          _)
                        _))))))))))
  _)

noncomputable def Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration_1.observation0 : (p a : Nat) →
  (hp : Nat.Prime p) →
    (hp5 : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) p) →
      (ha : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) a) →
        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
          Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.signature PUnit.unit.{1} p :=
  fun (p a : Nat) (hp : Nat.Prime p)
    (hp5 : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) p)
    (ha : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) a) =>
  have τ : Nat :=
    @orderOf.{0}
      (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod p))
      (@Semiring.toMonoid.{0}
        (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod p))
        (@Matrix.semiring.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod p)
          (@CommSemiring.toSemiring.{0} (ZMod p) (@CommRing.toCommSemiring.{0} (ZMod p) (ZMod.commRing p)))
          (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@DFunLike.coe.{1, 1, 1}
        (Equiv.{1, 1}
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
            Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod p)
          (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod p)))
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
          Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod p)
        (fun
            (x :
              Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod p) =>
          Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod p))
        (@EquivLike.toFunLike.{1, 1, 1}
          (Equiv.{1, 1}
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
              Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod p)
            (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod p)))
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
            Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod p)
          (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod p))
          (@Equiv.instEquivLike.{1, 1}
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
              Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod p)
            (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod p))))
        (@Matrix.of.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod p))
        (@Matrix.vecCons.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod p)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@Matrix.vecCons.{0} (ZMod p) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@OfNat.ofNat.{0} (ZMod p) (nat_lit 1)
              (@One.toOfNat1.{0} (ZMod p)
                (@AddMonoidWithOne.toOne.{0} (ZMod p)
                  (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod p)
                    (@Ring.toAddGroupWithOne.{0} (ZMod p) (@CommRing.toRing.{0} (ZMod p) (ZMod.commRing p)))))))
            (@Matrix.vecCons.{0} (ZMod p) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat.{0} (ZMod p) (nat_lit 1)
                (@One.toOfNat1.{0} (ZMod p)
                  (@AddMonoidWithOne.toOne.{0} (ZMod p)
                    (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod p)
                      (@Ring.toAddGroupWithOne.{0} (ZMod p) (@CommRing.toRing.{0} (ZMod p) (ZMod.commRing p)))))))
              (@Matrix.vecEmpty.{0} (ZMod p))))
          (@Matrix.vecCons.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod p)
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@Matrix.vecCons.{0} (ZMod p) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@OfNat.ofNat.{0} (ZMod p) (nat_lit 1)
                (@One.toOfNat1.{0} (ZMod p)
                  (@AddMonoidWithOne.toOne.{0} (ZMod p)
                    (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod p)
                      (@Ring.toAddGroupWithOne.{0} (ZMod p) (@CommRing.toRing.{0} (ZMod p) (ZMod.commRing p)))))))
              (@Matrix.vecCons.{0} (ZMod p) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat.{0} (ZMod p) (nat_lit 0)
                  (@Zero.toOfNat0.{0} (ZMod p)
                    (@MulZeroClass.toZero.{0} (ZMod p)
                      (@instMulZeroClassOfSemiring.{0} (ZMod p)
                        (@CommSemiring.toSemiring.{0} (ZMod p)
                          (@CommRing.toCommSemiring.{0} (ZMod p) (ZMod.commRing p)))))))
                (@Matrix.vecEmpty.{0} (ZMod p))))
            (@Matrix.vecEmpty.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod p)))));
  have h : Nat := padicValNat p (Nat.fib (D5.S3.Arith.Primes.FiniteFibonacciRankClosure.fibonacciRank p));
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.signature
    Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.actual PUnit.unit.{1} p a

noncomputable def Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenPrimePowerMatrixPeriod\",\"golden_matrix_prime_power_period\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"letBody\",\"letBody\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenPrimePowerMatrixPeriod\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod, declaration := `D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.golden_matrix_prime_power_period, part := .type, path := [.body, .body, .body, .body, .body, .letBody, .letBody, .argument, .argument, .argument, .argument, .argument, .argument, .argument, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod, declaration := `Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenPrimePowerMatrixPeriod\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenPrimePowerMatrixPeriod\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenPrimePowerMatrixPeriod\",\"golden_matrix_prime_power_period\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod, declaration := `Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod, declaration := `D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.golden_matrix_prime_power_period, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration).actual (Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration).variation.2.choose (Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration).variation.1 (Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenPrimePowerMatrixPeriod\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenPrimePowerMatrixPeriod\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod, declaration := `Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod, declaration := `Reg.D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
