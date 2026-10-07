import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling
open _root_.D5.S3.Arith.FibonacciAtomic.TimeSampling
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling
noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ → ℕ → ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p n => localGcd p n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ _ => 0) (fun e => nomatch e)

def signed (R : Realization signature) (p : ℕ) (n z : ℤ) (k : ℕ) : ℕ :=
  R.readout () p n z k

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p : ℕ}, p.Prime →
    ∀ (S : Finset ℕ), (∀ k ∈ S, 0 < k) →
    let r := zeroRank p
    let A := S.image (fun k => k % r)
    let T := if r = p + 1 then r - 1 else r
    ((∀ n z n' z' : ℤ,
      (∀ k ∈ S, signed R p n z k = localGcd p n' z' k) →
      ∀ k, 0 < k → localGcd p n z k = localGcd p n' z' k) ↔ T ≤ A.card) ∧
    ((∀ a b a' b' : ℕ,
      (∀ k ∈ S, sourceGcd p a b k = sourceGcd p a' b' k) →
      ∀ k, 0 < k → sourceGcd p a b k = sourceGcd p a' b' k) ↔ T ≤ A.card) ∧
    (A.card < T → ∀ Q, 0 < Q →
      let H := Q * p
      ∃ n z n' z' : ℤ, ∃ a b a' b' : ℕ,
        primitive p n z ∧ primitive p n' z' ∧
        a < H ∧ b < H ∧ a' < H ∧ b' < H ∧
        (∀ k, 0 < k → sourceGcd H a b k = Q * localGcd p n z k ∧
          sourceGcd H a' b' k = Q * localGcd p n' z' k) ∧
        (∀ k ∈ S, localGcd p n z k = localGcd p n' z' k ∧
          sourceGcd H a b k = sourceGcd H a' b' k) ∧
        ∀ B, ∃ t, B < t ∧ 0 < t ∧ t ∉ S ∧
          localGcd p n z t = p ∧ localGcd p n' z' t = 1 ∧
          sourceGcd H a b t = H ∧ sourceGcd H a' b' t = Q ∧
          sourceGcd H a' b' t = H / p)

theorem actual_law : arena.Law actual := by
  intro p hp S hS
  exact prime_phase_gcd_sampling hp S hS

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hS : ∀ k ∈ ({1} : Finset ℕ), 0 < k := by simp
  have hbad := h Nat.prime_two {1} hS
  have hthreshold := hbad.1.mp (by
    intro n z n' z' hobs k hk
    have hz := hobs 1 (Finset.mem_singleton_self 1)
    change 0 = localGcd 2 n' z' 1 at hz
    have hpos : 0 < localGcd 2 n' z' 1 :=
      Nat.gcd_pos_of_pos_right _ (by decide)
    omega)
  have hactual := (prime_phase_gcd_sampling Nat.prime_two {1} hS).1.mpr hthreshold
  have hobs : ∀ k ∈ ({1} : Finset ℕ), localGcd 2 0 1 k = localGcd 2 1 1 k := by
    intro k hk
    have heq : k = 1 := Finset.mem_singleton.mp hk
    subst k
    norm_num [localGcd]
  have heq := hactual 0 1 1 1 hobs 2 (by decide)
  norm_num [localGcd] at heq

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨2, 0, 1, ?_⟩
    intro heq
    have h := congrFun (congrFun heq 0) 2
    norm_num [actual, realize, localGcd] at h

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.prime_phase_gcd_sampling) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ p n => localGcd p n) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "FibonacciAtomic") "PrimePhaseGcdSampling") "prime_phase_gcd_sampling") "Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling/Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ p n => localGcd p n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "body", "body", "body", "body", "domain", "body", "body", "fn", "arg", "fn", "fn", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling, declaration := `D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.prime_phase_gcd_sampling, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration_1.observationFact0, `Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration_1.anchorEnumeration }


#print axioms registration

end
end Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling


noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.arena
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimePhaseGcdSampling\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimePhaseGcdSampling\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.arena
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimePhaseGcdSampling\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimePhaseGcdSampling\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.arena
      Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.actual)
    Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration)

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimePhaseGcdSampling\",\"prime_phase_gcd_sampling\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimePhaseGcdSampling\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling, declaration := `D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.prime_phase_gcd_sampling, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.arena
    Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.actual)
  Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration)

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration_1.observation0 : {p : Nat} →
  (hp : Nat.Prime p) →
    (S : Finset.{0} Nat) →
      (hS :
          ∀ (k : Nat),
            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) S k →
              @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k) →
        (n z n' z' : Int) →
          (k : Nat) →
            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) S k →
              D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{0, 0, 0, 0, 0}
                  Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.signature p →
                D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                  Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.signature PUnit.unit.{1} p :=
  fun {p : Nat} (hp : Nat.Prime p) (S : Finset.{0} Nat)
    (hS :
      ∀ (k : Nat),
        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) S k →
          @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k) =>
  have r : Nat := D5.S3.Arith.FibonacciAtomic.TimeSampling.zeroRank p;
  have A : Finset.{0} Nat :=
    @Finset.image.{0, 0} Nat Nat instDecidableEqNat
      (fun (k : Nat) => @HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) k r) S;
  have T : Nat :=
    @ite.{1} Nat
      (@Eq.{1} Nat r
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) p
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (instDecidableEqNat r
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) p
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) r
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      r;
  fun (n z n' z' : Int) (k : Nat)
    (a :
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) S k) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.signature
    Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.actual PUnit.unit.{1} p

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimePhaseGcdSampling\",\"prime_phase_gcd_sampling\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"letBody\",\"letBody\",\"letBody\",\"function\",\"argument\",\"function\",\"argument\",\"body\",\"body\",\"body\",\"body\",\"domain\",\"body\",\"body\",\"function\",\"argument\",\"function\",\"function\",\"function\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimePhaseGcdSampling\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling, declaration := `D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.prime_phase_gcd_sampling, part := .type, path := [.body, .body, .body, .body, .letBody, .letBody, .letBody, .function, .argument, .function, .argument, .body, .body, .body, .body, .domain, .body, .body, .function, .argument, .function, .function, .function], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimePhaseGcdSampling\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimePhaseGcdSampling\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimePhaseGcdSampling\",\"prime_phase_gcd_sampling\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling, declaration := `D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.prime_phase_gcd_sampling, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration).actual (Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration).variation.2.choose (Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration).variation.1 (Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimePhaseGcdSampling\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimePhaseGcdSampling\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePhaseGcdSampling.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
