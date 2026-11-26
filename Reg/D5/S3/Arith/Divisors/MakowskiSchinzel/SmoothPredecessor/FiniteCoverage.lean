import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.FiniteCoverage
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source-bound audit of the candidate test on arbitrary prime predecessors. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.FiniteCoverage.candidate

open _root_.D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

attribute [local irreducible] smoothSum candidateWeight

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => candidate) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {q : ℕ}, q.Prime →
    (R.readout () () (q - 1) = true ↔ ¬∃ k : ℕ, q - 1 = 2 ^ k)

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  have hnon : ¬∃ k : ℕ, 7 - 1 = 2 ^ k := by
    rintro ⟨k, hk⟩
    have hd : 3 ∣ 2 ^ k := by rw [← hk]; decide
    have := Nat.prime_three.dvd_of_dvd_pow hd
    norm_num at this
  have := (h (q := 7) (by decide)).mpr hnon
  exact Bool.false_ne_true this

def family : Registration arena (type_of% (@candidate_of_prime)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨candidate_of_prime, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 6, ?_⟩
    change candidate 0 ≠ candidate 6
    decide

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@candidate_of_prime) (Realization signature) (ℕ → Bool) Unit where
  unitName := `D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor.candidate_of_prime.__information_unit
  realizationName :=
    `Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.FiniteCoverage.candidate.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => candidate) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.FiniteCoverage
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.FiniteCoverage.candidate

namespace Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.FiniteCoverage.tableAudit

open _root_.D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

attribute [local irreducible] smoothSum candidateWeight

abbrev signature : Signature where
  Params := Unit
  State _ := List ℕ × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => smoothSum candidateWeight x.1 bound x.2)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (T : List ℕ), T.all validEntry = true → (T.map entryValue).Nodup →
    R.readout () () (allPrimes, 2) ≤ T.length → ∀ {q : ℕ},
      (∃ e ∈ T, entryValue e = q) ↔
        q - 1 ≤ bound ∧ candidate (q - 1) = true ∧
          q - 1 ∈ Nat.smoothNumbers 98

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  have hsm : 6 ∈ Nat.smoothNumbers 98 := Nat.mem_smoothNumbers'.mpr (by
    intro p hp hpd
    have : p ∣ 2 ∨ p ∣ 3 := hp.dvd_mul.mp (by simpa using hpd)
    rcases this with h | h
    · have := (Nat.prime_two.eq_one_or_self_of_dvd p h).resolve_left hp.ne_one
      omega
    · have := (Nat.prime_three.eq_one_or_self_of_dvd p h).resolve_left hp.ne_one
      omega)
  have hh := (h [] (by rfl) (by simp) (by rfl) (q := 7)).mpr
    ⟨by decide, by decide, hsm⟩
  simpa using hh

def family : Registration arena (type_of% @prime_mem_table) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@prime_mem_table, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), ([], 0), ([], 6), ?_⟩
    change smoothSum candidateWeight [] bound 0 ≠ smoothSum candidateWeight [] bound 6
    unfold smoothSum
    decide +kernel

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@prime_mem_table) (Realization signature) (List ℕ → ℕ → ℕ → ℕ) Unit where
  unitName := `D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor.prime_mem_table.__information_unit
  realizationName :=
    `Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.FiniteCoverage.tableAudit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ x => smoothSum candidateWeight x.1 bound x.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.FiniteCoverage
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.FiniteCoverage.tableAudit
