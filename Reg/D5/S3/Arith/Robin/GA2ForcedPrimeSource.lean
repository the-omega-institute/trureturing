import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.GA2ForcedPrimeSource
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Robin.GA2ForcedPrimeSource

open _root_.D5.S3.Arith.Robin.GA2ForcedPrimeSource
open _root_.D5.S3.Arith.Robin.PaddingRatio (robinRatio loglog_pos)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

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
  realize signature (fun _ _ n => robinRatio n) (fun e => nomatch e)

def ga2 (R : Realization signature) (q : ℕ) : Prop :=
  3 ≤ q ∧ ∀ a : ℕ, 1 ≤ a → R.readout () () (a * q) ≤ R.readout () () q

abbrev tailArena : Arena where
  signature := signature
  Law R := ∀ {q n : ℕ}, ga2 R q → 3 ≤ n →
    R.readout () () n ≤ R.readout () () q *
      (1 + Real.log (q : ℝ) /
        (Real.log (n : ℝ) * Real.log (Real.log (n : ℝ))))

def tailRejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

theorem tail_rejected_law : ¬ tailArena.Law tailRejected := by
  intro h
  have hga : ga2 tailRejected 3 := ⟨by norm_num, fun _ _ => le_rfl⟩
  have hf := h hga (by norm_num : 3 ≤ (3 : ℕ))
  have hlog : 1 < Real.log (3 : ℝ) :=
    (Real.lt_log_iff_exp_lt (by norm_num)).mpr Real.exp_one_lt_three
  have hpos : 0 < Real.log (3 : ℝ) /
      (Real.log (3 : ℝ) * Real.log (Real.log (3 : ℝ))) :=
    div_pos (by linarith) (mul_pos (by linarith) (Real.log_pos hlog))
  change (-1 : ℝ) ≤ -1 * (1 + Real.log (3 : ℝ) /
    (Real.log (3 : ℝ) * Real.log (Real.log (3 : ℝ)))) at hf
  linarith

theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 5041, ?_⟩
  change robinRatio 0 ≠ robinRatio 5041
  have hs : (ArithmeticFunction.sigma 1 5041 : ℝ) ≠ 0 := by
    exact_mod_cast (ArithmeticFunction.sigma_pos 1 5041 (by norm_num)).ne'
  have hn : (5041 : ℝ) ≠ 0 := by norm_num
  have hden := mul_ne_zero (mul_ne_zero (Real.exp_pos Real.eulerMascheroniConstant).ne' hn)
    (loglog_pos (n := 5041) (by norm_num)).ne'
  simpa only [robinRatio, Nat.cast_zero, Nat.cast_ofNat, mul_zero, zero_mul, div_zero] using
    (div_ne_zero hs hden).symm

def tailFamily : Registration tailArena (type_of% @robinRatio_le_ga2_tail_envelope) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨robinRatio_le_ga2_tail_envelope, tailRejected, tail_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨tailRejected, ?_, rfl, tail_rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

abbrev attainmentArena : Arena where
  signature := signature
  Law R := ∀ {m q : ℕ}, 3 ≤ m → m ∣ q → ga2 R q →
    ∃ N : ℕ, m ≤ N ∧ m ∣ N ∧ R.readout () () q ≤ R.readout () () N ∧ ga2 R N ∧
      ∀ n : ℕ, 1 ≤ n → m ∣ n → R.readout () () n ≤ R.readout () () N

def attainmentRejected : Realization signature :=
  realize signature (fun _ _ n => if n % 2 = 0 then 0 else (n : ℝ))
    (fun e => nomatch e)

theorem attainment_rejected_law : ¬ attainmentArena.Law attainmentRejected := by
  intro h
  have hga : ga2 attainmentRejected 6 := by
    refine ⟨by norm_num, ?_⟩
    intro a _
    simp [attainmentRejected, realize, Nat.mul_mod]
  obtain ⟨N, _, _, _, _, hmax⟩ := h (m := 3) (q := 6) (by norm_num) (by norm_num) hga
  have hk : 3 ∣ 6 * N + 3 := ⟨2 * N + 1, by ring⟩
  have hf := hmax (6 * N + 3) (by omega) hk
  have hodd : (6 * N + 3) % 2 ≠ 0 := by omega
  have hupper : attainmentRejected.readout () () N ≤ (N : ℝ) := by
    dsimp [attainmentRejected, realize]
    split_ifs
    · exact Nat.cast_nonneg N
    · exact le_rfl
  change (if (6 * N + 3) % 2 = 0 then 0 else ((6 * N + 3 : ℕ) : ℝ)) ≤
    attainmentRejected.readout () () N at hf
  rw [if_neg hodd] at hf
  push_cast at hf
  have := hf.trans hupper
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  linarith

def attainmentFamily : Registration attainmentArena
    (type_of% @exists_robin_maximizer_multiple_of_ga2) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exists_robin_maximizer_multiple_of_ga2,
    attainmentRejected, attainment_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨attainmentRejected, ?_, rfl, attainment_rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/- The complete dependent laws and kernel equivalence/variation/sensitivity
proofs are supplied. Exact raw-source reconstruction across the expanded
actualGA2 predicate and the multiply-scoped objective readouts is not claimed.
Both records keep that binding gap explicit for the existing owner issue 5214. -/
def tailAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@robinRatio_le_ga2_tail_envelope) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.GA2ForcedPrimeSource.robinRatio_le_ga2_tail_envelope.audit
  realizationName := `Reg.D5.S3.Arith.Robin.GA2ForcedPrimeSource.tailFamily
  realizationSource := none
  generated := false
  arena := .source ⟨tailArena⟩
  objectArena := .source ⟨tailArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source tailArena ⟨tailFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

def attainmentAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_robin_maximizer_multiple_of_ga2) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.GA2ForcedPrimeSource.exists_robin_maximizer_multiple_of_ga2.audit
  realizationName := `Reg.D5.S3.Arith.Robin.GA2ForcedPrimeSource.attainmentFamily
  realizationSource := none
  generated := false
  arena := .source ⟨attainmentArena⟩
  objectArena := .source ⟨attainmentArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source attainmentArena ⟨attainmentFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms tailFamily
#print axioms attainmentFamily
#print axioms tailAudit
#print axioms attainmentAudit

end
end Reg.D5.S3.Arith.Robin.GA2ForcedPrimeSource
