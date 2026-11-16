import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaRvm.HorizontalPrimeTail
import Reg.Support.SingleDependentReadout

/-! Source-bound cosine observation of the full actual prime-tail identity. -/

noncomputable section

namespace Reg.D5.S3.Weil.ZetaRvm.HorizontalPrimeTail

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Zeta23.RvM
open LeanInformationAudit

abbrev cosineSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def cosineActual : Realization cosineSignature :=
  realize cosineSignature (fun _ _ x => Real.cos x) (fun e => nomatch e)

def primeArena : Arena where
  signature := cosineSignature
  Law O := ∀ {R : ℝ}, 2 ≤ R → ∀ t : ℝ,
    Summable (fun n : ℕ => |zetaHorizontalPrimeCoeff R n|) ∧
    Summable (fun n : ℕ =>
      |zetaHorizontalPrimeCoeff R n * Real.cos (t * Real.log (n : ℝ))|) ∧
    zetaHorizontalLogTail R t =
      ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n /
        ((n : ℝ) ^ R * (Real.log (n : ℝ)) ^ 2)) *
          O.readout () () (t * Real.log (n : ℝ))

def cosineBad : Realization cosineSignature :=
  realize cosineSignature (fun _ _ _ => 0) (fun e => nomatch e)

private lemma coefficient_nonneg (R : ℝ) (n : ℕ) :
    0 ≤ zetaHorizontalPrimeCoeff R n := by
  exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      (sq_nonneg (Real.log (n : ℝ))))

private lemma coefficient_two_pos : 0 < zetaHorizontalPrimeCoeff 2 2 := by
  unfold zetaHorizontalPrimeCoeff
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  exact div_pos (Real.log_pos (by norm_num) : 0 < Real.log 2)
    (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (sq_pos_of_pos (Real.log_pos (by norm_num) : 0 < Real.log 2)))

private lemma cosineBad_rejected : ¬ primeArena.Law cosineBad := by
  intro h
  have hh := (h (R := 2) (by norm_num) 0).2.2
  change zetaHorizontalLogTail 2 0 = ∑' n : ℕ,
    (ArithmeticFunction.vonMangoldt n /
      ((n : ℝ) ^ (2 : ℝ) * (Real.log (n : ℝ)) ^ 2)) * 0 at hh
  simp only [mul_zero, tsum_zero] at hh
  have ha := zetaHorizontalLogTail_prime_expansion (R := 2) (by norm_num) 0
  have hs : Summable (fun n : ℕ => zetaHorizontalPrimeCoeff 2 n) :=
    summable_norm_iff.mp (by simpa only [Real.norm_eq_abs] using ha.1)
  have hp := hs.tsum_pos (coefficient_nonneg 2) 2 coefficient_two_pos
  have he : zetaHorizontalLogTail 2 0 = ∑' n : ℕ, zetaHorizontalPrimeCoeff 2 n := by
    simpa only [zero_mul, Real.cos_zero, mul_one, zetaHorizontalPrimeCoeff] using ha.2.2
  linarith

private lemma cosineDependence : ObservationalDependence cosineSignature cosineActual := by
  intro i
  refine ⟨(), 0, Real.pi, ?_⟩
  change Real.cos 0 ≠ Real.cos Real.pi
  norm_num

def primeEvidence : Registration primeArena (type_of% @zetaHorizontalLogTail_prime_expansion) where
  actual := cosineActual
  bridge := Iff.rfl
  variation := ⟨zetaHorizontalLogTail_prime_expansion, cosineBad, cosineBad_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    primeArena.Law cosineActual cosineBad cosineBad_rejected
  dependence := cosineDependence

def primeAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@zetaHorizontalLogTail_prime_expansion) (Realization cosineSignature) Unit Unit where
  unitName := `Zeta23.RvM.zetaHorizontalLogTail_prime_expansion.audit
  realizationName := `Reg.D5.S3.Weil.ZetaRvm.HorizontalPrimeTail.primeEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨primeArena⟩
  objectArena := .source ⟨primeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source primeArena ⟨primeEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize cosineSignature (fun _ _ x => Real.cos x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaRvm.HorizontalPrimeTail
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "arg", "fn", "arg", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.ZetaRvm.HorizontalPrimeTail
