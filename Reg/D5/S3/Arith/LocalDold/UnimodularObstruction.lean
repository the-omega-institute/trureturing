import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.LocalDold.UnimodularObstruction
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.LocalDold.UnimodularObstruction

open _root_.D5.S3.Arith.LocalDold.UnimodularObstruction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped ArithmeticFunction.Moebius

noncomputable section

abbrev signature : Signature where
  Params := Σ d : ℕ, Σ _ : GLInt d, Fin d
  State x := Fin x.1 → ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} (A : GLInt d) (v : Fin d → ℤ) (i : Fin d)
    (hInvCoord : R.readout () ⟨d, A, i⟩ v = 0)
    (a : ℕ → ℕ)
    (hcoord : ∀ n, 0 < n → (a n : ℤ) = ((A.val ^ n).mulVec v) i)
    (hpos : ∀ n, 0 < n → 0 < a n)
    (ha1 : a 1 = 1)
    (p : ℕ) (hp : p.Prime),
    ∀ H : ℕ, ∃ q > H, q.Prime ∧
      0 < ∑ d ∈ q.divisors, (μ (q / d)) * (pPart p (a d) : ℤ) ∧
      (∑ d ∈ q.divisors, (μ (q / d)) * (pPart p (a d) : ℤ)) < q ∧
      ¬ (q : ℤ) ∣ ∑ d ∈ q.divisors, (μ (q / d)) * (pPart p (a d) : ℤ)

def actual : Realization signature :=
  realize signature (fun _ x v => ((x.2.1⁻¹).val.mulVec v) x.2.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨q, hq0, hq, hpos, hlt, hnd⟩ := h (1 : GLInt 1) (fun _ => 1) 0 rfl
    (fun _ => 1) (by intro n hn; simp) (by intro n hn; norm_num) rfl
    2 Nat.prime_two 0
  have hsum : (∑ d ∈ q.divisors, (μ (q / d)) * (pPart 2 1 : ℤ)) = 0 := by
    rw [show q = q ^ 1 by simp, Nat.divisors_prime_pow hq 1]
    norm_num [Finset.sum_range_succ, pPart]
    rw [ArithmeticFunction.moebius_apply_prime hq, Nat.div_self hq.pos]
    norm_num
  exact (by simpa only [hsum] using hpos : (0 : ℤ) < 0).false

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 1, 0⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  change ((1 : GLInt 1)⁻¹).val.mulVec (fun _ => (0 : ℤ)) 0 ≠
    ((1 : GLInt 1)⁻¹).val.mulVec (fun _ => (1 : ℤ)) 0
  simp

def registration : Registration arena
  (∀ {d : ℕ} (A : GLInt d) (v : Fin d → ℤ) (i : Fin d)
    (hInvCoord : ((A⁻¹).val.mulVec v) i = 0)
    (a : ℕ → ℕ)
    (hcoord : ∀ n, 0 < n → (a n : ℤ) = ((A.val ^ n).mulVec v) i)
    (hpos : ∀ n, 0 < n → 0 < a n)
    (ha1 : a 1 = 1)
    (p : ℕ) (hp : p.Prime),
    ∀ H : ℕ, ∃ q > H, q.Prime ∧
      0 < ∑ d ∈ q.divisors, (μ (q / d)) * (pPart p (a d) : ℤ) ∧
      (∑ d ∈ q.divisors, (μ (q / d)) * (pPart p (a d) : ℤ)) < q ∧
      ¬ (q : ℤ) ∣ ∑ d ∈ q.divisors, (μ (q / d)) * (pPart p (a d) : ℤ)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨unimodular_coordinate_obstruction, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    funext (fun e => nomatch e), rejected_law⟩, fun i => nomatch i⟩
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@unimodular_coordinate_obstruction)
    (type_of% (realize.{0,0,0,0,0} signature
      (fun _ x v => ((x.2.1⁻¹).val.mulVec v) x.2.2) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Arith.LocalDold.UnimodularObstruction.unimodular_coordinate_obstruction.audit
  realizationName := `Reg.D5.S3.Arith.LocalDold.UnimodularObstruction.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} signature
    (fun _ x v => ((x.2.1⁻¹).val.mulVec v) x.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.LocalDold.UnimodularObstruction
    definition := none
    coordinates := #[0,1,3]
    readouts := #[{
      path := #["body", "body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Arith.LocalDold.UnimodularObstruction
