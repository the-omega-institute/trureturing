import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.OriginalEndpointFirstLayerBand
import Reg.Support.DependentFamily
import Reg.D5.S3.Arith.Robin.OriginalEndpointPrimeTail

/- Source candidates only. No Reg/native/producer validation was run by
this lane. Four complete original Laws below intervene only in the actual
tail(N) occurrence. They do not cover endpoint_price_lower_of_largest or
endpoint_first_layer_band. All clauses and hypotheses of each selected
source theorem are retained, with one role and no anchors.

The imported existing tail family's kernel-checked observational dependence
is reused; its producer state declared_unresolved/source.residual_requires_open
is NOT evidence that these or the imported registration are declared_validated.
The source selectors are authored from the complete source telescopes and
raw comparison-argument positions. Compiled source-binding evidence is unpaid.
-/

noncomputable section
set_option autoImplicit false

namespace Reg.D5.S3.Arith.Robin.OriginalEndpointFirstLayerBand

open Finset
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Arith.Robin.ActualTwoPriceDefect
open _root_.D5.S3.Arith.Robin.ActualGlobalBracketing
open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail
open _root_.D5.S3.Arith.Robin.OriginalEndpointFirstLayerBand
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace TailObservation

abbrev signature (P : Type) : Signature where
  Params := P
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual (P : Type) : Realization (signature P) :=
  realize (signature P) (fun _ _ N => tail N) (fun e => nomatch e)

private theorem dependence (P : Type) (p0 : P) :
    ObservationalDependence (signature P) (actual P) := by
  intro _
  obtain ⟨q, x, y, hxy⟩ :=
    _root_.Reg.D5.S3.Arith.Robin.OriginalEndpointPrimeTail.family.dependence ()
  refine ⟨p0, x, y, ?_⟩
  change tail x ≠ tail y
  change tail x ≠ tail y at hxy
  exact hxy

end TailObservation

/-- A whole source Law has a genuine admissible endpoint at any requested
largest-prime threshold. This is not a supplied endpoint-existence premise. -/
private theorem exists_strict_endpoint_largest_ge (K : ℕ) :
    ∃ q : ℝ, ∃ N : ℕ, 0 < q ∧ N = strictInteger q ∧ K ≤ largestPrime N := by
  obtain ⟨p, hpK, hp⟩ := Nat.exists_infinite_primes K
  have hm : 0 < goldenLayerMarginal p 1 :=
    _root_.D5.S3.Arith.GoldenResource.GoldenResourcePriceInterval.marginal_pos hp (by omega)
  let q : ℝ := goldenLayerMarginal p 1 / 2
  have hq : 0 < q := half_pos hm
  have hfirst : q < goldenLayerMarginal p 1 := by dsimp only [q]; linarith
  have ha : 1 ≤ (strictInteger q).factorization p :=
    (strict_layer_iff hq hp (by omega : 1 ≤ (1 : ℕ))).mpr hfirst
  have hmem : p ∈ (strictInteger q).primeFactors :=
    hp.mem_primeFactors (Nat.dvd_of_factorization_pos (by omega))
      (by have hpos := strictInteger_pos hq; omega)
  exact ⟨q, strictInteger q, hq, rfl, hpK.trans (Finset.le_sup (f := id) hmem)⟩

namespace BertrandTail

def rejected : Realization (TailObservation.signature ℝ) :=
  realize (TailObservation.signature ℝ)
    (fun _ _ N => 1 / (16 * (largestPrime N : ℝ)) - 1)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := TailObservation.signature ℝ
  Law R := ∀ {q : ℝ}, 0 < q → ∀ {N : ℕ},
    (N = strictInteger q ∨ N = maximalInteger q) →
    16 ≤ largestPrime N → 1 / (16 * (largestPrime N : ℝ)) < R.readout () q N

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨q, N, hq, hN, hu⟩ := exists_strict_endpoint_largest_ge 16
  have hbad := h (q := q) hq (N := N) (Or.inl hN) hu
  change 1 / (16 * (largestPrime N : ℝ)) <
    1 / (16 * (largestPrime N : ℝ)) - 1 at hbad
  linarith

def family : Registration arena (type_of% (@endpoint_tail_gt_inv_sixteen_mul_largest)) where
  actual := TailObservation.actual ℝ
  bridge := Iff.rfl
  variation := ⟨@endpoint_tail_gt_inv_sixteen_mul_largest, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, (by funext e; exact nomatch e), rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := TailObservation.dependence ℝ 1

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@endpoint_tail_gt_inv_sixteen_mul_largest)
    (type_of% (realize (TailObservation.signature ℝ)
      (fun _ _ N => tail N) (fun e => nomatch e))) Type Unit where
  unitName := `D5.S3.Arith.Robin.OriginalEndpointFirstLayerBand.endpoint_tail_gt_inv_sixteen_mul_largest.audit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalEndpointFirstLayerBand.BertrandTail.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (TailObservation.signature ℝ)
    (fun _ _ N => tail N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalEndpointFirstLayerBand
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end BertrandTail

namespace ThetaBand

def rejected : Realization (TailObservation.signature (ℝ × ℝ × ℝ)) :=
  realize (TailObservation.signature (ℝ × ℝ × ℝ))
    (fun _ p _ => (Chebyshev.theta p.2.2 - Chebyshev.theta p.2.1) /
      (p.2.2 ^ 2 * Real.log p.2.2) - 1)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := TailObservation.signature (ℝ × ℝ × ℝ)
  Law R := ∀ {q : ℝ}, 0 < q → ∀ {N : ℕ},
    (N = strictInteger q ∨ N = maximalInteger q) →
    2 ≤ largestPrime N → ∀ {A B : ℝ},
    2 * Real.sqrt (largestPrime N : ℝ) ≤ A →
    A ≤ B → B ≤ (largestPrime N : ℝ) →
    (Chebyshev.theta B - Chebyshev.theta A) / (B ^ 2 * Real.log B) ≤
      R.readout () (q, A, B) N

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨q, N, hq, hN, hu⟩ := exists_strict_endpoint_largest_ge 16
  have huR : (16 : ℝ) ≤ (largestPrime N : ℝ) := by exact_mod_cast hu
  have hs2 : (2 : ℝ) ≤ Real.sqrt (largestPrime N : ℝ) :=
    Real.le_sqrt_of_sq_le (by nlinarith only [huR])
  have hsEq := Real.sq_sqrt (by positivity : 0 ≤ (largestPrime N : ℝ))
  have hlarge : 2 * Real.sqrt (largestPrime N : ℝ) ≤ (largestPrime N : ℝ) := by
    have hmul := mul_nonneg (Real.sqrt_nonneg (largestPrime N : ℝ))
      (sub_nonneg.mpr hs2)
    nlinarith only [hmul, hsEq]
  have hbad := h (q := q) hq (N := N) (Or.inl hN) (by omega : 2 ≤ largestPrime N)
    (A := (largestPrime N : ℝ)) (B := (largestPrime N : ℝ)) hlarge le_rfl le_rfl
  change (Chebyshev.theta (largestPrime N : ℝ) - Chebyshev.theta (largestPrime N : ℝ)) /
      ((largestPrime N : ℝ) ^ 2 * Real.log (largestPrime N : ℝ)) ≤
    (Chebyshev.theta (largestPrime N : ℝ) - Chebyshev.theta (largestPrime N : ℝ)) /
      ((largestPrime N : ℝ) ^ 2 * Real.log (largestPrime N : ℝ)) - 1 at hbad
  linarith

def family : Registration arena (type_of% (@endpoint_tail_ge_theta_band)) where
  actual := TailObservation.actual (ℝ × ℝ × ℝ)
  bridge := Iff.rfl
  variation := ⟨@endpoint_tail_ge_theta_band, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, (by funext e; exact nomatch e), rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := TailObservation.dependence (ℝ × ℝ × ℝ) (1, 0, 0)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@endpoint_tail_ge_theta_band)
    (type_of% (realize (TailObservation.signature (ℝ × ℝ × ℝ))
      (fun _ _ N => tail N) (fun e => nomatch e))) Type Unit where
  unitName := `D5.S3.Arith.Robin.OriginalEndpointFirstLayerBand.endpoint_tail_ge_theta_band.audit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalEndpointFirstLayerBand.ThetaBand.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (TailObservation.signature (ℝ × ℝ × ℝ))
    (fun _ _ N => tail N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalEndpointFirstLayerBand
    definition := none
    coordinates := #[0, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ThetaBand

namespace ChebyshevTail

def rejected : Realization (TailObservation.signature ℝ) :=
  realize (TailObservation.signature ℝ)
    (fun _ _ N => max 0 (chebyshevBandLower (largestPrime N : ℝ)) /
      (64 * (largestPrime N : ℝ) * Real.log (8 * Real.sqrt (largestPrime N : ℝ))) - 1)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := TailObservation.signature ℝ
  Law R := ∀ {q : ℝ}, 0 < q → ∀ {N : ℕ},
    (N = strictInteger q ∨ N = maximalInteger q) →
    64 ≤ largestPrime N →
    max 0 (chebyshevBandLower (largestPrime N : ℝ)) /
      (64 * (largestPrime N : ℝ) * Real.log (8 * Real.sqrt (largestPrime N : ℝ))) ≤
        R.readout () q N

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨q, N, hq, hN, hu⟩ := exists_strict_endpoint_largest_ge 64
  have hbad := h (q := q) hq (N := N) (Or.inl hN) hu
  change max 0 (chebyshevBandLower (largestPrime N : ℝ)) /
      (64 * (largestPrime N : ℝ) * Real.log (8 * Real.sqrt (largestPrime N : ℝ))) ≤
    max 0 (chebyshevBandLower (largestPrime N : ℝ)) /
      (64 * (largestPrime N : ℝ) * Real.log (8 * Real.sqrt (largestPrime N : ℝ))) - 1 at hbad
  linarith

def family : Registration arena (type_of% (@endpoint_tail_ge_chebyshev)) where
  actual := TailObservation.actual ℝ
  bridge := Iff.rfl
  variation := ⟨@endpoint_tail_ge_chebyshev, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, (by funext e; exact nomatch e), rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := TailObservation.dependence ℝ 1

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@endpoint_tail_ge_chebyshev)
    (type_of% (realize (TailObservation.signature ℝ)
      (fun _ _ N => tail N) (fun e => nomatch e))) Type Unit where
  unitName := `D5.S3.Arith.Robin.OriginalEndpointFirstLayerBand.endpoint_tail_ge_chebyshev.audit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalEndpointFirstLayerBand.ChebyshevTail.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (TailObservation.signature ℝ)
    (fun _ _ N => tail N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalEndpointFirstLayerBand
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ChebyshevTail

namespace SqrtLogTail

def rejected : Realization (TailObservation.signature ℝ) :=
  realize (TailObservation.signature ℝ)
    (fun _ _ N => Real.log 2 / (32 * Real.sqrt (largestPrime N : ℝ) *
      Real.log (8 * Real.sqrt (largestPrime N : ℝ))) - 1)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := TailObservation.signature ℝ
  Law R := ∀ {q : ℝ}, 0 < q → ∀ {N : ℕ},
    (N = strictInteger q ∨ N = maximalInteger q) →
    2 ^ 22 ≤ largestPrime N →
    Real.log 2 / (32 * Real.sqrt (largestPrime N : ℝ) *
      Real.log (8 * Real.sqrt (largestPrime N : ℝ))) ≤ R.readout () q N

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨q, N, hq, hN, hu⟩ := exists_strict_endpoint_largest_ge (2 ^ 22)
  have hbad := h (q := q) hq (N := N) (Or.inl hN) hu
  change Real.log 2 / (32 * Real.sqrt (largestPrime N : ℝ) *
      Real.log (8 * Real.sqrt (largestPrime N : ℝ))) ≤
    Real.log 2 / (32 * Real.sqrt (largestPrime N : ℝ) *
      Real.log (8 * Real.sqrt (largestPrime N : ℝ))) - 1 at hbad
  linarith

def family : Registration arena (type_of% (@endpoint_tail_ge_sqrt_log)) where
  actual := TailObservation.actual ℝ
  bridge := Iff.rfl
  variation := ⟨@endpoint_tail_ge_sqrt_log, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, (by funext e; exact nomatch e), rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := TailObservation.dependence ℝ 1

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@endpoint_tail_ge_sqrt_log)
    (type_of% (realize (TailObservation.signature ℝ)
      (fun _ _ N => tail N) (fun e => nomatch e))) Type Unit where
  unitName := `D5.S3.Arith.Robin.OriginalEndpointFirstLayerBand.endpoint_tail_ge_sqrt_log.audit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalEndpointFirstLayerBand.SqrtLogTail.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (TailObservation.signature ℝ)
    (fun _ _ N => tail N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalEndpointFirstLayerBand
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SqrtLogTail

end Reg.D5.S3.Arith.Robin.OriginalEndpointFirstLayerBand
