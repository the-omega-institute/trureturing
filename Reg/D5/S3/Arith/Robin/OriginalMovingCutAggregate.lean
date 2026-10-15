import D5.S3.Arith.Robin.OriginalMovingCutAggregate
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

noncomputable section
set_option autoImplicit false
open _root_.D5.S3.Arith.Robin.OriginalMovingWindowMoment
open _root_.D5.S3.Arith.Robin.OriginalMovingCutRow
open _root_.D5.S3.Arith.Robin.OriginalMovingCutBudget
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open MeasureTheory Set
open scoped BigOperators

open _root_.D5.S3.Arith.Robin.OriginalMovingCutAggregate

/- Source-owner information audit is unfinished, tracked in
   https://github.com/the-omega-institute/trureturing/issues/15968.
   The exact actual/rejected laws, equivalence bridges and whole-family
   variation/sensitivity proofs below are retained. No Contract.Registration
   is fabricated: actual observational dependence on qualifying rows/sets
   and lawful sourceSelection/current binding remain missing. No validated
   four-slot registration is claimed. -/

namespace Reg.D5.S3.Arith.Robin.OriginalMovingCutAggregate

abbrev aggregateSignature : Signature where
  Params := ℝ × ℝ
  State _ := Set ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def aggregateActual : Realization aggregateSignature :=
  realize aggregateSignature
    (fun _ p S => cutLattice p.1 p.2 S + cutPosterior p.1 p.2 S)
    (fun e => nomatch e)

def aggregateRejected : Realization aggregateSignature :=
  realize aggregateSignature (fun _ p S =>
    (∫ t in S, ∑ d ∈ Finset.Icc 1 ⌊2 * p.2⌋₊,
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * latticeRowRemainder p.1 p.2 t d) + 1)
    (fun e => nomatch e)

abbrev aggregateArena : Arena where
  signature := aggregateSignature
  Law V := ∀ {ell R : ℝ}, 256 ≤ ell → ell < R →
    ∀ {S : Set ℝ}, MeasurableSet S → S ⊆ Set.Icc ell R →
    0 < (MeasureTheory.volume S).toReal →
    V.readout () (ell, R) S =
        (∫ t in S, ∑ d ∈ Finset.Icc 1 ⌊2 * R⌋₊,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) * latticeRowRemainder ell R t d) ∧
    |V.readout () (ell, R) S| ≤
        6 * (∫ t in S, t ^ (-99 / 500 : ℝ) * Real.log (2 * t)) ∧
    6 * (∫ t in S, t ^ (-99 / 500 : ℝ) * Real.log (2 * t)) ≤
        6 * (MeasureTheory.volume S).toReal * ell ^ (-99 / 500 : ℝ) * Real.log (2 * ell)

private theorem aggregateActual_law : aggregateArena.Law aggregateActual :=
  @original_cut_aggregate_estimate

private theorem aggregateRejected_law : ¬ aggregateArena.Law aggregateRejected := by
  intro h
  have hh := h (ell := 256) (R := 257) (by norm_num) (by norm_num)
    (S := Set.Icc 256 257) measurableSet_Icc Subset.rfl (by norm_num)
  have he := hh.1
  change _ + 1 = _ at he
  linarith

private theorem aggregateVariation : Variation aggregateArena aggregateActual :=
  ⟨aggregateActual_law, aggregateRejected, aggregateRejected_law⟩

private theorem aggregateSensitivity : Sensitivity aggregateArena aggregateActual := by
  constructor
  · intro i
    refine ⟨aggregateRejected, ?_, rfl, aggregateRejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim
  · intro e
    exact nomatch e

private theorem aggregateBridge :
    (type_of% (@original_cut_aggregate_estimate)) ↔ aggregateArena.Law aggregateActual := Iff.rfl


#print axioms aggregateBridge
#print axioms aggregateVariation
#print axioms aggregateSensitivity

end Reg.D5.S3.Arith.Robin.OriginalMovingCutAggregate
