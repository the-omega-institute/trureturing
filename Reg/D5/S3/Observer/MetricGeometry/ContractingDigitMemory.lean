import D5.S3.Observer.MetricGeometry.ContractingDigitMemory
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

open _root_.D5.S3.Observer.MetricGeometry.ContractingDigitMemory
open _root_.D5.S3.Observer.MetricGeometry.ForwardInvariantPredictorCover
namespace Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => 2 ^ n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Preserve every original hypothesis and the full least-state assertion. -/
def arena : Arena where
  signature := signature
  Law obs := ∀ {lam eps : ℝ} (hlampos : 0 < lam) (hlamhalf : lam < 1 / 2)
    (L : ℕ) (_hL : 1 ≤ L)
    (_heps_lower : lam ^ L / 2 ≤ eps)
    (_heps_upper : eps < (1 - lam) * lam ^ (L - 1) / 2),
    IsLeast
      {s : ℕ |
        HasFinitePredictor
          (digitStep lam hlampos.le (by linarith))
          (fun x : DigitState lam => x.1) eps s}
      (obs.readout () () L)

theorem positiveLaw : arena.Law actual :=
  @contracting_digit_memory_exact

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero := (h (lam := 1/4) (eps := 1/8) (by norm_num) (by norm_num)
    1 (by norm_num) (by norm_num) (by norm_num)).1
  obtain ⟨S, finiteS, hne, hcard, _⟩ := hzero
  let : Fintype S := finiteS
  let : Nonempty S := hne
  have hpos := Fintype.card_pos (α := S)
  change Fintype.card S ≤ 0 at hcard
  omega

theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hj
    exact (hj (@Subsingleton.elim Unit _ j i)).elim
  · intro e; exact nomatch e

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def registration : Registration arena (arena.Law actual) :=
  Registration.mk actual Iff.rfl ⟨positiveLaw, rejected, rejected_law⟩ sensitivity dependence

register_information_theorem
  _root_.D5.S3.Observer.MetricGeometry.ContractingDigitMemory.contracting_digit_memory_exact
  in arena
  readout via (realize signature (fun _ _ t => 2 ^ t) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Observer.MetricGeometry.ContractingDigitMemory
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateOperand := some #["arg"] }] })
  escape continues (open)

#print axioms registration
end Reg.D5.S3.Observer.MetricGeometry.ContractingDigitMemory
