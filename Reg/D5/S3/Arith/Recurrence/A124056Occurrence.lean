import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Recurrence.A124056Occurrence
import Reg.Support.SingleDependentReadout

/-! Whole-family realization, variation, sensitivity and observational evidence. -/

namespace Reg.D5.S3.Arith.Recurrence.A124056Occurrence

open LeanInformationAudit
open _root_.D5.S3.Arith.Recurrence.A124056Occurrence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev natSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def sourceActual : Realization natSignature :=
  realize natSignature (fun _ _ n => sourceTerm n) (fun e => nomatch e)

def zeroRejected : Realization natSignature :=
  realize natSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev sourceArena : Arena where
  signature := natSignature
  Law R := R.readout () () 1 = 1 ∧ ∀ n : ℕ, 0 < n →
    R.readout () () (n + 1) = ((Finset.Icc 1 n).filter
      (fun i => R.readout () () i ∣ R.readout () () n)).card

private theorem sourceRejected : ¬ sourceArena.Law zeroRejected := by
  intro h
  have := h.1
  norm_num [zeroRejected, realize] at this

private theorem sourceDependence : ObservationalDependence natSignature sourceActual := by
  intro _
  refine ⟨(), 1, 3, ?_⟩
  change term 0 ≠ term 2
  norm_num [term, values, Fin.snoc]

def sourceRegistration : Registration sourceArena (type_of% @source_specification) where
  actual := sourceActual
  bridge := Iff.rfl
  variation := ⟨source_specification, zeroRejected, sourceRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ sourceRejected
  dependence := sourceDependence

def termActual : Realization natSignature :=
  realize natSignature (fun _ _ n => term n) (fun e => nomatch e)

def threeRejected : Realization natSignature :=
  realize natSignature (fun _ _ _ => 3) (fun e => nomatch e)

abbrev occurrenceArena : Arena where
  signature := natSignature
  Law R := (∀ B : ℕ, ∃ n : ℕ, B ≤ n ∧ R.readout () () n = 3) →
    ∀ k : ℕ, 0 < k → ∃ n : ℕ, 0 < n ∧ R.readout () () (n - 1) = k

private theorem occurrenceRejected : ¬ occurrenceArena.Law threeRejected := by
  intro h
  have hthree : ∀ B : ℕ, ∃ n : ℕ, B ≤ n ∧ threeRejected.readout () () n = 3 :=
    fun B => ⟨B, le_rfl, rfl⟩
  obtain ⟨n, hn, hval⟩ := h hthree 1 (by decide)
  norm_num [threeRejected, realize] at hval

private theorem termDependence : ObservationalDependence natSignature termActual := by
  intro _
  refine ⟨(), 0, 2, ?_⟩
  norm_num [termActual, realize, term, values, Fin.snoc]

def occurrenceRegistration :
    Registration occurrenceArena (type_of% @full_occurrence_of_infinite_three) where
  actual := termActual
  bridge := Iff.rfl
  variation := ⟨full_occurrence_of_infinite_three, threeRejected, occurrenceRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ occurrenceRejected
  dependence := termDependence

def increasingRejected : Realization natSignature :=
  realize natSignature (fun _ _ n => n + 1) (fun e => nomatch e)

abbrev residueArena : Arena where
  signature := natSignature
  Law R := Set.Finite {n : ℕ | R.readout () () n = 3} →
    ∃ q : ℕ, 2 ≤ q ∧ ∀ n : ℕ, 1 < R.readout () () n →
      R.readout () () n % q ≠ 1

private theorem residueRejected : ¬ residueArena.Law increasingRejected := by
  intro h
  have hfinite : Set.Finite {n : ℕ | increasingRejected.readout () () n = 3} := by
    apply (Set.finite_singleton 2).subset
    intro n hn
    change n + 1 = 3 at hn
    simp only [Set.mem_singleton_iff]
    omega
  obtain ⟨q, hq, hresidue⟩ := h hfinite
  have hh := hresidue q (by change 1 < q + 1; omega)
  change (q + 1) % q ≠ 1 at hh
  exact hh (by simp [Nat.mod_eq_of_lt (show 1 < q by omega)])

def residueRegistration :
    Registration residueArena (type_of% @missing_residue_of_finite_three) where
  actual := termActual
  bridge := Iff.rfl
  variation := ⟨missing_residue_of_finite_three, increasingRejected, residueRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ residueRejected
  dependence := termDependence

abbrev countSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ × ℕ) (fun _ => ℕ)

def countActual : Realization countSignature :=
  realize countSignature (fun _ _ x => count x.1 x.2) (fun e => nomatch e)

def countRejected : Realization countSignature :=
  realize countSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev countArena : Arena where
  signature := countSignature
  Law R := ¬ ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ N d : ℕ, 0 < d →
    (R.readout () () (N, d) : ℝ) ≤ C * (prefixMax N : ℝ) ^ (1 - δ)

private theorem countRejectedLaw : ¬ countArena.Law countRejected := by
  intro h
  apply h
  refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
  intro N d hd
  norm_num [countRejected, realize]

private theorem countDependence : ObservationalDependence countSignature countActual := by
  intro _
  refine ⟨(), (0, 1), (1, 1), ?_⟩
  change count 0 1 ≠ count 1 1
  have hc0 : count 0 1 = 0 := by simp [count]
  have hc1 : count 1 1 = 1 := by
    change (({0} : Finset ℕ).filter (fun i => term i = 1)).card = 1
    rw [Finset.filter_singleton]
    simp [show term 0 = 1 from rfl]
  rw [hc0, hc1]
  decide

def countRegistration :
    Registration countArena (type_of% @no_uniform_sublinear_count_bound) where
  actual := countActual
  bridge := Iff.rfl
  variation := ⟨no_uniform_sublinear_count_bound, countRejected, countRejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ countRejectedLaw
  dependence := countDependence


def sourceAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@source_specification) (Realization natSignature) Type Unit where
  unitName := `A124056Occurrence.source_specification.audit
  realizationName := `Reg.D5.S3.Arith.Recurrence.A124056Occurrence.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ _ n => sourceTerm n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

def occurrenceAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@full_occurrence_of_infinite_three) (Realization natSignature) Type Unit where
  unitName := `A124056Occurrence.full_occurrence_of_infinite_three.audit
  realizationName := `Reg.D5.S3.Arith.Recurrence.A124056Occurrence.occurrenceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨occurrenceArena⟩
  objectArena := .source ⟨occurrenceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source occurrenceArena ⟨occurrenceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ _ n => term n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

def residueAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@missing_residue_of_finite_three) (Realization natSignature) Type Unit where
  unitName := `A124056Occurrence.missing_residue_of_finite_three.audit
  realizationName := `Reg.D5.S3.Arith.Recurrence.A124056Occurrence.residueRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨residueArena⟩
  objectArena := .source ⟨residueArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source residueArena ⟨residueRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ _ n => term n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

def countAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@no_uniform_sublinear_count_bound) (Realization countSignature) Type Unit where
  unitName := `A124056Occurrence.no_uniform_sublinear_count_bound.audit
  realizationName := `Reg.D5.S3.Arith.Recurrence.A124056Occurrence.countRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨countArena⟩
  objectArena := .source ⟨countArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source countArena ⟨countRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize countSignature (fun _ _ x => count x.1 x.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Arith.Recurrence.A124056Occurrence
