import LeanInformationAuditInterface.Contract.Registration
import D5.S3.CharacterSums.DyadicMangoldtPrimeSupply
import Reg.Support.SingleDependentReadout

/-! The audit observes the weight of successful primes as the dyadic band changes. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Filter
open _root_.D5.S3.CharacterSums.DyadicMangoldtPrimeSupply
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.CharacterSums.DyadicMangoldtPrimeSupply

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℕ) (fun _ => ℝ)

def observed : Realization signature :=
  realize signature (fun _ ε k => goodMass ε (k+1)) (fun e => nomatch e)

def emptyBands : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ ε : ℝ, 0 < ε → Summable (badMass ε) ∧
    Tendsto (fun K : ℕ => ∑ k ∈ Finset.range K, V.readout () ε k) atTop atTop

private theorem empty_fails : ¬ arena.Law emptyBands := by
  intro h
  have hf := (h 1 one_pos).2
  change Tendsto (fun K : ℕ => ∑ _k ∈ Finset.range K, (0:ℝ)) atTop atTop at hf
  exact not_tendsto_const_atTop (0:ℝ) (atTop : Filter ℕ) (by simpa only [Finset.sum_const_zero] using hf)

private theorem dependence : ObservationalDependence signature observed := by
  intro _
  by_contra h
  push Not at h
  have h0 : goodMass 1 (0+1) = 0 := by
    simp [goodMass, Finset.sum_filter]
  have hz (k : ℕ) : goodMass 1 (k+1) = 0 := by
    exact (h 1 k 0).trans h0
  have hf := (dyadic_quadratic_mangoldt_supply 1 one_pos).2
  simp only [hz,Finset.sum_const_zero,not_tendsto_const_atTop] at hf

def family : Registration arena (type_of% @dyadic_quadratic_mangoldt_supply) where
  actual := observed
  bridge := Iff.rfl
  variation := ⟨dyadic_quadratic_mangoldt_supply,emptyBands,empty_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law observed emptyBands empty_fails
  dependence := dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@dyadic_quadratic_mangoldt_supply) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.CharacterSums.DyadicMangoldtPrimeSupply.dyadic_quadratic_mangoldt_supply
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DyadicMangoldtPrimeSupply.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ ε k => goodMass ε (k+1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DyadicMangoldtPrimeSupply
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","arg","fn","fn","arg","body","arg","body"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace RealScale

open Real _root_.D5.S3.CharacterSums.PrimeProgressionWindowMass

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℝ × ℝ) (fun _ => Finset ℕ) (fun _ => ℝ)

def observed : Realization signature :=
  realize signature (fun _ p E => survivingMass p.1 p.2 E) (fun e => nomatch e)

def zeroMass : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, ∀ E : Finset ℕ,
    (E.card:ℝ) ≤ exp (x^(ε/5)/3) → x^(ε/5)/173065984000 ≤ V.readout () (ε,x) E

private theorem positive_somewhere (V : Realization signature) (h : arena.Law V) :
    ∃ x : ℝ, 0 < V.readout () (1,x) ∅ := by
  obtain ⟨x,hx,hl⟩ := ((eventually_gt_atTop (0:ℝ)).and (h 1 one_pos)).exists
  refine ⟨x,lt_of_lt_of_le (by positivity) (hl ∅ (by simpa only [Finset.card_empty,Nat.cast_zero] using (exp_pos _).le))⟩

private theorem zero_fails : ¬ arena.Law zeroMass := by
  intro h
  obtain ⟨x,hx⟩ := positive_somewhere _ h
  exact lt_irrefl _ hx

private theorem dependence : ObservationalDependence signature observed := by
  intro _
  obtain ⟨x,hx⟩ := positive_somewhere observed real_scale_quadratic_mangoldt_supply
  let allPrimes := primeBand (3:ZMod 8) (x^((1:ℝ)/5))
  refine ⟨(1,x),∅,allPrimes,?_⟩
  have he : survivingMass 1 x allPrimes = 0 := by
    simp +contextual [survivingMass,allPrimes]
  change survivingMass 1 x ∅ ≠ survivingMass 1 x allPrimes
  rw [he]; exact ne_of_gt hx

def family : Registration arena (type_of% @real_scale_quadratic_mangoldt_supply) where
  actual := observed
  bridge := Iff.rfl
  variation := ⟨real_scale_quadratic_mangoldt_supply,zeroMass,zero_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law observed zeroMass zero_fails
  dependence := dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@real_scale_quadratic_mangoldt_supply) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DyadicMangoldtPrimeSupply.real_scale_quadratic_mangoldt_supply
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DyadicMangoldtPrimeSupply.RealScale.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p E => survivingMass p.1 p.2 E) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DyadicMangoldtPrimeSupply
    definition := none
    coordinates := #[0,2]
    readouts := #[{
      path := #["body","body","fn","arg","body","body","body","arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end RealScale

end Reg.D5.S3.CharacterSums.DyadicMangoldtPrimeSupply
