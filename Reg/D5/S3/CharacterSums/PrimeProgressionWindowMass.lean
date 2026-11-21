import LeanInformationAuditInterface.Contract.Registration
import D5.S3.CharacterSums.PrimeProgressionWindowMass
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Set Real Finset
open _root_.D5.S3.CharacterSums.PrimeProgressionWindowMass
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.CharacterSums.PrimeProgressionWindowMass

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun m => ZMod m) (fun _ => ℝ → Finset ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ a => primeBand a) (fun e => nomatch e)

def emptyBand : Realization signature :=
  realize signature (fun _ _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {m : ℕ} [NeZero m] (a : ZMod m), IsUnit a →
    ∀ᶠ T : ℝ in atTop, T / ((21633248000:ℝ) * (m.totient:ℝ)) ≤
      ∑ n ∈ V.readout () m a T, log n / n

private theorem empty_fails : ¬ arena.Law emptyBand := by
  intro h
  have hz := h (1 : ZMod 8) isUnit_one
  obtain ⟨T, hT, hle⟩ := (hz.and (eventually_gt_atTop (0 : ℝ))).exists
  change T / ((21633248000 : ℝ) * (Nat.totient 8 : ℝ)) ≤ ∑ n ∈ (∅ : Finset ℕ), log n / n at hT
  have hn : Nat.totient 8 = 4 := by decide
  simp [hn] at hT
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨8, 3, 1, ?_⟩
  change primeBand (3 : ZMod 8) ≠ primeBand (1 : ZMod 8)
  intro he
  have hl : exp (log (3 : ℝ)/2) < (3 : ℝ) := by
    calc
      _ < exp (log 3) := exp_lt_exp.mpr (by linarith [log_pos (show (1:ℝ)<3 by norm_num)])
      _ = _ := exp_log (by norm_num)
  have h3 : 3 ∈ primeBand (3 : ZMod 8) (log 3) := by
    simp [primeBand, exp_log (show (0:ℝ)<3 by norm_num), hl, Nat.prime_three]
  have hbad := (Finset.mem_filter.mp ((congrFun he (log 3)) ▸ h3)).2.2.1
  exact (by decide : (3 : ZMod 8) ≠ 1) hbad

def family : Registration arena (type_of% @prime_progression_window_mass) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@prime_progression_window_mass, emptyBand, empty_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual emptyBand empty_fails
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@prime_progression_window_mass) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.PrimeProgressionWindowMass.prime_progression_window_mass
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.CharacterSums.PrimeProgressionWindowMass "family"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ a => primeBand a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.PrimeProgressionWindowMass
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "body", "arg", "fn", "arg", "fn"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.CharacterSums.PrimeProgressionWindowMass
