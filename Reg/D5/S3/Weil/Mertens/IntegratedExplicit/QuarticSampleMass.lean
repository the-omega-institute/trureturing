import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampleMass
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter LeanInformationAudit
open _root_.D5.S3.Arith.Robin.CompleteMertensPeak (U)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection (primeTail)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampleMass

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampleMass

abbrev massSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → ℝ)

def massActual : Realization massSignature :=
  realize massSignature (fun _ _ a => blockMass a) (fun e => nomatch e)

private theorem mass_dependence : ObservationalDependence massSignature massActual := by
  intro _
  refine ⟨(), 1, 2, ?_⟩
  intro heq
  have h := congrFun heq 1
  change blockMass 1 1 = blockMass 2 1 at h
  have hU : U 1 = 1 + Real.eulerMascheroniConstant := by simp [U, Chebyshev.psi]
  have hpos : 0 < 1 + Real.eulerMascheroniConstant := by
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  simp [blockMass, sample, hU, max_eq_left hpos.le, hpos.ne'] at h

namespace Comparison

def arena : Arena where
  signature := massSignature
  Law V := ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℕ, 2 ≤ a → a ≤ b →
    (∫ x in (a : ℝ)^4..(b : ℝ)^4, max (-primeTail x) 0 / Real.sqrt x) + 15 * sample b ≤
      135 * V.readout () () a b + C * (Real.log b - Real.log a)

private def rejected : Realization massSignature :=
  realize massSignature (fun _ _ _ _ => -1) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨C, -, h⟩
  have hbad := h 2 2 (by decide) le_rfl
  change (∫ x in (2 : ℝ)^4..(2 : ℝ)^4, max (-primeTail x) 0 / Real.sqrt x) + 15 * sample 2 ≤
    135 * (-1 : ℝ) + C * (Real.log 2 - Real.log 2) at hbad
  have hsample : 0 ≤ sample 2 := div_nonneg (le_max_right _ _) (by positivity)
  norm_num at hbad
  linarith

def evidence : Registration arena (type_of% @prime_mass_le_samples) where
  actual := massActual
  bridge := Iff.rfl
  variation := ⟨prime_mass_le_samples, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law massActual rejected rejected_law
  dependence := mass_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@prime_mass_le_samples) (Realization massSignature) Unit Unit where
  unitName := .str
    `D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampleMass.prime_mass_le_samples
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampleMass.Comparison "evidence"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize massSignature (fun _ _ a => blockMass a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampleMass
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg", "body", "body", "body", "body",
                 "arg", "fn", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Comparison

namespace Growth

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ z => riemannZeta z) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law V := ∀ {z : ℂ}, V.readout () () z = 0 → 1/2 < z.re → ∀ {ε : ℝ}, 0 < ε →
    ∀ᶠ k : ℕ in atTop, (k : ℝ)^(16 * (z.re - 1/2) - ε) ≤ blockMass (k^3) (k^4)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private lemma sample_le {n : ℕ} (hn : 1 ≤ n) : sample n ≤ 9 * (n : ℝ)^8 := by
  let x := (n : ℝ)^4
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hx : 1 ≤ x := one_le_pow₀ hn'
  have hsum : (∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt m / (m : ℝ)) ≤
      Chebyshev.psi x := by
    unfold Chebyshev.psi
    apply Finset.sum_le_sum
    intro m hm
    have hm' : 1 ≤ (m : ℝ) := by
      exact_mod_cast (show 1 ≤ m from (Finset.mem_Ioc.mp hm).1)
    exact div_le_self (by positivity) hm'
  have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
  have hpsi : Chebyshev.psi x ≤ 7 * x :=
    (Chebyshev.psi_le_const_mul_self (by linarith)).trans
      (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
  have hcent : (1 + Real.eulerMascheroniConstant) * x ≤ 2 * x :=
    mul_le_mul_of_nonneg_right (by linarith [Real.eulerMascheroniConstant_lt_two_thirds]) (by linarith)
  have hU : U x ≤ 9 * x^2 := by
    unfold U
    nlinarith [mul_le_mul_of_nonneg_left (hsum.trans hpsi) (show 0 ≤ x by linarith),
      Chebyshev.psi_nonneg x, Real.log_nonneg hx, mul_nonneg (show 0 ≤ x by linarith)
        (Real.log_nonneg hx), mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ x - 1 by linarith)]
  have hmax : max (U x) 0 ≤ 9 * x^2 := max_le hU (by positivity)
  calc
    sample n ≤ max (U x) 0 := div_le_self (le_max_right _ _) (one_le_pow₀ hn')
    _ ≤ 9 * x^2 := hmax
    _ = 9 * (n : ℝ)^8 := by dsimp [x]; ring

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (z := 4) rfl (by norm_num) (ε := 8) (by norm_num)
  obtain ⟨k, hk, hk2⟩ := (hbad.and (eventually_ge_atTop (2 : ℕ))).exists
  norm_num at hk
  have hk2' : 2 ≤ (k : ℝ) := by exact_mod_cast hk2
  have hk1 : 1 ≤ k := by omega
  have hcard : (Finset.Icc (k^3) (k^4)).card ≤ k^4 + 1 := by
    rw [← Finset.card_range (k^4 + 1)]
    exact Finset.card_le_card fun n hn => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hn).2)
  have hmass : blockMass (k^3) (k^4) ≤ 18 * (k : ℝ)^36 := by
    calc
      _ ≤ ∑ n ∈ Finset.Icc (k^3) (k^4), 9 * (k : ℝ)^32 := by
        apply Finset.sum_le_sum
        intro n hn
        have hm := Finset.mem_Icc.mp hn
        have hkn : k ≤ n := (le_self_pow₀ hk1 (by decide : 3 ≠ 0)).trans hm.1
        have hnk : (n : ℝ) ≤ (k : ℝ)^4 := by exact_mod_cast hm.2
        apply (sample_le (hk1.trans hkn)).trans
        calc
          _ ≤ 9 * ((k : ℝ)^4)^8 := by gcongr
          _ = _ := by ring
      _ ≤ _ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have hcard' : ((Finset.Icc (k^3) (k^4)).card : ℝ) ≤ (k : ℝ)^4 + 1 := by exact_mod_cast hcard
        have hmono := mul_le_mul_of_nonneg_right hcard' (by positivity : 0 ≤ 9 * (k : ℝ)^32)
        have hkfour := one_le_pow₀ (show 1 ≤ (k : ℝ) by linarith) (n := 4)
        nlinarith only [hmono, mul_nonneg (show 0 ≤ (k : ℝ)^4 - 1 by linarith)
          (pow_nonneg (show 0 ≤ (k : ℝ) by linarith) 32)]
  have hlarge := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hk2' 12
  have hstrict : 18 * (k : ℝ)^36 < (k : ℝ)^48 := by
    have hcoef : (18 : ℝ) < (k : ℝ)^12 := lt_of_lt_of_le (by norm_num) hlarge
    calc
      _ < (k : ℝ)^12 * (k : ℝ)^36 :=
        mul_lt_mul_of_pos_right hcoef (pow_pos (by linarith) _)
      _ = _ := by ring
  exact (not_lt_of_ge (hk.trans hmass)) hstrict

def evidence : Registration arena (type_of% @off_line_zero_forces_sample_mass) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@off_line_zero_forces_sample_mass, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(), (0 : ℂ), (-2 : ℂ), ?_⟩
    change riemannZeta 0 ≠ riemannZeta (-2)
    have hz : riemannZeta (-2) = 0 := by simpa using riemannZeta_neg_two_mul_nat_add_one 0
    rw [hz, riemannZeta_zero]
    norm_num

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@off_line_zero_forces_sample_mass) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampleMass.off_line_zero_forces_sample_mass
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampleMass.Growth "evidence"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => riemannZeta z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampleMass
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "domain", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Growth

namespace Criterion

def arena : Arena where
  signature := massSignature
  Law V := RiemannHypothesis ↔ ∀ η : ℝ, 0 < η → ∀ A : ℕ, ∃ k ≥ max A 2,
    V.readout () () (k^3) (k^4) ≤ (k : ℝ)^η

private def rejected : Realization massSignature := by
  classical
  exact realize massSignature (fun _ _ a _ => if RiemannHypothesis then a else 0) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  classical
  change ¬(RiemannHypothesis ↔ ∀ η : ℝ, 0 < η → ∀ A : ℕ, ∃ k ≥ max A 2,
    (if RiemannHypothesis then ((k^3 : ℕ) : ℝ) else 0) ≤ (k : ℝ)^η)
  intro h
  by_cases hr : RiemannHypothesis
  · obtain ⟨k, hk, hbad⟩ := h.mp hr 1 one_pos 2
    have hk' : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
    simp only [hr, ite_true, Nat.cast_pow, Real.rpow_one] at hbad
    exact (not_lt_of_ge hbad) (by simpa using pow_lt_pow_right₀ hk' (by decide : 1 < 3))
  · apply hr
    apply h.mpr
    intro η _ A
    exact ⟨max A 2, le_rfl, by simpa [hr] using Real.rpow_nonneg (by positivity) η⟩

def evidence : Registration arena (type_of% @rh_iff_subpower_sample_mass) where
  actual := massActual
  bridge := Iff.rfl
  variation := ⟨rh_iff_subpower_sample_mass, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law massActual rejected rejected_law
  dependence := mass_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@rh_iff_subpower_sample_mass) (Realization massSignature) Unit Unit where
  unitName := .str
    `D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampleMass.rh_iff_subpower_sample_mass
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampleMass.Criterion "evidence"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize massSignature (fun _ _ a => blockMass a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampleMass
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "body", "body", "arg", "body", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Criterion

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampleMass
