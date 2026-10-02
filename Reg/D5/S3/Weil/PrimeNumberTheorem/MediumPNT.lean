import D5.S3.Weil.PrimeNumberTheorem.MediumPNT
import Reg.Support.DependentFamily
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT

open Filter Asymptotics
open scoped Topology Chebyshev
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => Chebyshev.psi x - x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∃ c > 0,
    (fun x => r.readout () () x) =O[atTop]
      fun (x : ℝ) => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change ∃ c > 0, (id : ℝ → ℝ) =O[atTop]
    fun (x : ℝ) => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) at h
  obtain ⟨c, hc, hBigO⟩ := h
  have hPow : Tendsto (fun x : ℝ => (Real.log x) ^ ((1 : ℝ) / 10))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (1 : ℝ) / 10)).comp
      Real.tendsto_log_atTop
  have hExponent : Tendsto
      (fun x : ℝ => -c * (Real.log x) ^ ((1 : ℝ) / 10))
      atTop atBot :=
    (tendsto_const_mul_atBot_of_neg (by linarith : -c < 0)).2 hPow
  have hDecay : Tendsto
      (fun x : ℝ => Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))
      atTop (𝓝 0) := Real.tendsto_exp_atBot.comp hExponent
  have hDecayLittleO :
      (fun x : ℝ => Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))
        =o[atTop] (fun _ : ℝ => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).2 hDecay
  have hWeightedLittleO :
      (fun x : ℝ => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))
        =o[atTop] (fun x : ℝ => x) := by
    simpa only [Pi.mul_apply, Pi.one_apply, mul_one] using
      (isBigO_refl (fun x : ℝ => x) atTop).mul_isLittleO hDecayLittleO
  have hSelf : (id : ℝ → ℝ) =o[atTop] (id : ℝ → ℝ) :=
    hBigO.trans_isLittleO hWeightedLittleO
  obtain ⟨x, hx, hpos⟩ :=
    ((hSelf.bound (by norm_num : 0 < (1 : ℝ) / 2)).and
      (eventually_gt_atTop (0 : ℝ))).exists
  change ‖x‖ ≤ (1 / 2 : ℝ) * ‖x‖ at hx
  rw [Real.norm_eq_abs, abs_of_pos hpos] at hx
  linarith

def registration : Registration arena
    (∃ c > 0, (Chebyshev.psi - (id : ℝ → ℝ)) =O[atTop]
      fun (x : ℝ) => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.MediumPNT, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    change Chebyshev.psi 0 - 0 ≠ Chebyshev.psi 1 - 1
    norm_num [Chebyshev.psi_zero, Chebyshev.psi_one]

register_information_theorem _root_.MediumPNT
  in arena
  readout via (realize signature
    (fun _ _ x => Chebyshev.psi x - x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Weil.PrimeNumberTheorem.MediumPNT
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true }] })
  escape continues (open)

end

end Reg.D5.S3.Weil.PrimeNumberTheorem.MediumPNT
