/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortQuadratureCover
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform short-gap mixed derivative sign by quadrature over the compact grid. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Row01
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Row02
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Row03
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Row04
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Row05
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Row06
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Rows07To08
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Rows09To10
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Row11
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Row12
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Row13
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Rows14To15
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Rows16To17
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Rows18To19
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Rows20To21
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Rows22To23
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Rows24To25
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Rows26To27
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Rows28To29
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Rows30To31
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Rows32To33
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Rows34To35
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Rows36To37
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Rows38To39
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Rows40To41
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Rows42To43
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Rows44To45
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Rows46To47
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Rows48To49
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Rows50To51
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Rows52To53
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Rows54To55
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Rows56To57
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Rows58To59
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Rows60To61
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Rows62To63
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Rows64To65
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Rows66To67
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Rows68To69
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Rows70To71
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover.Row72

/-! The original mixed derivative is strictly negative on the compact short-gap band. -/

namespace RefinedBMV.PositiveCenter.CompactShortQuadratureCover

open CompactShortQuadratureBox (logKernel_mixed_lt_of_grid_checks)
open CompactTaylorModel.ShortTangentGrid (leaves)

private def splitRow (i : Fin 72) : Bool :=
  decide (i.val < 10) ||
    [10, 11, 12, 14, 15, 16, 17, 21, 22, 26, 27, 32].contains i.val

private theorem checked_rows (i : Fin 72) :
    if splitRow i then CheckedSubbox (row i) 0 (3 / 22) ∧ CheckedSubbox (row i) (3 / 22) (3 / 11)
    else CheckedSubbox (row i) 0 (3 / 11) := by
  fin_cases i
  · exact ⟨row01_low, row01_high⟩
  · exact ⟨row02_low, row02_high⟩
  · exact ⟨row03_low, row03_high⟩
  · exact ⟨row04_low, row04_high⟩
  · exact ⟨row05_low, row05_high⟩
  · exact ⟨row06_low, row06_high⟩
  · exact ⟨row07_low, row07_high⟩
  · exact ⟨row08_low, row08_high⟩
  · exact ⟨row09_low, row09_high⟩
  · exact ⟨row10_low, row10_high⟩
  · exact ⟨row11_low, row11_high⟩
  · exact ⟨row12_low, row12_high⟩
  · exact ⟨row13_low, row13_high⟩
  · exact row14
  · exact ⟨row15_low, row15_high⟩
  · exact ⟨row16_low, row16_high⟩
  · exact ⟨row17_low, row17_high⟩
  · exact ⟨row18_low, row18_high⟩
  · exact row19
  · exact row20
  · exact row21
  · exact ⟨row22_low, row22_high⟩
  · exact ⟨row23_low, row23_high⟩
  · exact row24
  · exact row25
  · exact row26
  · exact ⟨row27_low, row27_high⟩
  · exact ⟨row28_low, row28_high⟩
  · exact row29
  · exact row30
  · exact row31
  · exact row32
  · exact ⟨row33_low, row33_high⟩
  · exact row34
  · exact row35
  · exact row36
  · exact row37
  · exact row38
  · exact row39
  · exact row40
  · exact row41
  · exact row42
  · exact row43
  · exact row44
  · exact row45
  · exact row46
  · exact row47
  · exact row48
  · exact row49
  · exact row50
  · exact row51
  · exact row52
  · exact row53
  · exact row54
  · exact row55
  · exact row56
  · exact row57
  · exact row58
  · exact row59
  · exact row60
  · exact row61
  · exact row62
  · exact row63
  · exact row64
  · exact row65
  · exact row66
  · exact row67
  · exact row68
  · exact row69
  · exact row70
  · exact row71
  · exact row72

/-- The mixed logarithmic derivative is strictly negative for every degree at least eleven
throughout `1/2 ≤ u ≤ 4` and `0 < v - u ≤ 1`. -/
theorem logKernel_mixed_lt {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (huLo : 1 / 2 ≤ u) (huHi : u ≤ 4) (huv : u < v) (hdHi : v - u ≤ 1) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  apply logKernel_mixed_lt_of_grid_checks hp huLo huHi huv hdHi
  intro leaf hmem
  obtain ⟨n, hn, hleaf⟩ := List.mem_iff_getElem.mp hmem
  let i : Fin 72 := ⟨n, by simpa only [leaves_length] using hn⟩
  have hrow : row i = leaf.box := congrArg (·.box) hleaf
  rw [← hrow]
  have hpPos : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hpLo : (11 : ℝ) ≤ p := by exact_mod_cast hp
  have hhLo : (0 : ℝ) ≤ 3 / (p : ℝ) := by positivity
  have hhHi : 3 / (p : ℝ) ≤ 3 / 11 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpLo
  have checked := checked_rows i
  by_cases hsplit : splitRow i
  · rw [ite_eq_left hsplit] at checked
    by_cases hpHi : p ≤ 22
    · have hpHi' : (p : ℝ) ≤ 22 := by exact_mod_cast hpHi
      refine ⟨3 / 22, 3 / 11, uniformOrders, 0, 1, by norm_num, ?_, ?_,
        checked.2.1, by norm_num, checked.2.2⟩
      · push_cast
        exact div_le_div_of_nonneg_left (by norm_num) hpPos hpHi'
      · push_cast
        exact hhHi
    · have hpHi' : (22 : ℝ) ≤ p := by exact_mod_cast (by omega : 22 ≤ p)
      refine ⟨0, 3 / 22, uniformOrders, 0, 1, by norm_num, ?_, ?_,
        checked.1.1, by norm_num, checked.1.2⟩
      · push_cast
        exact hhLo
      · push_cast
        exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpHi'
  · rw [ite_eq_right hsplit] at checked
    refine ⟨0, 3 / 11, uniformOrders, 0, 1, by norm_num, ?_, ?_,
      checked.1, by norm_num, checked.2⟩
    · push_cast
      exact hhLo
    · push_cast
      exact hhHi

end RefinedBMV.PositiveCenter.CompactShortQuadratureCover
