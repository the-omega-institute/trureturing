/- GID: D5/S3/Observer/Hankel/RankOneInfiniteHorizonRisk
   generality: G
   mirror-B: D5/B/S3/Observer/Hankel/RankOneInfiniteHorizonRisk
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Stable rank-one responses have all-future minimax prediction risk one half. -/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.ENNReal.Real
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk

open Filter
open scoped ENNReal Topology

/-- The observations include both endpoints of the finite window. -/
abbrev Data (T : ℕ) := Fin (T + 1) → ℝ

/-- An arbitrary deterministic estimator returns the entire future sequence. -/
abbrev Estimator (T : ℕ) := Data T → {n : ℕ // T ≤ n} → ℝ

/-- Pointwise bounded observation errors, with no probability law. -/
def Compatible (T : ℕ) (η a : ℝ) (y : Data T) : Prop :=
  ∀ k, |y k - a ^ k.val| ≤ η

/-- The supremum ranges jointly over stable systems, legal data, and all future times. -/
def risk (T : ℕ) (η : ℝ) (Ψ : Estimator T) : ℝ≥0∞ :=
  ⨆ a : Set.Ioo (0 : ℝ) 1, ⨆ y : Data T, ⨆ (_ : Compatible T η a.val y),
    ⨆ n : {n : ℕ // T ≤ n}, ENNReal.ofReal |Ψ y n - a.val ^ n.val|

/-- Optimal worst-case loss, allowing all deterministic sequence estimators. -/
def minimaxRisk (T : ℕ) (η : ℝ) : ℝ≥0∞ := ⨅ Ψ : Estimator T, risk T η Ψ

/-- Every nonempty finite Hankel section of the scalar impulse response. -/
def hankel (a : ℝ) (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun i j => a ^ (i.val + j.val)

/-- With positive bounded noise and a finite observation window, all-future
prediction has exact minimax error one half. Every parameter remains strictly
stable and has positive semidefinite Hankel sections of rank exactly one. -/
theorem rank_one_infinite_horizon_risk (T : ℕ) (_hT : 1 ≤ T)
    (η : ℝ) (hη : 0 < η) :
    minimaxRisk T η = ENNReal.ofReal (1 / 2 : ℝ) ∧
    (∀ a ∈ Set.Ioo (0 : ℝ) 1,
      Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0) ∧
      ∀ N, (hankel a N).PosSemidef ∧ (hankel a N).rank = 1) := by
  classical
  have near_one (m : ℕ) (δ : ℝ) (hδ : 0 < δ) :
      ∃ a ∈ Set.Ioo (0 : ℝ) 1, ∀ k ≤ m, |1 - a ^ k| ≤ δ := by
    let d : ℝ := min (1 / 2) (δ / (m + 1))
    have hm : 0 < (m : ℝ) + 1 := by positivity
    have hd : 0 < d := lt_min (by norm_num) (div_pos hδ hm)
    have hdhalf : d ≤ 1 / 2 := min_le_left _ _
    have hdm : ((m : ℝ) + 1) * d ≤ δ := by
      have := (le_div_iff₀ hm).mp (min_le_right (1 / 2 : ℝ) (δ / (m + 1)))
      simpa [d, mul_comm] using this
    refine ⟨1 - d, ⟨by linarith, by linarith⟩, ?_⟩
    intro k hk
    have ha0 : 0 ≤ 1 - d := by linarith
    have ha1 : 1 - d ≤ 1 := by linarith
    rw [abs_of_nonneg (sub_nonneg.mpr (pow_le_one₀ ha0 ha1))]
    have hb := one_add_mul_sub_le_pow (show (-1 : ℝ) ≤ 1 - d by linarith) k
    have hkm : (k : ℝ) ≤ m := by exact_mod_cast hk
    have hkd := mul_le_mul_of_nonneg_right hkm hd.le
    nlinarith
  have lower (Ψ : Estimator T) : ENNReal.ofReal (1 / 2 : ℝ) ≤ risk T η Ψ := by
    by_contra h
    obtain ⟨r, hr0, hrisk, hrhalf⟩ :=
      ENNReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge h)
    have hr : r < 1 / 2 := (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mp hrhalf
    let ε : ℝ := (1 - 2 * r) / 4
    have hε : 0 < ε := by dsimp [ε]; linarith
    obtain ⟨b, hb, hbdata⟩ := near_one T η hη
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε hb.2
    let n : {n : ℕ // T ≤ n} := ⟨m + T, Nat.le_add_left T m⟩
    have hbn : b ^ n.val < ε := by
      calc
        b ^ n.val = b ^ m * b ^ T := by simp [n, pow_add]
        _ ≤ b ^ m * 1 := mul_le_mul_of_nonneg_left
          (pow_le_one₀ hb.1.le hb.2.le) (pow_nonneg hb.1.le _)
        _ < ε := by simpa using hm
    obtain ⟨a, ha, hadata⟩ := near_one n.val (min η ε) (lt_min hη hε)
    let y : Data T := fun _ => 1
    have hyb : Compatible T η b y := by
      intro k
      exact hbdata k.val (Nat.le_of_lt_succ k.isLt)
    have hya : Compatible T η a y := by
      intro k
      exact (hadata k.val ((Nat.le_of_lt_succ k.isLt).trans n.property)).trans
        (min_le_left _ _)
    have error_le (c : Set.Ioo (0 : ℝ) 1) (hy : Compatible T η c.val y) :
        |Ψ y n - c.val ^ n.val| ≤ r := by
      apply (ENNReal.ofReal_le_ofReal_iff hr0).mp
      have hc : ENNReal.ofReal |Ψ y n - c.val ^ n.val| ≤ risk T η Ψ := by
        unfold risk
        exact le_iSup_of_le c (le_iSup_of_le y (le_iSup_of_le hy
          (le_iSup_of_le n le_rfl)))
      exact hc.trans hrisk.le
    have hea := error_le ⟨a, ha⟩ hya
    have heb := error_le ⟨b, hb⟩ hyb
    have han := (hadata n.val le_rfl).trans (min_le_right η ε)
    have hdiff := abs_sub_le (a ^ n.val) (Ψ y n) (b ^ n.val)
    rw [abs_sub_comm (a ^ n.val) (Ψ y n)] at hdiff
    have habs := le_abs_self (a ^ n.val - b ^ n.val)
    have han' := le_abs_self (1 - a ^ n.val)
    dsimp [ε] at *
    linarith
  constructor
  · apply le_antisymm
    · refine (iInf_le (fun Ψ => risk T η Ψ) (fun _ _ => 1 / 2)).trans ?_
      refine iSup_le fun a => iSup_le fun y => iSup_le fun hy => iSup_le fun n => ?_
      apply ENNReal.ofReal_le_ofReal
      have hp0 := pow_nonneg a.property.1.le n.val
      have hp1 := pow_le_one₀ a.property.1.le a.property.2.le (n := n.val)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · exact le_iInf lower
  · intro a ha
    refine ⟨tendsto_pow_atTop_nhds_zero_of_lt_one ha.1.le ha.2, ?_⟩
    intro N
    have hfactor : hankel a N = Matrix.vecMulVec
        (fun i : Fin (N + 1) => a ^ i.val) (fun i : Fin (N + 1) => a ^ i.val) := by
      ext i j
      exact pow_add _ _ _
    constructor
    · simpa only [hfactor, star_trivial] using
        Matrix.posSemidef_vecMulVec_self_star (fun i : Fin (N + 1) => a ^ i.val)
    · apply le_antisymm
      · rw [hfactor]
        exact Matrix.rank_vecMulVec_le _ _
      · have hs := Matrix.rank_submatrix_le (hankel a N)
          (fun _ : Fin 1 => (0 : Fin (N + 1))) (fun _ : Fin 1 => (0 : Fin (N + 1)))
        have he : (hankel a N).submatrix (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0) = 1 := by
          ext i j
          simp [hankel, Matrix.submatrix, Matrix.one_apply, Subsingleton.elim i j]
        simpa only [he, Matrix.rank_one, Fintype.card_fin] using hs

#print axioms rank_one_infinite_horizon_risk

end D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk
