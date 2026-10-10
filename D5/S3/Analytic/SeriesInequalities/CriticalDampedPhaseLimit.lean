/- GID: D5/S3/Analytic/SeriesInequalities/CriticalDampedPhaseLimit
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/CriticalDampedPhaseLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive shrinking damping with a finite phase ratio gives the exact full-array distance limit. -/

import D5.S3.Analytic.SeriesInequalities.NegativeBoundaryEnvelope
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

open scoped BigOperators ENNReal
open Filter Set Topology

namespace D5.S3.Analytic.SeriesInequalities.CriticalDampedPhaseLimit

open FiniteSourceCriticalTail FiniteSourceClosure NegativeBoundaryEnvelope

noncomputable def sampledSup (w : ℕ → ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  sSup (Set.range fun n : ℕ => w n * f (((n : ℝ) + 1) * t))

/-- The weights converge at infinity while the sampling mesh shrinks to zero.
The conclusion retains all lattice sites in the supremum. -/
private theorem shrinking_mesh_sup_limit
    (f : ℝ → ℝ) (hf : Continuous f) (hf0 : f 0 = 0)
    (hfpos : ∀ s, 0 ≤ s → 0 ≤ f s)
    (hfbd : BddAbove (f '' Ici 0))
    (w : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hw : ∀ n, c ≤ w n) (hwlim : Tendsto w atTop (𝓝 c))
    (t : ℕ → ℝ) (ht : ∀ j, 0 < t j) (htlim : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun j => sampledSup w f (t j)) atTop (𝓝 (c * sSup (f '' Ici 0))) := by
  let G := sSup (f '' Ici 0)
  have hne : (f '' Ici 0).Nonempty :=
    ⟨f 0, mem_image_of_mem f (mem_Ici.mpr le_rfl)⟩
  have hfle (s : ℝ) (hs : 0 ≤ s) : f s ≤ G :=
    le_csSup hfbd ⟨s, hs, rfl⟩
  have hG : 0 ≤ G := by simpa [hf0] using hfle 0 le_rfl
  obtain ⟨W, hW⟩ := hwlim.bddAbove_range
  have hwW (n : ℕ) : w n ≤ W := hW (mem_range_self n)
  have hW0 : 0 ≤ W := hc.le.trans ((hw 0).trans (hwW 0))
  have hsbdd (j : ℕ) : BddAbove
      (range fun n : ℕ => w n * f (((n : ℝ) + 1) * t j)) := by
    refine ⟨W * G, ?_⟩
    rintro x ⟨n, rfl⟩
    have hs : 0 ≤ ((n : ℝ) + 1) * t j := mul_nonneg (by positivity) (ht j).le
    exact mul_le_mul (hwW n) (hfle _ hs) (hfpos _ hs) hW0
  have hsle (j n : ℕ) : w n * f (((n : ℝ) + 1) * t j) ≤ sampledSup w f (t j) :=
    le_csSup (hsbdd j) (mem_range_self n)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have haG : a / c < G := (div_lt_iff₀ hc).mpr (by simpa [mul_comm] using ha)
    obtain ⟨y, ⟨s, hs, rfl⟩, has⟩ := exists_lt_of_lt_csSup hne haG
    have hac : a < c * f s := by
      simpa [mul_comm] using (div_lt_iff₀ hc).mp has
    let n : ℕ → ℕ := fun j => ⌊s / t j⌋₊
    have hlower (j : ℕ) : s ≤ ((n j : ℝ) + 1) * t j := by
      have hh := Nat.lt_floor_add_one (s / t j)
      have hh' := (div_lt_iff₀ (ht j)).mp hh
      exact hh'.le
    have hupper (j : ℕ) : ((n j : ℝ) + 1) * t j ≤ s + t j := by
      have hh := Nat.floor_le (div_nonneg hs (ht j).le)
      have hh' := (le_div_iff₀ (ht j)).mp hh
      dsimp [n]
      nlinarith
    have hsample : Tendsto (fun j => ((n j : ℝ) + 1) * t j) atTop (𝓝 s) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds (by simpa using tendsto_const_nhds.add htlim)
      · exact hlower
      · exact hupper
    have hcf : Tendsto (fun j => c * f (((n j : ℝ) + 1) * t j))
        atTop (𝓝 (c * f s)) := (hf.continuousAt.tendsto.comp hsample).const_mul c
    filter_upwards [(tendsto_order.mp hcf).1 a hac] with j hj
    apply hj.trans_le
    apply le_trans _ (hsle j (n j))
    exact mul_le_mul_of_nonneg_right (hw _) (hfpos _ (mul_nonneg (by positivity) (ht j).le))
  · intro b hb
    let d := (c * G + b) / 2
    have hd : c * G < d := by dsimp [d]; linarith
    have hdb : d < b := by dsimp [d]; linarith
    have hd0 : 0 < d := lt_of_le_of_lt (mul_nonneg hc.le hG) hd
    let e := (d - c * G) / (G + 1)
    have he : 0 < e := div_pos (sub_pos.mpr hd) (by positivity)
    have htailbd : (c + e) * G ≤ d := by
      have hh : e * (G + 1) = d - c * G := by
        dsimp [e]
        exact div_mul_cancel₀ _ (by positivity)
      nlinarith
    obtain ⟨M, hM⟩ := eventually_atTop.mp ((tendsto_order.mp hwlim).2 (c + e) (by linarith))
    have hhead (n : ℕ) : ∀ᶠ j in atTop, w n * f (((n : ℝ) + 1) * t j) ≤ d := by
      have harg : Tendsto (fun j => ((n : ℝ) + 1) * t j) atTop (𝓝 0) := by
        simpa using htlim.const_mul ((n : ℝ) + 1)
      have hh := (hf.continuousAt.tendsto.comp harg).const_mul (w n)
      simp only [hf0, mul_zero] at hh
      filter_upwards [(tendsto_order.mp hh).2 d hd0] with j hj using hj.le
    have hall : ∀ᶠ j in atTop, ∀ n ∈ Finset.range M,
        w n * f (((n : ℝ) + 1) * t j) ≤ d :=
      (Filter.eventually_all_finset (Finset.range M)).mpr (fun n _ => hhead n)
    filter_upwards [hall] with j hj
    apply lt_of_le_of_lt _ hdb
    apply csSup_le (range_nonempty _)
    rintro x ⟨n, rfl⟩
    by_cases hn : n < M
    · exact hj n (Finset.mem_range.mpr hn)
    · have hs : 0 ≤ ((n : ℝ) + 1) * t j := mul_nonneg (by positivity) (ht j).le
      calc
        w n * f (((n : ℝ) + 1) * t j) ≤ (c + e) * G :=
          mul_le_mul (hM n (by omega)).le (hfle _ hs) (hfpos _ hs) (by positivity)
        _ ≤ d := htailbd



noncomputable def spiral (k s : ℝ) : ℝ :=
  ‖1 - (Real.exp (-s) : ℂ) * Complex.exp ((k * s : ℝ) * Complex.I)‖

noncomputable def envelope (k : ℝ) : ℝ := sSup (spiral k '' Ici 0)

private theorem spiral_bound (k s : ℝ) (hs : 0 ≤ s) : spiral k s ≤ 2 := by
  have h := norm_sub_le (1 : ℂ)
    ((Real.exp (-s) : ℂ) * Complex.exp ((k * s : ℝ) * Complex.I))
  simp only [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Complex.norm_exp_ofReal_mul_I, mul_one] at h
  have he : Real.exp (-s) ≤ 1 := by
    simpa using Real.exp_le_exp.mpr (show -s ≤ 0 by linarith)
  exact h.trans (by linarith)

private theorem spiral_parameter_bound (k l s : ℝ) (hs : 0 ≤ s) :
    |spiral k s - spiral l s| ≤ Real.exp (-1) * |k - l| := by
  have hfactor : Complex.exp ((k * s : ℝ) * Complex.I) -
      Complex.exp ((l * s : ℝ) * Complex.I) =
      Complex.exp ((l * s : ℝ) * Complex.I) *
        (Complex.exp (((k - l) * s : ℝ) * Complex.I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    have he : ((l * s : ℝ) : ℂ) * Complex.I +
        (((k - l) * s : ℝ) : ℂ) * Complex.I = ((k * s : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [he]
  have hchar : ‖Complex.exp ((k * s : ℝ) * Complex.I) -
      Complex.exp ((l * s : ℝ) * Complex.I)‖ ≤ |k - l| * s := by
    rw [hfactor, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := (k - l) * s)
    simpa [mul_comm, Real.norm_eq_abs, abs_mul, abs_of_nonneg hs] using h
  have hnorm := abs_norm_sub_norm_le
    (1 - (Real.exp (-s) : ℂ) * Complex.exp ((k * s : ℝ) * Complex.I))
    (1 - (Real.exp (-s) : ℂ) * Complex.exp ((l * s : ℝ) * Complex.I))
  have hdist : ‖(1 - (Real.exp (-s) : ℂ) * Complex.exp ((k * s : ℝ) * Complex.I)) -
      (1 - (Real.exp (-s) : ℂ) * Complex.exp ((l * s : ℝ) * Complex.I))‖ =
      Real.exp (-s) * ‖Complex.exp ((k * s : ℝ) * Complex.I) -
        Complex.exp ((l * s : ℝ) * Complex.I)‖ := by
    have heq : (1 - (Real.exp (-s) : ℂ) * Complex.exp ((k * s : ℝ) * Complex.I)) -
        (1 - (Real.exp (-s) : ℂ) * Complex.exp ((l * s : ℝ) * Complex.I)) =
        -(Real.exp (-s) : ℂ) * (Complex.exp ((k * s : ℝ) * Complex.I) -
          Complex.exp ((l * s : ℝ) * Complex.I)) := by ring
    rw [heq, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  calc
    |spiral k s - spiral l s| ≤ Real.exp (-s) *
        ‖Complex.exp ((k * s : ℝ) * Complex.I) -
          Complex.exp ((l * s : ℝ) * Complex.I)‖ := by
            rw [hdist] at hnorm
            exact hnorm
    _ ≤ Real.exp (-s) * (|k - l| * s) :=
      mul_le_mul_of_nonneg_left hchar (Real.exp_pos _).le
    _ = (s * Real.exp (-s)) * |k - l| := by ring
    _ ≤ Real.exp (-1) * |k - l| :=
      mul_le_mul_of_nonneg_right (Real.mul_exp_neg_le_exp_neg_one s) (abs_nonneg _)

/-- The infinite weighted supremum, with an arbitrary limiting
ratio and arbitrary positive sampling meshes tending to zero. -/
private theorem spiral_finite_ratio_limit
    (c b ρ k : ℝ) (hc : 0 < c) (hb : 0 ≤ b) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (t v : ℕ → ℝ) (ht : ∀ j, 0 < t j)
    (htlim : Tendsto t atTop (𝓝 0)) (hvlim : Tendsto v atTop (𝓝 k)) :
    Tendsto (fun j => sampledSup (fun n => c + b * (ρ ^ 2) ^ n)
      (spiral (v j)) (t j)) atTop (𝓝 (c * envelope k)) := by
  let w : ℕ → ℝ := fun n => c + b * (ρ ^ 2) ^ n
  have hwc (n : ℕ) : c ≤ w n := by
    exact le_add_of_nonneg_right (mul_nonneg hb (pow_nonneg (sq_nonneg ρ) n))
  have hW (n : ℕ) : w n ≤ c + b := by
    have hp := pow_le_one₀ (sq_nonneg ρ) (show ρ ^ 2 ≤ 1 by nlinarith) (n := n)
    dsimp [w]
    nlinarith
  have hwlim : Tendsto w atTop (𝓝 c) := by
    have hg := tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg ρ)
      (show ρ ^ 2 < 1 by nlinarith)
    simpa [w] using (hg.const_mul b).const_add c
  have hf : Continuous (spiral k) := by unfold spiral; fun_prop
  have hf0 : spiral k 0 = 0 := by simp [spiral]
  have hfbd (q : ℝ) : BddAbove (spiral q '' Ici 0) := by
    refine ⟨2, ?_⟩
    rintro y ⟨s, hs, rfl⟩
    exact spiral_bound q s hs
  have hbase : Tendsto (fun j => sampledSup w (spiral k) (t j))
      atTop (𝓝 (c * envelope k)) :=
    shrinking_mesh_sup_limit (spiral k) hf hf0 (fun s _ => norm_nonneg _)
      (hfbd k) w c hc hwc hwlim t ht htlim
  have hbd (q : ℝ) (j : ℕ) : BddAbove
      (range fun n : ℕ => w n * spiral q (((n : ℝ) + 1) * t j)) := by
    refine ⟨(c + b) * 2, ?_⟩
    rintro y ⟨n, rfl⟩
    exact mul_le_mul (hW n)
      (spiral_bound q _ (mul_nonneg (by positivity) (ht j).le))
      (norm_nonneg _) (by positivity)
  let e : ℕ → ℝ := fun j => (c + b) * (Real.exp (-1) * |v j - k|)
  have helim : Tendsto e atTop (𝓝 0) := by
    have hh := ((hvlim.sub_const k).abs.const_mul (Real.exp (-1))).const_mul (c + b)
    simpa [e] using hh
  have hdiff (j n : ℕ) :
      |w n * spiral (v j) (((n : ℝ) + 1) * t j) -
        w n * spiral k (((n : ℝ) + 1) * t j)| ≤ e j := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (hc.le.trans (hwc n))]
    exact mul_le_mul (hW n) (spiral_parameter_bound _ _ _ (mul_nonneg (by positivity) (ht j).le))
      (abs_nonneg _) (by positivity)
  have hupper (j : ℕ) : sampledSup w (spiral (v j)) (t j) ≤
      sampledSup w (spiral k) (t j) + e j := by
    apply csSup_le (range_nonempty _)
    rintro y ⟨n, rfl⟩
    have hterm := le_csSup (hbd k j) (mem_range_self n)
    have hdiff' := (abs_le.mp (hdiff j n)).2
    change _ ≤ sampledSup w (spiral k) (t j) at hterm
    linarith
  have hlower (j : ℕ) : sampledSup w (spiral k) (t j) - e j ≤
      sampledSup w (spiral (v j)) (t j) := by
    suffices sampledSup w (spiral k) (t j) ≤ sampledSup w (spiral (v j)) (t j) + e j by linarith
    apply csSup_le (range_nonempty _)
    rintro y ⟨n, rfl⟩
    have hterm := le_csSup (hbd (v j) j) (mem_range_self n)
    have hdiff' := (abs_le.mp (hdiff j n)).1
    change _ ≤ sampledSup w (spiral (v j)) (t j) at hterm
    linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa using hbase.sub helim) (by simpa using hbase.add helim) hlower hupper


/-- The weighted damped character supremum. -/
noncomputable def phaseReadout (c b ρ t θ : ℝ) : ℝ :=
  sSup (range fun n : ℕ => (c + b * ρ ^ (2 * n)) *
    ‖1 - Complex.exp ((-(((n : ℝ) + 1) * t) : ℝ) +
      ((((n : ℝ) + 1) * θ : ℝ) : ℂ) * Complex.I)‖)

/-- The scalar full-layer limit, including zero limiting ratio. -/
private theorem damping_phase_sup_limit
    (c b ρ k : ℝ) (hc : 0 < c) (hb : 0 ≤ b) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (t θ : ℕ → ℝ) (ht : ∀ j, 0 < t j)
    (htlim : Tendsto t atTop (𝓝 0))
    (hratio : Tendsto (fun j => θ j / t j) atTop (𝓝 k)) :
    Tendsto (fun j => phaseReadout c b ρ (t j) (θ j)) atTop (𝓝 (c * envelope k)) := by
  have h := spiral_finite_ratio_limit c b ρ k hc hb hρ hρ1
    t (fun j => θ j / t j) ht htlim hratio
  convert h using 1
  funext j
  unfold phaseReadout sampledSup spiral
  apply congrArg sSup
  apply congrArg Set.range
  funext n
  have he : θ j / t j * (((n : ℝ) + 1) * t j) = ((n : ℝ) + 1) * θ j := by
    field_simp [(ht j).ne']
  simp only [pow_mul, Complex.ofReal_exp, ← Complex.exp_add, he]


end D5.S3.Analytic.SeriesInequalities.CriticalDampedPhaseLimit
