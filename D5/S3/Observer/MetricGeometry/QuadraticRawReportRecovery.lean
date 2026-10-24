/- GID: D5/S3/Observer/MetricGeometry/QuadraticRawReportRecovery
   generality: I
   mirror-B: D5/B/S3/Observer/MetricGeometry/QuadraticRawReportRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Jointly bounded quadratic reports admit exact recovery through finite common worlds. -/

import D5.S3.Analytic.OptimalRecovery.PointwiseMinimaxUpper
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! Deterministic recovery in the original six-coordinate quadratic report experiment. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace D5.S3.Observer.MetricGeometry.QuadraticRawReportRecovery

/-- The original six sampling positions. -/
def positions : Finset ℕ := {0, 1, 2, 8, 9, 10}

/-- A coordinate is its original natural sampling position. -/
abbrev Index := {i : ℕ // i ∈ positions}

/-- A preselected subset of the original positions, including the empty subset. -/
abbrev Design := Finset Index

/-- Arbitrary real raw reports on the selected coordinates. -/
abbrev Reports (J : Design) := J → ℝ

/-- The known signed prior, whose length is H. -/
def prior (H s : ℝ) : Set ℝ := Icc (-5 + (s - H) / 2) (-5 + (s + H) / 2)

/-- One world has one finite gain and offset, and a joint six-coordinate noise vector. -/
structure World where
  tau : ℝ
  gain : ℝ
  zero : ℝ
  noise : Index → ℝ

/-- Every coordinate of the original noise vector obeys the same cube constraint. -/
def Legal (m ε H s : ℝ) (w : World) : Prop :=
  w.tau ∈ prior H s ∧ m ≤ w.gain ∧ ∀ i, |w.noise i| ≤ ε

/-- A common quadratic calibration on all original coordinates. -/
def signature (t A B : ℝ) (i : Index) : ℝ := A * ((i.val : ℝ) + t) ^ 2 + B

/-- Projection changes only which original raw coordinates are observed. -/
def observe (J : Design) (w : World) : Reports J :=
  fun i => signature w.tau w.gain w.zero i.val + w.noise i.val

/-- All total deterministic recovery functions are allowed. -/
abbrev Rule (J : Design) := Reports J → ℝ

/-- A rule may have infinite worst-case absolute error. -/
def risk (m ε H s : ℝ) (J : Design) (δ : Rule J) : ℝ≥0∞ :=
  ⨆ w : World, ⨆ (_ : Legal m ε H s w), ENNReal.ofReal |δ (observe J w) - w.tau|

/-- The infimum ranges over all total rules, with no regularity restriction. -/
def minimaxRisk (m ε H s : ℝ) (J : Design) : ℝ≥0∞ :=
  ⨅ δ : Rule J, risk m ε H s J δ

/-- Compatibility uses actual legal worlds and the projected raw report. -/
def compatible (m ε H s : ℝ) (J : Design) (y : Reports J) : Set ℝ :=
  {t | ∃ w : World, Legal m ε H s w ∧ w.tau = t ∧ observe J w = y}

/-- The compatible-set midpoint, extended to every impossible report. -/
def midpointRule (m ε H s : ℝ) (J : Design) : Rule J := by
  classical
  exact fun y => if (compatible m ε H s J y).Nonempty then
    (sInf (compatible m ε H s J y) + sSup (compatible m ε H s J y)) / 2
    else -5 + s / 2

/-- Two independent finite calibrations are close on every selected raw coordinate. -/
def PairCompatible (m ε : ℝ) (J : Design) (u v : ℝ) : Prop :=
  ∃ A A' B B' : ℝ, m ≤ A ∧ m ≤ A' ∧
    ∀ i ∈ J, |signature u A B i - signature v A' B' i| ≤ 2 * ε

/-- The original joint strip constraints after eliminating one common constant. -/
def Strips (ε : ℝ) (J : Design) (U V : ℝ) : Prop :=
  ∀ i ∈ J, ∀ j ∈ J,
    (U * (i.val : ℝ) ^ 2 + V * i.val) -
      (U * (j.val : ℝ) ^ 2 + V * j.val) ≤ 4 * ε

/-- A supremum of finite common-world half-gaps; no attainment is asserted. -/
def ambiguityRadius (m ε H s : ℝ) (J : Design) : ℝ≥0∞ :=
  ⨆ u : ℝ, ⨆ v : ℝ, ⨆ (_ : u ∈ prior H s), ⨆ (_ : v ∈ prior H s),
    ⨆ (_ : PairCompatible m ε J u v), ENNReal.ofReal (|u - v| / 2)

/-- The residual-coordinate description is exactly the projected original cube. -/
theorem compatible_iff (m ε H s : ℝ) (hε : 0 ≤ ε) (J : Design)
    (y : Reports J) (t : ℝ) :
    (∃ w : World, Legal m ε H s w ∧ w.tau = t ∧ observe J w = y) ↔ t ∈ prior H s ∧
      ∃ A B : ℝ, m ≤ A ∧ ∀ i : J, |y i - signature t A B i.val| ≤ ε := by
  classical
  constructor
  · rintro ⟨w, hw, rfl, rfl⟩
    exact ⟨hw.1, w.gain, w.zero, hw.2.1, by simpa [observe] using fun i : J => hw.2.2 i.val⟩
  · rintro ⟨ht, A, B, hA, hy⟩
    let w : World := ⟨t, A, B, fun i => if hi : i ∈ J then
      y ⟨i, hi⟩ - signature t A B i else 0⟩
    refine ⟨w, ⟨ht, hA, ?_⟩, rfl, ?_⟩
    · intro i
      dsimp [w]
      split_ifs with hi
      · exact hy ⟨i, hi⟩
      · simpa using hε
    · funext i
      simp [observe, w, i.property]

/-- Close finite signatures yield one common raw report with two legal full noise vectors. -/
theorem common_report_iff (m ε H s : ℝ) (hε : 0 ≤ ε) (J : Design) (u v : ℝ) :
    (∃ w w' : World, Legal m ε H s w ∧ Legal m ε H s w' ∧
      w.tau = u ∧ w'.tau = v ∧ observe J w = observe J w') ↔
      u ∈ prior H s ∧ v ∈ prior H s ∧ PairCompatible m ε J u v := by
  classical
  constructor
  · rintro ⟨w, w', hw, hw', rfl, rfl, he⟩
    refine ⟨hw.1, hw'.1, w.gain, w'.gain, w.zero, w'.zero, hw.2.1, hw'.2.1, ?_⟩
    intro i hi
    have hh := congrFun he ⟨i, hi⟩
    have hn := abs_sub_le (w'.noise i) 0 (w.noise i)
    simp only [sub_zero, zero_sub, abs_neg] at hn
    have hid : signature w.tau w.gain w.zero i - signature w'.tau w'.gain w'.zero i =
        w'.noise i - w.noise i := by change _ + _ = _ + _ at hh; linarith
    rw [hid]
    exact hn.trans (by linarith [hw.2.2 i, hw'.2.2 i])
  · rintro ⟨hu, hv, A, A', B, B', hA, hA', hd⟩
    let y : Reports J := fun i => (signature u A B i.val + signature v A' B' i.val) / 2
    have hyu : u ∈ compatible m ε H s J y := by
      apply (compatible_iff m ε H s hε J y u).2
      refine ⟨hu, A, B, hA, ?_⟩
      intro i
      have hh := abs_le.mp (hd i.val i.property)
      exact abs_le.mpr ⟨by dsimp [y]; linarith, by dsimp [y]; linarith⟩
    have hyv : v ∈ compatible m ε H s J y := by
      apply (compatible_iff m ε H s hε J y v).2
      refine ⟨hv, A', B', hA', ?_⟩
      intro i
      have hh := abs_le.mp (hd i.val i.property)
      exact abs_le.mpr ⟨by dsimp [y]; linarith, by dsimp [y]; linarith⟩
    obtain ⟨w, hw, hwu, hyw⟩ := hyu
    obtain ⟨w', hw', hwv, hyw'⟩ := hyv
    exact ⟨w, w', hw, hw', hwu, hwv, hyw.trans hyw'.symm⟩

/-- Eliminating the common offset keeps the joint strip constraints exactly. -/
theorem pairCompatible_iff_strips (m ε : ℝ) (J : Design) (u v : ℝ) :
    (∃ A A' B B' : ℝ, m ≤ A ∧ m ≤ A' ∧
      ∀ i ∈ J, |signature u A B i - signature v A' B' i| ≤ 2 * ε) ↔
      ∃ A A' : ℝ, m ≤ A ∧ m ≤ A' ∧
      Strips ε J (A - A') (2 * (A * u - A' * v)) := by
  constructor
  · rintro ⟨A, A', B, B', hA, hA', hd⟩
    refine ⟨A, A', hA, hA', ?_⟩
    intro i hi j hj
    have hi' := abs_le.mp (hd i hi)
    have hj' := abs_le.mp (hd j hj)
    dsimp [signature] at hi' hj'
    nlinarith only [hi'.2, hj'.1]
  · rintro ⟨A, A', hA, hA', hd⟩
    classical
    let q : Index → ℝ := fun i => (A - A') * (i.val : ℝ) ^ 2 +
      2 * (A * u - A' * v) * i.val
    let S : Set ℝ := q '' (J : Set Index)
    let C : ℝ := -(sInf S + sSup S) / 2
    refine ⟨A, A', C - A * u ^ 2 + A' * v ^ 2, 0, hA, hA', ?_⟩
    intro i hi
    have hx : q i ∈ S := ⟨i, hi, rfl⟩
    have hfinite : S.Finite := J.finite_toSet.image q
    have hh := D5.S3.Analytic.OptimalRecovery.PointwiseMinimaxUpper.midpoint_error
      S (q i) (2 * ε) hx hfinite.bddBelow hfinite.bddAbove (by
        rintro a ⟨j, hj, rfl⟩ b ⟨k, hk, rfl⟩
        apply abs_le.mpr
        constructor
        · have := hd k hk j hj; dsimp [q]; linarith
        · have := hd j hj k hk; dsimp [q]; linarith)
    have he : signature u A (C - A * u ^ 2 + A' * v ^ 2) i - signature v A' 0 i =
        -((sInf S + sSup S) / 2 - q i) := by dsimp [signature, C, q]; ring
    simpa only [he, abs_neg] using hh

private lemma gap_bound (H s u v : ℝ) (hu : u ∈ prior H s) (hv : v ∈ prior H s) :
    |u - v| ≤ H := by
  rcases hu with ⟨hu₁, hu₂⟩
  rcases hv with ⟨hv₁, hv₂⟩
  apply abs_le.mpr
  constructor <;> linarith

private lemma world_loss_le (m ε H s : ℝ) (J : Design) (δ : Rule J)
    (w : World) (hw : Legal m ε H s w) :
    ENNReal.ofReal |δ (observe J w) - w.tau| ≤ risk m ε H s J δ :=
  le_iSup_of_le w (le_iSup_of_le hw le_rfl)

private lemma pair_lower (m ε H s : ℝ) (hε : 0 ≤ ε) (J : Design)
    (u v : ℝ) (hu : u ∈ prior H s) (hv : v ∈ prior H s)
    (hp : PairCompatible m ε J u v) :
    ENNReal.ofReal (|u - v| / 2) ≤ minimaxRisk m ε H s J := by
  obtain ⟨w, w', hw, hw', hwu, hwv, he⟩ :=
    (common_report_iff m ε H s hε J u v).2 ⟨hu, hv, hp⟩
  apply le_iInf
  intro δ
  have htri : |u - v| ≤ |δ (observe J w) - u| + |δ (observe J w) - v| := by
    simpa only [abs_sub_comm u (δ (observe J w))] using abs_sub_le u (δ (observe J w)) v
  by_cases hb : |u - v| / 2 ≤ |δ (observe J w) - u|
  · exact (ENNReal.ofReal_le_ofReal hb).trans (hwu ▸ world_loss_le m ε H s J δ w hw)
  · have hb' : |u - v| / 2 ≤ |δ (observe J w') - v| := by rw [← he]; linarith
    exact (ENNReal.ofReal_le_ofReal hb').trans (hwv ▸ world_loss_le m ε H s J δ w' hw')

private lemma radius_prior_bound (m ε H s : ℝ) (J : Design) :
    ambiguityRadius m ε H s J ≤ ENNReal.ofReal (H / 2) := by
  refine iSup_le fun u => iSup_le fun v => iSup_le fun hu => iSup_le fun hv =>
    iSup_le fun _ => ENNReal.ofReal_le_ofReal ?_
  linarith [gap_bound H s u v hu hv]

/-- Raw deterministic minimax risk equals the supremum of finite common-world half-gaps.
The compatible-set midpoint attains it, and the original prior makes it finite. -/
theorem raw_minimax (m ε H s : ℝ) (hε : 0 ≤ ε) (J : Design) :
    minimaxRisk m ε H s J = ambiguityRadius m ε H s J ∧
    risk m ε H s J (midpointRule m ε H s J) = ambiguityRadius m ε H s J ∧
    minimaxRisk m ε H s J ≤ ENNReal.ofReal (H / 2) ∧
    minimaxRisk m ε H s J < ⊤ := by
  let r := ambiguityRadius m ε H s J
  have hr : r ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (radius_prior_bound m ε H s J)
  have hl : r ≤ minimaxRisk m ε H s J := by
    exact iSup_le fun u => iSup_le fun v => iSup_le fun hu => iSup_le fun hv =>
      iSup_le fun hp => pair_lower m ε H s hε J u v hu hv hp
  have hm : risk m ε H s J (midpointRule m ε H s J) ≤ r := by
    refine iSup_le fun w => iSup_le fun hw => ?_
    let S := compatible m ε H s J (observe J w)
    have hx : w.tau ∈ S := ⟨w, hw, rfl, rfl⟩
    have hsub : S ⊆ prior H s := by rintro x ⟨w', hw', rfl, _⟩; exact hw'.1
    have hb : BddBelow S := ⟨-5 + (s - H) / 2, fun x hx => (hsub hx).1⟩
    have ha : BddAbove S := ⟨-5 + (s + H) / 2, fun x hx => (hsub hx).2⟩
    rw [midpointRule, ite_eq_left ⟨w.tau, hx⟩]
    apply (ENNReal.ofReal_le_ofReal ?_).trans (ENNReal.ofReal_toReal hr).le
    apply D5.S3.Analytic.OptimalRecovery.PointwiseMinimaxUpper.midpoint_error
      S w.tau r.toReal hx hb ha
    intro a ha' b hb'
    obtain ⟨wa, hwa, hwatau, hway⟩ := ha'
    obtain ⟨wb, hwb, hwbtau, hwby⟩ := hb'
    have hp := (common_report_iff m ε H s hε J a b).1
      ⟨wa, wb, hwa, hwb, hwatau, hwbtau, hway.trans hwby.symm⟩
    have hh : ENNReal.ofReal (|a - b| / 2) ≤ r :=
      le_iSup_of_le a (le_iSup_of_le b (le_iSup_of_le hp.1
        (le_iSup_of_le hp.2.1 (le_iSup_of_le hp.2.2 le_rfl))))
    have := (ENNReal.ofReal_le_iff_le_toReal hr).mp hh
    linarith
  have hi : minimaxRisk m ε H s J ≤ risk m ε H s J (midpointRule m ε H s J) := iInf_le _ _
  have he : minimaxRisk m ε H s J = r := le_antisymm (hi.trans hm) hl
  exact ⟨he, le_antisymm hm (hl.trans hi), he ▸ radius_prior_bound m ε H s J,
    he ▸ lt_top_iff_ne_top.mpr hr⟩

/-- Any fixed coordinate projection can only increase the original minimax risk. -/
theorem projection_monotone (m ε H s : ℝ) (J K : Design) (hJK : J ⊆ K) :
    minimaxRisk m ε H s K ≤ minimaxRisk m ε H s J := by
  apply le_iInf
  intro δ
  let δ' : Rule K := fun y => δ (fun i => y ⟨i.val, hJK i.property⟩)
  apply (iInf_le _ δ').trans
  refine iSup_le fun w => iSup_le fun hw => ?_
  have he : δ' (observe K w) = δ (observe J w) := rfl
  rw [he]
  exact world_loss_le m ε H s J δ w hw

private lemma same_layer_pair (m ε : ℝ) (hm : 0 < m) (hε : 0 ≤ ε)
    (p q : Index) (u v : ℝ)
    (hlayer : (-(p.val + q.val : ℝ) / 2 < u ∧ -(p.val + q.val : ℝ) / 2 < v) ∨
      (u < -(p.val + q.val : ℝ) / 2 ∧ v < -(p.val + q.val : ℝ) / 2)) :
    PairCompatible m ε {p, q} u v := by
  let k : ℝ := -(p.val + q.val : ℝ) / 2
  have hu : u - k ≠ 0 := by rcases hlayer with h | h <;> dsimp [k] <;> linarith
  have hv : v - k ≠ 0 := by rcases hlayer with h | h <;> dsimp [k] <;> linarith
  let M := |u - k| + |v - k|
  let A := m * M / |u - k|
  let A' := m * M / |v - k|
  have hA : m ≤ A := by
    apply (le_div_iff₀ (abs_pos.mpr hu)).2
    dsimp [M]
    nlinarith [mul_nonneg hm.le (abs_nonneg (v - k))]
  have hA' : m ≤ A' := by
    apply (le_div_iff₀ (abs_pos.mpr hv)).2
    dsimp [M]
    nlinarith [mul_nonneg hm.le (abs_nonneg (u - k))]
  have hbalance : A * (u - k) = A' * (v - k) := by
    rcases hlayer with h | h
    · have hp : 0 < u - k := by dsimp [k]; linarith
      have hq : 0 < v - k := by dsimp [k]; linarith
      dsimp [A, A']
      rw [abs_of_pos hp, abs_of_pos hq]
      field_simp
    · have hp : u - k < 0 := by dsimp [k]; linarith
      have hq : v - k < 0 := by dsimp [k]; linarith
      dsimp [A, A']
      rw [abs_of_neg hp, abs_of_neg hq]
      field_simp
  apply (pairCompatible_iff_strips m ε {p, q} u v).2
  refine ⟨A, A', hA, hA', ?_⟩
  have hpq : (A - A') * (p.val : ℝ) ^ 2 + 2 * (A * u - A' * v) * p.val =
      (A - A') * (q.val : ℝ) ^ 2 + 2 * (A * u - A' * v) * q.val := by
    have hz : 2 * (A * u - A' * v) = -(A - A') * (p.val + q.val : ℝ) := by
      dsimp [k] at hbalance
      linarith
    rw [hz]
    ring
  intro i hi j hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
    simpa only [hpq, sub_self] using (show (0 : ℝ) ≤ 4 * ε by linarith)

private lemma two_report_approximation (m ε H s : ℝ) (hm : 0 < m) (hε : 0 ≤ ε)
    (p q : Index) (d : ℝ) (hd : 0 < d) (hdH : d < H / 2) :
    ∃ u v : ℝ, u ∈ prior H s ∧ v ∈ prior H s ∧
      PairCompatible m ε {p, q} u v ∧ |u - v| = d := by
  let a := -5 + (s - H) / 2
  let b := -5 + (s + H) / 2
  let k : ℝ := -(p.val + q.val : ℝ) / 2
  by_cases hk : k ≤ -5 + s / 2
  · refine ⟨b - d, b, ⟨?_, ?_⟩, ⟨?_, le_rfl⟩,
      same_layer_pair m ε hm hε p q (b - d) b (Or.inl ⟨?_, ?_⟩), ?_⟩
    · dsimp [a, b]; linarith
    · dsimp [b]; linarith
    · dsimp [a, b]; linarith
    · change k < b - d; dsimp [b]; linarith
    · change k < b; dsimp [b]; linarith
    · rw [show b - d - b = -d by ring, abs_neg, abs_of_pos hd]
  · refine ⟨a, a + d, ⟨le_rfl, ?_⟩, ⟨?_, ?_⟩,
      same_layer_pair m ε hm hε p q a (a + d) (Or.inr ⟨?_, ?_⟩), ?_⟩
    · dsimp [a, b]; linarith
    · dsimp [a]; linarith
    · dsimp [a, b]; linarith
    · change a < k; dsimp [a]; linarith
    · change a + d < k; dsimp [a]; linarith
    · rw [show a - (a + d) = -d by ring, abs_neg, abs_of_pos hd]

/-- Every at-most-two-report experiment loses at least a quarter of the prior width.
Each strict smaller half-gap has finite common-world witnesses; the endpoint is a supremum. -/
theorem few_reports_floor (m ε H s : ℝ) (hm : 0 < m) (hε : 0 ≤ ε)
    (hH : 0 < H) (J : Design) (hJ : J.card ≤ 2) :
    ENNReal.ofReal (H / 4) ≤ minimaxRisk m ε H s J := by
  classical
  have hcover : ∃ p q : Index, J ⊆ {p, q} := by
    by_cases hj : J.card = 2
    · obtain ⟨p, q, _, h⟩ := Finset.card_eq_two.mp hj
      exact ⟨p, q, h ▸ Finset.Subset.refl _⟩
    · let z : Index := ⟨0, by norm_num [positions]⟩
      haveI : Nonempty Index := ⟨z⟩
      obtain ⟨p, hp⟩ := Finset.card_le_one_iff_subset_singleton.mp (show J.card ≤ 1 by omega)
      exact ⟨p, p, by simpa using hp⟩
  obtain ⟨p, q, hsub⟩ := hcover
  apply le_trans ?_ (projection_monotone m ε H s J {p, q} hsub)
  by_contra hn
  obtain ⟨r, hr0, hrisk, hrH⟩ := ENNReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hn)
  have hrH' : r < H / 4 := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hrH
  let d := r + H / 4
  have hd : 0 < d := by dsimp [d]; linarith
  obtain ⟨u, v, hu, hv, hp, hgap⟩ :=
    two_report_approximation m ε H s hm hε p q d hd (by dsimp [d]; linarith)
  have hlow : ENNReal.ofReal (|u - v| / 2) ≤ minimaxRisk m ε H s {p, q} := by
    rw [(raw_minimax m ε H s hε {p, q}).1]
    exact le_iSup_of_le u (le_iSup_of_le v (le_iSup_of_le hu
      (le_iSup_of_le hv (le_iSup_of_le hp le_rfl))))
  rw [hgap] at hlow
  have hlt : ENNReal.ofReal r < ENNReal.ofReal (d / 2) :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by dsimp [d]; linarith)
  exact (not_lt_of_ge hlow) (hrisk.trans hlt)

end D5.S3.Observer.MetricGeometry.QuadraticRawReportRecovery
