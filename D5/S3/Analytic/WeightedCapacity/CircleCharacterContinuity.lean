/- GID: D5/S3/Analytic/WeightedCapacity/CircleCharacterContinuity
   generality: G
   mirror-B: D5/B/S3/Analytic/WeightedCapacity/CircleCharacterContinuity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Continuity of an arbitrary circle character at a finite capacity state forces finite weighted absolute mass. -/
import D5.S3.Analytic.WeightedCapacity.DyadicTailFilling
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false

namespace D5.S3.Analytic.WeightedCapacity.CircleCharacterContinuity

open DyadicTailFilling Set Filter
open scoped Topology BigOperators

/-- The representative of a circle point in the half-open interval from minus one half to one half. -/
noncomputable def centered (t : AddCircle (1 : ℝ)) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) (-(1 / 2 : ℝ)) t : ℝ)

/-- The circle character of a total circle row on finite capacity states. -/
noncomputable def charRow {A : ℕ → ℕ} (θ : ℕ → AddCircle (1 : ℝ)) (u : B A) :
    AddCircle (1 : ℝ) :=
  ∑ n ∈ u.property.toFinset, ((u.val n : ℕ) : ℤ) • θ n

/-- The extended sum of the capacities multiplied by the absolute centered representatives. -/
noncomputable def mass (A : ℕ → ℕ) (θ : ℕ → AddCircle (1 : ℝ)) : ENNReal :=
  ∑' n, ENNReal.ofReal ((A n : ℝ) * |centered (θ n)|)

/-- Continuity at any finite capacity state forces the weighted absolute mass to be finite. -/
theorem mass_finite_of_continuousAt (A : ℕ → ℕ) (θ : ℕ → AddCircle (1 : ℝ))
    (w : B A) (hw : ContinuousAt (charRow θ) w) : mass A θ < ⊤ := by
  classical
  let a : ℕ → ℝ := fun n => centered (θ n)
  have hac (n : ℕ) : (a n : AddCircle (1 : ℝ)) = θ n := AddCircle.coe_equivIco
  have han (n : ℕ) : ‖θ n‖ = |a n| := by
    rw [← hac n]
    apply (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num : (1 : ℝ) ≠ 0)).mpr
    have h := (AddCircle.equivIco (1 : ℝ) (-(1 / 2 : ℝ)) (θ n)).property
    change -(1 / 2 : ℝ) ≤ a n ∧ a n < -(1 / 2 : ℝ) + 1 at h
    rw [abs_le]
    norm_num
    constructor <;> linarith [h.1, h.2]
  have hsmall (r : ℝ) (hr : |r| ≤ 1 / 2) : ‖(r : AddCircle (1 : ℝ))‖ = |r| := by
    exact (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num : (1 : ℝ) ≠ 0)).mpr (by simpa using hr)
  have hsum (u : B A) (s : Finset ℕ) (hs : u.property.toFinset ⊆ s) :
      charRow θ u = ∑ n ∈ s, (u.val n : ℕ) • θ n := by
    unfold charRow
    simp only [natCast_zsmul]
    apply Finset.sum_subset hs
    intro n _ hn
    have hz : (u.val n : ℕ) = 0 := by simpa using hn
    simp [hz]
  have hphase (s : Finset ℕ) (b : ℕ → ℕ) :
      ((∑ n ∈ s, (b n : ℝ) * a n : ℝ) : AddCircle (1 : ℝ)) =
        ∑ n ∈ s, b n • θ n := by
    change (QuotientAddGroup.mk' _ : ℝ →+ AddCircle (1 : ℝ)) _ = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [← nsmul_eq_mul, map_nsmul]
    exact congrArg (fun t : AddCircle (1 : ℝ) => b n • t) (hac n)
  let δ : ℝ := 1 / 16
  have hd : 0 < δ := by norm_num [δ]
  have hδ : 2 * δ < 1 / 2 := by norm_num [δ]
  have hnb : {u : B A | dist (charRow θ u) (charRow θ w) < δ} ∈ 𝓝 w :=
    hw (Metric.ball_mem_nhds _ hd)
  obtain ⟨o, ho, hos⟩ := (mem_nhds_subtype _ _ _).mp hnb
  rw [nhds_pi, Filter.mem_pi'] at ho
  obtain ⟨I, t, ht, hto⟩ := ho
  let K := max (I.sup id + 1) (w.property.toFinset.sup id + 1)
  have hIK (n : ℕ) (hn : n ∈ I) : n < K := by
    have hle : n ≤ I.sup id := Finset.le_sup (f := id) hn
    dsimp [K]; omega
  have hwK (n : ℕ) (hn : K ≤ n) : (w.val n : ℕ) = 0 := by
    by_contra h
    have hm : n ∈ w.property.toFinset := by simpa using h
    have hle : n ≤ w.property.toFinset.sup id := Finset.le_sup (f := id) hm
    dsimp [K] at hn; omega
  have htail (s : Finset ℕ) (hs : ∀ n ∈ s, K ≤ n) (b : ℕ → ℕ)
      (hb : ∀ n ∈ s, b n ≤ A n) :
      ‖((∑ n ∈ s, (b n : ℝ) * a n : ℝ) : AddCircle (1 : ℝ))‖ < δ := by
    let y : X A := fun n => if hn : n ∈ s then ⟨b n, Nat.lt_succ_of_le (hb n hn)⟩
      else w.val n
    have hyfin : (Function.support (fun n => (y n : ℕ))).Finite := by
      apply (s.finite_toSet.union w.property).subset
      intro n hn
      by_cases hns : n ∈ s
      · exact Or.inl hns
      · right
        simpa [y, hns] using hn
    let u : B A := ⟨y, hyfin⟩
    have huo : u.val ∈ o := by
      apply hto
      intro n hn
      have hns : n ∉ s := fun h => (not_lt_of_ge (hs n h)) (hIK n hn)
      change y n ∈ t n
      simpa [y, hns] using mem_of_mem_nhds (ht n)
    have hud := hos huo
    change dist (charRow θ u) (charRow θ w) < δ at hud
    have huS : u.property.toFinset ⊆ s ∪ w.property.toFinset := by
      intro n hn
      have hn' : (y n : ℕ) ≠ 0 := by simpa [u] using hn
      by_cases hns : n ∈ s
      · exact Finset.mem_union_left _ hns
      · apply Finset.mem_union_right
        simpa [y, hns] using hn'
    have hdis : Disjoint s w.property.toFinset := by
      apply Finset.disjoint_left.mpr
      intro n hn hnw
      have hne : (w.val n : ℕ) ≠ 0 := by simpa using hnw
      exact hne (hwK n (hs n hn))
    have hchar : charRow θ u = (∑ n ∈ s, b n • θ n) + charRow θ w := by
      rw [hsum u _ huS, Finset.sum_union hdis, hsum w _ (Finset.Subset.refl _)]
      congr 1
      · apply Finset.sum_congr rfl
        intro n hn
        simp [u, y, hn]
      · apply Finset.sum_congr rfl
        intro n hn
        have hns : n ∉ s := fun h => Finset.disjoint_left.mp hdis h hn
        simp [u, y, hns]
    rw [hchar, dist_eq_norm, add_sub_cancel_right, ← hphase] at hud
    exact hud
  have hcoord (n : ℕ) (hn : K ≤ n) : (A n : ℝ) * |a n| < δ := by
    by_cases hA : A n = 0
    · simpa [hA] using hd
    have hunit := htail {n} (by simpa using hn) (fun _ => 1)
      (by simpa using Nat.one_le_iff_ne_zero.mpr hA)
    have ha : |a n| < δ := by simpa [hac, han] using hunit
    by_contra h
    have hex : ∃ k : ℕ, k ≤ A n ∧ δ ≤ (k : ℝ) * |a n| :=
      ⟨A n, le_rfl, le_of_not_gt h⟩
    let k := Nat.find hex
    have hkA : k ≤ A n := (Nat.find_spec hex).1
    have hkδ : δ ≤ (k : ℝ) * |a n| := (Nat.find_spec hex).2
    have hk0 : 0 < k := by
      by_contra h0
      have hk : k = 0 := by omega
      simp [hk] at hkδ
      linarith
    have hprev : ((k - 1 : ℕ) : ℝ) * |a n| < δ := by
      have hmin := Nat.find_min hex (show k - 1 < k by omega)
      exact lt_of_not_ge fun hh => hmin ⟨by omega, hh⟩
    have hkstep : (k : ℝ) = (k - 1 : ℕ) + 1 := by
      exact_mod_cast (show k = (k - 1) + 1 by omega)
    have hupper : (k : ℝ) * |a n| < 2 * δ := by rw [hkstep]; nlinarith
    have habs : |(k : ℝ) * a n| = (k : ℝ) * |a n| := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    have hb := htail {n} (by simpa using hn) (fun _ => k) (by simpa using hkA)
    simp only [Finset.sum_singleton] at hb
    rw [hsmall _ (by rw [habs]; exact le_of_lt (hupper.trans hδ)), habs] at hb
    exact (not_lt_of_ge hkδ) hb
  have hsign (s : Finset ℕ) (hs : ∀ n ∈ s, K ≤ n)
      (hsign : (∀ n ∈ s, 0 ≤ a n) ∨ (∀ n ∈ s, a n ≤ 0)) :
      ∑ n ∈ s, (A n : ℝ) * |a n| < δ := by
    induction s using Finset.induction_on with
    | empty => simpa using hd
    | @insert n s hn ih =>
      have hs' : ∀ j ∈ s, K ≤ j := fun j hj => hs j (Finset.mem_insert_of_mem hj)
      have hsign' : (∀ j ∈ s, 0 ≤ a j) ∨ (∀ j ∈ s, a j ≤ 0) :=
        hsign.imp (fun h j hj => h j (Finset.mem_insert_of_mem hj))
          (fun h j hj => h j (Finset.mem_insert_of_mem hj))
      have hbefore := ih hs' hsign'
      have hterm := hcoord n (hs n (Finset.mem_insert_self _ _))
      have hupper : ∑ j ∈ insert n s, (A j : ℝ) * |a j| < 2 * δ := by
        rw [Finset.sum_insert hn]
        linarith
      have habs : |∑ j ∈ insert n s, (A j : ℝ) * a j| =
          ∑ j ∈ insert n s, (A j : ℝ) * |a j| := by
        rcases hsign with hp | hm
        · rw [abs_of_nonneg (Finset.sum_nonneg fun j hj =>
            mul_nonneg (Nat.cast_nonneg _) (hp j hj))]
          apply Finset.sum_congr rfl
          intro j hj
          rw [abs_of_nonneg (hp j hj)]
        · rw [abs_of_nonpos (Finset.sum_nonpos fun j hj =>
            mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (hm j hj)),
            ← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro j hj
          rw [abs_of_nonpos (hm j hj), mul_neg]
      have hb := htail (insert n s) hs A (fun _ _ => le_rfl)
      rw [hsmall _ (by rw [habs]; exact le_of_lt (hupper.trans hδ)), habs] at hb
      exact hb
  let m : ℕ → ℝ := fun n => (A n : ℝ) * |a n|
  have hm (n : ℕ) : 0 ≤ m n := mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
  have hbound (s : Finset ℕ) : ∑ n ∈ s, m n ≤
      (∑ n ∈ Finset.range K, m n) + 2 * δ := by
    let p := s.filter (fun n => n < K)
    let t := s.filter (fun n => ¬ n < K)
    let tp := t.filter (fun n => 0 ≤ a n)
    let tm := t.filter (fun n => ¬ 0 ≤ a n)
    have hsplit : (∑ n ∈ p, m n) + ∑ n ∈ t, m n = ∑ n ∈ s, m n :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    have hsplit' : (∑ n ∈ tp, m n) + ∑ n ∈ tm, m n = ∑ n ∈ t, m n :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    have hprefix : ∑ n ∈ p, m n ≤ ∑ n ∈ Finset.range K, m n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hn).2
      · exact fun n _ _ => hm n
    have htp : ∑ n ∈ tp, m n < δ := by
      apply hsign tp
      · intro n hn
        have := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2
        omega
      · exact Or.inl fun n hn => (Finset.mem_filter.mp hn).2
    have htm : ∑ n ∈ tm, m n < δ := by
      apply hsign tm
      · intro n hn
        have := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2
        omega
      · exact Or.inr fun n hn => le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hn).2)
    linarith
  exact (summable_of_sum_le hm hbound).tsum_ofReal_lt_top

#print axioms mass_finite_of_continuousAt

end D5.S3.Analytic.WeightedCapacity.CircleCharacterContinuity
