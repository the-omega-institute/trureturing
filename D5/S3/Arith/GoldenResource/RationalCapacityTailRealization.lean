/- GID: D5/S3/Arith/GoldenResource/RationalCapacityTailRealization
   generality: G
   mirror-B: D5/B/S3/Arith/GoldenResource/RationalCapacityTailRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cofinal divisible capacities fill rational tails and exact tail filling realizes every extended nonnegative total. -/
import D5.S3.Analytic.WeightedCapacity.DyadicTailFilling
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Rat.BigOperators
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

set_option autoImplicit false
open scoped BigOperators Topology
open Filter

namespace D5.S3.Arith.GoldenResource.RationalCapacityTailRealization

open D5.S3.Analytic.WeightedCapacity.DyadicTailFilling

/-- rational reading for a positive integral denominator row. -/
noncomputable def weightedRead (g : ℕ → ℕ) {A : ℕ → ℕ} (u : B A) : ℚ :=
  ∑ n ∈ u.property.toFinset, ((u.val n : ℕ) : ℚ) / (g n : ℚ)

/-- the mass strictly after the cutoff, including possible infinity. -/
noncomputable def tailMass (g A : ℕ → ℕ) (N : ℕ) : ENNReal :=
  ∑' n, if N < n then ENNReal.ofReal ((A n : ℝ) / (g n : ℝ)) else 0

/-- one positive threshold works for every modulus and cutoff. -/
def CofinalDivisibleCapacity (g A : ℕ → ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ d : ℕ, 0 < d → ∀ N : ℕ,
    ∃ n : ℕ, N < n ∧ d ∣ g n ∧ ε ≤ (A n : ℝ) / (g n : ℝ)

/-- exact nonnegative rational filling by a legal finite tail. -/
def FillsRationalTails (g A : ℕ → ℕ) : Prop :=
  ∀ q : ℚ, 0 ≤ q → ∀ N : ℕ, ∃ u : B A,
    (∀ n : ℕ, n ≤ N → (u.val n : ℕ) = 0) ∧ weightedRead g u = q

set_option maxHeartbeats 800000 in
/-- Cofinal divisible capacities fill every rational tail, and exact filling forces infinite tail mass. -/
theorem cofinal_capacity_rational_tail_filling (g A : ℕ → ℕ) (hg : ∀ n, 0 < g n) :
    (CofinalDivisibleCapacity g A → FillsRationalTails g A) ∧
    (FillsRationalTails g A → ∀ N : ℕ, tailMass g A N = ⊤) := by
  classical
  constructor
  · rintro ⟨ε, hε, hcof⟩ q hq N
    obtain ⟨k, hk⟩ := exists_nat_gt (max ((q : ℝ) / ε) 0)
    have hk0 : 0 < k := by exact_mod_cast (lt_of_le_of_lt (le_max_right _ _) hk)
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
    let r : ℚ := q / k
    have hr0 : 0 ≤ r := div_nonneg hq (Nat.cast_nonneg _)
    have hrε : (r : ℝ) ≤ ε := by
      dsimp [r]
      push_cast
      apply (div_le_iff₀ hkR).mpr
      have h := (div_lt_iff₀ hε).mp (lt_of_le_of_lt (le_max_left _ _) hk)
      linarith
    let a := r.num.toNat
    let b := r.den
    have hab : (a : ℚ) / b = r := by
      dsimp [a, b]
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (Rat.num_nonneg.mpr hr0)]
      exact r.num_div_den
    let S : Set ℕ := {n | N < n ∧ b ∣ g n ∧ ε ≤ (A n : ℝ) / g n}
    have hS : S.Infinite := by
      intro hf
      obtain ⟨n, hn, hd, hc⟩ := hcof b r.den_pos (max N (hf.toFinset.sup id))
      have hmem : n ∈ hf.toFinset := by
        exact hf.mem_toFinset.mpr ⟨lt_of_le_of_lt (le_max_left _ _) hn, hd, hc⟩
      have hle : n ≤ hf.toFinset.sup id := Finset.le_sup (f := id) hmem
      have := le_max_right N (hf.toFinset.sup id)
      omega
    obtain ⟨s, hsS, hsk⟩ := hS.exists_subset_card_eq k
    have hvalue (n : ℕ) (hn : n ∈ s) :
        ((a * (g n / b) : ℕ) : ℚ) / (g n : ℚ) = r := by
      rw [Nat.cast_mul, Nat.cast_div_charZero (hsS hn).2.1]
      calc
        (a : ℚ) * ((g n : ℚ) / b) / g n = ((a : ℚ) / b) *
            ((g n : ℚ) / g n) := by ring
        _ = r := by rw [div_self (by exact_mod_cast (hg n).ne'), mul_one, hab]
    have hcap (n : ℕ) (hn : n ∈ s) : a * (g n / b) ≤ A n := by
      have hv : ((a * (g n / b) : ℕ) : ℝ) / g n = (r : ℝ) := by
        simpa only [Rat.cast_div, Rat.cast_natCast] using
          congrArg (fun z : ℚ => (z : ℝ)) (hvalue n hn)
      have hle := hrε.trans (hsS hn).2.2
      rw [← hv] at hle
      exact_mod_cast (div_le_div_iff_of_pos_right (show (0 : ℝ) < g n by
        exact_mod_cast hg n)).mp hle
    let x : X A := fun n => if hn : n ∈ s then
      ⟨a * (g n / b), Nat.lt_succ_of_le (hcap n hn)⟩ else ⟨0, Nat.zero_lt_succ _⟩
    have hsupport : Function.support (fun n => (x n : ℕ)) ⊆ (s : Set ℕ) := by
      intro n hn
      by_contra h
      exact hn (by simp [x, show n ∉ s from h])
    let u : B A := ⟨x, s.finite_toSet.subset hsupport⟩
    refine ⟨u, ?_, ?_⟩
    · intro n hn
      have hns : n ∉ s := fun h => (Nat.not_lt_of_ge hn) (hsS h).1
      simp [u, x, hns]
    · unfold weightedRead
      calc
        _ = ∑ n ∈ s, ((x n : ℕ) : ℚ) / (g n : ℚ) := by
          apply Finset.sum_subset
          · intro n hn
            exact hsupport (by simpa using hn)
          · intro n _ hn
            have hz : (x n : ℕ) = 0 := by simpa [u] using hn
            simp [u, hz]
        _ = ∑ _n ∈ s, r := by
          apply Finset.sum_congr rfl
          intro n hn
          simpa [x, hn] using hvalue n hn
        _ = q := by
          simp only [Finset.sum_const, nsmul_eq_mul, hsk]
          dsimp [r]
          exact mul_div_cancel₀ q (by exact_mod_cast hk0.ne')
  · intro hfill N
    by_contra htop
    obtain ⟨k, hk⟩ := exists_nat_gt (tailMass g A N).toReal
    obtain ⟨u, huN, huq⟩ := hfill k (Nat.cast_nonneg _) N
    have hr : (weightedRead g u : ℝ) = k := by exact_mod_cast huq
    have hbound : ENNReal.ofReal (k : ℝ) ≤ tailMass g A N := by
      rw [← hr]
      unfold weightedRead
      simp only [Rat.cast_sum, Rat.cast_div, Rat.cast_natCast]
      unfold tailMass
      rw [ENNReal.ofReal_sum_of_nonneg (by intros; positivity)]
      apply le_trans (Finset.sum_le_sum ?_) (ENNReal.sum_le_tsum _)
      intro n hn
      have hne : (u.val n : ℕ) ≠ 0 := by simpa using hn
      have hN : N < n := by
        by_contra h
        exact hne (huN n (by omega))
      rw [if_pos hN]
      apply ENNReal.ofReal_le_ofReal
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast Nat.le_of_lt_succ (u.val n).isLt
    have hreal := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top htop).mpr hbound
    rw [ENNReal.toReal_ofReal (Nat.cast_nonneg _)] at hreal
    exact (not_le_of_gt hk) hreal

/-- the exact extended supremum of the inclusive real partial sums. -/
noncomputable def weightedTotal (g : ℕ → ℕ) {A : ℕ → ℕ} (x : X A) : ENNReal :=
  ⨆ N : ℕ, ENNReal.ofReal
    (∑ n ∈ Finset.range (N + 1), ((x n : ℕ) : ℝ) / (g n : ℝ))

set_option maxHeartbeats 800000 in
/-- Every extended nonnegative real is the total reading of a capacity state when rational tails fill exactly. -/
theorem rational_tail_filling_full_range (g A : ℕ → ℕ) (hg : ∀ n, 0 < g n)
    (hfill : FillsRationalTails g A) :
    Function.Surjective (@weightedTotal g A) := by
  classical
  have hread (u : B A) (s : Finset ℕ)
      (hs : u.property.toFinset ⊆ s) :
      weightedRead g u = ∑ n ∈ s, ((u.val n : ℕ) : ℚ) / g n := by
    apply Finset.sum_subset hs
    intro n _ hn
    have hz : (u.val n : ℕ) = 0 := by simpa using hn
    simp [hz]
  have hprefix (u : B A) (s : Finset ℕ) :
      (∑ n ∈ s, ((u.val n : ℕ) : ℚ) / g n) ≤ weightedRead g u := by
    rw [hread u (s ∪ u.property.toFinset) Finset.subset_union_right]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (by
      intros; positivity)
  have htotal (x : X A) : weightedTotal g x =
      ∑' n, ENNReal.ofReal (((x n : ℕ) : ℝ) / g n) := by
    unfold weightedTotal
    simp_rw [ENNReal.ofReal_sum_of_nonneg (fun n _ =>
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
    exact (ENNReal.tsum_eq_iSup_nat' (tendsto_add_atTop_nat 1)).symm
  intro t
  by_cases ht : t = ⊤
  · let x : X A := fun n => ⟨A n, Nat.lt_succ_self _⟩
    refine ⟨x, ?_⟩
    rw [ht, htotal]
    apply top_unique
    rw [← (cofinal_capacity_rational_tail_filling g A hg).2 hfill 0]
    apply ENNReal.tsum_le_tsum
    intro n
    dsimp [x]
    split_ifs <;> simp
  have htR : 0 ≤ t.toReal := ENNReal.toReal_nonneg
  obtain ⟨r, hrmono, hrlt, hrlim⟩ := Real.exists_seq_rat_strictMono_tendsto t.toReal
  let q : ℕ → ℚ := fun j => match j with
    | 0 => 0
    | i + 1 => max 0 (r i)
  have hq0 (j : ℕ) : 0 ≤ q j := by cases j <;> simp [q]
  have hqmono : Monotone q := by
    apply monotone_nat_of_le_succ
    intro j
    cases j with
    | zero => exact hq0 1
    | succ j => exact max_le_max_left 0 (hrmono.monotone (Nat.le_succ j))
  have hqle (j : ℕ) : (q j : ℝ) ≤ t.toReal := by
    cases j with
    | zero => simpa [q] using htR
    | succ j => simpa [q, Rat.cast_max] using max_le htR (hrlt j).le
  have hqlim : Tendsto (fun j => (q j : ℝ)) atTop (𝓝 t.toReal) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa [q, Rat.cast_max, max_eq_right htR] using
      (tendsto_const_nhds.max hrlim :
        Tendsto (fun j => max (0 : ℝ) (r j)) atTop (𝓝 (max 0 t.toReal)))
  have hstep (j : ℕ) (u : B A) (hu : weightedRead g u = q j) :
      ∃ v : B A, weightedRead g v = q (j + 1) ∧
        (∀ n, (u.val n : ℕ) ≤ (v.val n : ℕ)) ∧
        (∀ n ≤ j, v.val n = u.val n) := by
    let K := max j (u.property.toFinset.sup id)
    have huK (n : ℕ) (hn : K < n) : (u.val n : ℕ) = 0 := by
      by_contra h
      have hmem : n ∈ u.property.toFinset := by simpa using h
      have hle : n ≤ u.property.toFinset.sup id := Finset.le_sup (f := id) hmem
      dsimp [K] at hn
      omega
    obtain ⟨w, hwK, hwq⟩ := hfill (q (j + 1) - q j)
      (sub_nonneg.mpr (hqmono (Nat.le_succ j))) K
    let v : X A := fun n => if n ≤ K then u.val n else w.val n
    have hvsum (n : ℕ) : (v n : ℕ) = (u.val n : ℕ) + (w.val n : ℕ) := by
      by_cases hn : n ≤ K
      · simp [v, hn, hwK n hn]
      · simp [v, hn, huK n (by omega)]
    let s := u.property.toFinset ∪ w.property.toFinset
    have hvs : Function.support (fun n => (v n : ℕ)) ⊆ (s : Set ℕ) := by
      intro n hn
      by_contra h
      have hu0 : (u.val n : ℕ) = 0 := by
        have : n ∉ u.property.toFinset := fun hn => h (Finset.mem_union_left _ hn)
        simpa using this
      have hw0 : (w.val n : ℕ) = 0 := by
        have : n ∉ w.property.toFinset := fun hn => h (Finset.mem_union_right _ hn)
        simpa using this
      exact hn (by change (v n : ℕ) = 0; rw [hvsum, hu0, hw0])
    let vb : B A := ⟨v, s.finite_toSet.subset hvs⟩
    refine ⟨vb, ?_, ?_, ?_⟩
    · have hreads : weightedRead g vb = weightedRead g u + weightedRead g w := by
        rw [hread vb s (by intro n hn; exact hvs (by simpa using hn)),
          hread u s Finset.subset_union_left, hread w s Finset.subset_union_right,
          ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro n _
        change ((v n : ℕ) : ℚ) / g n = _
        rw [hvsum, Nat.cast_add, add_div]
      rw [hreads, hu, hwq]
      ring
    · intro n
      change (u.val n : ℕ) ≤ (v n : ℕ)
      rw [hvsum]
      omega
    · intro n hn
      change v n = u.val n
      exact if_pos (hn.trans (le_max_left j (u.property.toFinset.sup id)))
  choose next hnext using hstep
  let z : B A := ⟨fun n => ⟨0, Nat.zero_lt_succ _⟩, by
    simpa [Function.support] using Set.finite_empty⟩
  have hz : weightedRead g z = q 0 := by simp [weightedRead, z, q, Function.support]
  let U : (j : ℕ) → {u : B A // weightedRead g u = q j} :=
    Nat.rec ⟨z, hz⟩ (fun j u => ⟨next j u.val u.property, (hnext j u.val u.property).1⟩)
  have hUstep (j n : ℕ) : ((U j).val.val n : ℕ) ≤ ((U (j + 1)).val.val n : ℕ) :=
    (hnext j (U j).val (U j).property).2.1 n
  have hUfix (j n : ℕ) (hn : n ≤ j) :
      (U (j + 1)).val.val n = (U j).val.val n :=
    (hnext j (U j).val (U j).property).2.2 n hn
  have hUmono (n : ℕ) : Monotone (fun j => ((U j).val.val n : ℕ)) :=
    monotone_nat_of_le_succ (fun j => hUstep j n)
  have hUstable (i j n : ℕ) (hij : i ≤ j) (hni : n ≤ i) :
      (U j).val.val n = (U i).val.val n := by
    induction j, hij using Nat.le_induction with
    | base => rfl
    | succ j hij ih => rw [hUfix j n (hni.trans hij), ih]
  let x : X A := fun n => (U (n + 1)).val.val n
  have hUx (j n : ℕ) : ((U j).val.val n : ℕ) ≤ (x n : ℕ) := by
    by_cases hj : j ≤ n + 1
    · exact hUmono n hj
    · have he := hUstable (n + 1) j n (by omega) (by omega)
      exact le_of_eq (congrArg Fin.val he)
  have hxprefix (N n : ℕ) (hn : n ∈ Finset.range (N + 1)) :
      x n = (U (N + 1)).val.val n := by
    have hnN := Finset.mem_range.mp hn
    exact (hUstable (n + 1) (N + 1) n (by omega) (by omega)).symm
  refine ⟨x, le_antisymm ?_ ?_⟩
  · apply iSup_le
    intro N
    have hpr : (∑ n ∈ Finset.range (N + 1), ((x n : ℕ) : ℚ) / g n) ≤ q (N + 1) := by
      calc
        _ = ∑ n ∈ Finset.range (N + 1), (((U (N + 1)).val.val n : ℕ) : ℚ) / g n := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [hxprefix N n hn]
        _ ≤ weightedRead g (U (N + 1)).val := hprefix _ _
        _ = _ := (U (N + 1)).property
    have hprR : (∑ n ∈ Finset.range (N + 1), ((x n : ℕ) : ℝ) / g n) ≤
        (q (N + 1) : ℝ) := by
      have hh := Rat.cast_le (K := ℝ) |>.mpr hpr
      simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_natCast] using hh
    exact (ENNReal.ofReal_le_ofReal (hprR.trans (hqle (N + 1)))).trans_eq
      (ENNReal.ofReal_toReal ht)
  · rw [← ENNReal.ofReal_toReal ht]
    apply le_of_tendsto' (ENNReal.tendsto_ofReal hqlim)
    intro j
    rw [← (U j).property, weightedRead]
    simp only [Rat.cast_sum, Rat.cast_div, Rat.cast_natCast]
    rw [ENNReal.ofReal_sum_of_nonneg (by intros; positivity), htotal]
    apply le_trans (Finset.sum_le_sum ?_) (ENNReal.sum_le_tsum _)
    intro n _
    apply ENNReal.ofReal_le_ofReal
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast hUx j n

#print axioms cofinal_capacity_rational_tail_filling
#print axioms rational_tail_filling_full_range

end D5.S3.Arith.GoldenResource.RationalCapacityTailRealization
