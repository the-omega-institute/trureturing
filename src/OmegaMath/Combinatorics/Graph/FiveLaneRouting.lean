import OmegaBuild.Commands
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

compile_only_with_mathlib

/-! Omega original.

The nonlinear and linear routing costs of five-label local demands. The
cost of a capacity matrix is one half its sum over all ordered pairs.
-/
namespace FiveLaneRouting

open Finset
open scoped BigOperators
noncomputable section

abbrev Label := Fin 5
abbrev Current := Label → Label → ℝ
abbrev Imbalance := Label → ℝ

def total : Imbalance →ₗ[ℝ] ℝ := ∑ i : Label, LinearMap.proj i

abbrev Demand := LinearMap.ker total

@[simp] theorem total_apply (z : Imbalance) : total z = ∑ i, z i := by
  simp [total, LinearMap.sum_apply]

theorem demand_sum (z : Demand) : ∑ i, z.val i = 0 :=
  (total_apply _).symm.trans (LinearMap.mem_ker.mp z.property)

def unitCube (z : Imbalance) : Prop := ∀ i, |z i| ≤ 1

def Routes (q : Current) (z : Imbalance) : Prop :=
  (∀ i j, q j i = -q i j) ∧ ∀ i, ∑ j, q i j = z i

def covered (c q : Current) : Prop := ∀ i j, |q i j| ≤ c i j
def cost (c : Current) : ℝ := (∑ i, ∑ j, c i j) / 2

def NonlinearEnvelope (c : Current) : Prop :=
  ∀ z : Demand, unitCube z.val → ∃ q, Routes q z.val ∧ covered c q

def LinearEnvelope (c : Current) : Prop :=
  ∃ q : Demand →ₗ[ℝ] Current, ∀ z : Demand, unitCube z.val →
    Routes (q z) z.val ∧ covered c (q z)

def rootDemand (i j : Label) : Demand :=
  ⟨Pi.single i 1 - Pi.single j 1, by simp [Pi.sub_apply, sum_sub_distrib]⟩

theorem rootDemand_cube (i j : Label) : unitCube (rootDemand i j).val := by
  intro a
  change |(Pi.single i 1 - Pi.single j 1 : Imbalance) a| ≤ 1
  simp only [Pi.sub_apply, Pi.single_apply]
  split <;> split <;> norm_num

private theorem rootDemand_sub (i j a : Label) :
    rootDemand i j = rootDemand i a - rootDemand j a := by
  apply Subtype.ext
  change Pi.single (M := fun _ : Label => ℝ) i (1 : ℝ) - Pi.single j 1 =
    (Pi.single i 1 - Pi.single a 1) - (Pi.single j 1 - Pi.single a 1)
  abel

theorem linear_lower {c : Current} (hc : LinearEnvelope c) : 4 ≤ cost c := by
  obtain ⟨q, hq⟩ := hc
  let b (i : Label) := q (rootDemand i 0)
  have hskew (i a j : Label) : b i j a = -b i a j :=
    (hq _ (rootDemand_cube i 0)).1.1 a j
  have hdiv (i : Label) : ∑ j, b i i j = if i = 0 then 0 else 1 := by
    have h := (hq _ (rootDemand_cube i 0)).1.2 i
    by_cases hi : i = 0 <;> simpa [b, rootDemand, Pi.sub_apply, Pi.single_apply, hi] using h
  have hbound (i j : Label) : b i i j + b j j i ≤ c i j := by
    have h := (hq _ (rootDemand_cube i j)).2 i j
    rw [rootDemand_sub i j 0, map_sub] at h
    change |b i i j - b j i j| ≤ c i j at h
    rw [hskew j j i, sub_neg_eq_add] at h
    exact (le_abs_self _).trans h
  have h := sum_le_sum fun i (_ : i ∈ (univ : Finset Label)) =>
    sum_le_sum fun j (_ : j ∈ (univ : Finset Label)) => hbound i j
  change ∑ i : Label, ∑ j : Label, (b i i j + b j j i) ≤ ∑ i, ∑ j, c i j at h
  simp only [sum_add_distrib] at h
  rw [show (∑ i : Label, ∑ j : Label, b j j i) = ∑ i : Label, ∑ j : Label, b i i j from
    sum_comm] at h
  simp_rw [hdiv] at h
  have h8 : 2 * (∑ i : Label, if i = 0 then (0 : ℝ) else 1) = 8 := by
    norm_num [Fin.sum_univ_succ]
  rw [← two_mul, h8] at h
  unfold cost
  linarith

/-- The normalized linear choice uses the differences of the five demands. -/
def linearRoute : Demand →ₗ[ℝ] Current where
  toFun z i j := (z.val i - z.val j) / 5
  map_add' x y := by
    ext i j
    change (x.val i + y.val i - (x.val j + y.val j)) / 5 =
      (x.val i - x.val j) / 5 + (y.val i - y.val j) / 5
    ring
  map_smul' a x := by
    ext i j
    change (a * x.val i - a * x.val j) / 5 = a * ((x.val i - x.val j) / 5)
    ring

theorem linear_upper : LinearEnvelope (fun i j => if i = j then 0 else 2 / 5) := by
  refine ⟨linearRoute, fun z hz => ⟨⟨?_, ?_⟩, ?_⟩⟩
  · intro i j
    change (z.val j - z.val i) / 5 = -((z.val i - z.val j) / 5)
    ring
  · intro i
    change ∑ j : Label, (z.val i - z.val j) / 5 = z.val i
    rw [← sum_div, sum_sub_distrib, demand_sum z]
    simp
  · intro i j
    change |(z.val i - z.val j) / 5| ≤ if i = j then 0 else 2 / 5
    by_cases h : i = j
    · subst j
      simp
    rw [ite_eq_right h, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 5)]
    exact (div_le_div_iff_of_pos_right (by norm_num)).2
      (abs_le.mpr ⟨by linarith [(abs_le.mp (hz i)).1, (abs_le.mp (hz j)).2],
        by linarith [(abs_le.mp (hz i)).2, (abs_le.mp (hz j)).1]⟩)

private def interior (z : Demand) : Finset Label := univ.filter fun i => |z.val i| < 1

private theorem rootDemand_rev (i j : Label) : rootDemand j i = -rootDemand i j := by
  apply Subtype.ext
  change Pi.single (M := fun _ : Label => ℝ) j 1 - Pi.single i 1 =
    -(Pi.single i 1 - Pi.single j 1)
  abel

private theorem slide_to_boundary (z : Demand) (hz : unitCube z.val) {i j : Label}
    (hi : |z.val i| < 1) (hj : |z.val j| < 1) (hij : i ≠ j) :
    ∃ a : ℝ, 0 < a ∧ unitCube (z + a • rootDemand i j).val ∧
      (interior (z + a • rootDemand i j)).card < (interior z).card := by
  let a := min (1 - z.val i) (1 + z.val j)
  have hlow : 0 < a := lt_min
    (by linarith [(abs_lt.mp hi).2]) (by linarith [(abs_lt.mp hj).1])
  let w := z + a • rootDemand i j
  have hwi : w.val i = z.val i + a := by
    simp [w, rootDemand, hij]
  have hwj : w.val j = z.val j - a := by
    simp [w, rootDemand, hij.symm, sub_eq_add_neg]
  have hwk (k : Label) (hki : k ≠ i) (hkj : k ≠ j) : w.val k = z.val k := by
    simp [w, rootDemand, hki, hkj]
  refine ⟨a, hlow, ?_, card_lt_card ?_⟩
  · intro k
    rcases eq_or_ne k i with hki | hki
    · subst k
      rw [hwi, abs_le]
      exact ⟨by linarith [(abs_lt.mp hi).1], by linarith [min_le_left (1-z.val i) (1+z.val j)]⟩
    rcases eq_or_ne k j with hkj | hkj
    · subst k
      rw [hwj, abs_le]
      exact ⟨by linarith [min_le_right (1-z.val i) (1+z.val j)], by linarith [(abs_lt.mp hj).2]⟩
    rw [hwk _ hki hkj]
    exact hz k
  · have hsub : interior w ⊆ interior z := by
      intro k hk
      simp only [interior, mem_filter, mem_univ, true_and] at hk ⊢
      by_cases hki : k = i
      · rwa [hki]
      by_cases hkj : k = j
      · rwa [hkj]
      rwa [hwk k hki hkj] at hk
    apply (ssubset_iff_of_subset hsub).mpr
    rcases le_total (1-z.val i) (1+z.val j) with h | h
    · refine ⟨i, by simp [interior, hi], ?_⟩
      have : w.val i = 1 := by rw [hwi, show a = 1-z.val i from min_eq_left h]; ring
      simp [interior, this]
    · refine ⟨j, by simp [interior, hj], ?_⟩
      have : w.val j = -1 := by rw [hwj, show a = 1+z.val j from min_eq_right h]; ring
      simp [interior, this]

private theorem corners {z : Demand} (hz : unitCube z.val) (a : Label)
    (ha : ∀ i, i ≠ a → ¬ |z.val i| < 1) :
    (∀ i, z.val i = -1 ∨ z.val i = 0 ∨ z.val i = 1) ∧
      ∑ i : Label, z.val i ^ 2 = 4 := by
  let τ := Equiv.swap 0 a
  let w (i : Label) := z.val (τ i)
  have hswap : τ 0 = a := Equiv.swap_apply_left _ _
  have hcorner (i : Label) (hi : i ≠ 0) : w i = -1 ∨ w i = 1 := by
    have he := le_antisymm (hz (τ i)) (le_of_not_gt (ha (τ i) fun h =>
      hi (τ.injective (h.trans hswap.symm))))
    simpa [w, abs_eq, or_comm] using he
  have hsum : ∑ i, w i = 0 := (Equiv.sum_comp τ z.val).trans (demand_sum z)
  have hsum' : w 0 + w 1 + w 2 + w 3 + w 4 = 0 := by
    norm_num [Fin.sum_univ_succ] at hsum
    linarith
  have hzero : w 0 = 0 := by
    have h0 := abs_le.mp (hz (τ 0))
    rcases hcorner 1 (by decide) with h1 | h1 <;>
    rcases hcorner 2 (by decide) with h2 | h2 <;>
    rcases hcorner 3 (by decide) with h3 | h3 <;>
    rcases hcorner 4 (by decide) with h4 | h4 <;>
    linarith [h0.1, h0.2]
  constructor
  · intro j
    obtain ⟨i, rfl⟩ := τ.surjective j
    change w i = -1 ∨ w i = 0 ∨ w i = 1
    by_cases hi : i = 0
    · exact Or.inr (Or.inl (hi.symm ▸ hzero))
    rcases hcorner i hi with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · rw [← Equiv.sum_comp τ (fun i => z.val i ^ 2)]
    change ∑ i : Label, w i ^ 2 = 4
    have hsq (i : Label) (hi : i ≠ 0) : w i ^ 2 = 1 := by
      rcases hcorner i hi with h | h <;> norm_num [h]
    norm_num [Fin.sum_univ_succ, hzero, hsq]

private def nonlinearCapacity : Current := fun i j => if i = j then 0 else 1 / 3

private theorem corner_route (z : Demand)
    (hz : ∀ i, z.val i = -1 ∨ z.val i = 0 ∨ z.val i = 1)
    (hfour : ∑ i : Label, z.val i ^ 2 = 4) :
    ∃ q, Routes q z.val ∧ covered nonlinearCapacity q := by
  let q (i j : Label) := (z.val i - z.val j) * (2 + z.val i * z.val j) / 6
  refine ⟨q, ⟨?_, ?_⟩, ?_⟩
  · intro i j
    dsimp [q]
    ring
  · intro i
    have he (j : Label) : q i j = (2 * z.val i + (z.val i ^ 2 - 2) * z.val j
        - z.val i * z.val j ^ 2) / 6 := by dsimp [q]; ring
    simp only [he, ← sum_div, sum_sub_distrib, sum_add_distrib, ← mul_sum, hfour, demand_sum,
      sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  · intro i j
    by_cases h : i = j
    · subst j
      simp [q, nonlinearCapacity]
    rcases hz i with hi | hi | hi <;> rcases hz j with hj | hj | hj <;>
      norm_num [q, nonlinearCapacity, h, hi, hj]

/-- Every five-label balanced unit demand fits the pair capacity of one third. -/
theorem nonlinear_upper : NonlinearEnvelope nonlinearCapacity := by
  have claim (n : ℕ) (z : Demand) (hz : unitCube z.val) (hn : (interior z).card = n) :
      ∃ q, Routes q z.val ∧ covered nonlinearCapacity q := by
    induction n using Nat.strong_induction_on generalizing z with
    | h n ih =>
      by_cases he : ∃ i j : Label, i ≠ j ∧ |z.val i| < 1 ∧ |z.val j| < 1
      · obtain ⟨i, j, hij, hi, hj⟩ := he
        obtain ⟨a, ha, hp, hap⟩ := slide_to_boundary z hz hi hj hij
        obtain ⟨b, hb, hm, hbm⟩ := slide_to_boundary z hz hj hi hij.symm
        rw [hn] at hap hbm
        obtain ⟨q₁, ⟨hs₁, hd₁⟩, hc₁⟩ := ih _ hap _ hp rfl
        obtain ⟨q₂, ⟨hs₂, hd₂⟩, hc₂⟩ := ih _ hbm _ hm rfl
        let t := b / (a+b)
        let u := a / (a+b)
        have hden := add_pos ha hb
        have ht : 0 ≤ t := div_nonneg hb.le hden.le
        have hu : 0 ≤ u := div_nonneg ha.le hden.le
        have hsum : t+u=1 := by dsimp [t,u]; field_simp; ring
        have hmul : t*a=u*b := by dsimp [t,u]; ring
        let q (i j : Label) := t * q₁ i j + u * q₂ i j
        refine ⟨q, ⟨?_, ?_⟩, ?_⟩
        · intro i j
          simp only [q, hs₁ i j, hs₂ i j]
          ring
        · intro l
          simp only [q, sum_add_distrib, ← mul_sum, hd₁, hd₂, rootDemand_rev i j,
            Submodule.coe_add, Submodule.coe_smul, Submodule.coe_neg,
            Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
          calc
            _ = (t+u)*z.val l + (t*a-u*b)*(rootDemand i j).val l := by ring
            _ = _ := by simp [hsum, hmul]
        · intro i j
          change |t * q₁ i j + u * q₂ i j| ≤ nonlinearCapacity i j
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg ht, abs_of_nonneg hu]
          calc
            _ ≤ t * nonlinearCapacity i j + u * nonlinearCapacity i j :=
              add_le_add (mul_le_mul_of_nonneg_left (hc₁ i j) ht)
                (mul_le_mul_of_nonneg_left (hc₂ i j) hu)
            _ = _ := by rw [← add_mul, hsum, one_mul]
      · have hex : ∃ a : Label, ∀ i, i ≠ a → ¬ |z.val i| < 1 := by
          by_cases h : ∃ a : Label, |z.val a| < 1
          · obtain ⟨a, ha⟩ := h
            exact ⟨a, fun i hi hk => he ⟨i, a, hi, hk, ha⟩⟩
          · exact ⟨0, fun i _ hi => h ⟨i,hi⟩⟩
        obtain ⟨a, ha⟩ := hex
        exact (fun ⟨hg, hq⟩ => corner_route z hg hq) (corners hz a ha)
  exact fun z hz => claim _ z hz rfl

private def cutDemand (a b : Label) : Demand := by
  let z (i : Label) := -(2/3 : ℝ) + (if i = a then 5/3 else 0) + (if i = b then 5/3 else 0)
  refine ⟨z, LinearMap.mem_ker.mpr ?_⟩
  simp only [total_apply, z, sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, sum_ite_eq', mem_univ, ite_true]
  ring

private theorem cutDemand_apply (a b : Label) (hab : a ≠ b) (i : Label) :
    (cutDemand a b).val i = if i = a ∨ i = b then 1 else -(2/3 : ℝ) := by
  by_cases ha : i = a <;> by_cases hb : i = b
  · exact (hab (ha.symm.trans hb)).elim
  all_goals norm_num [cutDemand, ha, hb, hab, hab.symm]

private theorem cut_lower {c : Current} (hc : NonlinearEnvelope c) {a b : Label} (hab : a ≠ b) :
    2 ≤ ∑ i : Label, if i = a ∨ i = b then 0 else c a i + c b i := by
  let z := cutDemand a b
  have hz : unitCube z.val := by
    intro i
    rw [cutDemand_apply a b hab]
    split <;> norm_num
  obtain ⟨q, ⟨hskew, hdiv⟩, hq⟩ := hc z hz
  have hdiag (i : Label) : q i i = 0 := by linarith [hskew i i]
  have hlocal (i : Label) :
      (if i = a ∨ i = b then q a i + q b i else 0) =
        (if i = a then q b a else 0) + (if i = b then q a b else 0) := by
    by_cases ha : i = a
    · subst i
      simp [hab, hdiag]
    by_cases hb : i = b
    · subst i
      simp [hab.symm, hdiag]
    simp [ha, hb]
  have hcancel : (∑ i : Label, if i = a ∨ i = b then q a i + q b i else 0) = 0 := by
    simp only [hlocal, sum_add_distrib, sum_ite_eq', mem_univ, ite_true]
    linarith [hskew a b]
  have he (i : Label) :
      (if i = a ∨ i = b then 0 else q a i + q b i) ≤
        if i = a ∨ i = b then 0 else c a i + c b i := by
    split
    · exact le_rfl
    · exact add_le_add ((le_abs_self _).trans (hq a i)) ((le_abs_self _).trans (hq b i))
  have h := sum_le_sum fun i (_ : i ∈ (univ : Finset Label)) => he i
  have hsum :
      (∑ i : Label, if i = a ∨ i = b then 0 else q a i + q b i) =
        (∑ i : Label, (q a i + q b i)) -
          (∑ i : Label, if i = a ∨ i = b then q a i + q b i else 0) := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    by_cases hi : i = a ∨ i = b <;> simp [hi]
  rw [hsum, hcancel, sub_zero, sum_add_distrib, hdiv, hdiv] at h
  norm_num [z, cutDemand_apply a b hab] at h
  exact h

/-- The ten two-element cuts charge each off-diagonal capacity six times
when both orientations are counted. -/
theorem nonlinear_lower {c : Current} (hc : NonlinearEnvelope c) : 10 / 3 ≤ cost c := by
  have h (a b : Label) :
      (if a = b then 0 else 2 : ℝ) ≤
        if a = b then 0 else ∑ i : Label, if i = a ∨ i = b then 0 else c a i + c b i := by
    by_cases h : a = b
    · simp [h]
    · simpa [h] using cut_lower hc h
  have htotal := sum_le_sum fun a (_ : a ∈ (univ : Finset Label)) =>
    sum_le_sum fun b (_ : b ∈ (univ : Finset Label)) => h a b
  have hdiag (i : Label) : 0 ≤ c i i := by
    obtain ⟨q, _, hq⟩ := hc 0 (by intro j; simp)
    exact (abs_nonneg _).trans (hq i i)
  norm_num [Fin.sum_univ_succ] at htotal
  unfold cost
  norm_num [Fin.sum_univ_succ]
  linarith [hdiag 0, hdiag 1, hdiag 2, hdiag 3, hdiag 4]

/-- Sharp normalized local costs for unrestricted and linear pair routing. -/
theorem exact_pair_costs :
    (∃ c, NonlinearEnvelope c ∧ cost c = 10 / 3) ∧
    (∀ c, NonlinearEnvelope c → 10 / 3 ≤ cost c) ∧
    (∃ c, LinearEnvelope c ∧ cost c = 4) ∧
    ∀ c, LinearEnvelope c → 4 ≤ cost c := by
  refine ⟨⟨nonlinearCapacity, nonlinear_upper, ?_⟩, fun _ => nonlinear_lower,
    ⟨_, linear_upper, ?_⟩, fun _ => linear_lower⟩ <;>
    norm_num [cost, nonlinearCapacity, Fin.sum_univ_succ]

end
end FiveLaneRouting
