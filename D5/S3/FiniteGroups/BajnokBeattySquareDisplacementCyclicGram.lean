/- GID: D5/S3/FiniteGroups/BajnokBeattySquareDisplacementCyclicGram
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattySquareDisplacementCyclicGram
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Actual count-threshold covariance is the counting Gram of torsion-square indicators in one finite cyclic group for every finite parameter set. -/

import D5.S3.FiniteGroups.BajnokBeattySquareDisplacementActualMoments
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.FiniteGroups.BajnokBeattySquareDisplacementCyclicGram

open Filter Set
open scoped Classical Topology BigOperators
open _root_.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementThresholdDistribution
open _root_.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementActualMoments

abbrev Params :=
  _root_.D5.S3.FiniteGroups.BajnokBeattySquareDisplacementActualMoments.Params

def E (T : Params → ℕ → ℕ) (p : Params) (k : ℕ) : ℝ :=
  D T p k - 1 / 2

def modulus (S : Finset Params) : ℕ := ∏ p ∈ S, p.val.toNat

private theorem param_pos_int (p : Params) : (0 : ℤ) < p.val := by
  exact_mod_cast param_pos p

private theorem param_pos_nat (p : Params) : 0 < p.val.toNat :=
  Int.pos_iff_toNat_pos.mp (param_pos_int p)

private theorem param_nat_cast (p : Params) : (p.val.toNat : ℤ) = p.val :=
  Int.toNat_of_nonneg (param_pos_int p).le

private theorem modulus_pos (S : Finset Params) : 0 < modulus S := by
  unfold modulus
  exact Finset.prod_pos (fun p _ => param_pos_nat p)

private theorem modulus_ne_zero (S : Finset Params) : modulus S ≠ 0 :=
  (modulus_pos S).ne'

-- Installed before any finite-group sum; the empty product is 1.
private instance modulusNeZero (S : Finset Params) : NeZero (modulus S) :=
  ⟨modulus_ne_zero S⟩

abbrev G (S : Finset Params) := ZMod (modulus S)

def H (S : Finset Params) (d : ℕ) : AddSubgroup (G S) :=
  (nsmulAddMonoidHom d : G S →+ G S).ker

def v (S : Finset Params) (p : S) (z : G S × G S) : ℝ :=
  (1 / (p.val.val : ℝ)) *
    (if z.1 ∈ H S p.val.val.toNat then 1 else 0) *
      (if z.2 ∈ H S p.val.val.toNat then 1 else 0)

def A (T : Params → ℕ → ℕ) (S : Finset Params) (c : S → ℝ) (k : ℕ) : ℝ :=
  ∑ p : S, c p * E T p.val k

def V (S : Finset Params) (c : S → ℝ) : ℝ :=
  (1 / 12) * ∑ z : G S × G S, (∑ p : S, c p * v S p z) ^ 2

private theorem nat_dvd_modulus {S : Finset Params} {p : Params} (hp : p ∈ S) :
    p.val.toNat ∣ modulus S := by
  exact Finset.dvd_prod_of_mem (fun q : Params => q.val.toNat) hp

private theorem gcd_toNat (p r : Params) :
    Nat.gcd p.val.toNat r.val.toNat = Int.gcd p.val r.val := by
  have hp : p.val.natAbs = p.val.toNat := by
    simpa only [Int.natAbs_natCast] using
      (congrArg Int.natAbs (param_nat_cast p)).symm
  have hr : r.val.natAbs = r.val.toNat := by
    simpa only [Int.natAbs_natCast] using
      (congrArg Int.natAbs (param_nat_cast r)).symm
  simp only [Int.gcd_def, hp, hr]

private theorem card_H_of_dvd (S : Finset Params) (d : ℕ) (hd : d ∣ modulus S) :
    Nat.card (H S d) = d := by
  simpa only [H, Nat.card_zmod, Nat.gcd_eq_right hd] using
    (IsAddCyclic.card_nsmulAddMonoidHom_ker (G := G S) d)

private theorem H_intersection (S : Finset Params) (p r : ℕ) :
    H S p ⊓ H S r = H S (Nat.gcd p r) := by
  ext x
  change (p • x = 0 ∧ r • x = 0) ↔ Nat.gcd p r • x = 0
  rw [← addOrderOf_dvd_iff_nsmul_eq_zero,
    ← addOrderOf_dvd_iff_nsmul_eq_zero,
    ← addOrderOf_dvd_iff_nsmul_eq_zero, Nat.dvd_gcd_iff]

private theorem card_H_intersection (S : Finset Params) (p r : ℕ)
    (hp : p ∣ modulus S) :
    Nat.card ↥(H S p ⊓ H S r) = Nat.gcd p r := by
  rw [H_intersection]
  exact card_H_of_dvd S (Nat.gcd p r)
    (Nat.dvd_trans (Nat.gcd_dvd_left p r) hp)

private theorem sum_indicator (α : Type*) [AddGroup α] [Fintype α]
    (H K : AddSubgroup α) (a b : ℝ) :
    (∑ x : α, (if x ∈ H then a else 0) * (if x ∈ K then b else 0)) =
      (Nat.card ↥(H ⊓ K) : ℝ) * (a * b) := by
  classical
  let P : α → Prop := fun x => x ∈ H ∧ x ∈ K
  have hcard : (Finset.univ.filter P).card = Nat.card ↥(H ⊓ K) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    apply congrArg Finset.card
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, P, AddSubgroup.mem_inf]
  have hsum :
      (∑ x : α, (if x ∈ H then a else 0) * (if x ∈ K then b else 0)) =
        ∑ x ∈ Finset.univ.filter P, a * b := by
    calc
      _ = ∑ x : α, if P x then a * b else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hH : x ∈ H <;> by_cases hK : x ∈ K <;> simp [P, hH, hK]
      _ = _ := by rw [← Finset.sum_filter]
  rw [hsum, Finset.sum_const, hcard, nsmul_eq_mul]

private theorem gram_pair (S : Finset Params) (p r : S) :
    (∑ z : G S × G S, v S p z * v S r z) =
      (Int.gcd p.val r.val : ℝ)^2 /
        ((p.val : ℝ) * (r.val : ℝ)) := by
  classical
  let Hp := H S p.val.val.toNat
  let Hr := H S r.val.val.toNat
  have hp : p.val.val.toNat ∣ modulus S := nat_dvd_modulus p.property
  have hprod :
      (∑ z : G S × G S, v S p z * v S r z) =
        (∑ x : G S,
          (if x ∈ Hp then 1 / (p.val.val : ℝ) else 0) *
            (if x ∈ Hr then 1 / (r.val.val : ℝ) else 0)) *
          (∑ y : G S,
            (if y ∈ Hp then (1 : ℝ) else 0) *
              (if y ∈ Hr then 1 else 0)) := by
    calc
      _ = ∑ x : G S, ∑ y : G S,
          ((if x ∈ Hp then 1 / (p.val.val : ℝ) else 0) *
            (if x ∈ Hr then 1 / (r.val.val : ℝ) else 0)) *
          ((if y ∈ Hp then (1 : ℝ) else 0) *
            (if y ∈ Hr then 1 else 0)) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        dsimp only [v, Hp, Hr]
        split_ifs <;> ring
      _ = _ := (Fintype.sum_mul_sum _ _).symm
  rw [hprod, sum_indicator, sum_indicator]
  dsimp only [Hp, Hr]
  simp only [card_H_intersection S p.val.val.toNat r.val.val.toNat hp,
    gcd_toNat p.val r.val]
  field_simp [(param_pos p.val).ne', (param_pos r.val).ne'] <;> ring

-- Reuse the supplier average subtraction and scalar-multiplication identities; add only the missing finite-average formulas.
private theorem avg_add (f g : ℕ → ℝ) (N : ℕ) :
    avg (fun k => f k + g k) N = avg f N + avg g N := by
  simp only [avg, Finset.sum_add_distrib, add_div]

private theorem avg_const (c : ℝ) (N : ℕ) (hN : N ≠ 0) :
    avg (fun _ => c) N = c := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  simp only [avg, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp [hn] <;> ring

private theorem avg_sum {ι : Type*} [Fintype ι] (f : ι → ℕ → ℝ) (N : ℕ) :
    avg (fun k => ∑ i, f i k) N = ∑ i, avg (f i) N := by
  classical
  simp only [avg]
  rw [Finset.sum_comm, Finset.sum_div]

private theorem centered_limits (T : Params → ℕ → ℕ)
    (hmarg : ∀ p : Params, Tendsto (avg (D T p)) atTop (𝓝 (1 / 2)))
    (hmix : ∀ p r : Params,
      Tendsto (avg (fun k => D T p k * D T r k)) atTop
        (𝓝 (1 / 4 + (Int.gcd p.val r.val : ℝ)^2 /
          (12 * (p.val : ℝ) * (r.val : ℝ)))))
    (p r : Params) :
    Tendsto (avg (E T p)) atTop (𝓝 0) ∧
      Tendsto (avg (fun k => E T p k * E T r k)) atTop
        (𝓝 ((Int.gcd p.val r.val : ℝ)^2 /
          (12 * (p.val : ℝ) * (r.val : ℝ)))) := by
  have hp := hmarg p
  have hr := hmarg r
  have hmean : Tendsto (fun N => avg (D T p) N - 1 / 2) atTop (𝓝 0) := by
    simpa only [sub_self] using hp.sub_const (1 / 2)
  have hprod := (((hmix p r).sub (hp.const_mul (1 / 2))).sub
    (hr.const_mul (1 / 2))).add_const (1 / 4)
  have hval : (1 / 4 : ℝ) + (Int.gcd p.val r.val : ℝ)^2 /
        (12 * (p.val : ℝ) * (r.val : ℝ)) - (1 / 2) * (1 / 2) -
        (1 / 2) * (1 / 2) + 1 / 4 =
      (Int.gcd p.val r.val : ℝ)^2 / (12 * (p.val : ℝ) * (r.val : ℝ)) := by ring
  rw [hval] at hprod
  constructor
  · apply hmean.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    change avg (D T p) N - 1 / 2 = avg (fun k => D T p k - 1 / 2) N
    rw [avg_sub, avg_const (1 / 2) N (Nat.ne_of_gt hN)]
  · apply hprod.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have he : (fun k => E T p k * E T r k) =
        (fun k => D T p k * D T r k - (1 / 2) * D T p k -
          (1 / 2) * D T r k + 1 / 4) := by
      funext k
      dsimp only [E]
      ring
    rw [he, avg_add, avg_sub, avg_sub, avg_const_mul, avg_const_mul,
      avg_const (1 / 4) N (Nat.ne_of_gt hN)]

private theorem weighted_product_average (T : Params → ℕ → ℕ) (S : Finset Params)
    (c : S → ℝ) (N : ℕ) :
    avg (fun k => A T S c k ^ 2) N =
      ∑ p : S, ∑ r : S, c p * c r *
        avg (fun k => E T p k * E T r k) N := by
  classical
  have he : (fun k => A T S c k ^ 2) =
      (fun k => ∑ p : S, ∑ r : S,
        c p * c r * (E T p k * E T r k)) := by
    funext k
    unfold A
    rw [pow_two, Fintype.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [he, avg_sum]
  simp_rw [avg_sum, avg_const_mul]

private theorem V_expand (S : Finset Params) (c : S → ℝ) :
    V S c = (1 / 12) * ∑ p : S, ∑ r : S,
      c p * c r * (∑ z : G S × G S, v S p z * v S r z) := by
  classical
  have he (z : G S × G S) :
      (∑ p : S, c p * v S p z)^2 =
        ∑ p : S, ∑ r : S, c p * c r * (v S p z * v S r z) := by
    rw [pow_two, Fintype.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro r _
    ring
  unfold V
  simp_rw [he]
  apply congrArg (fun x : ℝ => (1 / 12) * x)
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.mul_sum]

private theorem V_nonneg (S : Finset Params) (c : S → ℝ) : 0 ≤ V S c := by
  unfold V
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg (fun z _ => sq_nonneg _)

private theorem gram_strict (S : Finset Params) (c : S → ℝ)
    (hc : ¬ ∀ p : S, c p = 0) : 0 < V S c := by
  classical
  let supp : Finset S := Finset.univ.filter (fun p => c p ≠ 0)
  have hsupp : supp.Nonempty := by
    by_contra h
    have hempty : supp = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    apply hc
    intro p
    by_contra hp
    have hmem : p ∈ supp := by simp [supp, hp]
    simpa [hempty] using hmem
  let p₀ : S := supp.max' hsupp
  have hp₀mem : p₀ ∈ supp := Finset.max'_mem supp hsupp
  have hp₀ : c p₀ ≠ 0 := (Finset.mem_filter.mp hp₀mem).2
  let g : G S := (modulus S / p₀.val.val.toNat) • (1 : G S)
  have hdiv : p₀.val.val.toNat ∣ modulus S := nat_dvd_modulus p₀.property
  have horder : addOrderOf g = p₀.val.val.toNat := by
    dsimp only [g]
    rw [Nat.smul_one_eq_cast, ZMod.addOrderOf_coe _ (modulus_ne_zero S)]
    have hL : modulus S / p₀.val.val.toNat ∣ modulus S := Nat.div_dvd_of_dvd hdiv
    rw [Nat.gcd_eq_right hL, Nat.div_div_self hdiv (modulus_ne_zero S)]
  have hmem (r : S) : g ∈ H S r.val.val.toNat ↔ p₀.val.val.toNat ∣ r.val.val.toNat := by
    change r.val.val.toNat • g = 0 ↔ _
    rw [← addOrderOf_dvd_iff_nsmul_eq_zero, horder]
  have hterm (r : S) : c r * v S r (g, 0) =
      if r = p₀ then c p₀ / (p₀.val.val : ℝ) else 0 := by
    by_cases hr : r = p₀
    · subst r
      have hgp : g ∈ H S p₀.val.val.toNat := (hmem p₀).2 (dvd_refl _)
      simp [v, hgp, div_eq_mul_inv]
    · by_cases hd : p₀.val.val.toNat ∣ r.val.val.toNat
      · by_cases hcr : c r = 0
        · simp [hcr, hr]
        · have hle₁ : r ≤ p₀ := Finset.le_max' supp r (by simp [supp, hcr])
          have hle₂ : p₀ ≤ r := by
            have hn := Nat.le_of_dvd (param_pos_nat r.val) hd
            have hz : (p₀.val.val.toNat : ℤ) ≤ (r.val.val.toNat : ℤ) := by
              exact_mod_cast hn
            rw [param_nat_cast p₀.val, param_nat_cast r.val] at hz
            change p₀.val.val ≤ r.val.val
            exact hz
          exact (hr (le_antisymm hle₁ hle₂)).elim
      · have hgr : g ∉ H S r.val.val.toNat := (hmem r).not.mpr hd
        simp [v, hgr, hr]
  have hfeature : (∑ r : S, c r * v S r (g, 0)) = c p₀ / (p₀.val.val : ℝ) := by
    calc
      (∑ r : S, c r * v S r (g, 0)) =
          ∑ r : S, (if r = p₀ then c p₀ / (p₀.val.val : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro r _
        exact hterm r
      _ = c p₀ / (p₀.val.val : ℝ) := by simp
  have hpos : 0 < (c p₀ / (p₀.val.val : ℝ))^2 := by
    apply sq_pos_of_ne_zero
    exact div_ne_zero hp₀ (param_pos p₀.val).ne'
  have hsingle :
      (∑ p : S, c p * v S p (g, 0))^2 ≤
        ∑ z : G S × G S, (∑ p : S, c p * v S p z)^2 :=
    Finset.single_le_sum
      (f := fun z : G S × G S => (∑ p : S, c p * v S p z)^2)
      (fun z _ => sq_nonneg _) (Finset.mem_univ (g, (0 : G S)))
  rw [hfeature] at hsingle
  have h12 : 0 < (1 / 12 : ℝ) := by norm_num
  have hscaled := mul_le_mul_of_nonneg_left hsingle h12.le
  unfold V
  exact lt_of_lt_of_le (mul_pos h12 hpos) hscaled

/-- One global actual count-threshold family realizes every finite covariance
    matrix as the ordinary counting Gram matrix of scaled torsion-subgroup-square
    indicators in `ZMod (∏ p)`. The finite set is fixed before the Cesaro limit. -/
theorem actual_square_displacement_cyclic_gram :
    ∃ T : Params → ℕ → ℕ,
      (∀ (p : Params) (k : ℕ), bracketSC p.val (qAt k) (T p k) ∧
        ∀ t : ℕ, originalSC p.val (qAt k) t → t = T p k) ∧
      (∀ p : Params,
        Tendsto (avg (D T p)) atTop (𝓝 (1 / 2)) ∧
        Tendsto (avg (fun k => D T p k ^ 2)) atTop (𝓝 (1 / 3))) ∧
      (∀ p r : Params,
        Tendsto (avg (fun k => D T p k * D T r k)) atTop
          (𝓝 (1 / 4 + (Int.gcd p.val r.val : ℝ)^2 /
            (12 * (p.val : ℝ) * (r.val : ℝ)))) ∧
        Tendsto (fun N : ℕ => avg (fun k => D T p k * D T r k) N -
          avg (D T p) N * avg (D T r) N) atTop
          (𝓝 ((Int.gcd p.val r.val : ℝ)^2 /
            (12 * (p.val : ℝ) * (r.val : ℝ))))) ∧
      ∀ (S : Finset Params) (c : S → ℝ),
        (∀ p r : S, (∑ z : G S × G S, v S p z * v S r z) =
          (Int.gcd p.val r.val : ℝ)^2 /
            ((p.val : ℝ) * (r.val : ℝ))) ∧
        Tendsto (avg (A T S c)) atTop (𝓝 0) ∧
        Tendsto (avg (fun k => A T S c k ^ 2)) atTop (𝓝 (V S c)) ∧
        Tendsto (fun N => avg (fun k => A T S c k ^ 2) N -
          (avg (A T S c) N)^2) atTop (𝓝 (V S c)) ∧
        0 ≤ V S c ∧ (V S c = 0 ↔ ∀ p : S, c p = 0) := by
  classical
  obtain ⟨T, hT, hmarg, hpair⟩ := actual_square_displacement_actual_moments
  refine ⟨T, hT, hmarg, hpair, ?_⟩
  intro S c
  have hcent (p r : S) := centered_limits T (fun q => (hmarg q).1)
    (fun q s => (hpair q s).1) p.val r.val
  have hgram : ∀ p r : S, (∑ z : G S × G S, v S p z * v S r z) =
      (Int.gcd p.val r.val : ℝ)^2 /
        ((p.val : ℝ) * (r.val : ℝ)) := by
    intro p r
    exact gram_pair S p r
  have hmean : Tendsto (avg (A T S c)) atTop (𝓝 0) := by
    have hh := tendsto_finsetSum (Finset.univ : Finset S)
      (fun p _ => (hcent p p).1.const_mul (c p))
    have hh' : Tendsto (fun N => ∑ p : S, c p * avg (E T p) N)
        atTop (𝓝 0) := by
      simpa only [mul_zero, Finset.sum_const_zero] using hh
    apply hh'.congr'
    exact Eventually.of_forall (fun N => by
      change (∑ p : S, c p * avg (E T p) N) =
        avg (fun k => ∑ p : S, c p * E T p k) N
      rw [avg_sum]
      simp_rw [avg_const_mul])
  have hsecond : Tendsto (avg (fun k => A T S c k ^ 2)) atTop (𝓝 (V S c)) := by
    have hh := tendsto_finsetSum (Finset.univ : Finset S)
      (fun p _ => tendsto_finsetSum (Finset.univ : Finset S)
        (fun r _ => (hcent p r).2.const_mul (c p * c r)))
    have hlim : Tendsto (fun N => ∑ p : S, ∑ r : S,
        c p * c r * avg (fun k => E T p k * E T r k) N) atTop
        (𝓝 (∑ p : S, ∑ r : S,
          c p * c r * ((Int.gcd p.val r.val : ℝ)^2 /
            (12 * (p.val : ℝ) * (r.val : ℝ))))) := by
      exact hh
    have hlimval :
        (∑ p : S, ∑ r : S,
          c p * c r * ((Int.gcd p.val r.val : ℝ)^2 /
            (12 * (p.val : ℝ) * (r.val : ℝ)))) = V S c := by
      rw [V_expand, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [hgram p r]
      field_simp [(param_pos p.val).ne', (param_pos r.val).ne'] <;> ring
    rw [hlimval] at hlim
    exact hlim.congr' (Eventually.of_forall fun N =>
      (weighted_product_average T S c N).symm)
  have hvar : Tendsto (fun N => avg (fun k => A T S c k ^ 2) N -
      (avg (A T S c) N)^2) atTop (𝓝 (V S c)) := by
    simpa only [pow_two, mul_zero, sub_zero] using hsecond.sub (hmean.mul hmean)
  exact ⟨hgram, hmean, hsecond, hvar, V_nonneg S c,
    ⟨fun hz => by
      by_contra hc
      exact (gram_strict S c hc).ne' hz,
      fun hc => by simp [V, hc]⟩⟩

end D5.S3.FiniteGroups.BajnokBeattySquareDisplacementCyclicGram
