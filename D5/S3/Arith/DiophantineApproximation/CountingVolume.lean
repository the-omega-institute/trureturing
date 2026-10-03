/- GID: D5/S3/Arith/DiophantineApproximation/CountingVolume
   generality: G
   mirror-B: D5/B/S3/Arith/DiophantineApproximation/CountingVolume
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The volume of a cube-simplex intersection has an exponential upper bound. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section

noncomputable section

open Set
open scoped Pointwise ENNReal Nat

namespace Nat

/-- `6 ^ k * k ! ≤ (2 k + 1)!`: the termwise comparison between the series of `sinh` and the
series of `exp (u ^ 2 / 6)`. -/
theorem six_pow_mul_factorial_le (k : ℕ) : 6 ^ k * k ! ≤ (2 * k + 1)! := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e1 : 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 := by ring
    rw [e1, Nat.factorial_succ, Nat.factorial_succ, pow_succ, Nat.factorial_succ]
    calc 6 ^ k * 6 * ((k + 1) * k !)
        = 6 * (k + 1) * (6 ^ k * k !) := by ring
      _ ≤ (2 * k + 1 + 1 + 1) * (2 * k + 1 + 1) * (2 * k + 1)! :=
          Nat.mul_le_mul (by nlinarith) ih
      _ = (2 * k + 1 + 1 + 1) * ((2 * k + 1 + 1) * (2 * k + 1)!) := by ring

end Nat

namespace Real

/-- **`sinh u ≤ u exp (u ² / 6)`** for `u ≥ 0`. Comparing the two power series term by term,
this is `6 ^ k * k ! ≤ (2 k + 1)!`. -/
theorem sinh_le_mul_exp_sq_div_six {u : ℝ} (hu : 0 ≤ u) : sinh u ≤ u * exp (u ^ 2 / 6) := by
  have hexp : ∀ v : ℝ, HasSum (fun n : ℕ ↦ v ^ n / n !) (exp v) := fun v ↦ by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp v
  have hAB : HasSum (fun n : ℕ ↦ (u ^ n / (n ! : ℝ) - (-u) ^ n / (n ! : ℝ)) / 2) (sinh u) := by
    rw [Real.sinh_eq]; exact ((hexp u).sub (hexp (-u))).div_const 2
  have hinj : Function.Injective (fun k : ℕ ↦ 2 * k + 1) := fun a b h ↦ by
    dsimp only at h; omega
  have hzero : ∀ n ∉ Set.range (fun k : ℕ ↦ 2 * k + 1),
      (u ^ n / (n ! : ℝ) - (-u) ^ n / (n ! : ℝ)) / 2 = 0 := by
    intro n hn
    have hn' : Even n := by
      rcases Nat.even_or_odd n with h | h
      · exact h
      · obtain ⟨k, hk⟩ := h
        exact absurd (⟨k, by dsimp only; omega⟩ : n ∈ Set.range (fun k : ℕ ↦ 2 * k + 1)) hn
    rw [hn'.neg_pow]
    ring
  rw [← hinj.hasSum_iff hzero] at hAB
  have hodd : HasSum (fun k : ℕ ↦ u ^ (2 * k + 1) / ((2 * k + 1)! : ℝ)) (sinh u) := by
    refine hAB.congr_fun fun k ↦ ?_
    have : Odd (2 * k + 1) := ⟨k, by ring⟩
    simp only [Function.comp_apply, this.neg_pow]
    ring
  have hC : HasSum (fun k : ℕ ↦ u * ((u ^ 2 / 6) ^ k / (k ! : ℝ))) (u * exp (u ^ 2 / 6)) :=
    (hexp (u ^ 2 / 6)).mul_left u
  refine hasSum_le (fun k ↦ ?_) hodd hC
  have h1 : u * ((u ^ 2 / 6) ^ k / (k ! : ℝ)) = u ^ (2 * k + 1) / (6 ^ k * (k ! : ℝ)) := by
    rw [div_pow, ← pow_mul]
    field_simp
    ring
  have h2 : ((6 ^ k * k ! : ℕ) : ℝ) ≤ (((2 * k + 1)! : ℕ) : ℝ) := by
    exact_mod_cast Nat.six_pow_mul_factorial_le k
  push_cast at h2
  rw [h1]
  gcongr

end Real

namespace MeasureTheory

variable {m : ℕ}

/-- The part of the unit cube below the hyperplane `∑ x j = t`, Bombieri–Gubler's `𝒱_m(t)`. -/
def cubeSimplex (m : ℕ) (t : ℝ) : Set (Fin m → ℝ) :=
  (univ.pi fun _ ↦ Icc (0 : ℝ) 1) ∩ {x | ∑ j, x j ≤ t}

/-- The volume `V_m(t)` of `MeasureTheory.cubeSimplex`. -/
def cubeSimplexVolume (m : ℕ) (t : ℝ) : ℝ := (volume (cubeSimplex m t)).toReal

/-- **The region has positive volume as soon as `t` is positive**: it contains the cube of side
`min 1 (t / m)`, which is nondegenerate. This is what makes the hypothesis
`r * ∑ k, V_m (t k) < 1` of Layer 2.6 a genuine restriction on the number of points. -/
theorem cubeSimplexVolume_pos (m : ℕ) {t : ℝ} (ht : 0 < t) : 0 < cubeSimplexVolume m t := by
  let nativeSource59 := (open Set in (open scoped Pointwise ENNReal Nat in (fun (m : ℕ) (t : ℝ) => (show MeasureTheory.MeasureSpace.volume (MeasureTheory.cubeSimplex m t) ≠ ⊤ from ne_top_of_le_ne_top (show MeasureTheory.MeasureSpace.volume (univ.pi fun _ : Fin m ↦ Icc (0 : ℝ) 1) ≠ ⊤ from by
        rw [MeasureTheory.volume_pi_pi]
        simp)
      (MeasureTheory.measure_mono ((fun m t ↦ (show MeasureTheory.cubeSimplex m t ⊆ Set.univ.pi (fun _ ↦ Set.Icc (0 : ℝ) 1) from
        Set.inter_subset_left)) m t))))))
  set c : ℝ := min 1 (t / m) with hcdef
  have hc0 : 0 ≤ c := le_min zero_le_one (by positivity)
  have hsub : (univ.pi fun _ : Fin m ↦ Icc (0 : ℝ) c) ⊆ cubeSimplex m t := by
    intro x hx
    simp only [mem_univ_pi, mem_Icc] at hx
    refine (show x ∈ cubeSimplex m t ↔
        (∀ j, 0 ≤ (x) j ∧ (x) j ≤ 1) ∧ ∑ j, (x) j ≤ t from by
      simp [cubeSimplex, Pi.le_def, forall_and]).mpr ⟨fun j ↦ ⟨(hx j).1, (hx j).2.trans (min_le_left _ _)⟩, ?_⟩
    have hle : ∑ j, x j ≤ (m : ℝ) * c := by
      calc ∑ j, x j ≤ ∑ _j : Fin m, c := Finset.sum_le_sum fun j _ ↦ (hx j).2
        _ = (m : ℝ) * c := by simp
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [Finset.univ_eq_empty, Finset.sum_empty]
      exact ht.le
    · have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
      have : (m : ℝ) * c ≤ t := by
        have : c ≤ t / m := min_le_right _ _
        calc (m : ℝ) * c ≤ (m : ℝ) * (t / m) := by nlinarith
          _ = t := by field_simp
      linarith
  have hvol : volume (univ.pi fun _ : Fin m ↦ Icc (0 : ℝ) c) = ENNReal.ofReal c ^ m := by
    rw [volume_pi_pi]
    simp [Real.volume_Icc]
  have hne : (ENNReal.ofReal c) ^ m ≠ 0 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · refine pow_ne_zero _ ?_
      have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, hcdef]
      exact lt_min zero_lt_one (by positivity)
  rw [cubeSimplexVolume, ENNReal.toReal_pos_iff]
  refine ⟨lt_of_lt_of_le (pos_iff_ne_zero.mpr ?_) (measure_mono hsub),
    lt_top_iff_ne_top.mpr (nativeSource59 m t)⟩
  rw [hvol]
  exact hne

/-- The lattice points `i` of the box `∏ j, [0, d j]` with `∑ j, i j / d j ≤ t`: the conditions
that Bombieri–Gubler's auxiliary polynomial has to satisfy. -/
def latticePoints (d : Fin m → ℕ) (t : ℝ) : Finset (Fin m → ℕ) :=
  {i ∈ Fintype.piFinset fun j ↦ Finset.range (d j + 1) | ∑ j, (i j : ℝ) / (d j : ℝ) ≤ t}

/-- The half-open box of side `1 / d j` attached to a lattice point. -/
def latticeBox (d : Fin m → ℕ) (i : Fin m → ℕ) : Set (Fin m → ℝ) :=
  univ.pi fun j ↦ Ico ((i j : ℝ) / (d j : ℝ)) (((i j : ℝ) + 1) / (d j : ℝ))

/-- **Lattice points, the upper bound** (Bombieri–Gubler 6.3.4): at most
`V_m(t) (1 + max 1 t⁻¹ ∑ j, 1 / d j) ^ m ∏ d j` of them do. -/
theorem card_latticePoints_le {d : Fin m → ℕ} (hd : ∀ j, 0 < d j) {t : ℝ} (ht : 0 < t) :
    ((latticePoints d t).card : ℝ)
      ≤ cubeSimplexVolume m t * (1 + max 1 t⁻¹ * ∑ j, (d j : ℝ)⁻¹) ^ m * ∏ j, (d j : ℝ) := by
  let nativeSource54 := (open Set in (open scoped Pointwise ENNReal Nat in (fun {m : ℕ} {d : Fin m → ℕ} (hd : ∀ j, 0 < d j) {i : Fin m → ℕ} {x : Fin m → ℝ} => (show x ∈ MeasureTheory.latticeBox d i ↔ ∀ j, (i j : ℝ) ≤ x j * d j ∧ x j * d j < (i j : ℝ) + 1 from by
    have hpos : ∀ j, (0 : ℝ) < d j := fun j ↦ by exact_mod_cast hd j
    simp only [MeasureTheory.latticeBox, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Ico,
      div_le_iff₀ (hpos _), lt_div_iff₀ (hpos _)]))))
  let nativeSource55 := (open Set in (open scoped Pointwise ENNReal Nat in (fun {m : ℕ} {d : Fin m → ℕ} (hd : ∀ j, 0 < d j) {i i' : Fin m → ℕ}
      {x : Fin m → ℝ} (h : x ∈ MeasureTheory.latticeBox d i) (h' : x ∈ MeasureTheory.latticeBox d i') => (show i = i' from by
    rw [nativeSource54 hd] at h h'
    funext j
    have h1 : (i j : ℝ) < (i' j : ℝ) + 1 := lt_of_le_of_lt (h j).1 (h' j).2
    have h2 : (i' j : ℝ) < (i j : ℝ) + 1 := lt_of_le_of_lt (h' j).1 (h j).2
    have h1' : i j < i' j + 1 := by exact_mod_cast h1
    have h2' : i' j < i j + 1 := by exact_mod_cast h2
    omega))))
  let nativeSource58 := (open Set in (open scoped Pointwise ENNReal Nat in (fun {m : ℕ} {d : Fin m → ℕ} (hd : ∀ j, 0 < d j) (s : Set (Fin m → ℕ)) => (show s.PairwiseDisjoint (MeasureTheory.latticeBox d) from fun i _ i' _ hne ↦ by
    rw [Function.onFun, Set.disjoint_left]
    exact fun x hx hx' ↦ hne (nativeSource55 hd hx hx')))))
  let nativeSource59 := (open Set in (open scoped Pointwise ENNReal Nat in (fun (m : ℕ) (t : ℝ) => (show MeasureTheory.MeasureSpace.volume (MeasureTheory.cubeSimplex m t) ≠ ⊤ from ne_top_of_le_ne_top (show MeasureTheory.MeasureSpace.volume (univ.pi fun _ : Fin m ↦ Icc (0 : ℝ) 1) ≠ ⊤ from by
        rw [MeasureTheory.volume_pi_pi]
        simp)
      (MeasureTheory.measure_mono ((fun m t ↦ (show MeasureTheory.cubeSimplex m t ⊆ Set.univ.pi (fun _ ↦ Set.Icc (0 : ℝ) 1) from
        Set.inter_subset_left)) m t))))))
  let nativeSource60 := (open Set in (open scoped Pointwise ENNReal Nat in (fun {m : ℕ} {d : Fin m → ℕ} (hd : ∀ j, 0 < d j) (i : Fin m → ℕ) => (show MeasureTheory.MeasureSpace.volume (MeasureTheory.latticeBox d i) = ENNReal.ofReal (∏ j, (d j : ℝ))⁻¹ from by
    have hpos : ∀ j, (0 : ℝ) < d j := fun j ↦ by exact_mod_cast hd j
    rw [MeasureTheory.latticeBox, MeasureTheory.volume_pi_pi]
    have : ∀ j : Fin m, MeasureTheory.MeasureSpace.volume (Set.Ico ((i j : ℝ) / (d j : ℝ)) (((i j : ℝ) + 1) / (d j : ℝ)))
        = ENNReal.ofReal ((d j : ℝ))⁻¹ := by
      intro j
      rw [Real.volume_Ico, div_sub_div_same, add_sub_cancel_left, one_div]
    rw [Finset.prod_congr rfl fun j _ ↦ this j, ← ENNReal.ofReal_prod_of_nonneg
      (fun j _ ↦ by positivity), ← Finset.prod_inv_distrib]))))
  have hpos : ∀ j, (0 : ℝ) < d j := fun j ↦ by exact_mod_cast hd j
  have hprod : (0 : ℝ) < ∏ j, (d j : ℝ) := Finset.prod_pos fun j _ ↦ hpos j
  obtain ⟨del, hdel⟩ : ∃ del, del = ∑ j, (d j : ℝ)⁻¹ := ⟨_, rfl⟩
  obtain ⟨rho, hrho⟩ : ∃ rho, rho = max 1 t⁻¹ * del := ⟨_, rfl⟩
  have hdel0 : 0 ≤ del := hdel ▸ Finset.sum_nonneg fun j _ ↦ by positivity
  have hmax1 : (1 : ℝ) ≤ max 1 t⁻¹ := le_max_left _ _
  have hrho0 : 0 ≤ rho := hrho ▸ mul_nonneg (by linarith) hdel0
  have hdelrho : del ≤ rho := by rw [hrho]; nlinarith
  have hdrho : ∀ j, (d j : ℝ)⁻¹ ≤ rho := fun j ↦ le_trans
    (hdel ▸ Finset.single_le_sum (f := fun j ↦ (d j : ℝ)⁻¹) (fun j _ ↦ by positivity)
      (Finset.mem_univ j)) hdelrho
  have htrho : del ≤ t * rho := by
    have h1 : t⁻¹ * del ≤ max 1 t⁻¹ * del := mul_le_mul_of_nonneg_right (le_max_right _ _) hdel0
    calc del = t * (t⁻¹ * del) := by field_simp
      _ ≤ t * (max 1 t⁻¹ * del) := mul_le_mul_of_nonneg_left h1 ht.le
      _ = t * rho := by rw [hrho]
  have h1rho : (0 : ℝ) < 1 + rho := by linarith
  -- the boxes fit, after shrinking by `1 + rho`, inside the region
  have hsub : (⋃ i ∈ latticePoints d t, latticeBox d i) ⊆ (1 + rho) • cubeSimplex m t := by
    intro x hx
    simp only [Set.mem_iUnion, exists_prop] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    rw [(show i ∈ MeasureTheory.latticePoints d t ↔ (∀ j, i j ≤ d j) ∧
      ∑ j, (i j : ℝ) / (d j : ℝ) ≤ t from by simp [MeasureTheory.latticePoints])] at hi
    rw [nativeSource54 hd] at hxi
    have hxl : ∀ j, (i j : ℝ) / (d j : ℝ) ≤ x j := fun j ↦ (div_le_iff₀ (hpos j)).2 (hxi j).1
    have hxu : ∀ j, x j < (i j : ℝ) / (d j : ℝ) + (d j : ℝ)⁻¹ := fun j ↦ by
      have h := (lt_div_iff₀ (hpos j)).2 (hxi j).2
      rwa [add_div, one_div] at h
    have hxnn : ∀ j, 0 ≤ x j := fun j ↦
      le_trans (by positivity : (0 : ℝ) ≤ (i j : ℝ) / (d j : ℝ)) (hxl j)
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ h1rho.ne']
    rw [(show ((1 + rho)⁻¹ • x) ∈ cubeSimplex m t ↔
        (∀ j, 0 ≤ (((1 + rho)⁻¹ • x)) j ∧ (((1 + rho)⁻¹ • x)) j ≤ 1) ∧ ∑ j, (((1 + rho)⁻¹ • x)) j ≤ t from by
      simp [cubeSimplex, Pi.le_def, forall_and])]
    refine ⟨fun j ↦ ⟨?_, ?_⟩, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg (by positivity) (hxnn j)
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [inv_mul_le_iff₀ h1rho, mul_one]
      have h1 : (i j : ℝ) / (d j : ℝ) ≤ 1 :=
        (div_le_one (hpos j)).2 (by exact_mod_cast hi.1 j)
      linarith [hxu j, hdrho j]
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      rw [inv_mul_le_iff₀ h1rho]
      have hsum : ∑ j, x j ≤ (∑ j, (i j : ℝ) / (d j : ℝ)) + del := by
        rw [hdel, ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun j _ ↦ (hxu j).le
      nlinarith [hi.2, htrho]
  -- volumes
  have hunion : volume (⋃ i ∈ latticePoints d t, latticeBox d i)
      = ((latticePoints d t).card : ℝ≥0∞) * ENNReal.ofReal (∏ j, (d j : ℝ))⁻¹ := by
    rw [measure_biUnion_finset (nativeSource58 hd _)
      (fun i _ ↦ (fun d i ↦ (show MeasurableSet (MeasureTheory.latticeBox d i) from
      MeasurableSet.univ_pi fun _ ↦ measurableSet_Ico)) d i),
      Finset.sum_congr rfl fun i _ ↦ nativeSource60 hd i, Finset.sum_const, nsmul_eq_mul]
  have hsmulvol : volume ((1 + rho) • cubeSimplex m t)
      = ENNReal.ofReal ((1 + rho) ^ m) * volume (cubeSimplex m t) := by
    rw [Measure.addHaar_smul]
    simp [abs_of_nonneg (pow_nonneg h1rho.le m)]
  have hle : volume (⋃ i ∈ latticePoints d t, latticeBox d i)
      ≤ volume ((1 + rho) • cubeSimplex m t) := measure_mono hsub
  rw [hunion, hsmulvol] at hle
  have hle' := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by finiteness) (nativeSource59 m t)) hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at hle'
  rw [← hdel, ← hrho]
  calc ((latticePoints d t).card : ℝ)
      = ((latticePoints d t).card : ℝ) * (∏ j, (d j : ℝ))⁻¹ * ∏ j, (d j : ℝ) := by
        field_simp
    _ ≤ (1 + rho) ^ m * cubeSimplexVolume m t * ∏ j, (d j : ℝ) := by
        exact mul_le_mul_of_nonneg_right hle' hprod.le
    _ = cubeSimplexVolume m t * (1 + rho) ^ m * ∏ j, (d j : ℝ) := by ring

/-- **The Chernoff bound in `m` coordinates.** For a nonnegative weight `g` on the line, the
integral of `∏ j, g (x j)` over the half-space `∑ j, x j ≤ s` is at most `exp (λ s)` times the
`m`-th power of the one-variable exponential moment `∫ exp (-λ x) g x`. Both estimates of this
file are this lemma at a different `g`: the indicator of `[0, 1]`, and the density of one
coordinate of a point of the standard simplex. -/
theorem setIntegral_prod_le_exp_mul_pow {g : ℝ → ℝ} (hg0 : ∀ x, 0 ≤ g x) (hg : Integrable g)
    {lam : ℝ} (hlam : 0 ≤ lam) (hgl : Integrable fun x ↦ Real.exp (-(lam * x)) * g x)
    (m : ℕ) (s : ℝ) :
    ∫ x in {y : Fin m → ℝ | ∑ j, y j ≤ s}, ∏ j, g (x j)
      ≤ Real.exp (lam * s) * (∫ x, Real.exp (-(lam * x)) * g x) ^ m := by
  have hS : MeasurableSet {y : Fin m → ℝ | ∑ j, y j ≤ s} :=
    measurableSet_le (by fun_prop) measurable_const
  have hvol : (volume : Measure (Fin m → ℝ)) = Measure.pi fun _ ↦ volume := volume_pi
  have hint1 : Integrable fun x : Fin m → ℝ ↦ ∏ j, g (x j) := by
    rw [hvol]; exact Integrable.fintype_prod fun _ ↦ hg
  have hint2 : Integrable fun x : Fin m → ℝ ↦ ∏ j, Real.exp (-(lam * x j)) * g (x j) := by
    rw [hvol]; exact Integrable.fintype_prod fun _ ↦ hgl
  rw [← integral_indicator hS]
  calc ∫ x : Fin m → ℝ, Set.indicator {y : Fin m → ℝ | ∑ j, y j ≤ s} (fun x ↦ ∏ j, g (x j)) x
      ≤ ∫ x : Fin m → ℝ, Real.exp (lam * s) * ∏ j, Real.exp (-(lam * x j)) * g (x j) := by
        refine integral_mono (hint1.indicator hS) (hint2.const_mul _) fun x ↦ ?_
        have hprodnn : 0 ≤ ∏ j, g (x j) := Finset.prod_nonneg fun j _ ↦ hg0 _
        have hfac : ∏ j, Real.exp (-(lam * x j)) * g (x j)
            = Real.exp (-(lam * ∑ j, x j)) * ∏ j, g (x j) := by
          rw [Finset.prod_mul_distrib, ← Real.exp_sum]
          congr 1
          simp [Finset.mul_sum]
        rcases le_or_gt (∑ j, x j) s with h | h
        · rw [Set.indicator_of_mem (show x ∈ {y : Fin m → ℝ | ∑ j, y j ≤ s} from h), hfac,
            ← mul_assoc, ← Real.exp_add]
          refine le_mul_of_one_le_left hprodnn (Real.one_le_exp ?_)
          have h2 := mul_nonneg hlam (sub_nonneg.2 h)
          rw [mul_sub] at h2
          linarith
        · rw [Set.indicator_of_notMem
            (show x ∉ {y : Fin m → ℝ | ∑ j, y j ≤ s} from not_le.2 h), hfac]
          positivity
    _ = Real.exp (lam * s) * ∫ x : Fin m → ℝ, ∏ j, Real.exp (-(lam * x j)) * g (x j) :=
        integral_const_mul _ _
    _ = Real.exp (lam * s) * (∫ x, Real.exp (-(lam * x)) * g x) ^ m := by
        rw [integral_fintype_prod_volume_eq_pow fun x ↦ Real.exp (-(lam * x)) * g x,
          Fintype.card_fin]

/-- **The tail estimate** (Bombieri–Gubler, Lemma 6.3.5): `V_m((1/2 - ε) m) ≤ exp (-6 m ε²)`.
The exponent `-6 m ε²` comes out of the Chernoff bound at `λ = 12 ε`. -/
theorem cubeSimplexVolume_le_exp_neg (m : ℕ) {eps : ℝ} (heps : 0 ≤ eps) :
    cubeSimplexVolume m ((1 / 2 - eps) * m) ≤ Real.exp (-(6 * m * eps ^ 2)) := by
  let nativeSource51 := (open Set in (open scoped Pointwise ENNReal Nat in (fun (m : ℕ) (x : Fin m → ℝ) => (show ∏ j, Set.indicator (Icc (0 : ℝ) 1) (1 : ℝ → ℝ) (x j)
        = Set.indicator (univ.pi fun _ : Fin m ↦ Icc (0 : ℝ) 1) (1 : (Fin m → ℝ) → ℝ) x from by
    by_cases h : ∀ j, x j ∈ Icc (0 : ℝ) 1
    · rw [Set.indicator_of_mem (show x ∈ univ.pi fun _ : Fin m ↦ Icc (0 : ℝ) 1 from
        fun j _ ↦ h j)]
      exact Finset.prod_eq_one fun j _ ↦ Set.indicator_of_mem (h j) _
    · push Not at h
      obtain ⟨j, hj⟩ := h
      have hx : x ∉ univ.pi fun _ : Fin m ↦ Icc (0 : ℝ) 1 := fun hall ↦ hj (hall j (mem_univ j))
      rw [Set.indicator_of_notMem hx]
      exact Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem hj _)))))
  let nativeSource52 := (open Set in (open scoped Pointwise ENNReal Nat in (fun (m : ℕ) (t : ℝ) => (show cubeSimplexVolume m t
        = ∫ x in {y : Fin m → ℝ | ∑ j, y j ≤ t},
            ∏ j, Set.indicator (Set.Icc (0 : ℝ) 1) (1 : ℝ → ℝ) (x j) from by
    have hS : MeasurableSet {y : Fin m → ℝ | ∑ j, y j ≤ t} :=
      measurableSet_le (by fun_prop) measurable_const
    rw [← MeasureTheory.integral_indicator hS]
    simp_rw [nativeSource51]
    rw [Set.indicator_indicator, MeasureTheory.integral_indicator_one (hS.inter
      (MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc)), measureReal_def, cubeSimplexVolume,
      MeasureTheory.cubeSimplex, Set.inter_comm]))))
  let nativeSource53 := (open Set in (open scoped Pointwise ENNReal Nat in (fun (m : ℕ) (t : ℝ) => (show MeasureTheory.cubeSimplexVolume m t ≤ 1 from by
    rw [MeasureTheory.cubeSimplexVolume, ← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top
      ((MeasureTheory.measure_mono ((fun m t ↦ (show MeasureTheory.cubeSimplex m t ⊆ Set.univ.pi (fun _ ↦ Set.Icc (0 : ℝ) 1) from
        Set.inter_subset_left)) m t)).trans_eq (show MeasureTheory.MeasureSpace.volume (univ.pi fun _ : Fin m ↦ Icc (0 : ℝ) 1) = 1 from by
        rw [MeasureTheory.volume_pi_pi]
        simp))))))
  let nativeSource56 := (open Set in (open scoped Pointwise ENNReal Nat in (fun (lam : ℝ) => (show MeasureTheory.Integrable fun x ↦ Real.exp (-(lam * x)) * Set.indicator (Icc (0 : ℝ) 1) (1 : ℝ → ℝ) x from by
    have : (fun x ↦ Real.exp (-(lam * x)) * Set.indicator (Icc (0 : ℝ) 1) (1 : ℝ → ℝ) x)
        = Set.indicator (Icc (0 : ℝ) 1) fun x ↦ Real.exp (-(lam * x)) := by
      funext x
      by_cases hx : x ∈ Icc (0 : ℝ) 1 <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
    rw [this]
    exact (fun {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Set.Icc a b)) ↦
        hf.integrableOn_Icc.integrable_indicator measurableSet_Icc) (by fun_prop)))))
  let nativeSource57 := (open Set in (open scoped Pointwise ENNReal Nat in (fun {lam : ℝ} (hlam : lam ≠ 0) => (show ∫ x, Real.exp (-(lam * x)) * Set.indicator (Icc (0 : ℝ) 1) (1 : ℝ → ℝ) x
        = (1 - Real.exp (-lam)) / lam from by
    have hrw : (fun x ↦ Real.exp (-(lam * x)) * Set.indicator (Icc (0 : ℝ) 1) (1 : ℝ → ℝ) x)
        = Set.indicator (Icc (0 : ℝ) 1) fun x ↦ Real.exp (-lam * x) := by
      funext x
      by_cases hx : x ∈ Icc (0 : ℝ) 1 <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx, neg_mul]
    rw [hrw, MeasureTheory.integral_indicator measurableSet_Icc, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_comp_mul_left (fun x ↦ Real.exp x) (neg_ne_zero.2 hlam)]
    simp only [MulZeroClass.mul_zero, mul_one, integral_exp, Real.exp_zero, smul_eq_mul]
    field_simp
    ring))))
  rcases eq_or_lt_of_le heps with h | h
  · rw [show -(6 * (m : ℝ) * eps ^ 2) = 0 by rw [← h]; ring, Real.exp_zero]
    exact nativeSource53 _ _
  · have hlam : (0 : ℝ) < 12 * eps := by linarith
    have hmom := setIntegral_prod_le_exp_mul_pow
      (g := Set.indicator (Icc (0 : ℝ) 1) (1 : ℝ → ℝ))
      (Set.indicator_nonneg fun y _ ↦ zero_le_one) (show Integrable (Set.indicator (Icc (0 : ℝ) 1) (1 : ℝ → ℝ)) from by
        have hc : ContinuousOn (1 : ℝ → ℝ) (Icc (0 : ℝ) 1) := by fun_prop
        exact hc.integrableOn_Icc.integrable_indicator measurableSet_Icc)
      hlam.le (nativeSource56 _) m ((1 / 2 - eps) * m)
    rw [← nativeSource52,
      nativeSource57 hlam.ne'] at hmom
    have hone : Real.exp (-(12 * eps)) ≤ 1 := by
      have := Real.exp_le_exp.2 (show -(12 * eps) ≤ 0 by linarith)
      rwa [Real.exp_zero] at this
    have hbase : (0 : ℝ) ≤ (1 - Real.exp (-(12 * eps))) / (12 * eps) :=
      div_nonneg (by linarith) hlam.le
    have hstep : (1 - Real.exp (-(12 * eps))) / (12 * eps)
        ≤ Real.exp (-((12 * eps) / 2) + (12 * eps) ^ 2 / 24) := by
      have hs := Real.sinh_le_mul_exp_sq_div_six (u := (12 * eps) / 2) (by linarith)
      rw [Real.sinh_eq, show ((12 * eps) / 2) ^ 2 / 6 = (12 * eps) ^ 2 / 24 by ring] at hs
      have h2 : Real.exp ((12 * eps) / 2) - Real.exp (-((12 * eps) / 2))
          ≤ (12 * eps) * Real.exp ((12 * eps) ^ 2 / 24) := by linarith
      have h3 := mul_le_mul_of_nonneg_right h2 (Real.exp_pos (-((12 * eps) / 2))).le
      have e1 : (Real.exp ((12 * eps) / 2) - Real.exp (-((12 * eps) / 2)))
          * Real.exp (-((12 * eps) / 2)) = 1 - Real.exp (-(12 * eps)) := by
        rw [sub_mul, ← Real.exp_add, ← Real.exp_add,
          show (12 * eps) / 2 + -((12 * eps) / 2) = 0 by ring,
          show -((12 * eps) / 2) + -((12 * eps) / 2) = -(12 * eps) by ring,
          Real.exp_zero]
      have e2 : (12 * eps) * Real.exp ((12 * eps) ^ 2 / 24)
          * Real.exp (-((12 * eps) / 2))
          = (12 * eps) * Real.exp (-((12 * eps) / 2) + (12 * eps) ^ 2 / 24) := by
        rw [mul_assoc, ← Real.exp_add, add_comm]
      rw [e1, e2] at h3
      apply (div_le_iff₀ hlam).mpr
      nlinarith [h3]
    refine hmom.trans ?_
    calc Real.exp (12 * eps * ((1 / 2 - eps) * m))
            * ((1 - Real.exp (-(12 * eps))) / (12 * eps)) ^ m
        ≤ Real.exp (12 * eps * ((1 / 2 - eps) * m))
            * Real.exp (-((12 * eps) / 2) + (12 * eps) ^ 2 / 24) ^ m := by gcongr
      _ = Real.exp (-(6 * m * eps ^ 2)) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]
          congr 1
          ring

end MeasureTheory

end

end
