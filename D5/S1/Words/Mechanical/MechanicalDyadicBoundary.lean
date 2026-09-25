/- GID: D5/S1/Words/Mechanical/MechanicalDyadicBoundary
   generality: G
   mirror-B: D5/B/S1/Words/Mechanical/MechanicalDyadicBoundary
   mirror-E: none(waiver:actual-mechanical-dyadic-boundary)
   anchors: []
   utility: none
   digest: Dyadic lower slopes converge in precision but miss an exact mechanical boundary bit. -/

import D5.S1.Words.Mechanical.MechanicalSlopeSensitivity
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S1.Words.Mechanical.MechanicalDyadicBoundary

open Finset Filter
open scoped Topology
open D5.S1.Words.Mechanical

def dyadicLower (alpha : ℝ) (p : ℕ) : ℝ :=
  (⌊((2 ^ p : ℕ) : ℝ) * alpha⌋ : ℝ) / ((2 ^ p : ℕ) : ℝ)

def dyadicUpper (alpha : ℝ) (p : ℕ) : ℝ :=
  (⌈((2 ^ p : ℕ) : ℝ) * alpha⌉ : ℝ) / ((2 ^ p : ℕ) : ℝ)

/-- Every finite lower binary approximation misses the exact boundary bit,
despite its error being strictly less than the requested binary unit. -/
theorem dyadic_lower_boundary_mismatch
    (alpha : ℝ) (halpha : Irrational alpha) (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (p : ℕ) :
    0 ≤ dyadicLower alpha p ∧
      0 < alpha - dyadicLower alpha p ∧
      alpha - dyadicLower alpha p < (1 : ℝ) / ((2 ^ p : ℕ) : ℝ) ∧
      lowerMechanicalWord alpha (1 - alpha) 0 = true ∧
      lowerMechanicalWord (dyadicLower alpha p) (1 - alpha) 0 = false := by
  let N : ℕ := 2 ^ p
  let t : ℝ := (N : ℝ) * alpha
  let beta : ℝ := dyadicLower alpha p
  have hNnat : N ≠ 0 := by dsimp [N]; positivity
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hNnat
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have hfloor0 : (0 : ℤ) ≤ ⌊t⌋ := Int.floor_nonneg.mpr ht0
  have hcast0 : (0 : ℝ) ≤ (⌊t⌋ : ℝ) := by exact_mod_cast hfloor0
  have hbetadef : beta = (⌊t⌋ : ℝ) / (N : ℝ) := by rfl
  have hbeta0 : 0 ≤ beta := by rw [hbetadef]; positivity
  have htIrr : Irrational t := by
    dsimp [t]
    exact halpha.natCast_mul hNnat
  have hfloorlt : (⌊t⌋ : ℝ) < t := by
    apply (Int.floor_lt_self_iff).2
    rintro ⟨z, hz⟩
    exact (htIrr.ne_int z) hz.symm
  have hbetalt : beta < alpha := by
    rw [hbetadef]
    apply (div_lt_iff₀ hN).2
    calc
      (⌊t⌋ : ℝ) < t := hfloorlt
      _ = alpha * (N : ℝ) := by dsimp [t]; ring
  have hfloorupper : t < (⌊t⌋ : ℝ) + 1 := Int.lt_floor_add_one t
  have hbetaupper : alpha < beta + 1 / (N : ℝ) := by
    rw [hbetadef, ← add_div]
    apply (lt_div_iff₀ hN).2
    calc
      alpha * (N : ℝ) = t := by dsimp [t]; ring
      _ < (⌊t⌋ : ℝ) + 1 := hfloorupper
  let x : ℝ := 1 - alpha
  have hx : x ∈ Set.Ico (0 : ℝ) 1 := by
    dsimp [x]
    constructor <;> linarith
  have hfloorx : ⌊x⌋ = (0 : ℤ) := Int.floor_eq_zero_iff.mpr hx
  have hflooralpha : ⌊x + alpha⌋ = (1 : ℤ) := by
    have hxa : x + alpha = 1 := by dsimp [x]; ring
    rw [hxa]
    norm_num
  have hfloorbeta : ⌊x + beta⌋ = (0 : ℤ) := by
    apply Int.floor_eq_zero_iff.mpr
    constructor
    · dsimp [x]
      linarith
    · dsimp [x]
      linarith
  have hletteralpha : lowerMechanicalLetter alpha x 0 = 1 := by
    simp [lowerMechanicalLetter, hflooralpha, hfloorx]
  have hletterbeta : lowerMechanicalLetter beta x 0 = 0 := by
    simp [lowerMechanicalLetter, hfloorbeta, hfloorx]
  refine ⟨hbeta0, by linarith, by dsimp [N] at hbetaupper ⊢; linarith, ?_, ?_⟩
  · change lowerMechanicalWord alpha x 0 = true
    exact (lowerMechanicalWord_eq_true_iff alpha x 0).2 hletteralpha
  · change lowerMechanicalWord beta x 0 = false
    simp [lowerMechanicalWord, hletterbeta]

/-- A fixed finite mechanical observation is eventually exact under upper
binary slope approximations, including phases on an integer boundary. -/
theorem dyadic_upper_eventually_word_eq (alpha x : ℝ) (n : ℕ) :
    ∃ p₀ : ℕ, ∀ p ≥ p₀, ∀ j < n,
      lowerMechanicalWord (dyadicUpper alpha p) x j =
        lowerMechanicalWord alpha x j := by
  let margin (k : ℕ) : ℝ :=
    (⌊x + (k : ℝ) * alpha⌋ : ℝ) + 1 - (x + (k : ℝ) * alpha)
  have hmargin (k : ℕ) : 0 < margin k := by
    dsimp [margin]
    linarith [Int.lt_floor_add_one (x + (k : ℝ) * alpha)]
  let gaps : Finset ℝ := (Finset.range (n + 1)).image margin
  have hnonempty : gaps.Nonempty := by
    refine ⟨margin 0, Finset.mem_image.mpr ?_⟩
    exact ⟨0, Finset.mem_range.mpr (by omega), rfl⟩
  let g := gaps.min' hnonempty
  have hg : 0 < g := by
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp (Finset.min'_mem gaps hnonempty)
    change 0 < gaps.min' hnonempty
    rw [← hk]
    exact hmargin k
  let radius : ℝ := g / ((n + 1 : ℕ) : ℝ)
  have hden : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hradius : 0 < radius := div_pos hg hden
  have hstable (beta : ℝ) (hlo : alpha ≤ beta) (hsmall : beta - alpha < radius)
      (k : ℕ) (hk : k ≤ n) :
      ⌊x + (k : ℝ) * beta⌋ = ⌊x + (k : ℝ) * alpha⌋ := by
    let t : ℝ := x + (k : ℝ) * alpha
    have hkgap : g ≤ margin k := Finset.min'_le gaps _
      (Finset.mem_image.mpr
        ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), rfl⟩)
    have hdelta : 0 ≤ beta - alpha := sub_nonneg.mpr hlo
    have hkcast : (k : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_succ_of_le hk
    have hprod : (beta - alpha) * ((n + 1 : ℕ) : ℝ) < g := by
      exact (lt_div_iff₀ hden).mp hsmall
    have hstep : (k : ℝ) * (beta - alpha) < g := by
      calc
        (k : ℝ) * (beta - alpha) ≤
            ((n + 1 : ℕ) : ℝ) * (beta - alpha) :=
          mul_le_mul_of_nonneg_right hkcast hdelta
        _ = (beta - alpha) * ((n + 1 : ℕ) : ℝ) := by ring
        _ < g := hprod
    have hbase : t ≤ x + (k : ℝ) * beta := by
      dsimp [t]
      nlinarith [mul_nonneg (Nat.cast_nonneg' k) hdelta]
    have htop : x + (k : ℝ) * beta < (⌊t⌋ : ℝ) + 1 := by
      have heq : x + (k : ℝ) * beta = t + (k : ℝ) * (beta - alpha) := by
        dsimp [t]
        ring
      change g ≤ (⌊t⌋ : ℝ) + 1 - t at hkgap
      rw [heq]
      linarith
    exact le_antisymm (Int.floor_le_iff.mpr htop) (Int.floor_mono hbase)
  have hpow : Tendsto (fun p : ℕ => (1 / 2 : ℝ) ^ p) atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨p₀, hp₀⟩ := Filter.eventually_atTop.mp
    ((tendsto_order.mp hpow).2 radius hradius)
  refine ⟨p₀, ?_⟩
  intro p hp j hj
  let N : ℕ := 2 ^ p
  let t : ℝ := (N : ℝ) * alpha
  let beta : ℝ := dyadicUpper alpha p
  have hN : (0 : ℝ) < N := by dsimp [N]; positivity
  have hbetadef : beta = (⌈t⌉ : ℝ) / (N : ℝ) := by rfl
  have hbetalo : alpha ≤ beta := by
    rw [hbetadef]
    apply (le_div_iff₀ hN).2
    calc
      alpha * (N : ℝ) = t := by dsimp [t]; ring
      _ ≤ (⌈t⌉ : ℝ) := Int.le_ceil t
  have hbetaerr : beta - alpha < (1 : ℝ) / (N : ℝ) := by
    have hnum : (⌈t⌉ : ℝ) - t < 1 := by
      linarith [Int.ceil_lt_add_one t]
    have halpha : alpha = t / (N : ℝ) := by
      dsimp [t]
      field_simp [ne_of_gt hN]
    rw [hbetadef, halpha]
    have heq : (⌈t⌉ : ℝ) / (N : ℝ) - t / (N : ℝ) =
        ((⌈t⌉ : ℝ) - t) / (N : ℝ) := by ring
    rw [heq]
    apply (div_lt_iff₀ hN).2
    simpa [ne_of_gt hN] using hnum
  have hunit : (1 : ℝ) / (N : ℝ) = (1 / 2 : ℝ) ^ p := by
    simp [N, Nat.cast_pow, one_div, inv_pow]
  have hsmall : beta - alpha < radius :=
    lt_trans (hbetaerr.trans_eq hunit) (hp₀ p hp)
  have hj0 : j ≤ n := Nat.le_of_lt hj
  have hj1 : j + 1 ≤ n := hj
  have hfloor0 := hstable beta hbetalo hsmall j hj0
  have hfloor1 := hstable beta hbetalo hsmall (j + 1) hj1
  have hfloor1' : ⌊x + ((j : ℝ) + 1) * beta⌋ =
      ⌊x + ((j : ℝ) + 1) * alpha⌋ := by
    simpa only [Nat.cast_add, Nat.cast_one] using hfloor1
  unfold lowerMechanicalWord lowerMechanicalLetter
  simp only [Nat.cast_add, Nat.cast_one]
  rw [hfloor0, hfloor1']

/-- Away from all positive-time integer hits in a fixed prefix, one slope
radius preserves every actual mechanical bit in that prefix. -/
theorem finite_word_stable_off_integer_hits (alpha x : ℝ) (n : ℕ)
    (hreg : ∀ k : ℕ, 0 < k → k ≤ n → ∀ z : ℤ,
      x + (k : ℝ) * alpha ≠ (z : ℝ)) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ beta : ℝ, |beta - alpha| < radius →
      (∀ k ≤ n, ⌊x + (k : ℝ) * beta⌋ = ⌊x + (k : ℝ) * alpha⌋) ∧
      (∀ j < n, lowerMechanicalWord beta x j = lowerMechanicalWord alpha x j) := by
  let margin : Fin n → ℝ := fun i =>
    let t := x + ((i.val + 1 : ℕ) : ℝ) * alpha
    min (t - (⌊t⌋ : ℝ)) ((⌊t⌋ : ℝ) + 1 - t) / ((i.val + 1 : ℕ) : ℝ)
  have hmpos (i : Fin n) : 0 < margin i := by
    let t := x + ((i.val + 1 : ℕ) : ℝ) * alpha
    have hne : t ≠ (⌊t⌋ : ℝ) := hreg (i.val + 1) (by omega) (by omega) ⌊t⌋
    have hlo : (⌊t⌋ : ℝ) < t := lt_of_le_of_ne (Int.floor_le t) (Ne.symm hne)
    have hhi : t < (⌊t⌋ : ℝ) + 1 := Int.lt_floor_add_one t
    exact div_pos (lt_min (sub_pos.mpr hlo) (sub_pos.mpr hhi)) (by positivity)
  let margins : Finset ℝ := insert 1 (Finset.univ.image margin)
  have hnonempty : margins.Nonempty := ⟨1, mem_insert_self _ _⟩
  have hpos : ∀ t ∈ margins, 0 < t := by
    intro t ht
    rcases mem_insert.mp ht with rfl | ht
    · norm_num
    · obtain ⟨i, _, rfl⟩ := mem_image.mp ht
      exact hmpos i
  let g := margins.min' hnonempty
  have hg : 0 < g := hpos g (min'_mem margins hnonempty)
  have hgm (i : Fin n) : g ≤ margin i :=
    min'_le margins _ (mem_insert_of_mem (mem_image.mpr ⟨i, mem_univ _, rfl⟩))
  refine ⟨g / 2, by positivity, ?_⟩
  intro beta hbeta
  have hsmall : |beta - alpha| < g := lt_trans hbeta (by linarith)
  have hfloors (k : ℕ) (hk : k ≤ n) :
      ⌊x + (k : ℝ) * beta⌋ = ⌊x + (k : ℝ) * alpha⌋ := by
    by_cases hk0 : k = 0
    · simp [hk0]
    · let i : Fin n := ⟨k - 1, by omega⟩
      have hi : i.val + 1 = k := by dsimp [i]; omega
      have hmi := hsmall.trans_le (hgm i)
      dsimp only [margin] at hmi
      rw [hi] at hmi
      let t := x + (k : ℝ) * alpha
      have hkR : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
      have hshift : |(k : ℝ) * (beta - alpha)| <
          min (t - (⌊t⌋ : ℝ)) ((⌊t⌋ : ℝ) + 1 - t) := by
        rw [abs_mul, abs_of_pos hkR, mul_comm]
        exact (lt_div_iff₀ hkR).mp hmi
      have hsl := (abs_lt.mp hshift).1
      have hsr := (abs_lt.mp hshift).2
      have heq : x + (k : ℝ) * beta = t + (k : ℝ) * (beta - alpha) := by
        dsimp [t]
        ring
      apply Int.floor_eq_iff.mpr
      constructor <;> linarith [min_le_left (t - (⌊t⌋ : ℝ)) ((⌊t⌋ : ℝ) + 1 - t),
        min_le_right (t - (⌊t⌋ : ℝ)) ((⌊t⌋ : ℝ) + 1 - t)]
  constructor
  · exact hfloors
  · intro j hj
    unfold lowerMechanicalWord lowerMechanicalLetter
    simp only [Nat.cast_add, Nat.cast_one]
    rw [hfloors (j + 1) (by omega), hfloors j (by omega)]

#print axioms dyadic_lower_boundary_mismatch
#print axioms dyadic_upper_eventually_word_eq
#print axioms finite_word_stable_off_integer_hits

end D5.S1.Words.Mechanical.MechanicalDyadicBoundary
