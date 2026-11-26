/- GID: D5/S3/Quantum/Gauge/ChiralAnomalyRigidity4D
   generality: I
   mirror-B: D5/B/S3/Quantum/Gauge/ChiralAnomalyRigidity4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Local anomaly cancellation, charge quantization, and Weyl traces for one generation. -/

import OmegaBuild.Commands
import D5.S3.Quantum.Gauge.FiniteSpectralTripleSM
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Gauge.ChiralAnomalyRigidity4D

/-- One generation in all-left-handed notation, including the conjugate neutrino. -/
structure Hypercharges (K : Type*) where
  yQ : K
  yu : K
  yd : K
  yL : K
  ye : K
  yn : K

variable {K : Type*} [Field K]

def suN_anomaly (y : Hypercharges K) : Prop :=
  2 * y.yQ + y.yu + y.yd = 0

def su2_anomaly (Nc : ℕ) (y : Hypercharges K) : Prop :=
  (Nc : K) * y.yQ + y.yL = 0

def grav_anomaly (Nc : ℕ) (y : Hypercharges K) : Prop :=
  2 * (Nc : K) * y.yQ + (Nc : K) * y.yu + (Nc : K) * y.yd +
    2 * y.yL + y.ye + y.yn = 0

def cubic_anomaly_poly (Nc : ℕ) (y : Hypercharges K) : K :=
  2 * (Nc : K) * y.yQ ^ 3 + (Nc : K) * y.yu ^ 3 + (Nc : K) * y.yd ^ 3 +
    2 * y.yL ^ 3 + y.ye ^ 3 + y.yn ^ 3

def cubic_anomaly (Nc : ℕ) (y : Hypercharges K) : Prop :=
  cubic_anomaly_poly Nc y = 0

def AnomalyFree (Nc : ℕ) (y : Hypercharges K) : Prop :=
  suN_anomaly y ∧ su2_anomaly Nc y ∧ grav_anomaly Nc y ∧ cubic_anomaly Nc y

private def linearFamily (Nc : ℕ) (a t w : K) : Hypercharges K :=
  ⟨a, t - a, -t - a, -(Nc : K) * a, (Nc : K) * a + w, (Nc : K) * a - w⟩

def piPlus (Nc : ℕ) (a t : K) : Hypercharges K :=
  ⟨a, t - a, -t - a, -(Nc : K) * a, (Nc : K) * a - t, (Nc : K) * a + t⟩

def piMinus (Nc : ℕ) (a t : K) : Hypercharges K := linearFamily Nc a t t

def piZero (b c : K) : Hypercharges K := ⟨0, b, -b, 0, c, -c⟩

def InPlanes (Nc : ℕ) (y : Hypercharges K) : Prop :=
  (∃ a t : K, y = piPlus Nc a t) ∨ (∃ a t : K, y = piMinus Nc a t) ∨
    (∃ b c : K, y = piZero b c)

private theorem eq_linear_family (Nc : ℕ) (y : Hypercharges K)
    (hc : suN_anomaly y) (hw : su2_anomaly Nc y) (hg : grav_anomaly Nc y) :
    y = linearFamily Nc y.yQ (y.yu + y.yQ) (y.ye - (Nc : K) * y.yQ) := by
  rcases y with ⟨a, u, d, l, e, n⟩
  simp only [suN_anomaly, su2_anomaly, grav_anomaly] at hc hw hg
  simp only [linearFamily, Hypercharges.mk.injEq]
  refine ⟨rfl, by ring, ?_, ?_, by ring, ?_⟩
  · linear_combination hc
  · linear_combination hw
  · linear_combination hg - (Nc : K) * hc - 2 * hw

/-- In the three linear coordinates the cubic has three linear factors. -/
theorem cubic_anomaly_factorization (Nc : ℕ) (y : Hypercharges K)
    (hc : suN_anomaly y) (hw : su2_anomaly Nc y) (hg : grav_anomaly Nc y) :
    let t := y.yu + y.yQ
    let w := y.ye - (Nc : K) * y.yQ
    cubic_anomaly_poly Nc y = 6 * (Nc : K) * y.yQ * (w - t) * (w + t) := by
  dsimp only
  conv_lhs => rw [eq_linear_family Nc y hc hw hg]
  simp only [cubic_anomaly_poly, linearFamily]
  ring

variable [CharZero K]

private theorem color_count_ne_zero {Nc : ℕ} (hNc : 1 ≤ Nc) : (Nc : K) ≠ 0 :=
  Nat.cast_ne_zero.mpr (by omega)

theorem anomaly_free_planes_iff (Nc : ℕ) (hNc : 1 ≤ Nc) (y : Hypercharges K) :
    AnomalyFree Nc y ↔ InPlanes Nc y := by
  constructor
  · rintro ⟨hc, hw, hg, hcube⟩
    let t := y.yu + y.yQ
    let w := y.ye - (Nc : K) * y.yQ
    have hy : y = linearFamily Nc y.yQ t w := eq_linear_family Nc y hc hw hg
    have hproduct : 6 * (Nc : K) * y.yQ * (w - t) * (w + t) = 0 :=
      (cubic_anomaly_factorization Nc y hc hw hg).symm.trans hcube
    rcases mul_eq_zero.mp hproduct with hrest | hplus
    · rcases mul_eq_zero.mp hrest with hcolor | hminus
      · have hzero : y.yQ = 0 :=
          (mul_eq_zero.mp hcolor).resolve_left (mul_ne_zero (by norm_num) (color_count_ne_zero hNc))
        right
        right
        exact ⟨t, w, by simpa [hzero, linearFamily, piZero] using hy⟩
      · right
        left
        exact ⟨y.yQ, t, hy.trans (by rw [sub_eq_zero.mp hminus]; rfl)⟩
    · left
      have h : w = -t := eq_neg_of_add_eq_zero_left hplus
      refine ⟨y.yQ, t, hy.trans ?_⟩
      simp [h, linearFamily, piPlus, sub_eq_add_neg]
  · rintro (⟨a, t, rfl⟩ | ⟨a, t, rfl⟩ | ⟨b, c, rfl⟩) <;>
      unfold AnomalyFree <;>
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [piPlus, piMinus, piZero, linearFamily, suN_anomaly, su2_anomaly,
        grav_anomaly, cubic_anomaly, cubic_anomaly_poly] <;> ring

theorem nc_one_counterexample :
    let y : Hypercharges K := ⟨1, 1, -1, -1, 0, 0⟩
    su2_anomaly 1 y ∧ grav_anomaly 1 y ∧ cubic_anomaly 1 y ∧ ¬ InPlanes 1 y := by
  dsimp only
  refine ⟨by norm_num [su2_anomaly], by norm_num [grav_anomaly],
    by norm_num [cubic_anomaly, cubic_anomaly_poly], ?_⟩
  intro hy
  have hc := ((anomaly_free_planes_iff 1 (by decide) _).2 hy).1
  norm_num [suN_anomaly] at hc

def InLines (Nc : ℕ) (y : Hypercharges K) : Prop :=
  (∃ a : K, y = ⟨a, -((Nc : K) + 1) * a, ((Nc : K) - 1) * a, -(Nc : K) * a,
    2 * (Nc : K) * a, 0⟩) ∨
  (∃ a : K, y = ⟨a, ((Nc : K) - 1) * a, -((Nc : K) + 1) * a, -(Nc : K) * a,
    2 * (Nc : K) * a, 0⟩) ∨
  (∃ b : K, y = piZero b 0)

theorem anomaly_free_lines_without_nuR_iff (Nc : ℕ) (hNc : 1 ≤ Nc) (y : Hypercharges K) :
    AnomalyFree Nc y ∧ y.yn = 0 ↔ InLines Nc y := by
  rw [anomaly_free_planes_iff Nc hNc]
  constructor
  · rintro ⟨⟨a, t, rfl⟩ | ⟨a, t, rfl⟩ | ⟨b, c, rfl⟩, hn⟩
    · have ht : t = -(Nc : K) * a := by
        change (Nc : K) * a + t = 0 at hn
        linear_combination hn
      left
      refine ⟨a, ?_⟩
      simp only [ht, piPlus, Hypercharges.mk.injEq]
      exact ⟨rfl, by ring, by ring, rfl, by ring, by ring⟩
    · have ht : t = (Nc : K) * a := by
        change (Nc : K) * a - t = 0 at hn
        linear_combination -hn
      right
      left
      refine ⟨a, ?_⟩
      simp only [ht, piMinus, linearFamily, Hypercharges.mk.injEq]
      exact ⟨rfl, by ring, by ring, rfl, by ring, by ring⟩
    · right
      right
      have hc : c = 0 := neg_eq_zero.mp hn
      exact ⟨b, by rw [hc]⟩
  · rintro (⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨b, rfl⟩)
    · refine ⟨Or.inl ⟨a, -(Nc : K) * a, ?_⟩, rfl⟩
      simp only [piPlus, Hypercharges.mk.injEq]
      exact ⟨rfl, by ring, by ring, rfl, by ring, by ring⟩
    · refine ⟨Or.inr (Or.inl ⟨a, (Nc : K) * a, ?_⟩), rfl⟩
      simp only [piMinus, linearFamily, Hypercharges.mk.injEq]
      exact ⟨rfl, by ring, by ring, rfl, by ring, by ring⟩
    · exact ⟨Or.inr (Or.inr ⟨b, 0, rfl⟩), neg_zero⟩

def DiracYukawa (h : K) (y : Hypercharges K) : Prop :=
  y.yQ + h + y.yu = 0 ∧ y.yQ - h + y.yd = 0 ∧
    y.yL - h + y.ye = 0 ∧ y.yL + h + y.yn = 0

omit [CharZero K] in
theorem dirac_yukawa_pi_plus_iff (Nc : ℕ) (a t h : K) :
    DiracYukawa h (piPlus Nc a t) ↔ t = -h := by
  constructor
  · intro hy
    have hu := hy.1
    change a + h + (t - a) = 0 at hu
    linear_combination hu
  · rintro rfl
    unfold DiracYukawa
    exact ⟨by simp only [piPlus]; ring, by simp only [piPlus]; ring,
      by simp only [piPlus]; ring, by simp only [piPlus]; ring⟩

def quantized (Nc : ℕ) (h : K) : Hypercharges K := piPlus Nc (h / (Nc : K)) (-h)

/-- The all-left-handed shift by baryon number minus lepton number applied to the
zero-neutrino assignment. -/
def blFamily (Nc : ℕ) (h eps : K) : Hypercharges K :=
  let y := quantized Nc h
  ⟨y.yQ + eps / (Nc : K), y.yu - eps / (Nc : K), y.yd - eps / (Nc : K),
    y.yL - eps, y.ye + eps, y.yn + eps⟩

private theorem bl_family_eq_pi_plus (Nc : ℕ) (hNc : 1 ≤ Nc) (h eps : K) :
    blFamily Nc h eps = piPlus Nc ((h + eps) / (Nc : K)) (-h) := by
  have hn : (Nc : K) ≠ 0 := color_count_ne_zero hNc
  simp only [blFamily, quantized, piPlus, Hypercharges.mk.injEq, add_div,
    mul_add, mul_div_cancel₀ _ hn, neg_mul]
  exact ⟨rfl, by ring, by ring, by ring, by ring, by ring⟩

theorem dirac_yukawa_bl_family_iff (Nc : ℕ) (hNc : 1 ≤ Nc) (h : K) (y : Hypercharges K) :
    AnomalyFree Nc y ∧ DiracYukawa h y ↔ ∃! eps : K, y = blFamily Nc h eps := by
  have hn : (Nc : K) ≠ 0 := color_count_ne_zero hNc
  constructor
  · rintro ⟨ha, hy⟩
    have hform : y = piPlus Nc y.yQ (-h) := by
      rcases y with ⟨a, u, d, l, e, n⟩
      have hw := ha.2.1
      rcases hy with ⟨hu, hd, he, hn'⟩
      simp only [su2_anomaly] at hw
      simp only [piPlus, Hypercharges.mk.injEq]
      exact ⟨rfl, by linear_combination hu, by linear_combination hd,
        by linear_combination hw, by linear_combination he - hw,
        by linear_combination hn' - hw⟩
    refine ⟨(Nc : K) * y.yQ - h, ?_, ?_⟩
    · rw [bl_family_eq_pi_plus Nc hNc, show h + ((Nc : K) * y.yQ - h) = y.yQ * Nc by ring,
        mul_div_cancel_right₀ _ hn]
      exact hform
    · intro eps heps
      have hq := congrArg Hypercharges.yQ heps
      rw [bl_family_eq_pi_plus Nc hNc] at hq
      change y.yQ = (h + eps) / (Nc : K) at hq
      rw [eq_div_iff hn] at hq
      linear_combination -hq
  · rintro ⟨eps, rfl, _⟩
    rw [bl_family_eq_pi_plus Nc hNc]
    exact ⟨(anomaly_free_planes_iff Nc hNc _).2 (Or.inl ⟨_, _, rfl⟩),
      (dirac_yukawa_pi_plus_iff Nc _ _ _).2 rfl⟩

theorem majorana_restores_charge_quantization (Nc : ℕ) (hNc : 1 ≤ Nc)
    (h : K) (y : Hypercharges K) :
    (AnomalyFree Nc y ∧ DiracYukawa h y ∧ 2 * y.yn = 0) ↔ y = quantized Nc h := by
  have hn : (Nc : K) ≠ 0 := color_count_ne_zero hNc
  constructor
  · rintro ⟨ha, hy, hm⟩
    obtain ⟨eps, heps, _⟩ := (dirac_yukawa_bl_family_iff Nc hNc h y).1 ⟨ha, hy⟩
    have hzero : eps = 0 := by
      rw [heps, bl_family_eq_pi_plus Nc hNc] at hm
      simp only [piPlus, mul_div_cancel₀ _ hn] at hm
      linear_combination (1 / 2 : K) * hm
    simpa [hzero, blFamily] using heps
  · rintro rfl
    unfold quantized
    refine ⟨(anomaly_free_planes_iff Nc hNc _).2 (Or.inl ⟨_, _, rfl⟩),
      (dirac_yukawa_pi_plus_iff Nc _ _ _).2 rfl, ?_⟩
    simp [piPlus, mul_div_cancel₀ _ hn]

/-- Particle electric charges from the two left-handed weak doublets. -/
structure ElectricCharges (K : Type*) where
  up : K
  down : K
  neutrino : K
  electron : K

def electricCharges (y : Hypercharges K) : ElectricCharges K :=
  ⟨y.yQ + 1 / 2, y.yQ - 1 / 2, y.yL + 1 / 2, y.yL - 1 / 2⟩

theorem dirac_family_electric_charges (Nc : ℕ) (hNc : 1 ≤ Nc) (eps : K) :
    electricCharges (blFamily Nc (1 / 2 : K) eps) =
      ⟨((Nc : K) + 1) / (2 * Nc) + eps / Nc,
        -((Nc : K) - 1) / (2 * Nc) + eps / Nc, -eps, -1 - eps⟩ ∧
    let q := electricCharges (blFamily Nc (1 / 2 : K) eps)
    (Nc : K) * (q.up + q.down) + q.neutrino + q.electron = 0 := by
  have hn : (Nc : K) ≠ 0 := color_count_ne_zero hNc
  rw [bl_family_eq_pi_plus Nc hNc]
  simp only [electricCharges, piPlus, ElectricCharges.mk.injEq, neg_mul, mul_div_cancel₀ _ hn]
  refine ⟨⟨?_, ?_, by ring, by ring⟩, ?_⟩ <;>
    field_simp <;> ring

theorem quantized_electric_charges (Nc : ℕ) (hNc : 1 ≤ Nc) :
    electricCharges (quantized Nc (1 / 2 : K)) =
      ⟨((Nc : K) + 1) / (2 * Nc), -((Nc : K) - 1) / (2 * Nc), 0, -1⟩ ∧
    let q := electricCharges (quantized Nc (1 / 2 : K))
    (Nc : K) * (q.up + q.down) + q.neutrino + q.electron = 0 := by
  simpa [blFamily] using dirac_family_electric_charges Nc hNc (0 : K)

def fixedQuarks (l e : K) : Hypercharges K := ⟨1 / 6, -2 / 3, 1 / 3, l, e, 0⟩

theorem quark_charges_uniquely_select_nc_three (Nc : ℕ) (hNc : 1 ≤ Nc) (l e : K) :
    AnomalyFree Nc (fixedQuarks l e) ↔ Nc = 3 ∧ l = -1 / 2 ∧ e = 1 := by
  constructor
  · rintro ⟨hc, hw, hg, hcube⟩
    have hl : l = -(Nc : K) / 6 := by
      simp only [su2_anomaly, fixedQuarks] at hw
      linear_combination hw
    have he : e = (Nc : K) / 3 := by
      simp only [grav_anomaly, fixedQuarks, hl] at hg
      linear_combination hg
    have hfactor :
        cubic_anomaly_poly Nc (fixedQuarks l e) =
          (Nc : K) * ((Nc : K) - 3) * ((Nc : K) + 3) / 36 := by
      rw [cubic_anomaly_factorization Nc _ hc hw hg]
      simp only [fixedQuarks, he]
      ring
    have hprod := hfactor.symm.trans hcube
    have hplus : (Nc : K) + 3 ≠ 0 := by exact_mod_cast (show Nc + 3 ≠ 0 by omega)
    have hprod := (div_eq_zero_iff.mp hprod).resolve_right (by norm_num)
    have hprod := (mul_eq_zero.mp hprod).resolve_right hplus
    have hminus := (mul_eq_zero.mp hprod).resolve_left (color_count_ne_zero hNc)
    have hthree : Nc = 3 := by exact_mod_cast (sub_eq_zero.mp hminus)
    subst Nc
    norm_num at hl he ⊢
    exact ⟨hl, he⟩
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num [AnomalyFree, suN_anomaly, su2_anomaly, grav_anomaly, cubic_anomaly,
      cubic_anomaly_poly, fixedQuarks]

/-- The spectral triple's left-handed weight table in the same six coordinates. -/
def spectralHypercharges : Hypercharges ℚ :=
  let y := FiniteSpectralTripleSM.hypercharge
  ⟨y .QL, y .uc, y .dc, y .LL, y .ec, y .nuc⟩

private theorem spectral_hypercharges_eq_fixed :
    spectralHypercharges = fixedQuarks (-1 / 2) 1 := by
  obtain ⟨hq, hu, hd, hl, he, hn⟩ := FiniteSpectralTripleSM.hypercharge_table
  simp [spectralHypercharges, fixedQuarks, hq, hu, hd, hl, he, hn]

/-- Four color copies of the trace of a normalized fundamental generator squared.
At one color this formula is an algebraic extension of the trace normalization. -/
def traceColorSq (K : Type*) [Field K] : K := 4 * (1 / 2)

def traceWeakSq (K : Type*) [Field K] (Nc : ℕ) : K :=
  ((Nc : K) + 1) * ((1 / 2) ^ 2 + (-(1 / 2)) ^ 2)

def traceWeakY (Nc : ℕ) (y : Hypercharges K) : K :=
  (Nc : K) * ((1 / 2) * y.yQ + (-(1 / 2)) * y.yQ) +
    ((1 / 2) * y.yL + (-(1 / 2)) * y.yL)

def traceYSq (Nc : ℕ) (y : Hypercharges K) : K :=
  (Nc : K) * (2 * y.yQ ^ 2 + y.yu ^ 2 + y.yd ^ 2) +
    2 * y.yL ^ 2 + y.ye ^ 2 + y.yn ^ 2

def traceElectricSq (Nc : ℕ) (y : Hypercharges K) : K :=
  let q := electricCharges y
  (Nc : K) * (q.up ^ 2 + q.down ^ 2 + y.yu ^ 2 + y.yd ^ 2) +
    q.neutrino ^ 2 + q.electron ^ 2 + y.ye ^ 2 + y.yn ^ 2

def sinSqAnomaly (K : Type*) [Field K] (Nc : ℕ) : K :=
  (Nc : K) / (2 * ((Nc : K) + 1))

def sinSqFixed (K : Type*) [Field K] (Nc : ℕ) : K :=
  9 * ((Nc : K) + 1) / (4 * (9 + 5 * (Nc : K)))

theorem weyl_traces_quantized (Nc : ℕ) (hNc : 1 ≤ Nc) :
    let y := quantized Nc (1 / 2 : K)
    traceColorSq K = 2 ∧ traceWeakSq K Nc = ((Nc : K) + 1) / 2 ∧
      traceWeakY Nc y = 0 ∧
      traceYSq Nc y = ((Nc : K) + 1) * ((Nc : K) + 2) / (2 * Nc) ∧
      traceElectricSq Nc y = ((Nc : K) + 1) ^ 2 / Nc ∧
      traceWeakSq K Nc / (traceWeakSq K Nc + traceYSq Nc y) = sinSqAnomaly K Nc := by
  have hn : (Nc : K) ≠ 0 := color_count_ne_zero hNc
  have hsucc : (Nc : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero Nc
  have hweak : traceWeakSq K Nc = ((Nc : K) + 1) / 2 := by unfold traceWeakSq; ring
  have hy : traceYSq Nc (quantized Nc (1 / 2 : K)) =
      ((Nc : K) + 1) * ((Nc : K) + 2) / (2 * Nc) := by
    simp only [traceYSq, quantized, piPlus, neg_mul, mul_div_cancel₀ _ hn]
    field_simp
    ring
  refine ⟨by norm_num [traceColorSq], hweak, ?_, hy, ?_, ?_⟩
  · unfold traceWeakY
    ring
  · simp only [traceElectricSq, (quantized_electric_charges (K := K) Nc hNc).1,
      quantized, piPlus, mul_div_cancel₀ _ hn]
    field_simp
    ring
  · dsimp only
    rw [hweak, hy]
    have hsum : ((Nc : K) + 1) / 2 +
        ((Nc : K) + 1) * ((Nc : K) + 2) / (2 * Nc) = ((Nc : K) + 1) ^ 2 / Nc := by
      field_simp
      ring
    rw [hsum]
    unfold sinSqAnomaly
    field_simp

theorem weyl_arc_trace_nc_three_and_weinberg_angle (Nc : ℕ) :
    traceWeakSq K Nc = traceColorSq K ↔
      Nc = 3 ∧
      traceYSq Nc (quantized Nc (1 / 2 : K)) / traceWeakSq K Nc = 5 / 3 ∧
      sinSqAnomaly K Nc = 3 / 8 := by
  constructor
  · intro h
    have hcast : (Nc : K) = 3 := by
      unfold traceWeakSq traceColorSq at h
      linear_combination 2 * h
    have hthree : Nc = 3 := by exact_mod_cast hcast
    subst Nc
    norm_num [traceYSq, quantized, piPlus, traceWeakSq, sinSqAnomaly]
  · rintro ⟨rfl, _, _⟩
    norm_num [traceWeakSq, traceColorSq]

/-- The fixed-charge benchmark keeps the standard quark and lepton weights while
varying the number of quark colors. -/
theorem fixed_charge_weak_mixing (Nc : ℕ) :
    traceWeakSq ℚ Nc / (traceWeakSq ℚ Nc + traceYSq Nc spectralHypercharges) =
      sinSqFixed ℚ Nc := by
  rw [spectral_hypercharges_eq_fixed]
  have hsum : traceWeakSq ℚ Nc + traceYSq Nc (fixedQuarks (-1 / 2) (1 : ℚ)) =
      (2 / 9) * (9 + 5 * (Nc : ℚ)) := by
    simp only [traceWeakSq, traceYSq, fixedQuarks]
    ring
  have hden : (9 + 5 * (Nc : ℚ)) ≠ 0 := by positivity
  rw [hsum]
  unfold traceWeakSq sinSqFixed
  field_simp
  <;> ring

theorem weinberg_angle_difference (Nc : ℕ) :
    sinSqAnomaly K Nc - sinSqFixed K Nc =
      ((Nc : K) - 3) * ((Nc : K) + 3) / (4 * ((Nc : K) + 1) * (9 + 5 * (Nc : K))) := by
  have hsucc : (Nc : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero Nc
  have hden : (9 + 5 * (Nc : K)) ≠ 0 := by
    exact_mod_cast (show 9 + 5 * Nc ≠ 0 by omega)
  unfold sinSqAnomaly sinSqFixed
  field_simp
  ring

theorem weinberg_angle_intersection_iff (Nc : ℕ) :
    sinSqAnomaly K Nc = sinSqFixed K Nc ↔ Nc = 3 := by
  rw [← sub_eq_zero, weinberg_angle_difference]
  have hsucc : (Nc : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero Nc
  have hden : (9 + 5 * (Nc : K)) ≠ 0 := by exact_mod_cast (show 9 + 5 * Nc ≠ 0 by omega)
  have hplus : (Nc : K) + 3 ≠ 0 := by exact_mod_cast (show Nc + 3 ≠ 0 by omega)
  rw [div_eq_zero_iff, or_iff_left (mul_ne_zero (mul_ne_zero (by norm_num) hsucc) hden),
    mul_eq_zero, or_iff_left hplus, sub_eq_zero]
  exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩

end D5.S3.Quantum.Gauge.ChiralAnomalyRigidity4D
