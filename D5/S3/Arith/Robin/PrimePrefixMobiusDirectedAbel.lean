/- GID: D5/S3/Arith/Robin/PrimePrefixMobiusDirectedAbel
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PrimePrefixMobiusDirectedAbel
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: The actual harmonic Mobius tail has its complete anchored Abel identity and a one-sided lower budget from directed prefix differences, including the exact signed anchor and zero first weight. -/

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Tactic

/-!
The actual harmonic prefix is the inclusive positive sum of Mathlib's Mobius
function. Finset.sum_Ioc_by_parts and Finset.sum_Ico_sub supply the existing
finite algebra; no generic supplier is ported or renamed as a public result.

The harmonic range adapter and finite telescoping proof are adapted from
dbsanfte/RiemannGaussian, RiemannGaussian/MoebiusHarmonicMonotoneTail.lean,
revision 24444671cee3bf643ff1307909b961a329372a9e, released under Apache
License Version 2.0. The source leaf has no author or copyright header.
Its root LICENSE carries Copyright 2026 David Sanftenberg, retained with
the complete upstream license in the source note.
This file changes names and objects into the repository namespace and adds
the actual anchored difference identity, one-sided comparison and exact
anchor budget. The original source and full license are retained by the
source note. No mathematical priority claim is made for finite Abel algebra.

All identities and estimates retain the terminal b(M)*Q_D(M) and the same
finite physical window. Prefix bounds remain caller-supplied hypotheses.
The Gaussian harmonic-decay proof, actual Robin weight transport, odd/full
reconstruction, infinite tails and RH endpoint are not conclusions here.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
open scoped BigOperators

namespace D5.S3.Arith.Robin.PrimePrefixMobiusDirectedAbel

/-- The actual harmonic Mobius prefix, including both positive endpoints. -/
def harmonicPrefix (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)

/-- The actual prefix difference anchored at the same lower cutoff. -/
def prefixDifference (D n : ℕ) : ℝ := harmonicPrefix n - harmonicPrefix D

/-- The actual finite harmonic Mobius tail against the supplied real weight. -/
def weightedTail (D M : ℕ) (b : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Ioc D M, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) * b n

private theorem harmonic_eq_range (N : ℕ) :
    harmonicPrefix N =
      ∑ n ∈ range (N+1), (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) := by
  rw [harmonicPrefix,
    show range (N+1) = Icc 1 N ∪ {0} by ext n; simp; omega,
    Finset.sum_union (by simp)]
  simp

theorem step_sum {D M : ℕ} (hDM : D < M) (b : ℕ → ℝ) :
    (∑ n ∈ Ioc D (M-1), (b n-b (n+1))) = b (D+1)-b M := by
  have hset : Ioc D (M-1) = Ico (D+1) M := by
    ext n
    simp only [mem_Ioc, mem_Ico]
    omega
  rw [hset]
  calc
    _ = -(∑ n ∈ Ico (D+1) M, (b (n+1)-b n)) := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro n _
      ring
    _ = _ := by rw [sum_Ico_sub b (by omega : D+1 ≤ M)]; ring

/-- Finite Abel algebra for any actual coefficient sequence, with its exact anchor. -/
theorem anchored_sum_by_parts {D M : ℕ} (hDM : D < M) (a b : ℕ → ℝ) :
    (∑ n ∈ Ioc D M, a n*b n) =
      b M*((∑ n ∈ range (M+1), a n)-(∑ n ∈ range (D+1), a n)) +
        ∑ n ∈ Ioc D (M-1), (b n-b (n+1))*
          ((∑ k ∈ range (n+1), a k)-(∑ k ∈ range (D+1), a k)) := by
  have h := Finset.sum_Ioc_by_parts b a hDM
  simp only [smul_eq_mul] at h
  have hraw : (∑ n ∈ Ioc D M, a n*b n) =
      b M*(∑ n ∈ range (M+1), a n) -
        b (D+1)*(∑ n ∈ range (D+1), a n) -
          ∑ n ∈ Ioc D (M-1), (b (n+1)-b n)*(∑ k ∈ range (n+1), a k) := by
    simpa only [mul_comm] using h
  have hsign : (∑ n ∈ Ioc D (M-1),
      (b (n+1)-b n)*(∑ k ∈ range (n+1), a k)) =
      -(∑ n ∈ Ioc D (M-1), (b n-b (n+1))*(∑ k ∈ range (n+1), a k)) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro n _
    ring
  rw [hraw, hsign]
  simp_rw [mul_sub]
  rw [sum_sub_distrib, ← sum_mul, step_sum hDM b]
  ring

private theorem anchored_identity {D M : ℕ} (hDM : D < M) (b : ℕ → ℝ) :
    weightedTail D M b = b M*prefixDifference D M +
      ∑ n ∈ Ioc D (M-1), (b n-b (n+1))*prefixDifference D n := by
  simpa only [weightedTail, prefixDifference, ← harmonic_eq_range] using
    anchored_sum_by_parts hDM
      (fun n => (ArithmeticFunction.moebius n : ℝ)/(n : ℝ)) b

private theorem directed_lower {D M : ℕ} (hDM : D < M) {b : ℕ → ℝ}
    (hb : ∀ n ∈ Icc (D+1) M, 0 ≤ b n)
    (hanti : AntitoneOn b (Set.Icc (D+1) M)) {e : ℝ}
    (_he : 0 ≤ e)
    (hq : ∀ n ∈ Ioc D M, -e ≤ prefixDifference D n) :
    -e*b (D+1) ≤ weightedTail D M b := by
  have hbM : 0 ≤ b M := hb M (mem_Icc.mpr ⟨by omega, le_rfl⟩)
  have hM : (-e)*b M ≤ b M*prefixDifference D M := by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (hq M (mem_Ioc.mpr ⟨hDM, le_rfl⟩)) hbM
  have hsum : (∑ n ∈ Ioc D (M-1), (-e)*(b n-b (n+1))) ≤
      ∑ n ∈ Ioc D (M-1), (b n-b (n+1))*prefixDifference D n := by
    apply sum_le_sum
    intro n hn
    have hn' := mem_Ioc.mp hn
    have hstep : b (n+1) ≤ b n := hanti
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
    have hq' := hq n (mem_Ioc.mpr ⟨hn'.1, by omega⟩)
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hq' (sub_nonneg.mpr hstep)
  rw [← mul_sum, step_sum hDM b] at hsum
  rw [anchored_identity hDM b]
  nlinarith

private theorem exact_anchor_lower {D M : ℕ} (hDM : D < M) {b : ℕ → ℝ}
    (hb : ∀ n ∈ Icc (D+1) M, 0 ≤ b n)
    (hanti : AntitoneOn b (Set.Icc (D+1) M)) {δ : ℝ}
    (hh : ∀ n ∈ Icc D M, |harmonicPrefix n| ≤ δ) :
    0 ≤ δ+harmonicPrefix D ∧
      -(δ+harmonicPrefix D)*b (D+1) ≤ weightedTail D M b := by
  have hD := (abs_le.mp (hh D (mem_Icc.mpr ⟨le_rfl, hDM.le⟩))).1
  have he : 0 ≤ δ+harmonicPrefix D := by linarith
  refine ⟨he, directed_lower hDM hb hanti he ?_⟩
  intro n hn
  have hn' := mem_Ioc.mp hn
  have hlow := (abs_le.mp (hh n (mem_Icc.mpr ⟨hn'.1.le, hn'.2⟩))).1
  unfold prefixDifference
  linarith

private theorem zero_first_weight {D M : ℕ} (hDM : D < M) {b : ℕ → ℝ}
    (hb : ∀ n ∈ Icc (D+1) M, 0 ≤ b n)
    (hanti : AntitoneOn b (Set.Icc (D+1) M)) (hz : b (D+1) = 0) :
    weightedTail D M b = 0 := by
  unfold weightedTail
  apply sum_eq_zero
  intro n hn
  have hn' := mem_Ioc.mp hn
  have hlo := hb n (mem_Icc.mpr ⟨by omega, hn'.2⟩)
  have hhi : b n ≤ b (D+1) := hanti
    ⟨le_rfl, by omega⟩ ⟨by omega, hn'.2⟩ (by omega)
  rw [hz] at hhi
  have hzero : b n = 0 := le_antisymm hhi hlo
  rw [hzero, mul_zero]

/-- Full anchored finite algebra and one-sided budgets for the same actual harmonic Mobius sums. -/
theorem result :
    (∀ (D M : ℕ), D < M → ∀ b : ℕ → ℝ,
      weightedTail D M b = b M*prefixDifference D M +
        ∑ n ∈ Ioc D (M-1), (b n-b (n+1))*prefixDifference D n) ∧
    (∀ (D M : ℕ), D < M → ∀ b : ℕ → ℝ,
      (∀ n ∈ Icc (D+1) M, 0 ≤ b n) →
      AntitoneOn b (Set.Icc (D+1) M) → ∀ e : ℝ, 0 ≤ e →
      (∀ n ∈ Ioc D M, -e ≤ prefixDifference D n) →
      -e*b (D+1) ≤ weightedTail D M b) ∧
    (∀ (D M : ℕ), D < M → ∀ b : ℕ → ℝ,
      (∀ n ∈ Icc (D+1) M, 0 ≤ b n) →
      AntitoneOn b (Set.Icc (D+1) M) → ∀ δ : ℝ,
      (∀ n ∈ Icc D M, |harmonicPrefix n| ≤ δ) →
      0 ≤ δ+harmonicPrefix D ∧
        -(δ+harmonicPrefix D)*b (D+1) ≤ weightedTail D M b) ∧
    (∀ (D M : ℕ), D < M → ∀ b : ℕ → ℝ,
      (∀ n ∈ Icc (D+1) M, 0 ≤ b n) →
      AntitoneOn b (Set.Icc (D+1) M) → b (D+1) = 0 →
      weightedTail D M b = 0) := by
  exact ⟨fun D M hDM b => anchored_identity hDM b,
    fun D M hDM b hb hanti e he hq => directed_lower hDM hb hanti he hq,
    fun D M hDM b hb hanti δ hh => exact_anchor_lower hDM hb hanti hh,
    fun D M hDM b hb hanti hz => zero_first_weight hDM hb hanti hz⟩

end D5.S3.Arith.Robin.PrimePrefixMobiusDirectedAbel

#print axioms D5.S3.Arith.Robin.PrimePrefixMobiusDirectedAbel.result
