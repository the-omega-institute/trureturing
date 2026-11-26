/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/SingularCycleAllocation
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMV/Tracial/SingularCycleAllocation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Simple four-cycles with unique path completion use disjoint backtrack trace terms. -/

import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap
import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ThreeBlockGram
import D5.S3.Quantum.Analysis.RefinedBMV.BinaryGramConditioning
import D5.S3.Quantum.Analysis.RefinedBMV.Tracial.SingularFourCycle
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
import D5.S3.Quantum.Matrix.CartesianVariance
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Cyclic Cauchy–Schwarz and disjoint allocation of the backtracks of
simple four-cycles. -/

namespace RefinedBMV.Tracial

open Matrix FourCopyGap
open D5.S3.Quantum.Matrix.CartesianVariance

noncomputable section

/-- The four slots of an ordered spectral cycle. -/
abbrev CycleSlots (s : Type*) := s × s × s × s

private def rotateCycle {s : Type*} (q : CycleSlots s) : CycleSlots s :=
  (q.2.1, q.2.2.1, q.2.2.2, q.1)

private def rotateCycleBack {s : Type*} (q : CycleSlots s) : CycleSlots s :=
  (q.2.2.2, q.1, q.2.1, q.2.2.1)

private def backtrack {s : Type*} (q : CycleSlots s) : CycleSlots s :=
  (q.1, q.2.1, q.2.2.1, q.2.1)

private def firstPath {s : Type*} (q : CycleSlots s) : s × s × s :=
  (q.1, q.2.1, q.2.2.1)

private def pathBacktrack {s : Type*} (q : s × s × s) : CycleSlots s :=
  (q.1, q.2.1, q.2.2, q.2.1)

private def cycleProduct {s : Type*} {n : ℕ} (C : s → s → Matrix (Fin n) (Fin n) ℂ)
    (q : CycleSlots s) : ℂ :=
  cycleTrace C q.1 q.2.1 q.2.2.1 q.2.2.2

private theorem cycleProduct_rotate {s : Type*} {n : ℕ}
    (C : s → s → Matrix (Fin n) (Fin n) ℂ) (q : CycleSlots s) :
    cycleProduct C (rotateCycle q) = cycleProduct C q := by
  rcases q with ⟨i, j, k, l⟩
  unfold rotateCycle cycleProduct cycleTrace
  simpa only [Matrix.mul_assoc] using
    Matrix.trace_mul_comm (C j k * C k l * C l i) (C i j)

private theorem backtrack_trace_eq_frobSq {s : Type*} {n : ℕ}
    (C : s → s → Matrix (Fin n) (Fin n) ℂ) (hC : ∀ i j, (C i j)ᴴ = C j i)
    (q : CycleSlots s) :
    (cycleProduct C (backtrack q)).re = RHLinalg.frobSq (C q.1 q.2.1 * C q.2.1 q.2.2.1) := by
  rcases q with ⟨i, j, k, l⟩
  unfold backtrack cycleProduct cycleTrace RHLinalg.frobSq
  rw [RCLike.re_eq_complex_re, Matrix.trace_mul_comm (_ᴴ) (_ : Matrix _ _ ℂ),
    Matrix.conjTranspose_mul, hC, hC]
  simp only [Matrix.mul_assoc]

private theorem cycle_abs_re_le_backtracks {s : Type*} {n : ℕ}
    (C : s → s → Matrix (Fin n) (Fin n) ℂ) (hC : ∀ i j, (C i j)ᴴ = C j i)
    (q : CycleSlots s) :
    |(cycleProduct C q).re| ≤
      Real.sqrt ((cycleProduct C (backtrack q)).re *
        (cycleProduct C (backtrack (rotateCycle (rotateCycle q)))).re) := by
  rcases q with ⟨i, j, k, l⟩
  let X := C i j * C j k
  let Y := C k l * C l i
  have hz : cycleProduct C (i, j, k, l) = trace (X * Y) := by
    simp only [cycleProduct, cycleTrace, X, Y, Matrix.mul_assoc]
  have h₁ := backtrack_trace_eq_frobSq C hC (i, j, k, l)
  have h₂ := backtrack_trace_eq_frobSq C hC (k, l, i, j)
  change (cycleProduct C (backtrack (i, j, k, l))).re = RHLinalg.frobSq X at h₁
  change (cycleProduct C (backtrack (k, l, i, j))).re = RHLinalg.frobSq Y at h₂
  change |(cycleProduct C (i, j, k, l)).re| ≤
    Real.sqrt ((cycleProduct C (backtrack (i, j, k, l))).re *
      (cycleProduct C (backtrack (k, l, i, j))).re)
  rw [h₁, h₂, hz]
  apply (Real.le_sqrt (abs_nonneg _) (mul_nonneg (frobSq_nonneg X) (frobSq_nonneg Y))).2
  rw [sq_abs]
  have hc := trace_product_cauchy X Y
  rw [Complex.normSq_apply] at hc
  nlinarith only [hc, sq_nonneg (trace (X * Y)).im]

private theorem opposite_pair_compensation {k l x y z : ℝ}
    (hk : 0 ≤ k) (hl : 0 ≤ l) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : |z| ≤ Real.sqrt (x * y)) :
    2 * Real.sqrt (k * l) * |z| ≤ k * x + l * y := by
  have h := mul_le_mul_of_nonneg_left hz
    (show 0 ≤ 2 * Real.sqrt (k * l) by positivity)
  have hprod : Real.sqrt (k * l) * Real.sqrt (x * y) =
      Real.sqrt (k * x) * Real.sqrt (l * y) := by
    rw [← Real.sqrt_mul (mul_nonneg hk hl), ← Real.sqrt_mul (mul_nonneg hk hx)]
    congr 1
    ring
  have hsq := sq_nonneg (Real.sqrt (k * x) - Real.sqrt (l * y))
  have hkx := Real.sq_sqrt (mul_nonneg hk hx)
  have hly := Real.sq_sqrt (mul_nonneg hl hy)
  calc
    _ ≤ 2 * Real.sqrt (k * l) * Real.sqrt (x * y) := h
    _ = 2 * (Real.sqrt (k * x) * Real.sqrt (l * y)) := by
      rw [mul_assoc, hprod]
    _ ≤ _ := by nlinarith only [hsq, hkx, hly]

/-- The weighted trace of a cycle with four slots. -/
def weightedCycle {s : Type*} {n : ℕ} (K : CycleSlots s → ℝ)
    (C : s → s → Matrix (Fin n) (Fin n) ℂ) (q : CycleSlots s) : ℝ :=
  K q * (cycleProduct C q).re

private theorem weightedCycle_rotate {s : Type*} {n : ℕ}
    (K : CycleSlots s → ℝ) (C : s → s → Matrix (Fin n) (Fin n) ℂ)
    (hK : ∀ q, K (rotateCycle q) = K q) (q : CycleSlots s) :
    weightedCycle K C (rotateCycle q) = weightedCycle K C q := by
  rw [weightedCycle, weightedCycle, hK, cycleProduct_rotate]

private theorem weightedCycle_backtrack_nonneg {s : Type*} {n : ℕ}
    (K : CycleSlots s → ℝ) (C : s → s → Matrix (Fin n) (Fin n) ℂ)
    (hK : ∀ q, 0 ≤ K q) (hC : ∀ i j, (C i j)ᴴ = C j i) (q : CycleSlots s) :
    0 ≤ weightedCycle K C (backtrack q) := by
  rw [weightedCycle, backtrack_trace_eq_frobSq C hC]
  exact mul_nonneg (hK _) (frobSq_nonneg _)

private theorem four_backtracks_pay_cycle {s : Type*} {n : ℕ}
    (K : CycleSlots s → ℝ) (C : s → s → Matrix (Fin n) (Fin n) ℂ)
    (hK : ∀ q, 0 ≤ K q) (hC : ∀ i j, (C i j)ᴴ = C j i)
    (q : CycleSlots s)
    (hmatch : K q ≤
      Real.sqrt (K (backtrack q) * K (backtrack (rotateCycle (rotateCycle q)))) +
      Real.sqrt (K (backtrack (rotateCycle q)) *
        K (backtrack (rotateCycle (rotateCycle (rotateCycle q)))))) :
    0 ≤ 2 * weightedCycle K C q + weightedCycle K C (backtrack q) +
      weightedCycle K C (backtrack (rotateCycle q)) +
      weightedCycle K C (backtrack (rotateCycle (rotateCycle q))) +
      weightedCycle K C (backtrack (rotateCycle (rotateCycle (rotateCycle q)))) := by
  have htrace (u : CycleSlots s) : 0 ≤ (cycleProduct C (backtrack u)).re := by
    rw [backtrack_trace_eq_frobSq C hC]
    exact frobSq_nonneg _
  have hfirst := opposite_pair_compensation (hK (backtrack q))
    (hK (backtrack (rotateCycle (rotateCycle q))))
    (htrace q) (htrace (rotateCycle (rotateCycle q))) (cycle_abs_re_le_backtracks C hC q)
  have hsecond := opposite_pair_compensation (hK (backtrack (rotateCycle q)))
    (hK (backtrack (rotateCycle (rotateCycle (rotateCycle q)))))
    (htrace (rotateCycle q)) (htrace (rotateCycle (rotateCycle (rotateCycle q))))
    (cycle_abs_re_le_backtracks C hC (rotateCycle q))
  rw [cycleProduct_rotate] at hsecond
  have hm := mul_le_mul_of_nonneg_right hmatch (abs_nonneg (cycleProduct C q).re)
  have hn := mul_le_mul_of_nonneg_left (neg_abs_le (cycleProduct C q).re) (hK q)
  unfold weightedCycle
  nlinarith only [hfirst, hsecond, hm, hn]

/-- Ordered simple four-cycles whose four edges belong to the given support. -/
def supportedFourCycles {s : Type*} [Fintype s] (adj : s → s → Prop) :
    Finset (CycleSlots s) := by
  classical
  exact Finset.univ.filter fun q ↦
    q.1 ≠ q.2.1 ∧ q.1 ≠ q.2.2.1 ∧ q.1 ≠ q.2.2.2 ∧
    q.2.1 ≠ q.2.2.1 ∧ q.2.1 ≠ q.2.2.2 ∧ q.2.2.1 ≠ q.2.2.2 ∧
    adj q.1 q.2.1 ∧ adj q.2.1 q.2.2.1 ∧ adj q.2.2.1 q.2.2.2 ∧ adj q.2.2.2 q.1

private theorem mem_supportedFourCycles {s : Type*} [Fintype s] (adj : s → s → Prop)
    (i j k l : s) :
    (i, j, k, l) ∈ supportedFourCycles adj ↔
      i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l ∧
      adj i j ∧ adj j k ∧ adj k l ∧ adj l i := by
  classical
  simp [supportedFourCycles]

private theorem supportedFourCycles_rotate {s : Type*} [Fintype s]
    (adj : s → s → Prop) (q : CycleSlots s) :
    rotateCycle q ∈ supportedFourCycles adj ↔ q ∈ supportedFourCycles adj := by
  rcases q with ⟨i, j, k, l⟩
  simp only [rotateCycle, mem_supportedFourCycles]
  aesop

private theorem sum_supportedFourCycles_rotate {s : Type*} [Fintype s]
    (adj : s → s → Prop) (f : CycleSlots s → ℝ) :
    (∑ q ∈ supportedFourCycles adj, f (rotateCycle q)) =
      ∑ q ∈ supportedFourCycles adj, f q := by
  apply Finset.sum_nbij' rotateCycle rotateCycleBack
  · exact fun q hq ↦ (supportedFourCycles_rotate adj q).2 hq
  · rintro ⟨i, j, k, l⟩ hq
    exact (supportedFourCycles_rotate adj (rotateCycleBack (i, j, k, l))).1 hq
  · rintro ⟨i, j, k, l⟩ _
    rfl
  · rintro ⟨i, j, k, l⟩ _
    rfl
  · intro q _
    rfl

private def distinctPaths {s : Type*} [Fintype s] : Finset (s × s × s) := by
  classical
  exact Finset.univ.filter fun t ↦ t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2

/-- With unique completion of each two-edge path, the three-label
backtracks pay for all supported simple four-cycles. Every ordered term
is counted with its actual multiplicity in the trace expansion. -/
theorem sum_simple_cycles_add_backtracks_nonneg {s : Type*} [Fintype s] {n : ℕ}
    (adj : s → s → Prop) (K : CycleSlots s → ℝ)
    (C : s → s → Matrix (Fin n) (Fin n) ℂ)
    (hC : ∀ i j, (C i j)ᴴ = C j i) (hK : ∀ q, 0 ≤ K q)
    (hKrot : ∀ i j k l, K (j, k, l, i) = K (i, j, k, l))
    (hunique : ∀ i j k l m, (i, j, k, l) ∈ supportedFourCycles adj →
      (i, j, k, m) ∈ supportedFourCycles adj → l = m)
    (hmatch : ∀ i j k l, (i, j, k, l) ∈ supportedFourCycles adj →
      K (i, j, k, l) ≤ Real.sqrt (K (i, j, k, j) * K (k, l, i, l)) +
        Real.sqrt (K (j, k, l, k) * K (l, i, j, i))) :
    0 ≤ (∑ q ∈ supportedFourCycles adj, weightedCycle K C q) +
      (∑ t ∈ distinctPaths, weightedCycle K C (pathBacktrack t)) +
      (∑ t ∈ distinctPaths, weightedCycle K C (rotateCycle (pathBacktrack t))) := by
  classical
  let cycles := supportedFourCycles adj
  let f := weightedCycle K C
  let w (q : CycleSlots s) := f (backtrack q)
  have hl : 0 ≤ ∑ q ∈ cycles, (2 * f q + w q + w (rotateCycle q) +
      w (rotateCycle (rotateCycle q)) + w (rotateCycle (rotateCycle (rotateCycle q)))) := by
    refine Finset.sum_nonneg ?_
    rintro ⟨i, j, k, l⟩ hq
    exact four_backtracks_pay_cycle K C hK hC (i, j, k, l) (hmatch i j k l hq)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hl
  have hrot (g : CycleSlots s → ℝ) : (∑ q ∈ cycles, g (rotateCycle q)) =
      ∑ q ∈ cycles, g q := sum_supportedFourCycles_rotate adj g
  simp only [hrot (fun q ↦ w (rotateCycle (rotateCycle q))),
    hrot (fun q ↦ w (rotateCycle q)), hrot w] at hl
  have hinj : Set.InjOn firstPath (↑cycles : Set (CycleSlots s)) := by
    rintro ⟨i, j, k, l⟩ hi ⟨a, b, c, d⟩ ha h
    have he : i = a ∧ j = b ∧ k = c := by simpa [firstPath] using h
    rcases he with ⟨rfl, rfl, rfl⟩
    rw [hunique i j k l d hi ha]
  have hsub : cycles.image firstPath ⊆ distinctPaths := by
    intro t ht
    obtain ⟨⟨i, j, k, l⟩, hq, rfl⟩ := Finset.mem_image.mp ht
    have h := (mem_supportedFourCycles adj i j k l).1 hq
    simp [firstPath, distinctPaths, h.1, h.2.1, h.2.2.2.1]
  have hpay : (∑ q ∈ cycles, w q) ≤ ∑ t ∈ distinctPaths, f (pathBacktrack t) := by
    calc
      _ = ∑ t ∈ cycles.image firstPath, f (pathBacktrack t) := by
        rw [Finset.sum_image hinj]
        rfl
      _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        rintro ⟨i, j, k⟩ _ _
        exact weightedCycle_backtrack_nonneg K C hK hC (i, j, k, j)
  have hKr (q : CycleSlots s) : K (rotateCycle q) = K q := by
    rcases q with ⟨i, j, k, l⟩
    exact hKrot i j k l
  simp only [weightedCycle_rotate K C hKr]
  change 0 ≤ (∑ q ∈ cycles, f q) + (∑ t ∈ distinctPaths, f (pathBacktrack t)) +
    (∑ t ∈ distinctPaths, f (pathBacktrack t))
  linarith only [hl, hpay]

private def distinctTriple {s : Type*} (i j k : s) : Prop :=
  i ≠ j ∧ i ≠ k ∧ j ≠ k

/-- A four-term trace walk visits at least three distinct labels. -/
def cycleUsesThreeLabels {s : Type*} (q : CycleSlots s) : Prop :=
  distinctTriple q.1 q.2.1 q.2.2.1 ∨ distinctTriple q.1 q.2.1 q.2.2.2 ∨
    distinctTriple q.1 q.2.2.1 q.2.2.2 ∨ distinctTriple q.2.1 q.2.2.1 q.2.2.2

private theorem mem_distinctPaths {s : Type*} [Fintype s] (i j k : s) :
    (i, j, k) ∈ (distinctPaths : Finset (s × s × s)) ↔ distinctTriple i j k := by
  classical
  simp [distinctPaths, distinctTriple]

open scoped Classical in
/-- In a triangle-free support, the terms visiting at least three labels
are nonnegative in total, provided simple four-cycles admit the matching
bound and each two-edge path completes to at most one such cycle. -/
theorem sum_three_label_terms_nonneg {s : Type*} [Fintype s] {n : ℕ}
    (adj : s → s → Prop) (K : CycleSlots s → ℝ)
    (C : s → s → Matrix (Fin n) (Fin n) ℂ)
    (hC : ∀ i j, (C i j)ᴴ = C j i) (hK : ∀ q, 0 ≤ K q)
    (hKrot : ∀ i j k l, K (j, k, l, i) = K (i, j, k, l))
    (hzero : ∀ i j, i ≠ j → ¬ adj i j → C i j = 0)
    (htriangle : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      adj i j → adj j k → adj k i → False)
    (hunique : ∀ i j k l m, (i, j, k, l) ∈ supportedFourCycles adj →
      (i, j, k, m) ∈ supportedFourCycles adj → l = m)
    (hmatch : ∀ i j k l, (i, j, k, l) ∈ supportedFourCycles adj →
      K (i, j, k, l) ≤ Real.sqrt (K (i, j, k, j) * K (k, l, i, l)) +
        Real.sqrt (K (j, k, l, k) * K (l, i, j, i))) :
    0 ≤ ∑ q : CycleSlots s, if cycleUsesThreeLabels q then weightedCycle K C q else 0 := by
  classical
  let cycles := supportedFourCycles adj
  let Paths := (distinctPaths : Finset (s × s × s))
  let W₁ := Paths.image pathBacktrack
  let W₂ := Paths.image (rotateCycle ∘ pathBacktrack)
  let U := (cycles ∪ W₁) ∪ W₂
  let H := Finset.univ.filter (cycleUsesThreeLabels : CycleSlots s → Prop)
  let f := weightedCycle K C
  have hw₁ (q : CycleSlots s) : q ∈ W₁ →
      q.2.1 = q.2.2.2 ∧ distinctTriple q.1 q.2.1 q.2.2.1 := by
    intro hq
    obtain ⟨⟨i, j, k⟩, hp, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨rfl, (mem_distinctPaths i j k).1 hp⟩
  have hw₂ (q : CycleSlots s) : q ∈ W₂ →
      q.1 = q.2.2.1 ∧ distinctTriple q.1 q.2.1 q.2.2.2 := by
    intro hq
    obtain ⟨⟨i, j, k⟩, hp, rfl⟩ := Finset.mem_image.mp hq
    have h := (mem_distinctPaths i j k).1 hp
    exact ⟨rfl, h.2.2, h.1.symm, h.2.1.symm⟩
  have hcycle (q : CycleSlots s) (hq : q ∈ cycles) :
      q.1 ≠ q.2.2.1 ∧ q.2.1 ≠ q.2.2.2 ∧ cycleUsesThreeLabels q := by
    rcases q with ⟨i, j, k, l⟩
    have h := (mem_supportedFourCycles adj i j k l).1 hq
    exact ⟨h.2.1, h.2.2.2.2.1, Or.inl ⟨h.1, h.2.1, h.2.2.2.1⟩⟩
  have hd₁ : Disjoint cycles W₁ := by
    refine Finset.disjoint_left.mpr (fun q hc hw ↦ ?_)
    exact (hcycle q hc).2.1 (hw₁ q hw).1
  have hd₂ : Disjoint (cycles ∪ W₁) W₂ := by
    refine Finset.disjoint_left.mpr (fun q hcw hw ↦ ?_)
    rcases Finset.mem_union.mp hcw with hc | hw'
    · exact (hcycle q hc).1 (hw₂ q hw).1
    · exact (hw₁ q hw').2.2.1 (hw₂ q hw).1
  have hsub : U ⊆ H := by
    intro q hq
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_union.mp hq with hcw | hw
    · rcases Finset.mem_union.mp hcw with hc | hw'
      · exact (hcycle q hc).2.2
      · exact Or.inl (hw₁ q hw').2
    · exact Or.inr (Or.inl (hw₂ q hw).2)
  have hrem : ∀ q ∈ H, q ∉ U → f q = 0 := by
    rintro ⟨i, j, k, l⟩ hq hn
    have ht := (Finset.mem_filter.mp hq).2
    by_contra hz
    have h₁ : C i j ≠ 0 := by
      intro h
      exact hz (by simp [f, weightedCycle, cycleProduct, cycleTrace, h])
    have h₂ : C j k ≠ 0 := by
      intro h
      exact hz (by simp [f, weightedCycle, cycleProduct, cycleTrace, h])
    have h₃ : C k l ≠ 0 := by
      intro h
      exact hz (by simp [f, weightedCycle, cycleProduct, cycleTrace, h])
    have h₄ : C l i ≠ 0 := by
      intro h
      exact hz (by simp [f, weightedCycle, cycleProduct, cycleTrace, h])
    have e₁ (h : i ≠ j) : adj i j := not_not.mp (fun e ↦ h₁ (hzero i j h e))
    have e₂ (h : j ≠ k) : adj j k := not_not.mp (fun e ↦ h₂ (hzero j k h e))
    have e₃ (h : k ≠ l) : adj k l := not_not.mp (fun e ↦ h₃ (hzero k l h e))
    have e₄ (h : l ≠ i) : adj l i := not_not.mp (fun e ↦ h₄ (hzero l i h e))
    by_cases hik : i = k
    · subst k
      have hd : distinctTriple l i j := by
        simp only [cycleUsesThreeLabels] at ht
        grind [distinctTriple]
      apply hn
      refine Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ?_))
      exact ⟨(l, i, j), (mem_distinctPaths l i j).2 hd, rfl⟩
    by_cases hjl : j = l
    · subst l
      have hd : distinctTriple i j k := by
        simp only [cycleUsesThreeLabels] at ht
        grind [distinctTriple]
      apply hn
      refine Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr ?_)))
      exact Finset.mem_image.mpr ⟨(i, j, k), (mem_distinctPaths i j k).2 hd, rfl⟩
    have hij : i ≠ j := by
      intro e
      subst j
      have hkl : k ≠ l := by
        simp only [cycleUsesThreeLabels] at ht
        grind [distinctTriple]
      exact htriangle i k l hik hjl hkl (e₂ hik) (e₃ hkl) (e₄ (fun h ↦ hjl h.symm))
    have hjk : j ≠ k := by
      intro e
      subst k
      have hil : i ≠ l := by
        simp only [cycleUsesThreeLabels] at ht
        grind [distinctTriple]
      exact htriangle i j l hij hil hjl (e₁ hij) (e₃ hjl) (e₄ hil.symm)
    have hkl : k ≠ l := by
      intro e
      subst l
      exact htriangle i j k hij hik hjk (e₁ hij) (e₂ hjk) (e₄ (fun h ↦ hik h.symm))
    have hli : l ≠ i := by
      intro e
      subst l
      exact htriangle i j k hij hik hjk (e₁ hij) (e₂ hjk) (e₃ (fun h ↦ hik h.symm))
    apply hn
    refine Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl ?_)))
    exact (mem_supportedFourCycles adj i j k l).2
      ⟨hij, hik, hli.symm, hjk, hjl, hkl, e₁ hij, e₂ hjk, e₃ hkl, e₄ hli⟩
  have hsum₁ : (∑ q ∈ W₁, f q) = ∑ t ∈ Paths, f (pathBacktrack t) := by
    unfold W₁
    refine Finset.sum_image ?_
    rintro ⟨i, j, k⟩ _ ⟨a, b, c⟩ _ h
    simp only [pathBacktrack, Prod.mk.injEq] at h ⊢
    tauto
  have hsum₂ : (∑ q ∈ W₂, f q) = ∑ t ∈ Paths, f (rotateCycle (pathBacktrack t)) := by
    unfold W₂
    refine Finset.sum_image ?_
    rintro ⟨i, j, k⟩ _ ⟨a, b, c⟩ _ h
    simp only [Function.comp_apply, pathBacktrack, rotateCycle, Prod.mk.injEq] at h ⊢
    tauto
  have h := sum_simple_cycles_add_backtracks_nonneg adj K C hC hK hKrot hunique hmatch
  classical
  change 0 ≤ ∑ q : CycleSlots s, if cycleUsesThreeLabels q then f q else 0
  rw [← Finset.sum_filter]
  change 0 ≤ ∑ q ∈ H, f q
  rw [← Finset.sum_subset hsub hrem]
  unfold U
  rw [Finset.sum_union hd₂, Finset.sum_union hd₁, hsum₁, hsum₂]
  exact h

private def reverseCycle {s : Type*} (q : CycleSlots s) : CycleSlots s :=
  (q.1, q.2.2.2, q.2.2.1, q.2.1)

private theorem cycleProduct_reverse {s : Type*} {n : ℕ}
    (C : s → s → Matrix (Fin n) (Fin n) ℂ) (hC : ∀ i j, (C i j)ᴴ = C j i)
    (q : CycleSlots s) :
    cycleProduct C (reverseCycle q) = star (cycleProduct C q) := by
  rcases q with ⟨i, j, k, l⟩
  unfold reverseCycle cycleProduct cycleTrace
  rw [← Matrix.trace_conjTranspose]
  simp only [Matrix.conjTranspose_mul, hC, Matrix.mul_assoc]

private theorem complex_cycle_sum_real {s : Type*} [Fintype s] {n : ℕ}
    (K : CycleSlots s → ℝ) (C : s → s → Matrix (Fin n) (Fin n) ℂ)
    (hC : ∀ i j, (C i j)ᴴ = C j i) (hKr : ∀ q, K (reverseCycle q) = K q) :
    (∑ q : CycleSlots s, (K q : ℂ) * cycleProduct C q).im = 0 := by
  let z : ℂ := ∑ q : CycleSlots s, (K q : ℂ) * cycleProduct C q
  have h : star z = z := by
    change star (∑ q : CycleSlots s, (K q : ℂ) * cycleProduct C q) =
      ∑ q : CycleSlots s, (K q : ℂ) * cycleProduct C q
    simp only [star_sum, star_mul', Complex.star_def, Complex.conj_ofReal]
    let e : CycleSlots s ≃ CycleSlots s :=
      ⟨reverseCycle, reverseCycle, fun ⟨_, _, _, _⟩ ↦ rfl, fun ⟨_, _, _, _⟩ ↦ rfl⟩
    refine Fintype.sum_equiv e _ _ fun q ↦ ?_
    change (K q : ℂ) * star (cycleProduct C q) =
      (K (reverseCycle q) : ℂ) * cycleProduct C (reverseCycle q)
    rw [hKr, cycleProduct_reverse C hC]
  have hi := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at hi
  change z.im = 0
  linarith

private theorem spectralBlock_adjoint {s : Type*} [DecidableEq s] {n : ℕ}
    (label : Fin n → s) {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsHermitian) (i j : s) :
    (spectralBlock label B i j)ᴴ = spectralBlock label B j i := by
  have hm (a : s) : (spectralMask label a)ᴴ = spectralMask label a := by
    unfold spectralMask
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext k
    by_cases hk : label k = a <;> simp [hk]
  simp only [spectralBlock, Matrix.conjTranspose_mul, hB.eq, hm, Matrix.mul_assoc]

private def spectralSlotKernel {s : Type*} (p : ℕ) (x : s → ℝ) (q : CycleSlots s) : ℝ :=
  gapDefect p (x q.1) (x q.2.1) (x q.2.2.1) (x q.2.2.2)

private theorem spectralSlotKernel_rotate {s : Type*} (p : ℕ) (x : s → ℝ) (q : CycleSlots s) :
    spectralSlotKernel p x (rotateCycle q) = spectralSlotKernel p x q := by
  rcases q with ⟨a, b, c, d⟩
  unfold spectralSlotKernel rotateCycle
  rw [ThreeBlockGram.gapDefect_swap23 p (x b) (x c) (x d) (x a),
    ThreeBlockGram.gapDefect_swap12 p (x b) (x c) (x a) (x d),
    ThreeBlockGram.gapDefect_swap01 p (x b) (x a) (x c) (x d)]

private theorem spectralSlotKernel_reverse {s : Type*} (p : ℕ) (x : s → ℝ) (q : CycleSlots s) :
    spectralSlotKernel p x (reverseCycle q) = spectralSlotKernel p x q := by
  rcases q with ⟨a, b, c, d⟩
  unfold spectralSlotKernel reverseCycle
  rw [ThreeBlockGram.gapDefect_swap23 p (x a) (x d) (x c) (x b),
    ThreeBlockGram.gapDefect_swap12 p (x a) (x d) (x b) (x c),
    ThreeBlockGram.gapDefect_swap23 p (x a) (x b) (x d) (x c)]

open private eigenDiagonal rootDiagonal contract diagonal_gap_scaled gaps_card_pos
  wordMean_conjugation monomial balanced gapDefect_diagonal
  from D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap

open scoped Classical ComplexOrder in
/-- For triangle-free spectral support with unique path completion,
the exact word comparison follows from the scalar cycle matchings
and the binary portion of the spectral trace sum. -/
theorem diagonal_word_bound_of_cycle_matchings_and_binary {s : Type*}
    [Fintype s] [DecidableEq s] {n : ℕ}
    (p : ℕ) (label : Fin n → s) (x : s → ℝ) (hx : ∀ s₀, 0 ≤ x s₀)
    (B : Matrix (Fin n) (Fin n) ℂ) (hB : B.IsHermitian) (adj : s → s → Prop)
    (hzero : ∀ i j, i ≠ j → ¬ adj i j → spectralBlock label B i j = 0)
    (htriangle : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      adj i j → adj j k → adj k i → False)
    (hunique : ∀ i j k l m, (i, j, k, l) ∈ supportedFourCycles adj →
      (i, j, k, m) ∈ supportedFourCycles adj → l = m)
    (hmatch : ∀ i j k l, (i, j, k, l) ∈ supportedFourCycles adj →
      spectralSlotKernel p x (i, j, k, l) ≤
        Real.sqrt (spectralSlotKernel p x (i, j, k, j) * spectralSlotKernel p x (k, l, i, l)) +
        Real.sqrt (spectralSlotKernel p x (j, k, l, k) * spectralSlotKernel p x (l, i, j, i)))
    (hbinary : 0 ≤ ∑ q : CycleSlots s, if cycleUsesThreeLabels q then 0 else
      weightedCycle (spectralSlotKernel p x) (spectralBlock label B) q) :
    trace ((rootDiagonal label x p * B) ^ 4) ≤
      FourCopyGap.wordMean p (eigenDiagonal label x) B := by
  classical
  let K := spectralSlotKernel p x
  let C := spectralBlock label B
  have hC : ∀ i j, (C i j)ᴴ = C j i := spectralBlock_adjoint label hB
  have hK (q : CycleSlots s) : 0 ≤ K q := gapDefect_nonneg p (hx _) (hx _) (hx _) (hx _)
  have hlarge := sum_three_label_terms_nonneg adj K C hC hK
    (fun i j k l ↦ spectralSlotKernel_rotate p x (i, j, k, l))
    hzero htriangle hunique hmatch
  have hRe : 0 ≤ ∑ q : CycleSlots s, weightedCycle K C q := by
    have hsplit :
        (∑ q : CycleSlots s, weightedCycle K C q) =
        (∑ q : CycleSlots s, if cycleUsesThreeLabels q then weightedCycle K C q else 0) +
        (∑ q : CycleSlots s, if cycleUsesThreeLabels q then 0 else weightedCycle K C q) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun q _ ↦ ?_)
      split_ifs <;> simp
    rw [hsplit]
    exact add_nonneg hlarge hbinary
  have hsum :
      ((gaps p).card : ℂ) * (FourCopyGap.wordMean p (eigenDiagonal label x) B -
        trace ((rootDiagonal label x p * B) ^ 4)) =
      ∑ q : CycleSlots s, (K q : ℂ) * cycleProduct C q := by
    rw [diagonal_gap_scaled]
    simp only [Fintype.sum_prod_type, K, C, contract, LinearMap.coe_mk, AddHom.coe_mk,
      spectralSlotKernel, cycleProduct]
  have hs : 0 ≤ ((gaps p).card : ℂ) * (FourCopyGap.wordMean p (eigenDiagonal label x) B -
      trace ((rootDiagonal label x p * B) ^ 4)) := by
    rw [hsum]
    refine Complex.nonneg_iff.mpr ⟨?_, ?_⟩
    · simpa only [Complex.re_sum, Complex.re_ofReal_mul, weightedCycle] using hRe
    · exact (complex_cycle_sum_real K C hC (spectralSlotKernel_reverse p x)).symm
  have hc : (0 : ℝ) < (gaps p).card := by exact_mod_cast gaps_card_pos p
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hs
  simp only [Complex.mul_re, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
    Complex.sub_re, Complex.sub_im, zero_mul, sub_zero, add_zero] at hre him
  exact Complex.le_def.mpr ⟨sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hc).mp hre),
    (sub_eq_zero.mp ((mul_eq_zero.mp him.symm).resolve_left hc.ne')).symm⟩

open scoped Classical in
private theorem continuous_gapDefect_at_four_functions (p : ℕ)
    {a b c d : ℝ → ℝ} (ha : Continuous a) (hb : Continuous b)
    (hc : Continuous c) (hd : Continuous d) :
    Continuous (fun t ↦ gapDefect p (a t) (b t) (c t) (d t)) := by
  unfold gapDefect monomial balanced
  have hpow (f : ℝ → ℝ) (hf : Continuous f) :
      Continuous (fun t ↦ f t ^ ((p : ℝ) / 4)) :=
    (Real.continuous_rpow_const (by positivity)).comp hf
  refine (continuous_finsetSum _ fun g _ ↦ ?_).sub
    (continuous_const.mul (((hpow a ha).mul (hpow b hb)).mul (hpow c hc) |>.mul (hpow d hd)))
  fun_prop

open Filter Set Topology in
private theorem gapDefect_binary_weak (p : ℕ) (hp : 0 < p) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    gapDefect p x x y y ^ 2 ≤ 4 * gapDefect p x x x y * gapDefect p y y y x := by
  by_cases hxy : x = y
  · subst y
    simp [gapDefect_diagonal p x hx]
  let a (t : ℝ) := x + t
  let b (t : ℝ) := y + t
  have ha : Continuous a := by unfold a; fun_prop
  have hb : Continuous b := by unfold b; fun_prop
  have hl := (continuous_gapDefect_at_four_functions p ha ha hb hb).pow 2
  have hr : Continuous (fun t ↦ 4 * gapDefect p (a t) (a t) (a t) (b t) *
      gapDefect p (b t) (b t) (b t) (a t)) :=
    (continuous_const.mul (continuous_gapDefect_at_four_functions p ha ha ha hb)).mul
    (continuous_gapDefect_at_four_functions p hb hb hb ha)
  have h := le_of_tendsto_of_tendsto
    (hl.continuousAt (x := 0) |>.continuousWithinAt (s := Set.Ioi (0 : ℝ)))
    (hr.continuousAt (x := 0) |>.continuousWithinAt (s := Set.Ioi (0 : ℝ))) (by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : 0 < t := ht
      have hat : 0 < a t := add_pos_of_nonneg_of_pos hx ht'
      have hbt : 0 < b t := add_pos_of_nonneg_of_pos hy ht'
      have hne : a t ≠ b t := by
        intro hab
        exact hxy (add_right_cancel hab)
      have hc := ThreeBlockGram.spectralDefect_binary_conditioning p hp
        ![a t, b t, 0] 0 1 hat hbt hne
      change gapDefect p (a t) (a t) (b t) (b t) ^ 2 <
        2 * gapDefect p (a t) (a t) (a t) (b t) *
          gapDefect p (b t) (b t) (b t) (a t) at hc
      have hf := gapDefect_nonneg p hat.le hat.le hat.le hbt.le
      have hg := gapDefect_nonneg p hbt.le hbt.le hbt.le hat.le
      exact hc.le.trans (by
        nlinarith only [mul_nonneg hf hg]))
  simpa [a, b] using h

private theorem binary_orbit_sum (F : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ)
    (hr : ∀ a b c d, F b c d a = F a b c d)
    (h₀ : F 0 0 0 0 = 0) (h₁ : F 1 1 1 1 = 0) :
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) =
      4 * (F 0 0 0 1 + F 0 1 1 1 + F 0 0 1 1) + 2 * F 0 1 0 1 := by
  have h0010 := hr 0 0 0 1
  have h0100 := (hr 0 0 1 0).trans h0010
  have h1000 := (hr 0 1 0 0).trans h0100
  have h1110 := hr 0 1 1 1
  have h1101 := (hr 1 1 1 0).trans h1110
  have h1011 := (hr 1 1 0 1).trans h1101
  have h0110 := hr 0 0 1 1
  have h1100 := (hr 0 1 1 0).trans h0110
  have h1001 := (hr 1 1 0 0).trans h1100
  have h1010 := hr 0 1 0 1
  simp only [Fin.sum_univ_two, h₀, h₁, h0010, h0100, h1000, h1110, h1101, h1011,
    h0110, h1100, h1001, h1010]
  ring

private theorem trace_self_square_re_eq_frobSq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : Mᴴ = M) : (trace (M * M)).re = RHLinalg.frobSq M := by
  unfold RHLinalg.frobSq
  rw [hM, RCLike.re_eq_complex_re]

private theorem trace_mul_adjoint_abs_re_le {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) :
    |(trace (X * Yᴴ)).re| ≤ Real.sqrt (RHLinalg.frobSq X * RHLinalg.frobSq Y) := by
  apply (Real.le_sqrt (abs_nonneg _) (mul_nonneg (frobSq_nonneg X) (frobSq_nonneg Y))).mpr
  rw [sq_abs]
  have h := trace_product_cauchy X Yᴴ
  rw [frobSq_star, Complex.normSq_apply] at h
  nlinarith only [h, sq_nonneg (trace (X * Yᴴ)).im]

set_option maxHeartbeats 600000 in
-- The four orbit representatives require normalizing the matrix trace and the scalar kernel.
private theorem binary_pair_orbit_nonneg {s : Type*} {n : ℕ}
    (p : ℕ) (hp : 0 < p) (x : s → ℝ) (hx : ∀ s₀, 0 ≤ x s₀)
    (C : s → s → Matrix (Fin n) (Fin n) ℂ) (hC : ∀ a b, (C a b)ᴴ = C b a)
    (i j : s) :
    0 ≤ (∑ a : Fin 2, ∑ b : Fin 2, ∑ c : Fin 2, ∑ d : Fin 2,
      weightedCycle (spectralSlotKernel p x) C
        ((![i, j] : Fin 2 → s) a, (![i, j] : Fin 2 → s) b,
         (![i, j] : Fin 2 → s) c, (![i, j] : Fin 2 → s) d)) := by
  let D := C i i
  let E := C j j
  let B := C i j
  let U := D * B
  let V := B * E
  let f := gapDefect p (x i) (x i) (x i) (x j)
  let g := gapDefect p (x i) (x i) (x j) (x j)
  let h := gapDefect p (x j) (x j) (x j) (x i)
  let K := spectralSlotKernel p x
  have hD : Dᴴ = D := hC i i
  have hE : Eᴴ = E := hC j j
  have hB : Bᴴ = C j i := hC i j
  have hu : (cycleProduct C (i, i, i, j)).re = RHLinalg.frobSq U := by
    change (trace (D * D * B * C j i)).re = (trace ((D * B)ᴴ * (D * B))).re
    rw [← hB, Matrix.conjTranspose_mul, hD]
    congr 1
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (D * D * B) Bᴴ
  have hv : (cycleProduct C (i, j, j, j)).re = RHLinalg.frobSq V := by
    change (trace (B * E * E * C j i)).re = (trace ((B * E)ᴴ * (B * E))).re
    rw [← hB, Matrix.conjTranspose_mul, hE]
    congr 1
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (B * E) (E * Bᴴ)
  have huv : (cycleProduct C (i, i, j, j)).re = (trace (U * Vᴴ)).re := by
    change (trace (D * B * E * C j i)).re = (trace ((D * B) * (B * E)ᴴ)).re
    rw [Matrix.conjTranspose_mul, hE, hB]
    simp only [Matrix.mul_assoc]
  have halt : 0 ≤ (cycleProduct C (i, j, i, j)).re := by
    have hG : (B * Bᴴ)ᴴ = B * Bᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    change 0 ≤ (trace (B * C j i * B * C j i)).re
    rw [← hB, show B * Bᴴ * B * Bᴴ = (B * Bᴴ) * (B * Bᴴ) by noncomm_ring,
      trace_self_square_re_eq_frobSq _ hG]
    exact frobSq_nonneg _
  have hkalt : K (i, j, i, j) = g :=
    (ThreeBlockGram.gapDefect_swap12 p (x i) (x i) (x j) (x j)).symm
  have h111 : K (i, j, j, j) = h := by
    have hr := spectralSlotKernel_rotate p x (i, j, j, j)
    exact hr.symm
  have hF : 0 ≤ f := gapDefect_nonneg p (hx i) (hx i) (hx i) (hx j)
  have hG : 0 ≤ g := gapDefect_nonneg p (hx i) (hx i) (hx j) (hx j)
  have hH : 0 ≤ h := gapDefect_nonneg p (hx j) (hx j) (hx j) (hx i)
  have hg : g ≤ 2 * Real.sqrt (f * h) := by
    apply le_of_pow_le_pow_left₀ two_ne_zero (by positivity)
    have he := gapDefect_binary_weak p hp (hx i) (hx j)
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hF hH)]
    norm_num
    simpa only [f, g, h, mul_assoc] using he
  have hpair := opposite_pair_compensation hF hH (frobSq_nonneg U) (frobSq_nonneg V)
    (trace_mul_adjoint_abs_re_le U V)
  have hgap := mul_le_mul_of_nonneg_right hg (abs_nonneg (trace (U * Vᴴ)).re)
  have hneg := mul_le_mul_of_nonneg_left (neg_abs_le (trace (U * Vᴴ)).re) hG
  have hs : 0 ≤ f * RHLinalg.frobSq U + h * RHLinalg.frobSq V + g * (trace (U * Vᴴ)).re := by
    nlinarith only [hpair, hgap.trans hpair, hneg]
  have ha : 0 ≤ g * (cycleProduct C (i, j, i, j)).re := mul_nonneg hG halt
  let e : Fin 2 → s := ![i, j]
  let F (a b c d : Fin 2) := weightedCycle K C (e a, e b, e c, e d)
  change 0 ≤ ∑ a, ∑ b, ∑ c, ∑ d, F a b c d
  rw [binary_orbit_sum F]
  · change 0 ≤ 4 * (weightedCycle K C (i, i, i, j) + weightedCycle K C (i, j, j, j) +
      weightedCycle K C (i, i, j, j)) + 2 * weightedCycle K C (i, j, i, j)
    simp only [weightedCycle, hu, hv, huv, h111, hkalt]
    change 0 ≤ 4 * (f * RHLinalg.frobSq U + h * RHLinalg.frobSq V + g * (trace (U * Vᴴ)).re) +
      2 * (g * (cycleProduct C (i, j, i, j)).re)
    have h₄ : (0 : ℝ) ≤ 4 := by norm_num
    have h₂ : (0 : ℝ) ≤ 2 := by norm_num
    exact add_nonneg (mul_nonneg h₄ hs) (mul_nonneg h₂ ha)
  · intro a b c d
    exact weightedCycle_rotate K C (spectralSlotKernel_rotate p x) (e a, e b, e c, e d)
  · change weightedCycle K C (i, i, i, i) = 0
    rw [weightedCycle, show K (i, i, i, i) = 0 from gapDefect_diagonal p (x i) (hx i), zero_mul]
  · change weightedCycle K C (j, j, j, j) = 0
    rw [weightedCycle, show K (j, j, j, j) = 0 from gapDefect_diagonal p (x j) (hx j), zero_mul]

private def cycleLabelSet {s : Type*} [DecidableEq s] (q : CycleSlots s) : Finset s :=
  {q.1, q.2.1, q.2.2.1, q.2.2.2}

private theorem card_cycleLabelSet_le_two {s : Type*} [DecidableEq s]
    (q : CycleSlots s) (h : ¬ cycleUsesThreeLabels q) : (cycleLabelSet q).card ≤ 2 := by
  rcases q with ⟨i, j, k, l⟩
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      simpa [cycleLabelSet] using (Finset.card_le_two (a := i) (b := l))
    · have hl : l = i ∨ l = k := by
        simp only [cycleUsesThreeLabels] at h
        grind [distinctTriple]
      apply (Finset.card_le_card (t := {i, k}) ?_).trans Finset.card_le_two
      intro a ha
      simp only [cycleLabelSet, Finset.mem_insert, Finset.mem_singleton] at ha ⊢
      grind
  · have hk : k = i ∨ k = j := by
      simp only [cycleUsesThreeLabels] at h
      grind [distinctTriple]
    have hl : l = i ∨ l = j := by
      simp only [cycleUsesThreeLabels] at h
      grind [distinctTriple]
    apply (Finset.card_le_card (t := {i, j}) ?_).trans Finset.card_le_two
    intro a ha
    simp only [cycleLabelSet, Finset.mem_insert, Finset.mem_singleton] at ha ⊢
    grind

open scoped Classical in
/-- The global part of the fourth trace involving at most two distinct
labels is a sum of binary positive forms, for Hermitian block data. -/
theorem sum_binary_spectral_terms_nonneg {s : Type*} [Fintype s] {n : ℕ}
    (p : ℕ) (hp : 0 < p) (x : s → ℝ) (hx : ∀ i, 0 ≤ x i)
    (C : s → s → Matrix (Fin n) (Fin n) ℂ) (hC : ∀ a b, (C a b)ᴴ = C b a) :
    0 ≤ ∑ q : CycleSlots s, if cycleUsesThreeLabels q then 0 else
      weightedCycle (spectralSlotKernel p x) C q := by
  classical
  let f := weightedCycle (spectralSlotKernel p x) C
  let H := (Finset.univ : Finset (CycleSlots s)).filter (fun q ↦ ¬ cycleUsesThreeLabels q)
  have hsum : (∑ q : CycleSlots s, if cycleUsesThreeLabels q then 0 else f q) =
      ∑ q ∈ H, f q := by
    unfold H
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun q _ ↦ by split_ifs <;> simp_all
  change 0 ≤ ∑ q : CycleSlots s, if cycleUsesThreeLabels q then 0 else f q
  rw [hsum, ← Finset.sum_fiberwise_of_maps_to (g := cycleLabelSet)
    (t := H.image cycleLabelSet) (fun q hq ↦ Finset.mem_image_of_mem _ hq)]
  refine Finset.sum_nonneg fun T hT ↦ ?_
  obtain ⟨q, hq, hqT⟩ := Finset.mem_image.mp hT
  have hcard : T.card ≤ 2 := hqT ▸ card_cycleLabelSet_le_two q (Finset.mem_filter.mp hq).2
  have hmem : q.1 ∈ T := by
    rw [← hqT]
    simp [cycleLabelSet]
  have hpos := Finset.card_pos.mpr ⟨q.1, hmem⟩
  by_cases hcard₂ : T.card = 2
  · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hcard₂
    let e : Fin 2 → s := ![i, j]
    let emap (v : CycleSlots (Fin 2)) : CycleSlots s :=
      (e v.1, e v.2.1, e v.2.2.1, e v.2.2.2)
    let W := (Finset.univ : Finset (CycleSlots (Fin 2))).image emap
    have he (a : s) (ha : a ∈ ({i, j} : Finset s)) : ∃ k : Fin 2, e k = a := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    let G := H.filter (fun q ↦ cycleLabelSet q = {i, j})
    have hsub : G ⊆ W := by
      intro q' hq'
      rcases q' with ⟨a, b, c, d⟩
      have h := (Finset.mem_filter.mp hq').2
      have ha : a ∈ ({i, j} : Finset s) := by rw [← h]; simp [cycleLabelSet]
      have hb : b ∈ ({i, j} : Finset s) := by rw [← h]; simp [cycleLabelSet]
      have hc : c ∈ ({i, j} : Finset s) := by rw [← h]; simp [cycleLabelSet]
      have hd : d ∈ ({i, j} : Finset s) := by rw [← h]; simp [cycleLabelSet]
      obtain ⟨a', ha'⟩ := he a ha
      obtain ⟨b', hb'⟩ := he b hb
      obtain ⟨c', hc'⟩ := he c hc
      obtain ⟨d', hd'⟩ := he d hd
      exact Finset.mem_image.mpr ⟨(a', b', c', d'), Finset.mem_univ _,
        by simp only [emap, ha', hb', hc', hd']⟩
    have hrem : ∀ q' ∈ W, q' ∉ G → f q' = 0 := by
      intro q' hq' hn
      obtain ⟨⟨a, b, c, d⟩, _, rfl⟩ := Finset.mem_image.mp hq'
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
        simp [G, H, emap, e, cycleLabelSet, cycleUsesThreeLabels, distinctTriple,
          hij, Ne.symm hij, Finset.pair_comm j i,
          f, weightedCycle, spectralSlotKernel, gapDefect_diagonal p _ (hx _)]
          at hn ⊢
    have heinj : Function.Injective e := by
      intro u v h
      fin_cases u <;> fin_cases v <;>
        first
        | rfl
        | exact (hij h).elim
        | exact (hij h.symm).elim
    have hmapinj : Set.InjOn emap (↑(Finset.univ : Finset (CycleSlots (Fin 2))) : Set _) := by
      rintro ⟨a, b, c, d⟩ _ ⟨a', b', c', d'⟩ _ h
      simp only [emap, Prod.mk.injEq] at h ⊢
      exact ⟨heinj h.1, heinj h.2.1, heinj h.2.2.1, heinj h.2.2.2⟩
    change 0 ≤ ∑ q' ∈ G, f q'
    rw [Finset.sum_subset hsub hrem, Finset.sum_image hmapinj]
    simpa only [Fintype.sum_prod_type] using binary_pair_orbit_nonneg p hp x hx C hC i j
  · have hone : T.card = 1 := by omega
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hone
    apply Finset.sum_nonneg
    rintro ⟨a, b, c, d⟩ hq'
    have h := (Finset.mem_filter.mp hq').2
    have ha : a ∈ ({i} : Finset s) := by rw [← h]; simp [cycleLabelSet]
    have hb : b ∈ ({i} : Finset s) := by rw [← h]; simp [cycleLabelSet]
    have hc : c ∈ ({i} : Finset s) := by rw [← h]; simp [cycleLabelSet]
    have hd : d ∈ ({i} : Finset s) := by rw [← h]; simp [cycleLabelSet]
    simp only [Finset.mem_singleton] at ha hb hc hd
    simp [ha, hb, hc, hd, f, weightedCycle, spectralSlotKernel, gapDefect_diagonal p (x i) (hx i)]

private def cycleMatching {s : Type*} (K : CycleSlots s → ℝ) (q : CycleSlots s) : Prop :=
  K q ≤ Real.sqrt (K (backtrack q) * K (backtrack (rotateCycle (rotateCycle q)))) +
    Real.sqrt (K (backtrack (rotateCycle q)) *
      K (backtrack (rotateCycle (rotateCycle (rotateCycle q)))))

private theorem cycleMatching_rotate {s : Type*} (K : CycleSlots s → ℝ)
    (hK : ∀ q, K (rotateCycle q) = K q) (q : CycleSlots s) :
    cycleMatching K (rotateCycle q) ↔ cycleMatching K q := by
  have h : rotateCycle (rotateCycle (rotateCycle (rotateCycle q))) = q := by
    rcases q with ⟨i, j, k, l⟩
    rfl
  unfold cycleMatching
  rw [h, hK q, mul_comm (K (backtrack (rotateCycle (rotateCycle q)))), add_comm]

private theorem spectralCycleMatching_of_zero {s : Type*}
    (p : ℕ) (hp : 0 < p) (x : s → ℝ) (hx : ∀ i, 0 ≤ x i) (q : CycleSlots s)
    (hz : x q.1 = 0 ∨ x q.2.1 = 0 ∨ x q.2.2.1 = 0 ∨ x q.2.2.2 = 0) :
    cycleMatching (spectralSlotKernel p x) q := by
  let K := spectralSlotKernel p x
  have hm (q' : CycleSlots s) (hzero : x q'.2.2.1 = 0) : cycleMatching K q' := by
    rcases q' with ⟨i, j, k, l⟩
    change x k = 0 at hzero
    have h := gapDefect_one_zero_le p hp (hx l) (hx i) (hx j)
    change K (i, j, k, l) ≤
      Real.sqrt (K (i, j, k, j) * K (k, l, i, l)) +
      Real.sqrt (K (j, k, l, k) * K (l, i, j, i))
    have h₁ : K (k, l, i, l) = K (i, l, k, l) := by
      change gapDefect p (x k) (x l) (x i) (x l) = gapDefect p (x i) (x l) (x k) (x l)
      rw [ThreeBlockGram.gapDefect_swap01 p (x k) (x l) (x i) (x l),
        ThreeBlockGram.gapDefect_swap12 p (x l) (x k) (x i) (x l),
        ThreeBlockGram.gapDefect_swap01 p (x l) (x i) (x k) (x l)]
    have h₂ : K (j, k, l, k) = K (k, j, k, l) :=
      spectralSlotKernel_rotate p x (k, j, k, l)
    have h₃ : K (l, i, j, i) = K (i, i, j, l) := calc
      _ = K (i, j, i, l) := (spectralSlotKernel_rotate p x (l, i, j, i)).symm
      _ = _ := (ThreeBlockGram.gapDefect_swap12 p (x i) (x i) (x j) (x l)).symm
    rw [h₁, h₂, h₃, mul_comm (K (i, j, k, j)), mul_comm (K (k, j, k, l))]
    simpa only [K, spectralSlotKernel, hzero] using h
  have hr (q' : CycleSlots s) : cycleMatching K (rotateCycle q') ↔ cycleMatching K q' :=
    cycleMatching_rotate K (spectralSlotKernel_rotate p x) q'
  rcases hz with h₁ | h₂ | h₃ | h₄
  · exact (hr q).1 ((hr (rotateCycle q)).1 (hm (rotateCycle (rotateCycle q)) h₁))
  · exact (hr q).1 ((hr (rotateCycle q)).1
      ((hr (rotateCycle (rotateCycle q))).1
        (hm (rotateCycle (rotateCycle (rotateCycle q))) h₂)))
  · exact hm q h₃
  · exact (hr q).1 (hm (rotateCycle q) h₄)

open scoped ComplexOrder in
/-- Four-copy comparison for a Hermitian second factor with triangle-free
spectral support, unique two-edge path completions, and a zero label on
every supported simple four-cycle. -/
theorem diagonal_word_bound_of_singular_four_cycles {s : Type*}
    [Fintype s] [DecidableEq s] {n : ℕ}
    (p : ℕ) (hp : 0 < p) (label : Fin n → s) (x : s → ℝ) (hx : ∀ i, 0 ≤ x i)
    (B : Matrix (Fin n) (Fin n) ℂ) (hB : B.IsHermitian) (adj : s → s → Prop)
    (hzero : ∀ i j, i ≠ j → ¬ adj i j → spectralBlock label B i j = 0)
    (htriangle : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      adj i j → adj j k → adj k i → False)
    (hunique : ∀ i j k l m, (i, j, k, l) ∈ supportedFourCycles adj →
      (i, j, k, m) ∈ supportedFourCycles adj → l = m)
    (hcycleZero : ∀ i j k l, (i, j, k, l) ∈ supportedFourCycles adj →
      x i = 0 ∨ x j = 0 ∨ x k = 0 ∨ x l = 0) :
    trace ((rootDiagonal label x p * B) ^ 4) ≤
      FourCopyGap.wordMean p (eigenDiagonal label x) B :=
  diagonal_word_bound_of_cycle_matchings_and_binary p label x hx B hB adj
    hzero htriangle hunique
    (fun i j k l hq ↦ spectralCycleMatching_of_zero p hp x hx (i, j, k, l)
      (hcycleZero i j k l hq))
    (sum_binary_spectral_terms_nonneg p hp x hx (spectralBlock label B)
      (spectralBlock_adjoint label hB))

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator in
/-- Hägele's four-copy comparison when the Hermitian factor has triangle-free
spectral support, unique two-edge path completions, and a zero eigenvalue on
each supported simple four-cycle. -/
theorem product_bound_of_singular_four_cycles {s : Type*}
    [Fintype s] [DecidableEq s] {n : ℕ}
    (p : ℕ) (hp : 0 < p) (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosSemidef) (hB : B.IsHermitian) (label : Fin n → s)
    (x : s → ℝ) (hx : ∀ i, 0 ≤ x i) (U : Matrix.unitaryGroup (Fin n) ℂ)
    (hdiag : Unitary.conjStarAlgAut ℂ _ U A = eigenDiagonal label x)
    (adj : s → s → Prop)
    (hzero : ∀ i j, i ≠ j → ¬ adj i j →
      spectralBlock label (Unitary.conjStarAlgAut ℂ _ U B) i j = 0)
    (htriangle : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      adj i j → adj j k → adj k i → False)
    (hunique : ∀ i j k l m, (i, j, k, l) ∈ supportedFourCycles adj →
      (i, j, k, m) ∈ supportedFourCycles adj → l = m)
    (hcycleZero : ∀ i j k l, (i, j, k, l) ∈ supportedFourCycles adj →
      x i = 0 ∨ x j = 0 ∨ x k = 0 ∨ x l = 0) :
    trace (((A ^ ((p : ℝ) / 4)) * B) ^ 4) ≤ FourCopyGap.wordMean p A B := by
  let φ := Unitary.conjStarAlgAut ℂ _ U
  have hB' : (φ B).IsHermitian := by
    change star (φ B) = φ B
    rw [← map_star, Matrix.star_eq_conjTranspose, hB.eq]
  have hr : φ (A ^ ((p : ℝ) / 4)) = rootDiagonal label x p := by
    let f : ℝ → ℝ := fun y ↦ y ^ ((p : ℝ) / 4)
    have hf : φ (cfc f A) = cfc f (φ A) :=
      StarAlgHomClass.map_cfc (p := IsSelfAdjoint) (q := IsSelfAdjoint) φ f A
        (hf := (Set.toFinite (spectrum ℝ A)).continuousOn f)
        (hφ := φ.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional)
        (ha := hA.isHermitian) (hφa := by
          have hSelf : IsSelfAdjoint A := hA.isHermitian
          exact hSelf.map φ)
    rw [CFC.rpow_eq_cfc_real hA.nonneg, hf, show φ A = _ from hdiag]
    exact D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_diagonal
      f (fun a ↦ x (label a))
  have hm : FourCopyGap.wordMean p (eigenDiagonal label x) (φ B) =
      FourCopyGap.wordMean p A B := by
    rw [← hdiag]
    exact wordMean_conjugation p U A B
  have ht : trace ((rootDiagonal label x p * φ B) ^ 4) =
      trace (((A ^ ((p : ℝ) / 4)) * B) ^ 4) := by
    rw [← hr, ← map_mul φ, ← map_pow φ]
    exact trace_conjugation U _
  simpa only [ht, hm] using diagonal_word_bound_of_singular_four_cycles p hp label x hx (φ B) hB'
    adj hzero htriangle hunique hcycleZero

end
end RefinedBMV.Tracial
