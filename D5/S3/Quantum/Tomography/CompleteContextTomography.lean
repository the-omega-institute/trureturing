/- GID: D5/S3/Quantum/Tomography/CompleteContextTomography
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/CompleteContextTomography
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A complete complementary context family spans every traceless Hermitian matrix. -/

import D5.S3.Quantum.Tomography.RankOneContextCommutator
import Mathlib.LinearAlgebra.Dimension.Constructions

/- Library-search audit trail (2026-08-21):
   * Repository searches for complete complementary context tomography, projector-trace
     completeness, and traceless diagonal direct sums found no theorem deriving all three
     conclusions below from pairwise complementary overlaps.
   * `D5/S3/QuantumContext/CompleteBasisReconstruction.lean` is a related exact-formula hit,
     but it assumes the projector-trace completeness that is derived here.
   * Pinned Mathlib has no packaged complementary-basis completeness theorem. Exact supporting
     hits `Fintype.linearIndependent_iff`,
     `LinearIndependent.span_eq_top_of_card_eq_finrank`, `Module.finrank_matrix`, and
     `Matrix.ext_iff_trace_mul_right` are applied below. -/

open scoped BigOperators

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.CompleteContextTomography

open Matrix
open D5.S3.Quantum.Tomography.RankOneContextCommutator

private def tomographyVector {n : Nat}
    (context : Fin (n + 2) -> RankOneContext (n + 1)) :
    Option (Fin (n + 2) × Fin n) -> Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ
  | none => 1
  | some (l, j) => (context l).projector j.succ - (context l).projector 0

private theorem trace_hermitian_product_real {n : Nat}
    {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ = X) (hY : Yᴴ = Y) :
    (trace (X * Y)).im = 0 := by
  have hstar : star (trace (X * Y)) = trace (X * Y) := by
    calc
      star (trace (X * Y)) = trace ((X * Y)ᴴ) := (trace_conjTranspose (X * Y)).symm
      _ = trace (Y * X) := by rw [conjTranspose_mul, hX, hY]
      _ = trace (X * Y) := trace_mul_comm Y X
  have him := congrArg Complex.im hstar
  simp only [Complex.star_def, Complex.conj_im] at him
  linarith

private theorem tomography_pairing {n : Nat}
    (context : Fin (n + 2) -> RankOneContext (n + 1))
    (hoverlap : ∀ l k j r,
      trace ((context l).projector j * (context k).projector r) =
        if l = k then (if j = r then 1 else 0) else ((n + 1 : Nat) : ℂ)⁻¹)
    (l k : Fin (n + 2)) (a b : Fin n) :
    trace (tomographyVector context (some (l, a)) *
      tomographyVector context (some (k, b))) =
        if l = k then (if a = b then 2 else 1) else 0 := by
  simp only [tomographyVector, Matrix.sub_mul, Matrix.mul_sub, trace_sub]
  by_cases hlk : l = k
  · subst k
    by_cases hab : a = b
    · subst b
      have hzero : (0 : Fin (n + 1)) ≠ a.succ := (Fin.succ_ne_zero a).symm
      simp [tomographyVector, hoverlap, hzero]
      norm_num
    · have hsucc : a.succ ≠ b.succ := fun h => hab (Fin.succ_injective _ h)
      have hzero : (0 : Fin (n + 1)) ≠ b.succ := (Fin.succ_ne_zero b).symm
      simp [tomographyVector, hoverlap, hab, hsucc, hzero]
  · have hzeroA : (0 : Fin (n + 1)) ≠ a.succ := (Fin.succ_ne_zero a).symm
    have hzeroB : (0 : Fin (n + 1)) ≠ b.succ := (Fin.succ_ne_zero b).symm
    simp [tomographyVector, hoverlap, hlk, hzeroA, hzeroB]

private theorem tomography_linearIndependent {n : Nat}
    (context : Fin (n + 2) -> RankOneContext (n + 1))
    (hoverlap : ∀ l k j r,
      trace ((context l).projector j * (context k).projector r) =
        if l = k then (if j = r then 1 else 0) else ((n + 1 : Nat) : ℂ)⁻¹) :
    LinearIndependent ℂ (tomographyVector context) := by
  rw [Fintype.linearIndependent_iff]
  intro coefficient hsum
  have hnone : coefficient none = 0 := by
    have htrace : ∑ i, coefficient i * trace (tomographyVector context i) = 0 := by
      simpa only [trace_sum, trace_smul, smul_eq_mul, trace_zero] using congrArg trace hsum
    rw [Fintype.sum_option] at htrace
    have hdifference (pair : Fin (n + 2) × Fin n) :
        trace (tomographyVector context (some pair)) = 0 := by
      simp [tomographyVector, (context pair.1).rankOne pair.2.succ |>.2.2.1,
        (context pair.1).rankOne 0 |>.2.2.1]
    simp_rw [hdifference] at htrace
    simp only [mul_zero, Finset.sum_const_zero, add_zero, tomographyVector, trace_one,
      Fintype.card_fin] at htrace
    have hdim : (((n + 1 : Nat) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    exact (mul_eq_zero.mp htrace).resolve_right hdim
  have hequation (l : Fin (n + 2)) (b : Fin n) :
      coefficient (some (l, b)) + ∑ a, coefficient (some (l, a)) = 0 := by
    have hpaired : ∑ i, coefficient i *
        trace (tomographyVector context i * tomographyVector context (some (l, b))) = 0 := by
      simpa only [Matrix.sum_mul, Matrix.smul_mul, trace_sum, trace_smul, zero_mul,
        trace_zero, smul_eq_mul] using
        congrArg (fun X => trace (X * tomographyVector context (some (l, b)))) hsum
    rw [Fintype.sum_option] at hpaired
    rw [hnone] at hpaired
    simp only [zero_mul, zero_add] at hpaired
    simp_rw [tomography_pairing context hoverlap] at hpaired
    rw [Fintype.sum_prod_type] at hpaired
    simp only [mul_ite, mul_zero] at hpaired
    simp only [mul_one] at hpaired
    have hinner (x : Fin (n + 2)) :
        (∑ y, if y = b then coefficient (some (x, y)) * 2
          else coefficient (some (x, y))) =
          coefficient (some (x, b)) + ∑ y, coefficient (some (x, y)) := by
      calc
        (∑ y, if y = b then coefficient (some (x, y)) * 2
            else coefficient (some (x, y))) =
            ∑ y, (coefficient (some (x, y)) +
              (if y = b then coefficient (some (x, y)) else 0)) := by
                apply Finset.sum_congr rfl
                intro y _
                by_cases hy : y = b <;> simp [hy] <;> ring
        _ = (∑ y, coefficient (some (x, y))) +
              ∑ y, (if y = b then coefficient (some (x, y)) else 0) :=
            Finset.sum_add_distrib
        _ = (∑ y, coefficient (some (x, y))) + coefficient (some (x, b)) := by
          simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
        _ = coefficient (some (x, b)) + ∑ y, coefficient (some (x, y)) := by ring
    have hinner_zero (x : Fin (n + 2)) :
        (∑ y, if x = l then if y = b then coefficient (some (x, y)) * 2
          else coefficient (some (x, y)) else 0) =
          if x = l then coefficient (some (x, b)) +
            ∑ y, coefficient (some (x, y)) else 0 := by
      by_cases hxl : x = l
      · simp only [hxl, if_true]
        rw [hinner]
      · simp [hxl]
    simp_rw [hinner_zero] at hpaired
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hpaired
    simpa using hpaired
  have hblock (l : Fin (n + 2)) : ∀ a, coefficient (some (l, a)) = 0 := by
    let total : ℂ := ∑ a, coefficient (some (l, a))
    have htotal : total = 0 := by
      have hsumEquations : ∑ a, (coefficient (some (l, a)) + total) = 0 := by
        apply Finset.sum_eq_zero
        intro a _
        exact hequation l a
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, total] at hsumEquations
      have hfactor : (((n + 1 : Nat) : ℂ)) * total = 0 := by
        calc
          (((n + 1 : Nat) : ℂ)) * total = total + ((n : ℂ) * total) := by
            rw [Nat.cast_add, Nat.cast_one]
            ring
          _ = (∑ a, coefficient (some (l, a))) +
              (∑ a, coefficient (some (l, a))) * (n : ℂ) := by
            dsimp only [total]
            ring
          _ = 0 := by
            simpa [mul_comm] using hsumEquations
      have hdim : (((n + 1 : Nat) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      exact (mul_eq_zero.mp hfactor).resolve_left hdim
    intro a
    have ha := hequation l a
    change coefficient (some (l, a)) + total = 0 at ha
    rw [htotal, add_zero] at ha
    exact ha
  intro i
  cases i with
  | none => exact hnone
  | some pair => exact hblock pair.1 pair.2

private theorem tomography_spans {n : Nat}
    (context : Fin (n + 2) -> RankOneContext (n + 1))
    (hoverlap : ∀ l k j r,
      trace ((context l).projector j * (context k).projector r) =
        if l = k then (if j = r then 1 else 0) else ((n + 1 : Nat) : ℂ)⁻¹) :
    Submodule.span ℂ (Set.range (tomographyVector context)) = ⊤ := by
  apply (tomography_linearIndependent context hoverlap).span_eq_top_of_card_eq_finrank
  rw [Fintype.card_option, Fintype.card_prod, Module.finrank_matrix]
  simp only [Fintype.card_fin, Module.finrank_self]
  ring

private theorem projector_traces_complete {n : Nat}
    (context : Fin (n + 2) -> RankOneContext (n + 1))
    (hoverlap : ∀ l k j r,
      trace ((context l).projector j * (context k).projector r) =
        if l = k then (if j = r then 1 else 0) else ((n + 1 : Nat) : ℂ)⁻¹)
    {X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (htraces : ∀ l j, trace (X * (context l).projector j) = 0) :
    X = 0 := by
  have htrace : trace X = 0 := by
    calc
      trace X = trace (X * 1) := by rw [Matrix.mul_one]
      _ = trace (X * ∑ j, (context 0).projector j) := by rw [(context 0).resolvesIdentity]
      _ = ∑ j, trace (X * (context 0).projector j) := by
        rw [Matrix.mul_sum, trace_sum]
      _ = 0 := by simp [htraces]
  have hcoordinate (i : Option (Fin (n + 2) × Fin n)) :
      trace (X * tomographyVector context i) = 0 := by
    cases i with
    | none => simpa [tomographyVector] using htrace
    | some pair =>
      rw [tomographyVector, Matrix.mul_sub, trace_sub, htraces, htraces, sub_zero]
  rw [Matrix.ext_iff_trace_mul_right]
  intro Y
  have hmem : Y ∈ Submodule.span ℂ (Set.range (tomographyVector context)) := by
    rw [tomography_spans context hoverlap]
    trivial
  obtain ⟨coefficient, hcoefficient⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
  rw [← hcoefficient]
  simp only [Matrix.mul_sum, Matrix.mul_smul, trace_sum, trace_smul, hcoordinate,
    smul_zero, Finset.sum_const_zero, zero_mul, trace_zero]

private theorem centered_coefficient_trace {n : Nat}
    (context : Fin (n + 2) -> RankOneContext (n + 1))
    (hoverlap : ∀ l k j r,
      trace ((context l).projector j * (context k).projector r) =
        if l = k then (if j = r then 1 else 0) else ((n + 1 : Nat) : ℂ)⁻¹)
    (coefficient : Fin (n + 2) -> Fin (n + 1) -> ℝ)
    (hcentered : ∀ l, ∑ j, coefficient l j = 0)
    (k : Fin (n + 2)) (r : Fin (n + 1)) :
    trace ((∑ l, ∑ j, (coefficient l j : ℂ) • (context l).projector j) *
      (context k).projector r) = coefficient k r := by
  simp only [Matrix.sum_mul, Matrix.smul_mul, trace_sum, trace_smul, smul_eq_mul]
  have hcontext (l : Fin (n + 2)) :
      ∑ j, (coefficient l j : ℂ) *
          trace ((context l).projector j * (context k).projector r) =
        if l = k then coefficient k r else 0 := by
    by_cases hlk : l = k
    · subst l
      simp [hoverlap]
    · simp only [hoverlap, hlk, if_false]
      rw [← Finset.sum_mul]
      have hcast : ∑ j, (coefficient l j : ℂ) = 0 := by
        exact_mod_cast hcentered l
      rw [hcast, zero_mul]
      norm_num
  simp_rw [hcontext]
  rw [← Complex.ofReal_sum]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- A complete family of complementary rank-one contexts has three simultaneous consequences:
every traceless Hermitian matrix has a unique centered real diagonal decomposition, the common
invisible traceless residual is zero, and all context probabilities uniquely determine a
Hermitian trace-one matrix. -/
theorem complete_context_tomography {n : Nat}
    (context : Fin (n + 2) -> RankOneContext (n + 1))
    (hoverlap : ∀ l k j r,
      trace ((context l).projector j * (context k).projector r) =
        if l = k then (if j = r then 1 else 0) else ((n + 1 : Nat) : ℂ)⁻¹) :
    (∀ X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      Xᴴ = X -> trace X = 0 ->
        ∃! coefficient : Fin (n + 2) -> Fin (n + 1) -> ℝ,
          (∀ l, ∑ j, coefficient l j = 0) ∧
            X = ∑ l, ∑ j, (coefficient l j : ℂ) • (context l).projector j) ∧
    (∀ X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      (∀ l j, trace (X * (context l).projector j) = 0) -> X = 0) ∧
    (∀ rho sigma : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      (∀ l j, trace (rho * (context l).projector j) =
          trace (sigma * (context l).projector j)) -> rho = sigma) := by
  have hdecomposition : ∀ X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      Xᴴ = X -> trace X = 0 ->
        ∃! coefficient : Fin (n + 2) -> Fin (n + 1) -> ℝ,
          (∀ l, ∑ j, coefficient l j = 0) ∧
            X = ∑ l, ∑ j, (coefficient l j : ℂ) • (context l).projector j := by
    intro X hX htrace
    let coefficient : Fin (n + 2) -> Fin (n + 1) -> ℝ :=
      fun l j => (trace (X * (context l).projector j)).re
    have hcentered (l : Fin (n + 2)) : ∑ j, coefficient l j = 0 := by
      have hcomplex : ∑ j, trace (X * (context l).projector j) = 0 := by
        calc
          ∑ j, trace (X * (context l).projector j) =
              trace (X * ∑ j, (context l).projector j) := by
                rw [Matrix.mul_sum, trace_sum]
          _ = 0 := by rw [(context l).resolvesIdentity, Matrix.mul_one, htrace]
      have hreal := congrArg Complex.re hcomplex
      simpa [coefficient, Complex.re_sum] using hreal
    have hreconstruct :
        X = ∑ l, ∑ j, (coefficient l j : ℂ) • (context l).projector j := by
      apply sub_eq_zero.mp
      apply projector_traces_complete context hoverlap
      intro k r
      rw [Matrix.sub_mul, trace_sub]
      rw [centered_coefficient_trace context hoverlap coefficient hcentered]
      have hreal := trace_hermitian_product_real hX ((context k).rankOne r |>.1)
      have hequal : trace (X * (context k).projector r) = (coefficient k r : ℂ) := by
        apply Complex.ext
        · simp [coefficient]
        · simp [coefficient, hreal]
      rw [hequal, sub_self]
    refine ⟨coefficient, ⟨hcentered, hreconstruct⟩, ?_⟩
    intro other hother
    funext l j
    have htraceCoefficient :=
      centered_coefficient_trace context hoverlap coefficient hcentered l j
    have htraceOther :=
      centered_coefficient_trace context hoverlap other hother.1 l j
    have hequality := congrArg (fun Y => trace (Y * (context l).projector j))
      (hreconstruct.symm.trans hother.2)
    rw [htraceCoefficient, htraceOther] at hequality
    exact_mod_cast hequality.symm
  refine ⟨hdecomposition, ?_, ?_⟩
  · intro X htraces
    exact projector_traces_complete context hoverlap htraces
  · intro rho sigma hprobability
    have hzero : rho - sigma = 0 := by
      apply projector_traces_complete context hoverlap
      intro l j
      rw [Matrix.sub_mul, trace_sub, hprobability l j, sub_self]
    exact sub_eq_zero.mp hzero

private def oneDimensionalContext : RankOneContext 1 where
  projector := fun _ => 1
  rankOne := by
    intro j
    refine ⟨by simp, by simp, by simp, ?_⟩
    intro X
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.trace, Matrix.mul_apply]
  resolvesIdentity := by simp

/-- The source overlap hypotheses are jointly satisfiable in dimension one. -/
example : ∃ context : Fin 2 -> RankOneContext 1,
    ∀ l k j r,
      trace ((context l).projector j * (context k).projector r) =
        if l = k then (if j = r then 1 else 0) else (1 : ℂ)⁻¹ := by
  refine ⟨fun _ => oneDimensionalContext, ?_⟩
  intro l k j r
  have hjr : j = r := Subsingleton.elim _ _
  subst r
  simp [oneDimensionalContext]

/-- The canonical context domain used by the theorem is inhabited. -/
example : RankOneContext 1 := oneDimensionalContext

#print axioms complete_context_tomography

end D5.S3.Quantum.Tomography.CompleteContextTomography
