/- GID: D5/S3/Quantum/TensorNetworks/UniformMPSExpectedDimensionRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/UniformMPSExpectedDimensionRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/TensorNetworks/UniformMPSExpectedDimensionRefutation.claim; result=D5/S3/Quantum/TensorNetworks/UniformMPSExpectedDimensionRefutation.result; claim=D5/S3/Quantum/TensorNetworks/UniformMPSExpectedDimensionRefutation.claim
   digest: Two-site uniform matrix product states can miss the expected dimension. -/

import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.Tactic.FinCases

/-! The two-site trace Gram determinant gives a strict expected-dimension defect. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Quantum.TensorNetworks.UniformMPSExpectedDimensionRefutation

open scoped BigOperators Matrix nonZeroDivisors

noncomputable section

/-- The coefficients of a uniform periodic matrix product state, in word order. -/
def traceWord (b d n : ℕ) (m : Fin d → Matrix (Fin b) (Fin b) ℂ)
    (i : Fin n → Fin d) : ℂ :=
  ((List.ofFn fun k => m (i k)).prod).trace

/-- Uniform matrix product states are the image of the trace-word parametrization. -/
def uMPS (b d n : ℕ) : Set ((Fin n → Fin d) → ℂ) :=
  Set.range (traceWord b d n)

/-- The dimension of the Zariski closure, measured by its coordinate ring. -/
def varietyDim {σ : Type*} (s : Set (σ → ℂ)) : WithBot ℕ∞ :=
  ringKrullDim (MvPolynomial σ ℂ ⧸ MvPolynomial.vanishingIdeal ℂ s)

/-- Tensors invariant under cyclic rotation of their word positions. -/
def Cyc (n d : ℕ) : Submodule ℂ ((Fin n → Fin d) → ℂ) where
  carrier := {t | ∀ i, t (i ∘ finRotate n) = t i}
  zero_mem' := by intro i; rfl
  add_mem' := by
    intro t u ht hu i
    exact congrArg₂ (· + ·) (ht i) (hu i)
  smul_mem' := by
    intro c t ht i
    exact congrArg (c * ·) (ht i)

/-- Czapliński–Michałek–Seynnaeve Conjecture 2.14: every uMPS has expected dimension. -/
def claim : Prop :=
  ∀ b d n : ℕ, 0 < b → 0 < d → 0 < n →
    varietyDim (uMPS b d n) =
      ((min ((d - 1) * b ^ 2 + 1) (Module.finrank ℂ (Cyc n d)) : ℕ) : WithBot ℕ∞)

private abbrev UpperPair := {p : Fin 5 × Fin 5 // p.1 ≤ p.2}

private def orderedPair (i j : Fin 5) : UpperPair :=
  ⟨(min i j, max i j), min_le_max⟩

private lemma upperPair_card : Fintype.card UpperPair = 15 := by
  decide

private lemma orderedPair_comm (i j : Fin 5) : orderedPair i j = orderedPair j i := by
  apply Subtype.ext
  exact Prod.ext (min_comm i j) (max_comm i j)

private lemma orderedPair_of_le (i j : Fin 5) (h : i ≤ j) :
    orderedPair i j = ⟨(i, j), h⟩ := by
  apply Subtype.ext
  exact Prod.ext (min_eq_left h) (max_eq_right h)

private lemma cyclic_finrank_lower : 15 ≤ Module.finrank ℂ (Cyc 2 5) := by
  classical
  let f : (UpperPair → ℂ) →ₗ[ℂ] Cyc 2 5 :=
    { toFun := fun v => ⟨fun i => v (orderedPair (i 0) (i 1)), by
        intro i
        change v (orderedPair (i (finRotate 2 0)) (i (finRotate 2 1))) =
          v (orderedPair (i 0) (i 1))
        have h0 : finRotate 2 0 = 1 := rfl
        have h1 : finRotate 2 1 = 0 := rfl
        rw [h0, h1, orderedPair_comm]⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hf : Function.Injective f := by
    intro v w h
    funext p
    have hp := congrArg (fun t : Cyc 2 5 => t.1 ![p.1.1, p.1.2]) h
    change v (orderedPair p.1.1 p.1.2) = w (orderedPair p.1.1 p.1.2) at hp
    rw [orderedPair_of_le _ _ p.2] at hp
    exact hp
  have h := LinearMap.finrank_le_finrank_of_injective hf
  rwa [Module.finrank_fintype_fun_eq_card, upperPair_card] at h

private lemma traceWord_two (m : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ)
    (i : Fin 2 → Fin 5) : traceWord 2 5 2 m i = (m (i 0) * m (i 1)).trace := by
  change ((List.ofFn fun k => m (i k)).prod).trace = _
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
  rfl

private lemma gram_factorization (m : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.of (fun i j => (m i * m j).trace) =
      Matrix.of (fun i (p : Fin 2 × Fin 2) => m i p.1 p.2) *
        Matrix.of (fun (p : Fin 2 × Fin 2) j => m j p.2 p.1) := by
  ext i j
  change (∑ a : Fin 2, ∑ b : Fin 2, m i a b * m j b a) =
    ∑ p : Fin 2 × Fin 2, m i p.1 p.2 * m j p.2 p.1
  rw [Fintype.sum_prod_type]

private lemma gram_det_zero (m : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.det (Matrix.of fun i j => (m i * m j).trace) = 0 := by
  classical
  let y : Matrix (Fin 2 × Fin 2) (Fin 5) ℂ := fun p j => m j p.2 p.1
  have hk : LinearMap.ker (Matrix.mulVecLin y) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by
      norm_num [Module.finrank_fintype_fun_eq_card])
  obtain ⟨v, hv, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨v, hn, ?_⟩
  rw [gram_factorization, ← Matrix.mulVec_mulVec]
  change Matrix.of (fun i (p : Fin 2 × Fin 2) => m i p.1 p.2) *ᵥ (y *ᵥ v) = 0
  change y *ᵥ v = 0 at hv
  rw [hv, Matrix.mulVec_zero]

private lemma coordinate_symmetry (i j : Fin 5) :
    MvPolynomial.X ![i, j] - MvPolynomial.X ![j, i] ∈
      MvPolynomial.vanishingIdeal ℂ (uMPS 2 5 2) := by
  rw [MvPolynomial.mem_vanishingIdeal_iff]
  intro t ht
  obtain ⟨m, rfl⟩ := ht
  simp only [map_sub, MvPolynomial.aeval_X, traceWord_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  exact sub_eq_zero.mpr (Matrix.trace_mul_comm (m i) (m j))

private def coordinateMap : MvPolynomial UpperPair ℂ →ₐ[ℂ]
    MvPolynomial (Fin 2 → Fin 5) ℂ ⧸ MvPolynomial.vanishingIdeal ℂ (uMPS 2 5 2) :=
  MvPolynomial.aeval fun p =>
    Ideal.Quotient.mkₐ ℂ (MvPolynomial.vanishingIdeal ℂ (uMPS 2 5 2))
      (MvPolynomial.X ![p.1.1, p.1.2])

private lemma coordinateMap_variable (i j : Fin 5) :
    coordinateMap (MvPolynomial.X (orderedPair i j)) =
      Ideal.Quotient.mkₐ ℂ (MvPolynomial.vanishingIdeal ℂ (uMPS 2 5 2))
        (MvPolynomial.X ![i, j]) := by
  change MvPolynomial.aeval _ (MvPolynomial.X (orderedPair i j)) = _
  rw [MvPolynomial.aeval_X]
  by_cases h : i ≤ j
  · rw [orderedPair_of_le i j h]
  · rw [orderedPair_comm, orderedPair_of_le j i (le_of_not_ge h)]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (coordinate_symmetry j i)

private lemma coordinateMap_surjective : Function.Surjective coordinateMap := by
  classical
  intro q
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  induction p using MvPolynomial.induction_on with
  | C c =>
      refine ⟨MvPolynomial.C c, ?_⟩
      exact coordinateMap.commutes c
  | add p q hp hq =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hq
      refine ⟨a + b, ?_⟩
      rw [map_add, ha, hb, map_add]
  | mul_X p i hp =>
      obtain ⟨a, ha⟩ := hp
      refine ⟨a * MvPolynomial.X (orderedPair (i 0) (i 1)), ?_⟩
      rw [map_mul, ha, coordinateMap_variable, map_mul]
      rw [Ideal.Quotient.mkₐ_eq_mk]
      have hi : ![i 0, i 1] = i := by
        funext k
        fin_cases k <;> rfl
      rw [hi]

private def symmetricDet : MvPolynomial UpperPair ℂ :=
  Matrix.det (Matrix.of fun i j => MvPolynomial.X (orderedPair i j))

private lemma symmetricDet_ne_zero : symmetricDet ≠ 0 := by
  classical
  let e : MvPolynomial UpperPair ℂ →ₐ[ℂ] ℂ :=
    MvPolynomial.aeval fun p => if p.1.1 = p.1.2 then 1 else 0
  have he : e symmetricDet = 1 := by
    change e (Matrix.det (Matrix.of fun i j => MvPolynomial.X (orderedPair i j))) = 1
    rw [e.map_det]
    have hm : Matrix.of (fun i j => e (MvPolynomial.X (orderedPair i j))) =
        (1 : Matrix (Fin 5) (Fin 5) ℂ) := by
      ext i j
      change MvPolynomial.aeval
        (fun p : UpperPair => if p.1.1 = p.1.2 then (1 : ℂ) else 0)
        (MvPolynomial.X (orderedPair i j)) = _
      rw [MvPolynomial.aeval_X]
      change (if min i j = max i j then (1 : ℂ) else 0) = _
      rw [Matrix.one_apply]
      have hc : ∀ a b : Fin 5, min a b = max a b ↔ a = b := by decide
      simp only [hc]
    change Matrix.det (Matrix.of fun i j => e (MvPolynomial.X (orderedPair i j))) = 1
    rw [hm, Matrix.det_one]
  intro h
  rw [h, map_zero] at he
  exact zero_ne_one he

private lemma coordinateMap_det_zero : coordinateMap symmetricDet = 0 := by
  classical
  let q := Ideal.Quotient.mkₐ ℂ (MvPolynomial.vanishingIdeal ℂ (uMPS 2 5 2))
  have he : coordinateMap symmetricDet =
      q (Matrix.det (Matrix.of fun i j : Fin 5 => MvPolynomial.X ![i, j])) := by
    change coordinateMap (Matrix.det _) = q (Matrix.det _)
    rw [coordinateMap.map_det, q.map_det]
    congr 1
    ext i j
    exact coordinateMap_variable i j
  rw [he]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [MvPolynomial.mem_vanishingIdeal_iff]
  intro t ht
  obtain ⟨m, rfl⟩ := ht
  rw [(MvPolynomial.aeval (traceWord 2 5 2 m)).map_det]
  convert gram_det_zero m using 2
  ext i j
  change MvPolynomial.aeval _ (MvPolynomial.X ![i, j]) = _
  rw [MvPolynomial.aeval_X, traceWord_two]
  rfl

private lemma actual_dimension_upper : varietyDim (uMPS 2 5 2) ≤ 14 := by
  have hd := ringKrullDim_succ_le_of_surjective coordinateMap.toRingHom
    coordinateMap_surjective (mem_nonZeroDivisors_iff_ne_zero.mpr symmetricDet_ne_zero)
    coordinateMap_det_zero
  have hp : ringKrullDim (MvPolynomial UpperPair ℂ) = 15 := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      Nat.card_eq_fintype_card, upperPair_card, ringKrullDim_eq_zero_of_field]
    norm_num
  rw [hp] at hd
  change ringKrullDim
    (MvPolynomial (Fin 2 → Fin 5) ℂ ⧸ MvPolynomial.vanishingIdeal ℂ (uMPS 2 5 2)) ≤ 14
  apply ENat.WithBot.add_le_add_one_right_iff.mp
  convert hd using 1
  norm_num

/-- At bond dimension two, five physical symbols and two sites, dimension is at most fourteen
while the conjectured dimension is at least fifteen. -/
theorem result : ¬ claim := by
  intro h
  have heq := h 2 5 2 (by decide) (by decide) (by decide)
  have hlo : 15 ≤ min ((5 - 1) * 2 ^ 2 + 1) (Module.finrank ℂ (Cyc 2 5)) :=
    le_min (by decide) cyclic_finrank_lower
  have hcast : (15 : WithBot ℕ∞) ≤
      ((min ((5 - 1) * 2 ^ 2 + 1) (Module.finrank ℂ (Cyc 2 5)) : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast hlo
  have hbad : (15 : WithBot ℕ∞) ≤ 14 := by
    rw [← heq] at hcast
    exact hcast.trans actual_dimension_upper
  norm_num at hbad

end

end D5.S3.Quantum.TensorNetworks.UniformMPSExpectedDimensionRefutation
