/- GID: D5/S3/Quantum/Information/CoherenceAssistanceRoofEquality
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/CoherenceAssistanceRoofEquality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/CoherenceAssistanceRoofEquality.claim; result=D5/S3/Quantum/Information/CoherenceAssistanceRoofEquality.result; claim=D5/S3/Quantum/Information/CoherenceAssistanceRoofEquality.claim
   digest: A rank-two state in four dimensions has equal coherence roofs. -/


import Mathlib.Analysis.Convex.Mul
import D5.S3.Quantum.Measurement.AntidistinguishabilityGram

set_option autoImplicit false
set_option linter.style.longLine false
open scoped BigOperators ComplexOrder
open Matrix

noncomputable section
namespace D5.S3.Quantum.Information.CoherenceAssistanceRoofEquality

/-- The source class of symmetric concave functions on the probability simplex.
Vanishing at every vertex is equivalent, by symmetry, to vanishing at the first vertex. -/
def IsCoherenceFunction {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ConcaveOn ℝ (stdSimplex ℝ (Fin n)) f ∧
    (∀ σ : Equiv.Perm (Fin n), ∀ p ∈ stdSimplex ℝ (Fin n), f (p ∘ σ) = f p) ∧
    ∀ i : Fin n, f (Pi.single i 1) = 0

/-- Squared absolute values of the amplitudes in the fixed reference basis. -/
def coherenceVector {n : ℕ} (ψ : Fin n → ℂ) : Fin n → ℝ :=
  fun i => Complex.normSq (ψ i)

/-- All finite pure-state decompositions, with Hilbert norm one for every vector. -/
def IsDecomposition {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) (k : ℕ)
    (p : Fin k → ℝ) (ψ : Fin k → Fin n → ℂ) : Prop :=
  (∀ j, 0 ≤ p j) ∧ (∑ j, p j) = 1 ∧
    (∀ j, ∑ i, Complex.normSq (ψ j i) = 1) ∧
    ρ = ∑ j, (p j : ℂ) • vecMulVec (ψ j) (star (ψ j))

/-- The source averages over all finite pure-state decompositions. -/
def decompositionValues {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (ρ : Matrix (Fin n) (Fin n) ℂ) : Set ℝ :=
  {x | ∃ k p ψ, IsDecomposition ρ k p ψ ∧ x = ∑ j, p j * f (coherenceVector (ψ j))}

noncomputable def convexRoof {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (ρ : Matrix (Fin n) (Fin n) ℂ) : ℝ := sInf (decompositionValues f ρ)

noncomputable def assistance {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (ρ : Matrix (Fin n) (Fin n) ℂ) : ℝ := sSup (decompositionValues f ρ)

/-- A density matrix with purity different from one; for density matrices this
is equivalent to not being a unit rank-one projector. -/
def IsMixed {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1 ∧ (ρ * ρ).trace ≠ 1

/-- The universal strict gap asked for in arXiv:2103.08818v1. -/
def claim : Prop :=
  ∀ n : ℕ, ∀ f : (Fin n → ℝ) → ℝ, IsCoherenceFunction f →
    (∃ p ∈ stdSimplex ℝ (Fin n), f p ≠ 0) →
    ∀ ρ : Matrix (Fin n) (Fin n) ℂ, IsMixed ρ → convexRoof f ρ < assistance f ρ

private def quadratic (p : Fin 4 → ℝ) : ℝ := 1 - ∑ i, p i ^ 2

/-- Rationalized coordinates of `(1/√2,1/√6,1/√6,1/√6)`. -/
private def v : Fin 4 → ℂ :=
  ![((Real.sqrt 2 / 2 : ℝ) : ℂ), ((Real.sqrt 6 / 6 : ℝ) : ℂ),
    ((Real.sqrt 6 / 6 : ℝ) : ℂ), ((Real.sqrt 6 / 6 : ℝ) : ℂ)]

/-- Rationalized coordinates of `(0,1/√3,ω/√3,ω²/√3)` for `ω=(-1+i√3)/2`. -/
private def w : Fin 4 → ℂ :=
  ![0, ((Real.sqrt 3 / 3 : ℝ) : ℂ),
    ((-Real.sqrt 3 / 6 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I,
    ((-Real.sqrt 3 / 6 : ℝ) : ℂ) - ((1 / 2 : ℝ) : ℂ) * Complex.I]

private def projection : Matrix (Fin 4) (Fin 4) ℂ :=
  vecMulVec v (star v) + vecMulVec w (star w)

private def rho : Matrix (Fin 4) (Fin 4) ℂ := (1 / 2 : ℂ) • projection

private lemma frame :
    star v ⬝ᵥ v = 1 ∧ star w ⬝ᵥ w = 1 ∧ star v ⬝ᵥ w = 0 ∧ star w ⬝ᵥ v = 0 ∧
      (∑ i, Complex.normSq (v i)) = 1 ∧ (∑ i, Complex.normSq (w i)) = 1 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hv : (∑ i, Complex.normSq (v i)) = 1 := by
    norm_num [v, Fin.sum_univ_succ, Complex.normSq_apply]
    nlinarith
  have hw : (∑ i, Complex.normSq (w i)) = 1 := by
    norm_num [w, Fin.sum_univ_succ, Complex.normSq_apply]
    nlinarith
  have hn : ∀ x : Fin 4 → ℂ, star x ⬝ᵥ x = ((∑ i, Complex.normSq (x i) : ℝ) : ℂ) := by
    intro x
    change (∑ i, star (x i) * x i) = _
    simp only [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_sum]
  refine ⟨?_, ?_, ?_, ?_, hv, hw⟩
  · rw [hn, hv, Complex.ofReal_one]
  · rw [hn, hw, Complex.ofReal_one]
  · change (∑ i, star (v i) * w i) = 0
    apply Complex.ext <;> norm_num [v, w, Fin.sum_univ_succ, Complex.star_def] <;> ring
  · change (∑ i, star (w i) * v i) = 0
    apply Complex.ext <;> norm_num [v, w, Fin.sum_univ_succ, Complex.star_def] <;> ring

private lemma projection_properties :
    projection.IsHermitian ∧ projection * projection = projection ∧
      ((1 - projection) * rho).trace = 0 := by
  have hf := frame
  have hh : projection.IsHermitian :=
    ((Matrix.posSemidef_vecMulVec_self_star v).add
      (Matrix.posSemidef_vecMulVec_self_star w)).isHermitian
  have hpp : projection * projection = projection := by
    change (vecMulVec v (star v) + vecMulVec w (star w)) *
      (vecMulVec v (star v) + vecMulVec w (star w)) = _
    simp only [add_mul, mul_add, Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul,
      hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, one_smul, zero_smul, add_zero, zero_add]
    rfl
  refine ⟨hh, hpp, ?_⟩
  change ((1 - projection) * ((1 / 2 : ℂ) • projection)).trace = 0
  rw [Matrix.mul_smul, sub_mul, one_mul, hpp, sub_self, smul_zero, Matrix.trace_zero]

private lemma decomposition_support {n k : ℕ}
    (ρ q : Matrix (Fin n) (Fin n) ℂ) (p : Fin k → ℝ) (ψ : Fin k → Fin n → ℂ)
    (hd : IsDecomposition ρ k p ψ) (hq : q.PosSemidef) (hzero : (q * ρ).trace = 0)
    (j : Fin k) (hp : 0 < p j) : q *ᵥ ψ j = 0 := by
  have htrace : (q * ρ).trace =
      ∑ t, (p t : ℂ) * (star (ψ t) ⬝ᵥ (q *ᵥ ψ t)) := by
    rw [hd.2.2.2, Matrix.mul_sum, Matrix.trace_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_vecMulVec,
      Matrix.trace_vecMulVec, dotProduct_comm]
    rfl
  have hs : (∑ t, p t * (star (ψ t) ⬝ᵥ (q *ᵥ ψ t)).re) = 0 := by
    have hz := congrArg Complex.re (htrace.symm.trans hzero)
    simpa only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.zero_re] using hz
  have hn : ∀ t ∈ (Finset.univ : Finset (Fin k)),
      0 ≤ p t * (star (ψ t) ⬝ᵥ (q *ᵥ ψ t)).re :=
    fun t _ => mul_nonneg (hd.1 t) (hq.re_dotProduct_nonneg (ψ t))
  have hj := (Finset.sum_eq_zero_iff_of_nonneg hn).mp hs j (Finset.mem_univ j)
  have hr : (star (ψ j) ⬝ᵥ (q *ᵥ ψ j)).re = 0 := (mul_eq_zero.mp hj).resolve_left hp.ne'
  have hi := (Complex.nonneg_iff.mp (hq.dotProduct_mulVec_nonneg (ψ j))).2
  exact hq.dotProduct_mulVec_zero_iff.mp (Complex.ext hr hi.symm)

private lemma fourth_moment (a b : ℂ) :
    (∑ i, Complex.normSq (a * v i + b * w i) ^ 2) =
      (Complex.normSq a + Complex.normSq b) ^ 2 / 3 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have h24 : Real.sqrt 2 ^ 4 = 4 := by
    calc _ = (Real.sqrt 2 ^ 2) ^ 2 := by ring
         _ = 4 := by rw [h2]; norm_num
  have h34 : Real.sqrt 3 ^ 4 = 9 := by
    calc _ = (Real.sqrt 3 ^ 2) ^ 2 := by ring
         _ = 9 := by rw [h3]; norm_num
  have h33 : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by
    calc _ = Real.sqrt 3 ^ 2 * Real.sqrt 3 := by ring
         _ = 3 * Real.sqrt 3 := by rw [h3]
  have h64 : Real.sqrt 6 ^ 4 = 36 := by
    calc _ = (Real.sqrt 6 ^ 2) ^ 2 := by ring
         _ = 36 := by rw [h6]; norm_num
  norm_num [v, w, Fin.sum_univ_succ, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  ring_nf
  simp only [h2, h3, h6, h24, h34, h64, h33]
  ring

private lemma unit_span_value (ψ : Fin 4 → ℂ)
    (hunit : ∑ i, Complex.normSq (ψ i) = 1)
    (hspan : (1 - projection) *ᵥ ψ = 0) : quadratic (coherenceVector ψ) = 2 / 3 := by
  let a : ℂ := star v ⬝ᵥ ψ
  let b : ℂ := star w ⬝ᵥ ψ
  have hrep : ψ = a • v + b • w := by
    have hz : ψ - projection *ᵥ ψ = 0 := by
      simpa only [Matrix.sub_mulVec, Matrix.one_mulVec] using hspan
    rw [sub_eq_zero.mp hz]
    change (vecMulVec v (star v) + vecMulVec w (star w)) *ᵥ ψ = _
    rw [Matrix.add_mulVec, Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec]
    ext i
    change v i * a + w i * b = a * v i + b * w i
    ring
  have hunitc : star ψ ⬝ᵥ ψ = 1 := by
    change (∑ i, star (ψ i) * ψ i) = 1
    simp only [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_sum,
      hunit, Complex.ofReal_one]
  have hc : ((Complex.normSq a + Complex.normSq b : ℝ) : ℂ) = 1 := by
    rw [hrep] at hunitc
    simpa only [star_add, star_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, frame.1, frame.2.1, frame.2.2.1, frame.2.2.2.1,
      smul_eq_mul, mul_one, mul_zero, add_zero, zero_add, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_add] using hunitc
  have hab : Complex.normSq a + Complex.normSq b = 1 := by exact_mod_cast hc
  have hpoint : ∀ i, ψ i = a * v i + b * w i := fun i => congrFun hrep i
  change 1 - ∑ i, Complex.normSq (ψ i) ^ 2 = 2 / 3
  simp only [hpoint]
  rw [fourth_moment, hab]
  norm_num

private lemma quadratic_coherence : IsCoherenceFunction quadratic := by
  refine ⟨⟨convex_stdSimplex ℝ (Fin 4), ?_⟩, ?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    have hs : (∑ i, (a * x i + b * y i) ^ 2) ≤
        ∑ i, (a * x i ^ 2 + b * y i ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      exact (convexOn_pow (𝕜 := ℝ) 2).2 (hx.1 i) (hy.1 i) ha hb hab
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
    change a * (1 - ∑ i, x i ^ 2) + b * (1 - ∑ i, y i ^ 2) ≤
      1 - ∑ i, (a * x i + b * y i) ^ 2
    linarith
  · intro σ p _
    change 1 - ∑ i, (p (σ i)) ^ 2 = 1 - ∑ i, p i ^ 2
    rw [Equiv.sum_comp σ (fun i => p i ^ 2)]
  · intro i
    change 1 - ∑ j, (Pi.single i (1 : ℝ) j) ^ 2 = 0
    simp only [Pi.single_apply, ite_pow, one_pow, zero_pow (by decide : 2 ≠ 0)]
    simp

private lemma quadratic_nonzero :
    ∃ p ∈ stdSimplex ℝ (Fin 4), quadratic p ≠ 0 := by
  refine ⟨fun _ => 1 / 4, ⟨fun _ => by norm_num, ?_⟩, ?_⟩
  · norm_num [Fin.sum_univ_succ]
  · norm_num [quadratic, Fin.sum_univ_succ]

private lemma witness_decomposition :
    IsDecomposition rho 2 (fun _ => 1 / 2) ![v, w] := by
  refine ⟨fun _ => by norm_num, ?_, ?_, ?_⟩
  · norm_num [Fin.sum_univ_succ]
  · intro j
    fin_cases j
    · exact frame.2.2.2.2.1
    · exact frame.2.2.2.2.2
  · change (1 / 2 : ℂ) • (vecMulVec v (star v) + vecMulVec w (star w)) = _
    simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero]
    norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    exact smul_add _ _ _

private lemma values_singleton : decompositionValues quadratic rho = {2 / 3} := by
  have hproj := projection_properties
  have hq := D5.S3.Quantum.Measurement.AntidistinguishabilityGram.hermitian_projection_complement_psd
    projection hproj.1 hproj.2.1
  have havg : ∀ k p ψ, IsDecomposition rho k p ψ →
      (∑ j, p j * quadratic (coherenceVector (ψ j))) = 2 / 3 := by
    intro k p ψ hd
    calc
      _ = ∑ j, p j * (2 / 3) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hp : p j = 0
        · rw [hp, zero_mul, zero_mul]
        · rw [unit_span_value (ψ j) (hd.2.2.1 j)
            (decomposition_support rho (1 - projection) p ψ hd hq hproj.2.2 j
              (lt_of_le_of_ne (hd.1 j) (Ne.symm hp)))]
      _ = 2 / 3 := by rw [← Finset.sum_mul, hd.2.1, one_mul]
  ext x
  constructor
  · rintro ⟨k, p, ψ, hd, rfl⟩
    exact Set.mem_singleton_iff.mpr (havg k p ψ hd)
  · intro hx
    refine ⟨2, (fun _ => 1 / 2), ![v, w], witness_decomposition, ?_⟩
    exact (Set.mem_singleton_iff.mp hx).trans (havg _ _ _ witness_decomposition).symm

private lemma witness_mixed : IsMixed rho := by
  have htrace : projection.trace = 2 := by
    change (vecMulVec v (star v) + vecMulVec w (star w)).trace = 2
    rw [Matrix.trace_add, Matrix.trace_vecMulVec, Matrix.trace_vecMulVec,
      dotProduct_comm v, dotProduct_comm w, frame.1, frame.2.1]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · exact ((Matrix.posSemidef_vecMulVec_self_star v).add
      (Matrix.posSemidef_vecMulVec_self_star w)).smul (a := (1 / 2 : ℂ)) (by norm_num)
  · change ((1 / 2 : ℂ) • projection).trace = 1
    rw [Matrix.trace_smul, htrace]
    norm_num
  · change (((1 / 2 : ℂ) • projection) * ((1 / 2 : ℂ) • projection)).trace ≠ 1
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, projection_properties.2.1,
      Matrix.trace_smul, htrace]
    norm_num

theorem result : ¬ claim := by
  intro h
  have hlt := h 4 quadratic quadratic_coherence quadratic_nonzero rho witness_mixed
  change sInf (decompositionValues quadratic rho) < sSup (decompositionValues quadratic rho) at hlt
  rw [values_singleton, csInf_singleton, csSup_singleton] at hlt
  exact (lt_irrefl _ hlt)

end D5.S3.Quantum.Information.CoherenceAssistanceRoofEquality
