/- GID: D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurements/ThreeDistinguishabilityCubic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.weighted_phase_columns_iff_cubic; instance=D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic.infeasible_weighted_phase_columns
   digest: A guarded cubic decides the closed-simplex four-weight problem for three orthonormal columns. -/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.IntermediateValue

/-! # Three weighted phase columns on four atoms

Korzekwa, Czachórski, Puchała and Życzkowski (arXiv:1812.09083v3, p. 5,
Lemma 5 and Eq. (19), §III.B and Appendix C) relate pure-state distinguishability
to a unistochastic matrix with repeated columns. Their Appendix C.3 uses
Haagerup's order-four procedure, described by Rajchel, Gąsiorowski and Życzkowski
(arXiv:1804.10715v2, Appendix A), on this repeated-column family.

The guarded cubic applies on the closed simplex. The two exact examples are both strictly below the row cap.
-/

open scoped BigOperators Matrix

noncomputable section

namespace D5.S3.Quantum.Measurements.ThreeDistinguishabilityCubic

open Matrix

/-- The diagonal entries of the rank-two complementary projection. -/
def q (p : Fin 4 → ℝ) (i : Fin 4) : ℝ := 1 - 2 * p i

/-- The required anisotropic part of the diagonal. -/
def d (p : Fin 4 → ℝ) (i : Fin 4) : ℝ := 4 * p i - 1

/-- The four-radical elimination polynomial in the squared radicals. -/
private def phaseQuartic (x : Fin 4 → ℝ) : ℝ :=
  ((x 0 + x 1 - x 2 - x 3)^2 - 4 * x 0 * x 1 - 4 * x 2 * x 3)^2 -
    64 * x 0 * x 1 * x 2 * x 3

-- Expanding the product of eight linear factors requires extra heartbeats.
set_option maxHeartbeats 800000 in
private theorem phaseQuartic_squares (a : Fin 4 → ℝ) :
    phaseQuartic (fun i => a i ^ 2) =
      (a 0 + a 1 + a 2 + a 3) * (a 0 + a 1 + a 2 - a 3) *
      (a 0 + a 1 - a 2 + a 3) * (a 0 + a 1 - a 2 - a 3) *
      (a 0 - a 1 + a 2 + a 3) * (a 0 - a 1 + a 2 - a 3) *
      (a 0 - a 1 - a 2 + a 3) * (a 0 - a 1 - a 2 - a 3) := by
  unfold phaseQuartic
  ring

private theorem phaseQuartic_zero_of_sum_zero (a : Fin 4 → ℝ) (ha : ∑ i, a i = 0) :
    phaseQuartic (fun i => a i ^ 2) = 0 := by
  have h : a 0 + a 1 + a 2 + a 3 = 0 := by
    simpa only [Fin.sum_univ_four, add_assoc] using ha
  simp only [phaseQuartic_squares, h, zero_mul]

/-- A root of the quartic is exactly a zero sum of signed real square roots.
The squared-root formulation also includes every zero coordinate. -/
private theorem phaseQuartic_eq_zero_iff (x : Fin 4 → ℝ) (hx : ∀ i, 0 ≤ x i) :
    phaseQuartic x = 0 ↔ ∃ y : Fin 4 → ℝ, (∀ i, y i ^ 2 = x i) ∧ ∑ i, y i = 0 := by
  constructor
  · intro h
    let a : Fin 4 → ℝ := fun i => Real.sqrt (x i)
    have ha (i : Fin 4) : a i ^ 2 = x i := Real.sq_sqrt (hx i)
    have hf := phaseQuartic_squares a
    simp only [ha, h] at hf
    have hz := hf.symm
    simp only [mul_eq_zero] at hz
    rcases hz with (((((((h0 | h1) | h2) | h3) | h4) | h5) | h6) | h7)
    · exact ⟨a, ha, by simpa only [Fin.sum_univ_four, add_assoc] using h0⟩
    · refine ⟨![a 0, a 1, a 2, -a 3], ?_, ?_⟩
      · intro i; fin_cases i <;> simp [ha]
      · simp [Fin.sum_univ_four]; linarith
    · refine ⟨![a 0, a 1, -a 2, a 3], ?_, ?_⟩
      · intro i; fin_cases i <;> simp [ha]
      · simp [Fin.sum_univ_four]; linarith
    · refine ⟨![a 0, a 1, -a 2, -a 3], ?_, ?_⟩
      · intro i; fin_cases i <;> simp [ha]
      · simp [Fin.sum_univ_four]; linarith
    · refine ⟨![a 0, -a 1, a 2, a 3], ?_, ?_⟩
      · intro i; fin_cases i <;> simp [ha]
      · simp [Fin.sum_univ_four]; linarith
    · refine ⟨![a 0, -a 1, a 2, -a 3], ?_, ?_⟩
      · intro i; fin_cases i <;> simp [ha]
      · simp [Fin.sum_univ_four]; linarith
    · refine ⟨![a 0, -a 1, -a 2, a 3], ?_, ?_⟩
      · intro i; fin_cases i <;> simp [ha]
      · simp [Fin.sum_univ_four]; linarith
    · refine ⟨![a 0, -a 1, -a 2, -a 3], ?_, ?_⟩
      · intro i; fin_cases i <;> simp [ha]
      · simp [Fin.sum_univ_four]; linarith
  · rintro ⟨y, hy, hsum⟩
    simpa only [hy] using phaseQuartic_zero_of_sum_zero y hsum

/-- The coefficients of the cubic obtained from the quartic by dropping its
constant coefficient and shifting the other coefficients down one degree. -/
def cubicAfterConstant (u v : Fin 4 → ℝ) (t : ℝ) : ℝ :=
  let a := u 0 + u 1 - u 2 - u 3
  let b := v 0 + v 1 - v 2 - v 3
  let l := a^2 - 4 * (u 0 * u 1 + u 2 * u 3)
  let m := -2 * a * b + 4 * (u 0 * v 1 + v 0 * u 1 + u 2 * v 3 + v 2 * u 3)
  let n := b^2 - 4 * (v 0 * v 1 + v 2 * v 3)
  let f := u 0 * u 1
  let g := u 0 * v 1 + v 0 * u 1
  let h := v 0 * v 1
  let j := u 2 * u 3
  let k := u 2 * v 3 + v 2 * u 3
  let r := v 2 * v 3
  (l^2 - 64 * f * j) * t^3 + (2 * l * m + 64 * (f * k + g * j)) * t^2 +
    (m^2 + 2 * l * n - 64 * (f * r + g * k + h * j)) * t +
    (2 * m * n + 64 * (g * r + h * k))

-- Expanding the generic quartic with eight coefficient variables requires extra heartbeats.
set_option maxHeartbeats 1500000 in
private theorem quartic_expand (u v : Fin 4 → ℝ) (t : ℝ) :
    phaseQuartic (fun i => u i * t - v i) =
      t * cubicAfterConstant u v t + phaseQuartic v := by
  unfold phaseQuartic cubicAfterConstant
  ring

/-- The cubic for the four-atom weight law. -/
def phaseCubic (p : Fin 4 → ℝ) (t : ℝ) : ℝ :=
  cubicAfterConstant (fun i => q p i ^ 2) (fun i => d p i ^ 2) t

private theorem sum_q (p : Fin 4 → ℝ) (hp : ∑ i, p i = 1) : ∑ i, q p i = 2 := by
  norm_num [q, Finset.sum_sub_distrib, ← Finset.mul_sum, hp]

private theorem sum_d (p : Fin 4 → ℝ) (hp : ∑ i, p i = 1) : ∑ i, d p i = 0 := by
  norm_num [d, Finset.sum_sub_distrib, ← Finset.mul_sum, hp]

/-- The constant coefficient vanishes under normalization. -/
private theorem phaseQuartic_eq_mul_phaseCubic (p : Fin 4 → ℝ) (hp : ∑ i, p i = 1) (t : ℝ) :
    phaseQuartic (fun i => q p i ^ 2 * t - d p i ^ 2) = t * phaseCubic p t := by
  unfold phaseCubic
  rw [quartic_expand, phaseQuartic_zero_of_sum_zero (d p) (sum_d p hp), add_zero]

/-- The real rank-two diagonal Gram condition. The two complementary axes
can be ordered either way so the spectral difference may have either sign. -/
private def RealDiagonalGram (p : Fin 4 → ℝ) : Prop :=
  ∃ (C : Matrix (Fin 4) (Fin 2) ℝ) (s : ℝ),
    Cᵀ * C = 1 ∧ -1 ≤ s ∧ s ≤ 1 ∧
    (∀ i, C i 0 ^ 2 + C i 1 ^ 2 = q p i) ∧
    ∀ i, (1 + s) / 2 * C i 0 ^ 2 + (1 - s) / 2 * C i 1 ^ 2 = p i

theorem real_gram_entry {m n : Type*} [Fintype m] [DecidableEq n]
    (C : Matrix m n ℝ) (hC : Cᵀ * C = 1) (j k : n) :
    (fun i => C i j) ⬝ᵥ (fun i => C i k) = if j = k then 1 else 0 := by
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, dotProduct] using
    congrFun (congrFun hC j) k

private theorem real_gram_diag {m : Type*} (C : Matrix m (Fin 2) ℝ) (i : m) :
    (C * Cᵀ) i i = C i 0 ^ 2 + C i 1 ^ 2 := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, pow_two]

private theorem diagonal_relation (p : Fin 4 → ℝ) (i : Fin 4) (u v s : ℝ)
    (h : u + v = q p i) :
    (1 + s) / 2 * u + (1 - s) / 2 * v = p i ↔ s * (u - v) = d p i := by
  unfold q at h
  unfold d
  constructor <;> intro he <;> nlinarith only [he, h]

/-- The real diagonal condition is equivalent to the cubic test on its
positive domain, including uniform weights and zero radicands. -/
private theorem realDiagonalGram_iff_cubic (p : Fin 4 → ℝ) (hp : ∑ i, p i = 1)
    (hq : ∀ i, 0 ≤ q p i) :
    RealDiagonalGram p ↔ ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      (∀ i, d p i ^ 2 ≤ q p i ^ 2 * t) ∧ phaseCubic p t = 0 := by
  constructor
  · rintro ⟨C, s, hC, hslo, hshi, hrow, hdiag⟩
    have hd (i : Fin 4) := (diagonal_relation p i _ _ s (hrow i)).1 (hdiag i)
    have hcubic (t : ℝ) (ht : 0 < t)
        (hy : ∃ y : Fin 4 → ℝ, (∀ i, y i ^ 2 = q p i ^ 2 * t - d p i ^ 2) ∧
          ∑ i, y i = 0) : phaseCubic p t = 0 := by
      obtain ⟨y, hy, hy0⟩ := hy
      have hF := phaseQuartic_zero_of_sum_zero y hy0
      simp only [hy, phaseQuartic_eq_mul_phaseCubic p hp] at hF
      exact (mul_eq_zero.mp hF).resolve_left ht.ne'
    by_cases hs : s = 0
    · have hdp (i : Fin 4) : d p i = 0 := by simpa only [hs, zero_mul] using (hd i).symm
      have hqp (i : Fin 4) : q p i = 1 / 2 := by
        have h := hdp i
        unfold q
        unfold d at h
        linarith
      refine ⟨1, zero_lt_one, le_rfl, ?_, hcubic 1 zero_lt_one ?_⟩
      · intro i
        norm_num [hdp, hqp]
      · refine ⟨![1 / 2, -(1 / 2), 1 / 2, -(1 / 2)], ?_, ?_⟩
        · intro i; fin_cases i <;> norm_num [hqp, hdp]
        · norm_num [Fin.sum_univ_four]
    · let y : Fin 4 → ℝ := fun i => (2 * s) * (C i 0 * C i 1)
      have hy (i : Fin 4) : y i ^ 2 = q p i ^ 2 * s ^ 2 - d p i ^ 2 := by
        rw [← hrow i, ← hd i]
        dsimp [y]
        ring
      have hC01 : (∑ i, C i 0 * C i 1) = 0 := by
        simpa [dotProduct] using real_gram_entry C hC 0 1
      have hy0 : ∑ i, y i = 0 := by simp [y, ← Finset.mul_sum, hC01]
      have ht := sq_pos_of_ne_zero hs
      refine ⟨s ^ 2, ht, ?_, ?_, hcubic _ ht ⟨y, hy, hy0⟩⟩
      · have h1 := (abs_le.mpr ⟨by simpa using hslo, hshi⟩ : |s| ≤ (1 : ℝ))
        simpa only [sq_abs, one_pow] using
          (sq_le_sq₀ (abs_nonneg s) zero_le_one).2 h1
      · intro i
        apply sub_nonneg.mp
        rw [← hy i]
        exact sq_nonneg _
  · rintro ⟨t, ht, ht1, hx, hcubic⟩
    have hF : phaseQuartic (fun i => q p i ^ 2 * t - d p i ^ 2) = 0 := by
      rw [phaseQuartic_eq_mul_phaseCubic p hp t, hcubic, mul_zero]
    obtain ⟨y, hy, hy0⟩ := (phaseQuartic_eq_zero_iff _ (fun i => sub_nonneg.mpr (hx i))).1 hF
    let s := Real.sqrt t
    have hs : 0 < s := Real.sqrt_pos.2 ht
    have hs2 : s ^ 2 = t := Real.sq_sqrt ht.le
    have hs1 : s ≤ 1 := (sq_le_sq₀ hs.le zero_le_one).1 (by simpa [hs2] using ht1)
    have hb (i : Fin 4) : -(q p i * s) ≤ d p i ∧ d p i ≤ q p i * s := by
      apply abs_le.mp
      apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (hq i) hs.le)).1
      simpa only [sq_abs, mul_pow, hs2] using hx i
    let P : Fin 4 → ℝ := fun i => (q p i + d p i / s) / 2
    let N : Fin 4 → ℝ := fun i => (q p i - d p i / s) / 2
    have hP (i : Fin 4) : 0 ≤ P i := by
      have h : -q p i ≤ d p i / s :=
        (le_div_iff₀ hs).2 (by simpa only [neg_mul] using (hb i).1)
      dsimp [P]
      linarith
    have hN (i : Fin 4) : 0 ≤ N i := by
      have h := (div_le_iff₀ hs).2 (hb i).2
      dsimp [N]
      linarith
    let c : Fin 4 → ℝ := fun i => Real.sqrt (P i)
    let e : Fin 4 → ℝ := fun i => if 0 ≤ y i then Real.sqrt (N i) else -Real.sqrt (N i)
    have hc (i : Fin 4) : c i ^ 2 = P i := Real.sq_sqrt (hP i)
    have he (i : Fin 4) : e i ^ 2 = N i := by
      by_cases hi : 0 ≤ y i <;> simp [e, hi, Real.sq_sqrt (hN i)]
    have hce (i : Fin 4) : (2 * s) * (c i * e i) = y i := by
      have heq : ((2 * s) * (c i * e i)) ^ 2 = y i ^ 2 := by
        simp only [mul_pow, hc, he, hy]
        dsimp [P, N]
        rw [← hs2]
        field_simp [hs.ne']; ring
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp heq with h | h
      · exact h
      · by_cases hi : 0 ≤ y i
        · have hz : 0 ≤ (2 * s) * (c i * e i) := by
            simp only [c, e, ite_eq_left hi]
            positivity
          linarith
        · have hz : (2 * s) * (c i * e i) ≤ 0 := by
            simp only [c, e, ite_eq_right hi, mul_neg, neg_nonpos]
            positivity
          linarith [lt_of_not_ge hi]
    have hc1 : ∑ i, c i ^ 2 = 1 := by
      norm_num [hc, P, ← Finset.sum_div, Finset.sum_add_distrib, sum_q p hp, sum_d p hp]
    have he1 : ∑ i, e i ^ 2 = 1 := by
      norm_num [he, N, ← Finset.sum_div, Finset.sum_sub_distrib, sum_q p hp, sum_d p hp]
    have hcross : ∑ i, c i * e i = 0 := by
      have hz : (2 * s) * (∑ i, c i * e i) = 0 := by
        rw [Finset.mul_sum, Finset.sum_congr rfl (fun i _ => hce i), hy0]
      exact (mul_eq_zero.mp hz).resolve_left (by positivity)
    have hcross_rev : ∑ i, e i * c i = 0 := by
      calc
        (∑ i, e i * c i) = ∑ i, c i * e i := Finset.sum_congr rfl fun i _ => mul_comm _ _
        _ = 0 := hcross
    let C : Matrix (Fin 4) (Fin 2) ℝ := Matrix.of fun i => ![c i, e i]
    have hC : Cᵀ * C = 1 := by
      ext j k
      fin_cases j <;> fin_cases k <;>
        norm_num [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, C,
          ← pow_two, hc1, he1, hcross, hcross_rev]
    have hrow (i : Fin 4) : c i ^ 2 + e i ^ 2 = q p i := by
      rw [hc, he]
      dsimp [P, N]
      ring
    refine ⟨C, s, hC, by linarith, hs1, hrow, ?_⟩
    intro i
    change (1 + s) / 2 * c i ^ 2 + (1 - s) / 2 * e i ^ 2 = p i
    apply (diagonal_relation p i _ _ s (hrow i)).2
    rw [hc, he]
    dsimp [P, N]
    field_simp [hs.ne']; ring

theorem complete_real_pair (A : Matrix (Fin 4) (Fin 2) ℝ) (hA : Aᵀ * A = 1) :
    ∃ R : Matrix (Fin 4) (Fin 4) ℝ, Rᵀ * R = 1 ∧
      (∀ i, R i 0 = A i 0) ∧ ∀ i, R i 1 = A i 1 := by
  let v : Fin 4 → EuclideanSpace ℝ (Fin 4) :=
    fun j => WithLp.toLp 2 (fun i => if j = 0 then A i 0 else A i 1)
  let s : Set (Fin 4) := {j | j = 0 ∨ j = 1}
  let z : s := ⟨0, Or.inl rfl⟩
  let o : s := ⟨1, Or.inr rfl⟩
  have hcases (j : s) : j = z ∨ j = o := by
    rcases j.property with hj | hj
    · exact Or.inl (Subtype.ext hj)
    · exact Or.inr (Subtype.ext hj)
  have hzo : z ≠ o := by
    intro h
    have := congrArg Subtype.val h
    change (0 : Fin 4) = 1 at this
    exact (by decide : (0 : Fin 4) ≠ 1) this
  have hv : Orthonormal ℝ (s.domRestrict v) := by
    rw [orthonormal_iff_ite]
    intro j k
    change inner ℝ (v j.val) (v k.val) = _
    have hvz : v z.val = WithLp.toLp 2 (fun i => A i 0) := by simp [v, z]
    have hvo : v o.val = WithLp.toLp 2 (fun i => A i 1) := by norm_num [v, o]
    rcases hcases j with rfl | rfl <;> rcases hcases k with rfl | rfl
    · simpa only [hvz, EuclideanSpace.inner_toLp_toLp, star_trivial, ↓reduceIte] using
        real_gram_entry A hA 0 0
    · simpa [hzo, hvz, hvo, EuclideanSpace.inner_toLp_toLp] using real_gram_entry A hA 1 0
    · simpa [Ne.symm hzo, hvz, hvo, EuclideanSpace.inner_toLp_toLp] using real_gram_entry A hA 0 1
    · simpa only [hvo, EuclideanSpace.inner_toLp_toLp, star_trivial, ↓reduceIte] using
        real_gram_entry A hA 1 1
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  let R : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun i j => b j i
  refine ⟨R, ?_, ?_, ?_⟩
  · have hGram : Rᴴ * R = 1 := by
      ext i j
      rw [Matrix.one_apply, ← orthonormal_iff_ite.mp b.orthonormal i j,
        EuclideanSpace.inner_eq_star_dotProduct]
      change (fun k => b i k) ⬝ᵥ (fun k => b j k) = (fun k => b j k) ⬝ᵥ (fun k => b i k)
      exact dotProduct_comm _ _
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hGram
  · intro i
    change b 0 i = A i 0
    rw [hb 0 (Or.inl rfl)]
    simp [v]
  · intro i
    change b 1 i = A i 1
    rw [hb 1 (Or.inr rfl)]
    norm_num [v]

private theorem real_frame_rows (R : Matrix (Fin 4) (Fin 4) ℝ) (hR : Rᵀ * R = 1) :
    ∀ i, R i 0 ^ 2 + R i 1 ^ 2 + R i 2 ^ 2 + R i 3 ^ 2 = 1 := by
  intro i
  have hr : R * Rᵀ = 1 := mul_eq_one_comm.mp hR
  have hi := congrFun (congrFun hr i) i
  simpa [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_four, pow_two, add_assoc] using hi

/-- Compress the real Gram of the third column to the orthogonal complement
of the conjugate pair and diagonalize that two-dimensional compression. -/
private theorem diagonalize_real_complement (p : Fin 4 → ℝ) (hp : ∑ i, p i = 1)
    (A B : Matrix (Fin 4) (Fin 2) ℝ) (hA : Aᵀ * A = 1) (hAB : Aᵀ * B = 0)
    (ha : ∀ i, A i 0 ^ 2 + A i 1 ^ 2 = 2 * p i)
    (hb : ∀ i, B i 0 ^ 2 + B i 1 ^ 2 = p i) : RealDiagonalGram p := by
  obtain ⟨R, hR, hR0, hR1⟩ := complete_real_pair A hA
  let tail : Fin 2 → Fin 4 := ![2, 3]
  let S : Matrix (Fin 4) (Fin 2) ℝ := R.submatrix id tail
  have hS : Sᵀ * S = 1 := by
    ext j k
    change (fun i => R i (tail j)) ⬝ᵥ (fun i => R i (tail k)) = _
    rw [real_gram_entry R hR, Matrix.one_apply]
    have hinj : Function.Injective tail := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [tail]
    simp only [hinj.eq_iff]
  let D := Rᵀ * B
  have hd0 (j : Fin 2) : D 0 j = 0 := by
    simpa [D, Matrix.mul_apply, hR0] using congrFun (congrFun hAB 0) j
  have hd1 (j : Fin 2) : D 1 j = 0 := by
    simpa [D, Matrix.mul_apply, hR1] using congrFun (congrFun hAB 1) j
  let K : Matrix (Fin 2) (Fin 2) ℝ := D.submatrix tail id
  have hSK : S * K = B := by
    have hRD : R * D = B := by
      change R * (Rᵀ * B) = B
      rw [← Matrix.mul_assoc, mul_eq_one_comm.mp hR, Matrix.one_mul]
    ext i j
    have hij := congrFun (congrFun hRD i) j
    change (∑ k : Fin 4, R i k * D k j) = B i j at hij
    simp only [Fin.sum_univ_four, hd0, hd1, mul_zero, zero_add] at hij
    change (∑ k : Fin 2, R i (tail k) * D (tail k) j) = B i j
    simpa [tail, Fin.sum_univ_two] using hij
  let T := K * Kᵀ
  have hT : T.PosSemidef := by
    simpa only [T, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose K
  have hTB : S * T * Sᵀ = B * Bᵀ := by
    rw [← hSK, Matrix.transpose_mul]
    simp only [T, Matrix.mul_assoc]
  have htrace : T.trace = 1 := by
    calc
      T.trace = (S * T * Sᵀ).trace := by
        rw [Matrix.trace_mul_comm (S * T) Sᵀ, ← Matrix.mul_assoc, hS, Matrix.one_mul]
      _ = (B * Bᵀ).trace := congrArg Matrix.trace hTB
      _ = 1 := by simpa only [Matrix.trace, Matrix.diag_apply, real_gram_diag, hb] using hp
  let l : Fin 2 → ℝ := hT.1.eigenvalues
  have hl (j : Fin 2) : 0 ≤ l j := hT.eigenvalues_nonneg j
  have hlsum : l 0 + l 1 = 1 := by
    simpa [l, Fin.sum_univ_two, htrace] using hT.1.trace_eq_sum_eigenvalues.symm
  let U : Matrix (Fin 2) (Fin 2) ℝ := hT.1.eigenvectorUnitary
  have hU : Uᵀ * U = 1 :=
    by
      have hu := Matrix.mem_unitaryGroup_iff'.mp (SetLike.coe_mem hT.1.eigenvectorUnitary)
      simpa only [U, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial] using hu
  have hspectral : T = U * Matrix.diagonal l * Uᵀ := by
    simpa only [U, l, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id,
      Function.id_comp] using hT.1.spectral_theorem
  let C := S * U
  have hC : Cᵀ * C = 1 := by
    dsimp only [C]
    rw [Matrix.transpose_mul, ← Matrix.mul_assoc (Uᵀ * Sᵀ) S U,
      Matrix.mul_assoc Uᵀ Sᵀ S, hS, Matrix.mul_one, hU]
  have hCC : C * Cᵀ = S * Sᵀ := by
    dsimp only [C]
    rw [Matrix.transpose_mul, Matrix.mul_assoc S U, ← Matrix.mul_assoc U Uᵀ,
      mul_eq_one_comm.mp hU, Matrix.one_mul]
  have hrow (i : Fin 4) : C i 0 ^ 2 + C i 1 ^ 2 = q p i := by
    rw [← real_gram_diag C i, hCC, real_gram_diag]
    change R i 2 ^ 2 + R i 3 ^ 2 = q p i
    have hit := real_frame_rows R hR i
    rw [hR0 i, hR1 i, ha i] at hit
    unfold q
    linarith
  have hdiagM : C * Matrix.diagonal l * Cᵀ = B * Bᵀ := by
    calc
      C * Matrix.diagonal l * Cᵀ = S * T * Sᵀ := by
        dsimp only [C]
        rw [hspectral, Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
      _ = B * Bᵀ := hTB
  have hdiag (i : Fin 4) : l 0 * C i 0 ^ 2 + l 1 * C i 1 ^ 2 = p i := by
    calc
      _ = (C * Matrix.diagonal l * Cᵀ) i i := by
        rw [Matrix.mul_apply, Fin.sum_univ_two]
        simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
        ring
      _ = p i := by rw [hdiagM, real_gram_diag, hb]
  refine ⟨C, l 0 - l 1, hC, by linarith [hl 0], by linarith [hl 1], hrow, ?_⟩
  intro i
  have h0 : (1 + (l 0 - l 1)) / 2 = l 0 := by linarith
  have h1 : (1 - (l 0 - l 1)) / 2 = l 1 := by linarith
  rw [h0, h1]
  exact hdiag i

private theorem conjugate_pair_gauge (z w : ℂ) (p : ℝ) (hp : 0 < p)
    (hz : Complex.normSq z = p) (hw : Complex.normSq w = p) :
    ∃ g : ℂ, Complex.normSq g = 1 ∧ g * z = star (g * w) := by
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (z * w) (n := 2) (by decide)
  have hr2 : Complex.normSq r ^ 2 = p ^ 2 := by
    simpa only [map_pow, Complex.normSq_mul, hz, hw, pow_two] using congrArg Complex.normSq hr
  have hrp : Complex.normSq r = p := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hr2 with h | h
    · exact h
    · linarith [Complex.normSq_nonneg r]
  have hr0 : r ≠ 0 := Complex.normSq_pos.mp (by simpa only [hrp] using hp)
  let g : ℂ := (Real.sqrt p : ℂ) / r
  have hg : Complex.normSq g = 1 := by
    dsimp only [g]
    rw [Complex.normSq_div, Complex.normSq_ofReal, ← pow_two, Real.sq_sqrt hp.le, hrp,
      div_self hp.ne']
  have hgprod : (g * w) * (g * z) = (p : ℂ) := by
    calc
      _ = g ^ 2 * (z * w) := by ring
      _ = (Real.sqrt p : ℂ) ^ 2 := by
        rw [← hr]
        dsimp [g]
        field_simp [hr0]
      _ = (p : ℂ) := by rw [← Complex.ofReal_pow, Real.sq_sqrt hp.le]
  have hgw : Complex.normSq (g * w) = p := by rw [Complex.normSq_mul, hg, hw, one_mul]
  have hgw0 : g * w ≠ 0 := Complex.normSq_pos.mp (by simpa only [hgw] using hp)
  refine ⟨g, hg, mul_left_cancel₀ hgw0 ?_⟩
  rw [hgprod, Complex.star_def, Complex.mul_conj, hgw]

/-- Unit row phase for a pair of equal weights, including simultaneous zero. -/
theorem conjugate_pair_gauge_nonneg (z w : ℂ) (p : ℝ) (hp : 0 ≤ p)
    (hz : Complex.normSq z = p) (hw : Complex.normSq w = p) :
    ∃ g : ℂ, Complex.normSq g = 1 ∧ g * z = star (g * w) := by
  rcases eq_or_lt_of_le hp with hzero | hpos
  · have hz0 : z = 0 := Complex.normSq_eq_zero.mp (hz.trans hzero.symm)
    have hw0 : w = 0 := Complex.normSq_eq_zero.mp (hw.trans hzero.symm)
    exact ⟨1, by simp, by simp [hz0, hw0]⟩
  · exact conjugate_pair_gauge z w p hpos hz hw

private theorem gauge_matrix (p : Fin 4 → ℝ) (hp : ∀ i, 0 ≤ p i)
    (W : Matrix (Fin 4) (Fin 3) ℂ) (hW : Wᴴ * W = 1)
    (hm : ∀ i j, Complex.normSq (W i j) = p i) :
    ∃ Z : Matrix (Fin 4) (Fin 3) ℂ, Zᴴ * Z = 1 ∧
      (∀ i j, Complex.normSq (Z i j) = p i) ∧ ∀ i, Z i 0 = star (Z i 1) := by
  choose g hg hpair using fun i =>
    conjugate_pair_gauge_nonneg (W i 0) (W i 1) (p i) (hp i) (hm i 0) (hm i 1)
  let Z : Matrix (Fin 4) (Fin 3) ℂ := Matrix.of fun i j => g i * W i j
  have hnorm (i : Fin 4) : star (g i) * g i = 1 := by
    rw [Complex.star_def, mul_comm, Complex.mul_conj, hg i, Complex.ofReal_one]
  refine ⟨Z, ?_, ?_, hpair⟩
  · rw [← hW]
    ext j k
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    apply Finset.sum_congr rfl
    intro i _
    change star (g i * W i j) * (g i * W i k) = star (W i j) * W i k
    rw [star_mul, mul_assoc, ← mul_assoc (star (g i)), hnorm, one_mul]
  · intro i j
    change Complex.normSq (g i * W i j) = p i
    rw [Complex.normSq_mul, hg, one_mul, hm]

theorem complex_gram_re {m n : Type*} [Fintype m]
    (Z : Matrix m n ℂ) (j k : n) :
    ((Zᴴ * Z) j k).re =
      (fun i => (Z i j).re) ⬝ᵥ (fun i => (Z i k).re) +
      (fun i => (Z i j).im) ⬝ᵥ (fun i => (Z i k).im) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum, Complex.star_def,
    Complex.mul_re, Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add,
    Finset.sum_add_distrib, dotProduct]

theorem complex_gram_im {m n : Type*} [Fintype m]
    (Z : Matrix m n ℂ) (j k : n) :
    ((Zᴴ * Z) j k).im =
      (fun i => (Z i j).re) ⬝ᵥ (fun i => (Z i k).im) -
      (fun i => (Z i j).im) ⬝ᵥ (fun i => (Z i k).re) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.im_sum, Complex.star_def,
    Complex.mul_im, Complex.conj_re, Complex.conj_im, neg_mul, ← sub_eq_add_neg,
    Finset.sum_sub_distrib, dotProduct]

private theorem real_diagonal_of_weighted_isometry (p : Fin 4 → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (W : Matrix (Fin 4) (Fin 3) ℂ) (hW : Wᴴ * W = 1)
    (hm : ∀ i j, Complex.normSq (W i j) = p i) : RealDiagonalGram p := by
  obtain ⟨Z, hZ, hz, hpairs⟩ := gauge_matrix p hp W hW hm
  let x (j : Fin 3) : Fin 4 → ℝ := fun i => (Z i j).re
  let y (j : Fin 3) : Fin 4 → ℝ := fun i => (Z i j).im
  have hx : x 0 = x 1 := by
    funext i
    exact (by simpa [x, Complex.star_def] using congrArg Complex.re (hpairs i))
  have hy : y 0 = -y 1 := by
    funext i
    exact (by simpa [y, Complex.star_def] using congrArg Complex.im (hpairs i))
  have hre (j k : Fin 3) :
      x j ⬝ᵥ x k + y j ⬝ᵥ y k = if j = k then 1 else 0 := by
    change (fun i => (Z i j).re) ⬝ᵥ (fun i => (Z i k).re) +
      (fun i => (Z i j).im) ⬝ᵥ (fun i => (Z i k).im) = _
    rw [← complex_gram_re Z j k, hZ, Matrix.one_apply]
    split_ifs <;> simp
  have him (j k : Fin 3) : x j ⬝ᵥ y k - y j ⬝ᵥ x k = 0 := by
    change (fun i => (Z i j).re) ⬝ᵥ (fun i => (Z i k).im) -
      (fun i => (Z i j).im) ⬝ᵥ (fun i => (Z i k).re) = _
    rw [← complex_gram_im Z j k, hZ, Matrix.one_apply]
    split_ifs <;> simp
  have h11 := hre 1 1
  have h01 := hre 0 1
  have hi01 := him 0 1
  have hxy : y 1 ⬝ᵥ x 1 = x 1 ⬝ᵥ y 1 := dotProduct_comm _ _
  norm_num [hx, hy, neg_dotProduct, dotProduct_neg, hxy] at h11 h01 hi01
  have hxx : x 1 ⬝ᵥ x 1 = 1 / 2 := by linarith only [h11, h01]
  have hyy : y 1 ⬝ᵥ y 1 = 1 / 2 := by linarith only [h11, h01]
  have hzero : x 1 ⬝ᵥ y 1 = 0 := by linarith only [hi01]
  have h02 := hre 0 2
  have h12 := hre 1 2
  have hi02 := him 0 2
  have hi12 := him 1 2
  norm_num [hx, hy, neg_dotProduct, dotProduct_neg] at h02 h12 hi02 hi12
  have hxu : x 1 ⬝ᵥ x 2 = 0 := by linarith only [h02, h12]
  have hyv : y 1 ⬝ᵥ y 2 = 0 := by linarith only [h02, h12]
  have hxv : x 1 ⬝ᵥ y 2 = 0 := by linarith only [hi02, hi12]
  have hyu : y 1 ⬝ᵥ x 2 = 0 := by linarith only [hi02, hi12]
  let k := Real.sqrt 2
  have hk : k ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  let av : Fin 2 → Fin 4 → ℝ := ![k • x 1, k • y 1]
  let bv : Fin 2 → Fin 4 → ℝ := ![x 2, y 2]
  let A : Matrix (Fin 4) (Fin 2) ℝ := Matrix.of fun i j => av j i
  let B : Matrix (Fin 4) (Fin 2) ℝ := Matrix.of fun i j => bv j i
  have hA : Aᵀ * A = 1 := by
    ext j l
    change av j ⬝ᵥ av l = (1 : Matrix (Fin 2) (Fin 2) ℝ) j l
    fin_cases j <;> fin_cases l <;>
      norm_num [av, Matrix.one_apply, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        hxx, hyy, hxy, hzero, ← pow_two, hk] <;> nlinarith only [hk]
  have hAB : Aᵀ * B = 0 := by
    ext j l
    change av j ⬝ᵥ bv l = 0
    fin_cases j <;> fin_cases l <;>
      simp [av, bv, smul_dotProduct, hxu, hxv, hyu, hyv]
  have ha (i : Fin 4) : A i 0 ^ 2 + A i 1 ^ 2 = 2 * p i := by
    have hz1 : x 1 i ^ 2 + y 1 i ^ 2 = p i := by
      simpa only [x, y, Complex.normSq_apply, pow_two] using hz i 1
    change (k * x 1 i) ^ 2 + (k * y 1 i) ^ 2 = 2 * p i
    rw [mul_pow, mul_pow, ← mul_add, hk, hz1]
  have hb (i : Fin 4) : B i 0 ^ 2 + B i 1 ^ 2 = p i := by
    change x 2 i ^ 2 + y 2 i ^ 2 = p i
    simpa only [x, y, Complex.normSq_apply, pow_two] using hz i 2
  exact diagonalize_real_complement p hp1 A B hA hAB ha hb

private theorem weighted_isometry_of_real_diagonal (p : Fin 4 → ℝ)
    (h : RealDiagonalGram p) :
    ∃ W : Matrix (Fin 4) (Fin 3) ℂ, Wᴴ * W = 1 ∧
      ∀ i j, Complex.normSq (W i j) = p i := by
  obtain ⟨C, s, hC, hslo, hshi, hCrow, hdiag⟩ := h
  obtain ⟨R, hR, hR0, hR1⟩ := complete_real_pair C hC
  let c : Fin 4 → ℝ := fun i => R i 0
  let e : Fin 4 → ℝ := fun i => R i 1
  let a : Fin 4 → ℝ := fun i => R i 2
  let b : Fin 4 → ℝ := fun i => R i 3
  have hab (i : Fin 4) : a i ^ 2 + b i ^ 2 = 2 * p i := by
    have h := real_frame_rows R hR i
    rw [hR0 i, hR1 i, hCrow i] at h
    unfold q at h
    change R i 2 ^ 2 + R i 3 ^ 2 = _
    linarith only [h]
  let k := Real.sqrt (1 / 2)
  let α := Real.sqrt ((1 + s) / 2)
  let β := Real.sqrt ((1 - s) / 2)
  have hk : k ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have hα : α ^ 2 = (1 + s) / 2 := Real.sq_sqrt (by linarith only [hslo])
  have hβ : β ^ 2 = (1 - s) / 2 := Real.sq_sqrt (by linarith only [hshi])
  let X : Fin 3 → Fin 4 → ℝ := ![k • a, k • a, α • c]
  let Y : Fin 3 → Fin 4 → ℝ := ![-(k • b), k • b, β • e]
  let W : Matrix (Fin 4) (Fin 3) ℂ := Matrix.of fun i j => ⟨X j i, Y j i⟩
  have hdot (j l : Fin 4) :
      (fun i => R i j) ⬝ᵥ (fun i => R i l) = if j = l then 1 else 0 :=
    real_gram_entry R hR j l
  have hsquares : α ^ 2 + β ^ 2 = 1 := by linarith only [hα, hβ]
  refine ⟨W, ?_, ?_⟩
  · ext j l
    apply Complex.ext
    · rw [complex_gram_re]
      change X j ⬝ᵥ X l + Y j ⬝ᵥ Y l = ((1 : Matrix (Fin 3) (Fin 3) ℂ) j l).re
      fin_cases j <;> fin_cases l <;>
        norm_num [X, Y, a, b, c, e, hdot, smul_dotProduct, dotProduct_smul, smul_eq_mul,
          neg_dotProduct, dotProduct_neg, Matrix.one_apply, ← pow_two, hsquares, hk]
    · rw [complex_gram_im]
      change X j ⬝ᵥ Y l - Y j ⬝ᵥ X l = ((1 : Matrix (Fin 3) (Fin 3) ℂ) j l).im
      fin_cases j <;> fin_cases l <;>
        norm_num [X, Y, a, b, c, e, hdot, smul_dotProduct, dotProduct_smul, smul_eq_mul,
          neg_dotProduct, dotProduct_neg, Matrix.one_apply]
  · intro i j
    have hpair : (k * a i)^2 + (k * b i)^2 = p i := by
      rw [mul_pow, mul_pow, ← mul_add, hk, hab]
      ring
    have hthird : (α * c i)^2 + (β * e i)^2 = p i := by
      rw [mul_pow, mul_pow, hα, hβ]
      simpa only [c, e, hR0 i, hR1 i] using hdiag i
    have hWnorm : Complex.normSq (W i j) = (X j i)^2 + (Y j i)^2 := by
      change Complex.normSq (Complex.mk (X j i) (Y j i)) = _
      simp only [Complex.normSq_mk, pow_two]
    rw [hWnorm]
    fin_cases j
    · simpa [X, Y, smul_eq_mul] using hpair
    · simpa [X, Y, smul_eq_mul] using hpair
    · simpa [X, Y, smul_eq_mul] using hthird

/-- A complex isometry with the prescribed row moduli exists exactly when a
real two-dimensional complementary frame has the prescribed Gram diagonal. -/
private theorem weighted_isometry_iff_real_diagonal_nonneg (p : Fin 4 → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    (∃ W : Matrix (Fin 4) (Fin 3) ℂ, Wᴴ * W = 1 ∧ ∀ i j, ‖W i j‖ ^ 2 = p i) ↔
      RealDiagonalGram p := by
  simp only [← Complex.normSq_eq_norm_sq]
  constructor
  · rintro ⟨W, hW, hm⟩
    exact real_diagonal_of_weighted_isometry p hp hp1 W hW hm
  · exact weighted_isometry_of_real_diagonal p

private theorem weight_le_third_of_isometry (p : Fin 4 → ℝ)
    (W : Matrix (Fin 4) (Fin 3) ℂ) (hW : Wᴴ * W = 1)
    (hm : ∀ i j, Complex.normSq (W i j) = p i) : ∀ i, p i ≤ 1 / 3 := by
  let P := W * Wᴴ
  have hP : P * P = P := by
    change (W * Wᴴ) * (W * Wᴴ) = W * Wᴴ
    rw [Matrix.mul_assoc W Wᴴ, ← Matrix.mul_assoc Wᴴ W, hW, Matrix.one_mul]
  let Q := 1 - P
  have hQ : Qᴴ = Q := by
    simp only [Q, P, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hQQ : Q * Qᴴ = Q := by
    rw [hQ]
    change (1 - P) * (1 - P) = 1 - P
    rw [sub_mul, Matrix.one_mul, mul_sub, Matrix.mul_one, hP, sub_self, sub_zero]
  have hdiag (i : Fin 4) : (P i i).re = 3 * p i := by
    change ((W * Wᴴ) i i).re = _
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
      Complex.mul_conj, Complex.add_re, Complex.ofReal_re, hm, Fin.sum_univ_three]
    ring
  intro i
  have hnonneg : 0 ≤ (Q i i).re := by
    have heq : (Q i i).re = ∑ j, Complex.normSq (Q i j) := by
      conv_lhs => rw [← hQQ]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
        Complex.mul_conj, Complex.re_sum, Complex.ofReal_re]
    rw [heq]
    exact Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (Q i j)
  have hqi : (Q i i).re = 1 - 3 * p i := by
    simp [Q, Matrix.sub_apply, hdiag]
  linarith only [hnonneg, hqi]

/-- Exact cubic feasibility for three weighted phase columns on four atoms.
The positive parameter is bounded by one and all four radicands are
nonnegative. `phaseCubic` is the explicit quartic after dividing out the
zero constant term as in `phaseQuartic_eq_mul_phaseCubic`. -/
theorem weighted_phase_columns_iff_cubic_nonneg (p : Fin 4 → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    (∃ W : Matrix (Fin 4) (Fin 3) ℂ, Wᴴ * W = 1 ∧ ∀ i j, ‖W i j‖ ^ 2 = p i) ↔
      (∀ i, p i ≤ 1 / 3) ∧ ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
        (∀ i, q p i ^ 2 * t ≥ d p i ^ 2) ∧ phaseCubic p t = 0 := by
  have q_nonneg (hb : ∀ i, p i ≤ 1 / 3) (i : Fin 4) : 0 ≤ q p i := by
    unfold q
    linarith only [hb i]
  constructor
  · rintro ⟨W, hW, hm⟩
    have hb := weight_le_third_of_isometry p W hW
      (fun i j => (Complex.normSq_eq_norm_sq (W i j)).trans (hm i j))
    have hg := (weighted_isometry_iff_real_diagonal_nonneg p hp hp1).1 ⟨W, hW, hm⟩
    exact ⟨hb, (realDiagonalGram_iff_cubic p hp1 (q_nonneg hb)).1 hg⟩
  · rintro ⟨hb, ht⟩
    exact (weighted_isometry_iff_real_diagonal_nonneg p hp hp1).2
      ((realDiagonalGram_iff_cubic p hp1 (q_nonneg hb)).2 ht)

/-- The cubic criterion at a strictly positive law. -/
theorem weighted_phase_columns_iff_cubic (p : Fin 4 → ℝ)
    (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1) :
    (∃ W : Matrix (Fin 4) (Fin 3) ℂ, Wᴴ * W = 1 ∧ ∀ i j, ‖W i j‖ ^ 2 = p i) ↔
      (∀ i, p i ≤ 1 / 3) ∧ ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
        (∀ i, q p i ^ 2 * t ≥ d p i ^ 2) ∧ phaseCubic p t = 0 :=
  weighted_phase_columns_iff_cubic_nonneg p (fun i => (hp i).le) hp1

/-- Exact feasible law with four distinct weights. -/
def feasibleWeights : Fin 4 → ℝ := ![29 / 100, 27 / 100, 25 / 100, 19 / 100]

private theorem feasible_cubic (t : ℝ) :
    phaseCubic feasibleWeights t =
      -32 * (44631 * t^3 - 55970 * t^2 + 15072 * t - 1152) / 244140625 := by
  norm_num [phaseCubic, cubicAfterConstant, q, d, feasibleWeights]; ring

/-- The feasible law has a genuine root strictly between one half and one. -/
private theorem feasible_cubic_has_root :
    ∃ t : ℝ, 1 / 2 < t ∧ t < 1 ∧
      (∀ i, d feasibleWeights i ^ 2 ≤ q feasibleWeights i ^ 2 * t) ∧
      phaseCubic feasibleWeights t = 0 := by
  have hleft : 0 < phaseCubic feasibleWeights (1 / 2) := by
    rw [feasible_cubic]
    norm_num
  have hright : phaseCubic feasibleWeights 1 < 0 := by
    rw [feasible_cubic]
    norm_num
  have hcont : Continuous (phaseCubic feasibleWeights) := by
    have hfun : phaseCubic feasibleWeights =
        fun t : ℝ => -32 * (44631 * t^3 - 55970 * t^2 + 15072 * t - 1152) / 244140625 :=
      funext feasible_cubic
    rw [hfun]
    fun_prop
  obtain ⟨t, ht, hroot⟩ :=
    intermediate_value_Icc' (show (1 / 2 : ℝ) ≤ 1 by norm_num) hcont.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (phaseCubic feasibleWeights 1)
        (phaseCubic feasibleWeights (1 / 2)) from ⟨hright.le, hleft.le⟩)
  have htlo : 1 / 2 < t := lt_of_le_of_ne ht.1 (by
    intro he
    rw [← he] at hroot
    exact hleft.ne' hroot)
  have hthi : t < 1 := lt_of_le_of_ne ht.2 (by
    intro he
    rw [he] at hroot
    exact hright.ne hroot)
  refine ⟨t, htlo, hthi, ?_, hroot⟩
  intro i
  have hbound : d feasibleWeights i ^ 2 ≤ q feasibleWeights i ^ 2 * (1 / 2) := by
    fin_cases i <;> norm_num [d, q, feasibleWeights]
  exact hbound.trans (mul_le_mul_of_nonneg_left ht.1 (sq_nonneg _))

/-- The feasible law admits the prescribed three orthonormal phase columns. -/
theorem feasible_weighted_phase_columns :
    ∃ W : Matrix (Fin 4) (Fin 3) ℂ, Wᴴ * W = 1 ∧
      ∀ i j, ‖W i j‖ ^ 2 = feasibleWeights i := by
  have hpos (i : Fin 4) : 0 < feasibleWeights i := by
    fin_cases i <;> norm_num [feasibleWeights]
  have hsum : ∑ i, feasibleWeights i = 1 := by
    norm_num [Fin.sum_univ_four, feasibleWeights]
  have hcap (i : Fin 4) : feasibleWeights i ≤ 1 / 3 := by
    fin_cases i <;> norm_num [feasibleWeights]
  obtain ⟨t, ht, ht1, hrad, hroot⟩ := feasible_cubic_has_root
  exact (weighted_phase_columns_iff_cubic feasibleWeights hpos hsum).2
    ⟨hcap, t, lt_trans (by norm_num) ht, ht1.le, hrad, hroot⟩

/-- Exact infeasible law with four distinct weights strictly below one third. -/
def infeasibleWeights : Fin 4 → ℝ :=
  ![19999 / 60000, 15001 / 60000, 12000 / 60000, 13000 / 60000]

private theorem infeasible_cubic (t : ℝ) :
    phaseCubic infeasibleWeights t =
      (187047147977039896 * t^3 + 345304640904270873 * t^2 +
        158219836231921608 * t + 14368342729440656) / 11390625000000000000 := by
  norm_num [phaseCubic, cubicAfterConstant, q, d, infeasibleWeights]; ring

/-- The cubic for the infeasible law has no positive real root. -/
private theorem infeasible_cubic_pos (t : ℝ) (ht : 0 < t) : 0 < phaseCubic infeasibleWeights t := by
  rw [infeasible_cubic]
  positivity

/-- The row cap alone does not imply existence of the three phase columns. -/
theorem infeasible_weighted_phase_columns :
    (∀ i, infeasibleWeights i < 1 / 3) ∧
    ¬ (∃ W : Matrix (Fin 4) (Fin 3) ℂ, Wᴴ * W = 1 ∧
      ∀ i j, ‖W i j‖ ^ 2 = infeasibleWeights i) := by
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [infeasibleWeights]
  · have hpos (i : Fin 4) : 0 < infeasibleWeights i := by
      fin_cases i <;> norm_num [infeasibleWeights]
    have hsum : ∑ i, infeasibleWeights i = 1 := by
      norm_num [Fin.sum_univ_four, infeasibleWeights]
    intro hW
    obtain ⟨_, t, ht, _, _, hroot⟩ :=
      (weighted_phase_columns_iff_cubic infeasibleWeights hpos hsum).1 hW
    exact (infeasible_cubic_pos t ht).ne' hroot

end D5.S3.Quantum.Measurements.ThreeDistinguishabilityCubic
