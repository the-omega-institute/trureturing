/- GID: D5/S3/Quantum/Measurement/Auric/DisjointEffects
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/Auric/DisjointEffects
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two disjoint small effects give a common sharp binary entropy bound for both spectral objectives. -/

import D5.S3.Quantum.Measurement.Auric.DisjointSpectralSuppliers
import D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-! Sharp spectral entropy of three effects when the two smaller supports fit disjointly. -/

namespace D5.S3.Quantum.Measurement.Auric.DisjointEffects

open _root_.Matrix
open scoped Matrix BigOperators ComplexOrder MatrixOrder
open D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects (Feasible spectralSum)
open D5.S3.Quantum.Measurement.Auric.EqualBlockEffects
  (diagonal_entropy effect_le_one entropyIntegrand)

open D5.S3.Quantum.Measurement.Auric.EqualBlockEffects (integrand_concave integrand_zero)

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem labels_univ {i k a : Fin 3} (hik : i ≠ k) (hia : i ≠ a) (hka : k ≠ a) :
    ({i, k, a} : Finset (Fin 3)) = Finset.univ := by
  apply (Finset.card_eq_iff_eq_univ _).mp
  simp [Finset.card_insert_of_notMem, hik, hia, hka]

theorem sum_three_labels {R : Type*} [AddCommMonoid R] {i k a : Fin 3}
    (hik : i ≠ k) (hia : i ≠ a) (hka : k ≠ a) (g : Fin 3 → R) :
    (∑ j, g j) = g i + g k + g a := by
  rw [← labels_univ hik hia hka]
  simp [Finset.sum_insert, hik, hia, hka, add_assoc]

private theorem integrand_reflect (flip : Bool) (x : ℝ) :
    entropyIntegrand flip (1 - x) = entropyIntegrand (!flip) x := by
  cases flip <;> simp [entropyIntegrand, sub_sub_cancel]

private theorem complement_spectral_eq (flip : Bool) {S C : Matrix n n ℂ}
    (hS : S.IsHermitian) (hC : C.IsHermitian) (he : C = 1 - S) :
    (∑ p, entropyIntegrand flip (hC.eigenvalues p)) =
      ∑ p, entropyIntegrand (!flip) (hS.eigenvalues p) := by
  subst C
  calc
    _ = ∑ p, entropyIntegrand flip (1 - hS.eigenvalues p) :=
      spectral_sum_one_sub (n := n) (entropyIntegrand flip) (M := S) hS hC
    _ = _ := Finset.sum_congr rfl (fun p _ => integrand_reflect flip _)

private theorem integrand_binary (flip : Bool) (x : ℝ) :
    entropyIntegrand flip x + entropyIntegrand (!flip) x = Real.binEntropy x := by
  cases flip <;> simp [entropyIntegrand, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    add_comm]

private theorem integrand_one (flip : Bool) : entropyIntegrand flip 1 = 0 := by
  cases flip <;> simp [entropyIntegrand]

private theorem gram_bound_for_effect {s : Type*} [Fintype s] [DecidableEq s]
    (flip : Bool) (V : Matrix s n ℂ) {X : Matrix n n ℂ} (hx : Vᴴ * V = X)
    (hp : X.PosSemidef) (hle : X ≤ 1) :
    (∑ p, entropyIntegrand flip (hp.isHermitian.eigenvalues p)) ≤
      ∑ q, entropyIntegrand flip (((V * Vᴴ) q q).re) := by
  subst X
  exact gram_spectral_sum_le_diagonal V hle (integrand_zero flip) (integrand_concave flip)

-- This bound uses no comparison between the sum of the two caps and the ambient dimension.
set_option maxHeartbeats 800000 in
theorem spectral_sum_le_binary
    {m : Fin 3 → ℕ} {t : Fin 3 → ℝ} {A : Fin 3 → Matrix n n ℂ}
    (hA : Feasible m t A) {i k a : Fin 3} (hik : i ≠ k) (hia : i ≠ a) (hka : k ≠ a)
    (flip : Bool) :
    spectralSum (entropyIntegrand flip) A hA.1 ≤
      (m i : ℝ) * Real.binEntropy (t i / m i) +
        (m k : ℝ) * Real.binEntropy (t k / m k) := by
  classical
  obtain ⟨X, hX, hx⟩ := exists_flat_rows_of_rank_le (hA.1 i) (hA.2.2.2 i)
  obtain ⟨Y, hY, hy⟩ := exists_flat_rows_of_rank_le (hA.1 k) (hA.2.2.2 k)
  let Z := Matrix.fromRows X Y
  have hZ : Zᴴ * Z = A i + A k := by
    dsimp only [Z]
    rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows, hX, hY]
  have hsum : A i + A k + A a = 1 := (sum_three_labels hik hia hka A).symm.trans hA.2.1
  have hcomp : 1 - (A i + A k) = A a := by
    rw [← hsum]
    abel
  have hS : (A i + A k).PosSemidef := (hA.1 i).add (hA.1 k)
  have hSle : A i + A k ≤ 1 := Matrix.le_iff.mpr (hcomp.symm ▸ hA.1 a)
  have hcx := gram_bound_for_effect flip X hX (hA.1 i) (effect_le_one A hA.1 hA.2.1 i)
  have hcy := gram_bound_for_effect flip Y hY (hA.1 k) (effect_le_one A hA.1 hA.2.1 k)
  have hcz := gram_bound_for_effect (!flip) Z hZ hS hSle
  have hz (p : Fin (m i) ⊕ Fin (m k)) :
      ((Z * Zᴴ) p p).re = p.elim (fun _ => t i / m i) (fun _ => t k / m k) := by
    rcases p with p | p
    · simpa [Z, Matrix.mul_apply, Matrix.conjTranspose_apply, hA.2.2.1 i] using hx p
    · simpa [Z, Matrix.mul_apply, Matrix.conjTranspose_apply, hA.2.2.1 k] using hy p
  have hreflect :
      (∑ p, entropyIntegrand flip ((hA.1 a).isHermitian.eigenvalues p)) =
        ∑ p, entropyIntegrand (!flip) (hS.isHermitian.eigenvalues p) :=
    complement_spectral_eq (S := A i + A k) (C := A a) flip hS.isHermitian
      (hA.1 a).isHermitian hcomp.symm
  simp only [hx, hy, hA.2.2.1, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hcx hcy
  simp only [hz, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hcz
  rw [spectralSum, sum_three_labels hik hia hka, hreflect]
  calc
    _ ≤ (m i : ℝ) * entropyIntegrand flip (t i / m i) +
        (m k : ℝ) * entropyIntegrand flip (t k / m k) +
        ((m i : ℝ) * entropyIntegrand (!flip) (t i / m i) +
          (m k : ℝ) * entropyIntegrand (!flip) (t k / m k)) :=
      add_le_add (add_le_add hcx hcy) hcz
    _ = _ := by simp only [← integrand_binary flip, mul_add]; ring

private theorem mass_div_capacity {m : ℕ} {t : ℝ} (h : 0 ≤ t ∧ t ≤ (m : ℝ)) :
    (m : ℝ) * (t / m) = t := by
  by_cases hm : m = 0
  · have ht : t = 0 := le_antisymm (by simpa [hm] using h.2) h.1
    simp [hm, ht]
  · exact mul_div_cancel₀ t (by exact_mod_cast hm)

private theorem mean_mem_unit {m : ℕ} {t : ℝ} (h : 0 ≤ t ∧ t ≤ (m : ℝ)) :
    t / (m : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hm : m = 0
  · simp [hm]
  · have hm' : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    exact ⟨div_nonneg h.1 hm'.le, (div_le_iff₀ hm').mpr (by simpa using h.2)⟩

/-- Two disjoint constant coordinate blocks and the residual effect attain both objectives. -/
theorem exists_common_binary_attainer
    (m : Fin 3 → ℕ) (t : Fin 3 → ℝ) {i k a : Fin 3}
    (hik : i ≠ k) (hia : i ≠ a) (hka : k ≠ a)
    (ha : Fintype.card n ≤ m a) (hfit : m i + m k ≤ Fintype.card n)
    (ht : ∀ j, 0 ≤ t j ∧ t j ≤ (m j : ℝ))
    (htotal : (∑ j, t j) = (Fintype.card n : ℝ)) :
    ∃ A : Fin 3 → Matrix n n ℂ, ∃ hA : Feasible m t A,
      ∀ flip : Bool, spectralSum (entropyIntegrand flip) A hA.1 =
        (m i : ℝ) * Real.binEntropy (t i / m i) +
          (m k : ℝ) * Real.binEntropy (t k / m k) := by
  classical
  let L := Fintype.card n - (m i + m k)
  have hL : m i + (m k + L) = Fintype.card n := by dsimp [L]; omega
  let e : n ≃ Fin (m i) ⊕ (Fin (m k) ⊕ Fin L) :=
    Fintype.equivOfCardEq (by simpa using hL.symm)
  let u : ℝ := t i / m i
  let v : ℝ := t k / m k
  let x (p : n) : ℝ := (e p).elim (fun _ => u) (fun _ => 0)
  let y (p : n) : ℝ := (e p).elim (fun _ => 0) (Sum.elim (fun _ => v) (fun _ => 0))
  let z (p : n) : ℝ := 1 - x p - y p
  let value (j : Fin 3) (p : n) : ℝ :=
    if j = i then x p else if j = k then y p else z p
  have hblocks (g : ℝ → ℝ → ℝ) :
      (∑ p, g (x p) (y p)) =
        (m i : ℝ) * g u 0 + ((m k : ℝ) * g 0 v + (L : ℝ) * g 0 0) := by
    let onBlocks (p : Fin (m i) ⊕ (Fin (m k) ⊕ Fin L)) :=
      p.elim (fun _ => g u 0) (Sum.elim (fun _ => g 0 v) (fun _ => g 0 0))
    rw [Fintype.sum_equiv e _ onBlocks (by
      intro p
      rcases he : e p with q | (q | q) <;> simp [x, y, onBlocks, he])]
    simp [onBlocks, Fintype.sum_sum_type, nsmul_eq_mul]
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := mean_mem_unit (ht i)
  have hv : v ∈ Set.Icc (0 : ℝ) 1 := mean_mem_unit (ht k)
  have hnonneg (j : Fin 3) (p : n) : 0 ≤ value j p := by
    have hxyz : 0 ≤ x p ∧ 0 ≤ y p ∧ 0 ≤ z p := by
      rcases he : e p with q | (q | q) <;>
        simp [x, y, z, he, sub_nonneg, hu.1, hu.2, hv.1, hv.2]
    obtain ⟨hx, hy, hz⟩ := hxyz
    by_cases hj : j = i
    · simpa [value, hj] using hx
    · by_cases hj' : j = k
      · simpa only [value, ite_eq_right hj, ite_eq_left hj'] using hy
      · simpa [value, hj, hj'] using hz
  let A (j : Fin 3) : Matrix n n ℂ := diagonal (fun p => (value j p : ℂ))
  have hp (j : Fin 3) : (A j).PosSemidef := by
    exact Matrix.PosSemidef.diagonal (fun p => Complex.nonneg_iff.mpr
      ⟨by simpa using hnonneg j p, by simp⟩)
  have hs : (∑ j, A j) = 1 := by
    ext p q
    by_cases hpq : p = q
    · subst q
      simp only [Matrix.sum_apply, A, diagonal_apply_eq, one_apply_eq, ← Complex.ofReal_sum]
      rw [sum_three_labels hik hia hka]
      have he : value i p + value k p + value a p = 1 := by
        simp [value, hik.symm, hia.symm, hka.symm, z] <;> ring
      rw [he, Complex.ofReal_one]
    · simp [Matrix.sum_apply, A, hpq]
  have hmassX : (m i : ℝ) * u = t i := mass_div_capacity (ht i)
  have hmassY : (m k : ℝ) * v = t k := mass_div_capacity (ht k)
  have htraceX : (∑ p, x p) = t i := by
    simpa [hmassX] using hblocks (fun b _ => b)
  have htraceY : (∑ p, y p) = t k := by
    simpa [hmassY] using hblocks (fun _ b => b)
  have htraceZ : (∑ p, z p) = t a := by
    have h := htotal
    rw [sum_three_labels hik hia hka] at h
    simp only [z, Finset.sum_sub_distrib, htraceX, htraceY, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one]
    linarith
  have label_cases (j : Fin 3) : j = i ∨ j = k ∨ j = a := by
    have hj : j ∈ ({i, k, a} : Finset (Fin 3)) := by
      rw [labels_univ hik hia hka]
      exact Finset.mem_univ _
    simpa using hj
  have htrace (j : Fin 3) : (A j).trace.re = t j := by
    simp only [A, Matrix.trace_diagonal, Complex.re_sum, Complex.ofReal_re]
    rcases label_cases j with rfl | rfl | rfl
    · simpa [value] using htraceX
    · simpa [value, hik.symm] using htraceY
    · simpa [value, hia.symm, hka.symm] using htraceZ
  let count (b : ℝ) : ℝ := if b = 0 then 0 else 1
  have hrank_count (j : Fin 3) : ((A j).rank : ℝ) = ∑ p, count (value j p) := by
    change ((diagonal (fun p => (value j p : ℂ))).rank : ℝ) = _
    rw [Matrix.rank_diagonal, Fintype.card_subtype, Finset.natCast_card_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : value j p = 0 <;> simp [count, h]
  have hcount (b : ℝ) : count b ≤ 1 := by unfold count; split <;> norm_num
  have hrank (j : Fin 3) : (A j).rank ≤ m j := by
    rcases label_cases j with hji | hjk | hja
    · subst j
      suffices hh : ((A i).rank : ℝ) ≤ (m i : ℝ) by exact_mod_cast hh
      rw [hrank_count]
      have he : (∑ p, count (value i p)) = (m i : ℝ) * count u := by
        simpa [value, show count 0 = 0 by simp [count]] using hblocks (fun b _ => count b)
      rw [he]
      exact mul_le_of_le_one_right (Nat.cast_nonneg _) (hcount u)
    · subst j
      suffices hh : ((A k).rank : ℝ) ≤ (m k : ℝ) by exact_mod_cast hh
      rw [hrank_count]
      have he : (∑ p, count (value k p)) = (m k : ℝ) * count v := by
        simpa [value, hik.symm, show count 0 = 0 by simp [count]] using
          hblocks (fun _ b => count b)
      rw [he]
      exact mul_le_of_le_one_right (Nat.cast_nonneg _) (hcount v)
    · subst j
      exact (Matrix.rank_le_card_width (A a)).trans ha
  refine ⟨A, ⟨hp, hs, htrace, hrank⟩, ?_⟩
  intro flip
  let f := entropyIntegrand flip
  have h0 : f 0 = 0 := integrand_zero flip
  have h1 : f 1 = 0 := integrand_one flip
  have hbinary (b : ℝ) : f b + f (1 - b) = Real.binEntropy b := by
    simpa only [f, integrand_reflect] using integrand_binary flip b
  calc
    spectralSum f A hp = ∑ j, ∑ p, f (value j p) :=
      Finset.sum_congr rfl (fun j _ => diagonal_entropy f (value j) (hp j).isHermitian)
    _ = ∑ p, (f (x p) + f (y p) + f (1 - x p - y p)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      rw [sum_three_labels hik hia hka]
      simp [value, hik.symm, hia.symm, hka.symm, z]
    _ = _ := by
      rw [hblocks (fun b c => f b + f c + f (1 - b - c))]
      simp only [h0, h1, sub_zero, add_zero, zero_add, mul_zero, hbinary, u, v]

/-- Attained spectral maximum on the fixed-trace feasible set, for either projection branch. -/
theorem isGreatest_disjoint
    (m : Fin 3 → ℕ) (t : Fin 3 → ℝ) {i k a : Fin 3}
    (hik : i ≠ k) (hia : i ≠ a) (hka : k ≠ a)
    (ha : Fintype.card n ≤ m a) (hfit : m i + m k ≤ Fintype.card n)
    (ht : ∀ j, 0 ≤ t j ∧ t j ≤ (m j : ℝ))
    (htotal : (∑ j, t j) = (Fintype.card n : ℝ)) (flip : Bool) :
    IsGreatest {v : ℝ | ∃ A : Fin 3 → Matrix n n ℂ, ∃ hA : Feasible m t A,
      spectralSum (entropyIntegrand flip) A hA.1 = v}
      ((m i : ℝ) * Real.binEntropy (t i / m i) +
        (m k : ℝ) * Real.binEntropy (t k / m k)) := by
  obtain ⟨A, hA, he⟩ := exists_common_binary_attainer (n := n) m t hik hia hka ha hfit ht htotal
  refine ⟨⟨A, hA, he flip⟩, ?_⟩
  rintro w ⟨B, hB, rfl⟩
  exact spectral_sum_le_binary hB hik hia hka flip

end

end D5.S3.Quantum.Measurement.Auric.DisjointEffects
