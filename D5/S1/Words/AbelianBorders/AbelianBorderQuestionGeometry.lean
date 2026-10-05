/- GID: D5/S1/Words/AbelianBorders/AbelianBorderQuestionGeometry
   generality: G
   mirror-B: D5/B/S1/Words/AbelianBorders/AbelianBorderQuestionGeometry
   mirror-E: none(waiver:ternary-path-geometry)
   anchors: []
   utility: none
   digest: Continuous cylinder containment and recurring exposed fibers of the ternary path. -/

import D5.S1.Words.AbelianBorders.AbelianBorderQuestionWord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.AbelianBorders
open AbelianBorderQuestionDefs
namespace Counterexample

noncomputable def axis : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![1, 1, 1]

/-- Representatives of the four vertices, modulo the rational axis. -/
noncomputable def vertex (i : Fin 4) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (![![-3, -3, 0], ![0, -3, 0], ![2, 2, 0], ![0, 2, 0]] i)

set_option maxHeartbeats 1500000 in
-- Coordinate reduction covers every prefix of both balanced blocks.
/-- The full continuous path is cylindrical; every supporting single fiber recurs. -/
theorem geometric : GeometricHypotheses word := by
  classical
  obtain ⟨prefixFormula, balanced, _⟩ := word_structure
  have size (j : ℕ) : 3 ≤ (block j).length ∧ (block j).length ≤ 15 := by
    unfold block
    split <;> decide
  have growth : ∀ j, j ≤ (initial j).length := by
    intro j
    induction j with
    | zero => simp [initial]
    | succ j ih =>
      simp only [initial, List.length_append]
      have := (size j).1
      omega
  have locate (n : ℕ) : ∃ j r, n = (initial j).length + r ∧ r < (block j).length := by
    have ex : ∃ j, n < (initial (j + 1)).length := ⟨n, by have := growth (n + 1); omega⟩
    let j := Nat.find ex
    have hj : n < (initial (j + 1)).length := Nat.find_spec ex
    have lo : (initial j).length ≤ n := by
      cases hj0 : j with
      | zero => simp [initial]
      | succ k =>
        have h := Nat.find_min ex (show k < j by omega)
        omega
    refine ⟨j, n - (initial j).length, by omega, ?_⟩
    simp only [initial, List.length_append] at hj
    omega
  have blockRepr (j r : ℕ) (hr : r ≤ (block j).length) :
      ∃ t : Fin 4 → ℝ, (∀ i, 0 ≤ t i) ∧ (∑ i, t i) = 1 ∧
        (WithLp.toLp 2 (fun a : Fin 3 => (((block j).take r).count a : ℝ)) :
          EuclideanSpace ℝ (Fin 3)) =
        (∑ i, t i • vertex i) + (((block j).take r).count 2 : ℝ) • axis := by
    let wa : ℕ → Fin 4 → ℝ := fun r =>
      [![0, 2/5, 0, 3/5], ![0, 1/5, 0, 4/5], ![0, 0, 0, 1],
       ![0, 0, 1/2, 1/2], ![0, 0, 1, 0], ![1/5, 0, 4/5, 0],
       ![2/5, 0, 3/5, 0], ![3/5, 0, 2/5, 0], ![4/5, 0, 1/5, 0],
       ![1, 0, 0, 0], ![2/3, 1/3, 0, 0], ![1/3, 2/3, 0, 0],
       ![0, 1, 0, 0], ![0, 4/5, 0, 1/5], ![0, 3/5, 0, 2/5],
       ![0, 2/5, 0, 3/5]].getD r 0
    let wb : ℕ → Fin 4 → ℝ := fun r =>
      [![0, 2/5, 0, 3/5], ![0, 2/5, 1/2, 1/10],
       ![0, 1/5, 1/2, 3/10], ![0, 2/5, 0, 3/5]].getD r 0
    unfold block at hr ⊢
    by_cases hj : IsSquare j
    · simp only [if_pos hj] at hr ⊢
      refine ⟨wb r, ?_, ?_, ?_⟩
      · intro i
        have : r ≤ 3 := hr
        interval_cases r <;> fin_cases i <;> norm_num [wb]
      · have : r ≤ 3 := hr
        interval_cases r <;> norm_num [wb, Fin.sum_univ_succ]
      · have : r ≤ 3 := hr
        interval_cases r <;> ext a <;> fin_cases a <;>
          norm_num [B, wb, vertex, axis, Fin.sum_univ_succ, List.count_cons,
            List.count_nil, Fin.ext_iff]
    · simp only [if_neg hj] at hr ⊢
      refine ⟨wa r, ?_, ?_, ?_⟩
      · intro i
        have : r ≤ 15 := hr
        interval_cases r <;> fin_cases i <;> norm_num [wa]
      · have : r ≤ 15 := hr
        interval_cases r <;> norm_num [wa, Fin.sum_univ_succ]
      · have : r ≤ 15 := hr
        interval_cases r <;> ext a <;> fin_cases a <;>
          norm_num [A, wa, vertex, axis, Fin.sum_univ_succ, List.count_cons,
            List.count_nil, Fin.ext_iff]
  have discreteRepr (n : ℕ) :
      ∃ (t : Fin 4 → ℝ) (z : ℝ), (∀ i, 0 ≤ t i) ∧ (∑ i, t i) = 1 ∧
        parikhPoint word n = (∑ i, t i • vertex i) + z • axis := by
    obtain ⟨j, r, hn, hr⟩ := locate n
    obtain ⟨t, ht, hs, he⟩ := blockRepr j r (by omega)
    refine ⟨t, ((initial j).count 0 : ℝ) + (((block j).take r).count 2 : ℝ), ht, hs, ?_⟩
    rw [hn]
    unfold parikhPoint letterCount
    rw [prefixFormula j r (by omega)]
    ext a
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v a) he
    simp only [List.count_append, Nat.cast_add] at h ⊢
    rw [balanced j a]
    fin_cases a <;> simp [axis, PiLp.add_apply, PiLp.smul_apply] at h ⊢ <;> linarith
  have continuousRepr (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ graph word) :
      ∃ (t : Fin 4 → ℝ) (z : ℝ), (∀ i, 0 ≤ t i) ∧ (∑ i, t i) = 1 ∧
        x = (∑ i, t i • vertex i) + z • axis := by
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    rw [segment_eq_image ℝ] at hn
    obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := hn
    obtain ⟨u, z, hu, hu1, he⟩ := discreteRepr n
    obtain ⟨v, z', hv, hv1, he'⟩ := discreteRepr (n + 1)
    refine ⟨fun i => (1 - s) * u i + s * v i, (1 - s) * z + s * z', ?_, ?_, ?_⟩
    · intro i
      exact add_nonneg (mul_nonneg (by linarith) (hu i)) (mul_nonneg hs0 (hv i))
    · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hu1, hv1]
      ring
    · rw [he, he']
      simp only [smul_add, Finset.smul_sum, smul_smul, add_smul, Finset.sum_add_distrib]
      abel
  have atVertex (i : Fin 4) (n : ℕ) :
      ∃ (m : ℕ) (z : ℝ), n ≤ m ∧ m ≤ n + 60 ∧ parikhPoint word m = vertex i + z • axis := by
    obtain ⟨j, r, hn, hr⟩ := locate n
    have notBoth (q : ℕ) (hq : 0 < q) : ¬ (IsSquare q ∧ IsSquare (q + 1)) := by
      rintro ⟨hs, ht⟩
      obtain ⟨s, hs⟩ := IsSquare.exists_sq q hs
      obtain ⟨t, ht⟩ := IsSquare.exists_sq (q + 1) ht
      have hst : s < t := by nlinarith
      have hpos : 0 < s := by nlinarith
      have hh : (s + 1) ^ 2 ≤ t ^ 2 := Nat.pow_le_pow_left (by omega) 2
      nlinarith
    have good : ∃ k, j + 1 ≤ k ∧ k ≤ j + 2 ∧ ¬ IsSquare k := by
      by_cases h : IsSquare (j + 1)
      · exact ⟨j + 2, by omega, by omega, fun h' => notBoth (j + 1) (by omega) ⟨h, h'⟩⟩
      · exact ⟨j + 1, le_rfl, by omega, h⟩
    obtain ⟨k, hklo, hkhi, hk⟩ := good
    have hb : block k = A := by simp [block, hk]
    let off : Fin 4 → ℕ := ![9, 12, 4, 2]
    let m := (initial k).length + off i
    have step (q : ℕ) : (initial (q + 1)).length =
        (initial q).length + (block q).length := by simp [initial]
    have mono : StrictMono (fun q => (initial q).length) :=
      strictMono_nat_of_lt_succ fun q => by rw [step]; have := (size q).1; omega
    have lower := mono.monotone hklo
    have upper := mono.monotone hkhi
    have ho : off i ≤ 12 := by fin_cases i <;> decide
    refine ⟨m, ((initial k).count 0 : ℝ) + ((A.take (off i)).count 2 : ℝ), ?_, ?_, ?_⟩
    · simp only [initial, List.length_append] at lower
      dsimp [m]
      omega
    · rw [step, step] at upper
      have := (size j).2
      have := (size (j + 1)).2
      dsimp [m]
      omega
    · unfold parikhPoint letterCount
      rw [prefixFormula k (off i) (by rw [hb]; simp [A]; omega), hb]
      ext a
      simp only [List.count_append, Nat.cast_add, balanced k a]
      fin_cases i <;> fin_cases a <;>
        norm_num [off, A, vertex, axis, List.count_cons, List.count_nil,
          Fin.ext_iff] <;> ring
  refine ⟨0, axis, 10, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro h
      have := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) h
      norm_num [axis] at this
    · intro i
      refine ⟨1, ?_⟩
      fin_cases i <;> norm_num [axis]
  · intro x hx
    obtain ⟨t, z, ht, hs, he⟩ := continuousRepr x hx
    have hz : z • axis ∈ line 0 axis := ⟨z, by simp⟩
    apply (Metric.infDist_le_dist_of_mem hz).trans
    rw [dist_eq_norm, he, add_sub_cancel_right]
    have hv (i : Fin 4) : ‖vertex i‖ ≤ 10 := by
      have heq := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) (vertex i)
      have hp := norm_nonneg (vertex i)
      fin_cases i <;>
        norm_num [vertex, Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs] at heq hp ⊢ <;>
        nlinarith
    calc
      ‖∑ i, t i • vertex i‖ ≤ ∑ i, ‖t i • vertex i‖ := norm_sum_le _ _
      _ = ∑ i, t i * ‖vertex i‖ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ht i)]
      _ ≤ ∑ i, t i * 10 := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hv i) (ht i)
      _ = 10 := by rw [← Finset.sum_mul, hs]; ring
  · intro y hy
    obtain ⟨b, d, hb, hba, hsupport, hcontact, hline, hsingle⟩ := hy
    have realInner (t : ℝ) : inner ℝ b (t • axis) = 0 := by
      rw [inner_smul_right, hba, mul_zero]
    have bound (i : Fin 4) : d ≤ inner ℝ b (vertex i) := by
      obtain ⟨m, z, _, _, he⟩ := atVertex i 0
      have hm : parikhPoint word m ∈ graph word :=
        Set.mem_iUnion.mpr ⟨m, left_mem_segment ℝ _ _⟩
      have h := hsupport _ hm
      simpa [he, inner_add_right, realInner] using h
    have minimizing : ∃ i : Fin 4, inner ℝ b (vertex i) = d := by
      by_contra hn
      push Not at hn
      have strict (i : Fin 4) : d < inner ℝ b (vertex i) :=
        lt_of_le_of_ne (bound i) (Ne.symm (hn i))
      obtain ⟨x, hx, he⟩ := hcontact
      obtain ⟨t, z, ht, hs, hre⟩ := continuousRepr x hx
      have hp : ∃ i : Fin 4, 0 < t i := by
        by_contra hp
        push Not at hp
        have hall : ∀ i, t i = 0 := fun i => le_antisymm (hp i) (ht i)
        simp [hall] at hs
      obtain ⟨i, hi⟩ := hp
      have hsum : d < ∑ j, t j * inner ℝ b (vertex j) := by
        calc
          d = ∑ j : Fin 4, t j * d := by rw [← Finset.sum_mul, hs]; ring
          _ < ∑ j : Fin 4, t j * inner ℝ b (vertex j) := by
            apply Finset.sum_lt_sum
            · intro j _
              exact mul_le_mul_of_nonneg_left (bound j) (ht j)
            · exact ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left (strict i) hi⟩
      rw [hre, inner_add_right, realInner, add_zero, inner_sum] at he
      simp only [inner_smul_right] at he
      linarith
    obtain ⟨i, hi⟩ := minimizing
    refine ⟨60, ?_⟩
    intro n
    obtain ⟨m, z, hnm, hmn, he⟩ := atVertex i n
    refine ⟨m, hnm, hmn, hsingle _ (Set.mem_iUnion.mpr ⟨m, left_mem_segment ℝ _ _⟩) ?_⟩
    simp [he, inner_add_right, realInner, hi]

end Counterexample
end D5.S1.Words.AbelianBorders
