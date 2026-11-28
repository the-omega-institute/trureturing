/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/Paley/P48pPaleyNormFour
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/Paley/P48pPaleyNormFour
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A norm-four vector in the actual P48p odd neighbor forces a short Paley graph pair. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.Lattice.Orbifold.Paley.P48pTernaryPaleyGraph
import OmegaBuild.Commands

compile_only_with_mathlib

/-!
# The P48p Paley norm-four reduction

Half-frame pairings take a norm-four neighbor vector to an integral row with
square sum twelve. Its ternary residue gives a Paley graph pair. The conference
involution lets the lighter half serve as input to a small-support certificate.
-/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48pPaleyNormFour

open scoped BigOperators Matrix
open P48pOddNeighbor
  (IntRow RatRow oddNeighbor cataloguePairing cataloguePairing_eq halfFramePairings ratRow
    ternaryResidue frameSyndrome mem_oddNeighbor_iff_ternary)
open P48pFrameProjectiveAction (chartSign)
open P48pTernaryPaleyGraph
  (F3 signedChartWord paleyC paleyC_sq frameSyndrome_eq_zero_iff_signedChart_graph)

open private chartIndexEquiv chartIndex chartSign_sq from
  D5.S3.VertexAlgebra.Lattice.Orbifold.Paley.P48pTernaryPaleyGraph

private theorem hammingNorm_signedChartWord_add (u : Fin 48 → F3) :
    hammingNorm u = hammingNorm (signedChartWord u 0) + hammingNorm (signedChartWord u 1) := by
  have hSign (i : Fin 48) : (chartSign i : F3) ≠ 0 := by
    intro h
    have hs := chartSign_sq i
    rw [h, zero_mul] at hs
    exact zero_ne_one hs
  simp only [hammingNorm, Finset.card_filter]
  calc
    _ = ∑ p : Fin 24 × Fin 2, (if u (chartIndexEquiv p) ≠ 0 then (1 : ℕ) else 0) :=
      (chartIndexEquiv.sum_comp (fun i : Fin 48 => if u i ≠ 0 then (1 : ℕ) else 0)).symm
    _ = ∑ d : Fin 24, ∑ k : Fin 2, (if signedChartWord u k d ≠ 0 then (1 : ℕ) else 0) := by
      rw [← Finset.univ_product_univ, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro k _
      change (if u (chartIndex d k) ≠ 0 then (1 : ℕ) else 0) =
        (if (chartSign (chartIndex d k) : F3) * u (chartIndex d k) ≠ 0 then 1 else 0)
      simp only [mul_ne_zero_iff_left (hSign (chartIndex d k))]
    _ = _ := by simp only [Fin.sum_univ_two, Finset.sum_add_distrib]

private theorem paley_graph_swap {a b : Fin 24 → F3} (hab : b = a ᵥ* paleyC) :
    a = b ᵥ* paleyC := by
  rw [hab, Matrix.vecMul_vecMul, paleyC_sq, Matrix.vecMul_one]

/-- The integral half-frame row of a norm-four vector gives a nonzero ternary
kernel word of weight at most twelve, with two nonzero Paley graph halves. -/
theorem exists_ternary_kernel_word_of_norm_four
    (x : RatRow) (hx : x ∈ oddNeighbor) (hNorm : cataloguePairing x x = 4) :
    ∃ y : IntRow, halfFramePairings x = ratRow y ∧
      let u := ternaryResidue y
      let a := signedChartWord u 0
      let b := signedChartWord u 1
      u ≠ 0 ∧ frameSyndrome u = 0 ∧ b = a ᵥ* paleyC ∧ a ≠ 0 ∧ b ≠ 0 ∧
        hammingNorm u = hammingNorm a + hammingNorm b ∧ hammingNorm u ≤ 12 := by
  obtain ⟨y, hPair, hSyndrome⟩ := (mem_oddNeighbor_iff_ternary x).mp hx
  let u := ternaryResidue y
  have hSquares : (∑ j, y j ^ 2) = 12 := by
    have hPairNorm : cataloguePairing x x = ((∑ j, y j ^ 2 : ℤ) : ℚ) / 3 := by
      rw [cataloguePairing_eq, hPair]
      simp only [dotProduct, ratRow, Int.cast_sum, pow_two, Int.cast_mul]
    have hQ : ((∑ j, y j ^ 2 : ℤ) : ℚ) = 12 := by linarith only [hPairNorm, hNorm]
    exact_mod_cast hQ
  have hu : u ≠ 0 := by
    intro hZero
    have hDvd : (9 : ℤ) ∣ ∑ j, y j ^ 2 := by
      apply Finset.dvd_sum
      intro j _
      have hj : (y j : F3) = 0 := congrFun hZero j
      obtain ⟨w, hw⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (y j) 3).mp hj
      refine ⟨w ^ 2, ?_⟩
      rw [hw] <;> ring
    rw [hSquares] at hDvd
    exact (by decide : ¬ (9 : ℤ) ∣ 12) hDvd
  have hWeight : hammingNorm u ≤ 12 := by
    let support := Finset.univ.filter (fun j => u j ≠ 0)
    have hBound : (hammingNorm u : ℤ) ≤ ∑ j, y j ^ 2 := by
      calc
        _ = ∑ j ∈ support, (1 : ℤ) := by simp [hammingNorm, support]
        _ ≤ ∑ j ∈ support, y j ^ 2 := by
          apply Finset.sum_le_sum
          intro j hj
          have hResidue : u j ≠ 0 := (Finset.mem_filter.mp hj).2
          have hj' : y j ≠ 0 := fun hz => hResidue (by simp [u, ternaryResidue, hz])
          have hSquare := sq_pos_of_ne_zero hj'
          omega
        _ ≤ ∑ j, y j ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun j _ _ => sq_nonneg (y j))
    rw [hSquares] at hBound
    exact_mod_cast hBound
  let a := signedChartWord u 0
  let b := signedChartWord u 1
  have hab : b = a ᵥ* paleyC := (frameSyndrome_eq_zero_iff_signedChart_graph u).mp hSyndrome
  have hba : a = b ᵥ* paleyC := paley_graph_swap hab
  have hSplit : hammingNorm u = hammingNorm a + hammingNorm b :=
    hammingNorm_signedChartWord_add u
  have hNotBoth (ha : a = 0) (hb : b = 0) : False := by
    apply hu
    apply hammingNorm_eq_zero.mp
    simp only [hSplit, ha, hb, hammingNorm_zero, Nat.zero_add]
  have ha : a ≠ 0 := by
    intro h
    apply hNotBoth h
    rw [hab, h, Matrix.zero_vecMul]
  have hb : b ≠ 0 := by
    intro h
    refine hNotBoth ?_ h
    rw [hba, h, Matrix.zero_vecMul]
  exact ⟨y, hPair, hu, hSyndrome, hab, ha, hb, hSplit, hWeight⟩

/-- Orient the two signed halves of the same residue so the lighter half is
the input to the Paley matrix. -/
theorem exists_small_paley_graph_pair_of_norm_four
    (x : RatRow) (hx : x ∈ oddNeighbor) (hNorm : cataloguePairing x x = 4) :
    ∃ (y : IntRow) (a b : Fin 24 → F3),
      let u := ternaryResidue y
      halfFramePairings x = ratRow y ∧
      ((a, b) = (signedChartWord u 0, signedChartWord u 1) ∨
        (a, b) = (signedChartWord u 1, signedChartWord u 0)) ∧
      a ≠ 0 ∧ b ≠ 0 ∧ b = a ᵥ* paleyC ∧
      hammingNorm a ≤ hammingNorm b ∧ hammingNorm a ≤ 6 ∧
      hammingNorm a + hammingNorm b ≤ 12 := by
  obtain ⟨y, hPair, hWord⟩ := exists_ternary_kernel_word_of_norm_four x hx hNorm
  obtain ⟨_, _, hab, ha, hb, hSplit, hWeight⟩ := hWord
  let a := signedChartWord (ternaryResidue y) 0
  let b := signedChartWord (ternaryResidue y) 1
  have hTotal : hammingNorm a + hammingNorm b ≤ 12 := le_of_eq_of_le hSplit.symm hWeight
  by_cases hOrder : hammingNorm a ≤ hammingNorm b
  · exact ⟨y, a, b, hPair, Or.inl rfl, ha, hb, hab, hOrder, by omega, hTotal⟩
  · have hReverseOrder : hammingNorm b ≤ hammingNorm a := by omega
    have hReverseTotal : hammingNorm b + hammingNorm a ≤ 12 := by
      rw [Nat.add_comm]
      exact hTotal
    exact ⟨y, b, a, hPair, Or.inr rfl, hb, ha, paley_graph_swap hab,
      hReverseOrder, by omega, hReverseTotal⟩

/-- A certificate on nonzero Paley inputs of weight at most six suffices to
exclude norm four in the actual odd neighbor. -/
theorem norm_ne_four_of_paley_small_support
    (hCertificate : ∀ a : Fin 24 → F3, a ≠ 0 → hammingNorm a ≤ 6 →
      12 < hammingNorm a + hammingNorm (a ᵥ* paleyC))
    (x : RatRow) (hx : x ∈ oddNeighbor) : cataloguePairing x x ≠ 4 := by
  intro hNorm
  obtain ⟨_, a, b, _, _, ha, _, hab, _, hSix, hTotal⟩ :=
    exists_small_paley_graph_pair_of_norm_four x hx hNorm
  rw [hab] at hTotal
  exact (not_lt_of_ge hTotal) (hCertificate a ha hSix)

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48pPaleyNormFour
