/- GID: D5/S3/VertexAlgebra/Lattice/SimplexMinimalShell
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/SimplexMinimalShell
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integer cut-energy rigidity classifies the complete simplex minimal shell. -/

import Mathlib.Data.Fintype.Lattice
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
The doubled complete-graph energy of arbitrary integer coordinates is bounded
below by twice the cardinality minus two unless the coordinates are constant.
Equality reconstructs two adjacent levels with a singleton side. This is the
classical minimum-vector geometry of A_r dual; no novelty is claimed.

proof_shape: content
admission_basis: escape-witness
escape_witness: integer cut-energy rigidity and equality reconstruction.
Normalization and exact fixed-rank applications are not escape witnesses.
utility: none; all ranks and all integer coordinates remain quantified.
-/

set_option autoImplicit false
noncomputable section
namespace D5.S3.VertexAlgebra.Lattice.SimplexMinimalShell
open scoped BigOperators Classical
open Finset

/-- Twice the unordered complete-graph energy; diagonal terms vanish. -/
def energy {ι : Type*} [Fintype ι] (y : ι → ℤ) : ℤ :=
  ∑ i, ∑ j, (y i - y j) ^ 2

private def cut {ι : Type*} [DecidableEq ι] (A : Finset ι) (i j : ι) : ℤ :=
  if i ∈ A then (if j ∈ A then 0 else 1) else (if j ∈ A then 1 else 0)

private theorem cut_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Finset ι) :
    (∑ i, ∑ j, cut A i j) =
      2 * (A.card : ℤ) * ((univ.filter (fun i => i ∉ A)).card : ℤ) := by
  simp [cut, Finset.sum_ite]
  ring

private theorem cut_le {ι : Type*} [Fintype ι] [DecidableEq ι] (y : ι → ℤ) (a : ℤ)
    (i j : ι) :
    cut (univ.filter (fun i => y i = a)) i j ≤ (y i - y j) ^ 2 := by
  classical
  by_cases hi : y i = a <;> by_cases hj : y j = a
  · simp [cut, hi, hj]
  · have h : y i - y j ≠ 0 := by omega
    simpa [cut, hi, hj] using (one_le_sq_iff_one_le_abs _).mpr (Int.one_le_abs h)
  · have h : y i - y j ≠ 0 := by omega
    simpa [cut, hi, hj] using (one_le_sq_iff_one_le_abs _).mpr (Int.one_le_abs h)
  · simpa [cut, hi, hj] using sq_nonneg (y i - y j)

private theorem spike_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a e : ℤ) (p : ι) :
    energy (fun i => a + if i = p then e else 0) =
      2 * ((Fintype.card ι : ℤ) - 1) * e ^ 2 := by
  have ht (i j : ι) :
      ((a + if i = p then e else 0) - (a + if j = p then e else 0)) ^ 2 =
        if i = p then (if j = p then 0 else e ^ 2)
        else (if j = p then e ^ 2 else 0) := by
    split_ifs <;> ring
  simp only [energy, ht]
  simp [Finset.sum_ite, Finset.filter_eq', Finset.filter_ne', Finset.card_erase_of_mem,
    Int.natCast_sub (Fintype.card_pos_iff.mpr ⟨p⟩)]
  ring

/-- Complete minimum and equality classification for integer simplex energy.
The coordinates range over any finite type of cardinality at least two. -/
theorem complete_shell {ι : Type*} [Fintype ι]
    (hn : 2 ≤ Fintype.card ι) (y : ι → ℤ)
    (hvar : ∃ i j, y i ≠ y j) :
    2 * ((Fintype.card ι : ℤ) - 1) ≤ energy y ∧
      (energy y = 2 * ((Fintype.card ι : ℤ) - 1) ↔
        ∃ (a e : ℤ) (p : ι), (e = 1 ∨ e = -1) ∧
          ∀ i, y i = a + if i = p then e else 0) := by
  classical
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨p₀, hp₀⟩ := Finite.exists_min y
  let a := y p₀
  let A := univ.filter (fun i => y i = a)
  let B := univ.filter (fun i => i ∉ A)
  have hA : 1 ≤ (A.card : ℤ) := by
    have : 0 < A.card := card_pos.mpr ⟨p₀, by simp [A, a]⟩
    omega
  have hB : 1 ≤ (B.card : ℤ) := by
    obtain ⟨i, j, hij⟩ := hvar
    have : B.Nonempty := by
      by_cases hi : y i = a
      · exact ⟨j, by simp [B, A]; omega⟩
      · exact ⟨i, by simp [B, A, hi]⟩
    have := card_pos.mpr this
    omega
  have hcard : (A.card : ℤ) + B.card = Fintype.card ι := by
    have h : A.card + B.card = Fintype.card ι := by
      simpa [B] using (card_filter_add_card_filter_not (s := univ) (fun i => i ∈ A))
    exact_mod_cast h
  have hcut : 2 * (A.card : ℤ) * B.card ≤ energy y := by
    rw [← cut_sum]
    exact sum_le_sum fun i _ => sum_le_sum fun j _ => cut_le y a i j
  have hprod : (Fintype.card ι : ℤ) - 1 ≤ (A.card : ℤ) * B.card := by
    nlinarith [mul_nonneg (show 0 ≤ (A.card : ℤ) - 1 by omega)
      (show 0 ≤ (B.card : ℤ) - 1 by omega)]
  refine ⟨by nlinarith, ⟨?_, ?_⟩⟩
  · intro he
    have hab : A.card = 1 ∨ B.card = 1 := by
      have : ((A.card : ℤ) - 1) * ((B.card : ℤ) - 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · left; omega
      · right; omega
    have hecut : (∑ i, ∑ j, cut A i j) = energy y := by
      rw [cut_sum]
      nlinarith
    have hpair (i j : ι) : cut A i j = (y i - y j) ^ 2 := by
      have hrow := (sum_eq_sum_iff_of_le (fun i (_ : i ∈ univ) =>
        sum_le_sum fun j _ => cut_le y a i j)).mp hecut i (mem_univ i)
      exact (sum_eq_sum_iff_of_le (fun j (_ : j ∈ univ) =>
        cut_le y a i j)).mp hrow j (mem_univ j)
    have hlevel (j : ι) (hj : j ∉ A) : y j = a + 1 := by
      have hs := hpair p₀ j
      have hsq : (a - y j) ^ 2 = 1 := by simpa [cut, A, a, hj] using hs.symm
      have hmin := hp₀ j
      have hne : y j ≠ a := by simpa [A] using hj
      nlinarith
    rcases hab with ha | hb
    · obtain ⟨p, hp⟩ := card_eq_one.mp ha
      refine ⟨a + 1, -1, p, Or.inr rfl, ?_⟩
      intro i
      by_cases hi : i = p
      · have hmem : i ∈ A := by simp [hp, hi]
        have hval : y i = a := by simpa [A] using hmem
        simp only [if_pos hi, hval]; ring
      · have hnot : i ∉ A := by simp [hp, hi]
        simp only [if_neg hi, hlevel i hnot, add_zero]
    · obtain ⟨p, hp⟩ := card_eq_one.mp hb
      refine ⟨a, 1, p, Or.inl rfl, ?_⟩
      intro i
      by_cases hi : i = p
      · have hnot : i ∉ A := by
          have : i ∈ B := by simp [hp, hi]
          simpa [B] using this
        simp only [if_pos hi, hlevel i hnot]
      · have hmem : i ∈ A := by
          have : i ∉ B := by simp [hp, hi]
          simpa [B] using this
        have hval : y i = a := by simpa [A] using hmem
        simp only [if_neg hi, hval, add_zero]
  · rintro ⟨a, e, p, he, hy⟩
    have hy' : y = fun i => a + if i = p then e else 0 := funext hy
    rw [hy', spike_energy]
    rcases he with rfl | rfl <;> ring

end D5.S3.VertexAlgebra.Lattice.SimplexMinimalShell
