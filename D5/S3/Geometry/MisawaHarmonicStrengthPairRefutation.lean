/- GID: D5/S3/Geometry/MisawaHarmonicStrengthPairRefutation
   generality: I
   mirror-B: D5/B/S3/Geometry/MisawaHarmonicStrengthPairRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.Norm, mathlib/module/Mathlib.Tactic.LinearCombination]
   utility: none
   digest: Refutes Misawa--Nishimura Conjecture 3.3 at {2,4} by a forced sixth moment. -/

/- proof_shape: result: bind-only
   escape_witness: none
   admission_basis: open-problem-resolution (issue #8616)
   Direct frozen dependencies: none (pinned Mathlib only). -/

import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.LinearCombination

open scoped BigOperators

set_option autoImplicit false

namespace D5.S3.Geometry.MisawaHarmonicStrengthPairRefutation

/-- `P_k(X) = Σ_{x∈X} x^k`, the k-th complex moment of a finite set of complex numbers
(arXiv:2505.06893v2, pages 2--3). -/
def momentSum (X : Finset ℂ) (k : ℕ) : ℂ := ∑ x ∈ X, x ^ k

/-- `Hst(X) = {k ∈ ℕ | P_k(X) = 0}`, the harmonic strength in the paper's working form. -/
def harmonicStrength (X : Finset ℂ) : Set ℕ := {k | momentSum X k = 0}

/-- `X ⊂ S¹`: every point has modulus one. -/
def OnUnitCircle (X : Finset ℂ) : Prop := ∀ x ∈ X, ‖x‖ = 1

/-- `N(T,2) = min{|X| | X ⊂ S¹, Hst(X) = T}`, as `Nat.sInf` (the empty family gives `0`). -/
noncomputable def minimumSize (T : Set ℕ) : ℕ :=
  sInf {n : ℕ | ∃ X : Finset ℂ, OnUnitCircle X ∧ harmonicStrength X = T ∧ X.card = n}

/-- Conjecture 3.3 of arXiv:2505.06893v2. -/
def claim : Prop := ∀ p q : ℕ, 1 < p → 1 < q → p ≠ q → minimumSize {p, q} = 5

/-- Conjecture 3.3 is false at `{2, 4}`. -/
theorem result : ¬ claim := by
  intro hclaim
  have hminimum : minimumSize ({2, 4} : Set ℕ) = 5 := by
    exact hclaim 2 4 (by norm_num) (by norm_num) (by norm_num)
  let sizes : Set ℕ := {n : ℕ | ∃ X : Finset ℂ,
    OnUnitCircle X ∧ harmonicStrength X = ({2, 4} : Set ℕ) ∧ X.card = n}
  have hsizes : sizes.Nonempty := by
    apply Nat.nonempty_of_sInf_eq_succ (k := 4)
    simpa [minimumSize, sizes] using hminimum
  have hfive : 5 ∈ sizes := by
    have hmem := Nat.sInf_mem hsizes
    simpa [minimumSize, sizes] using hminimum ▸ hmem
  obtain ⟨X, hcircle, hstrength, hcard⟩ := hfive
  have hmoment2 : momentSum X 2 = 0 := by
    have : 2 ∈ harmonicStrength X := by
      rw [hstrength]
      simp
    exact this
  have hmoment4 : momentSum X 4 = 0 := by
    have : 4 ∈ harmonicStrength X := by
      rw [hstrength]
      simp
    exact this
  have hmoment6 : momentSum X 6 = 0 := by
    obtain ⟨a, X4, ha, hX, hcard4⟩ :=
      Finset.card_eq_succ.mp (show X.card = 4 + 1 by omega)
    subst X
    obtain ⟨b, X3, hb, hX4, hcard3⟩ :=
      Finset.card_eq_succ.mp (show X4.card = 3 + 1 by omega)
    subst X4
    obtain ⟨c, X2, hc, hX3, hcard2⟩ :=
      Finset.card_eq_succ.mp (show X3.card = 2 + 1 by omega)
    subst X3
    obtain ⟨d, X1, hd, hX2, hcard1⟩ :=
      Finset.card_eq_succ.mp (show X2.card = 1 + 1 by omega)
    subst X2
    obtain ⟨e, X0, he, hX1, hcard0⟩ :=
      Finset.card_eq_succ.mp (show X1.card = 0 + 1 by omega)
    subst X1
    have hX0 : X0 = ∅ := Finset.card_eq_zero.mp hcard0
    subst X0
    let y1 : ℂ := a ^ 2
    let y2 : ℂ := b ^ 2
    let y3 : ℂ := c ^ 2
    let y4 : ℂ := d ^ 2
    let y5 : ℂ := e ^ 2
    let z1 : ℂ := starRingEnd ℂ y1
    let z2 : ℂ := starRingEnd ℂ y2
    let z3 : ℂ := starRingEnd ℂ y3
    let z4 : ℂ := starRingEnd ℂ y4
    let z5 : ℂ := starRingEnd ℂ y5
    have hp1 : y1 + y2 + y3 + y4 + y5 = 0 := by
      dsimp [y1, y2, y3, y4, y5]
      have h := hmoment2
      simp only [momentSum] at h
      rw [Finset.sum_insert ha, Finset.sum_insert hb, Finset.sum_insert hc,
        Finset.sum_insert hd, Finset.sum_insert he, Finset.sum_empty, add_zero] at h
      linear_combination h
    have hp2 : y1 ^ 2 + y2 ^ 2 + y3 ^ 2 + y4 ^ 2 + y5 ^ 2 = 0 := by
      dsimp [y1, y2, y3, y4, y5]
      have h := hmoment4
      simp only [momentSum] at h
      rw [Finset.sum_insert ha, Finset.sum_insert hb, Finset.sum_insert hc,
        Finset.sum_insert hd, Finset.sum_insert he, Finset.sum_empty, add_zero] at h
      linear_combination h
    have hzp1 : z1 + z2 + z3 + z4 + z5 = 0 := by
      have h := congrArg (starRingEnd ℂ) hp1
      simpa only [map_add, map_zero] using h
    have hzp2 : z1 ^ 2 + z2 ^ 2 + z3 ^ 2 + z4 ^ 2 + z5 ^ 2 = 0 := by
      have h := congrArg (starRingEnd ℂ) hp2
      simpa only [map_add, map_pow, map_zero] using h
    have unit_relation (x : ℂ) (hx : ‖x‖ = 1) :
        x ^ 2 * starRingEnd ℂ (x ^ 2) = 1 := by
      calc
        x ^ 2 * starRingEnd ℂ (x ^ 2) = (x * starRingEnd ℂ x) ^ 2 := by
          simp only [map_pow]
          ring
        _ = 1 := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hx]
          norm_num
    have hu1 : y1 * z1 - 1 = 0 := by
      dsimp [y1, z1]
      rw [unit_relation a (hcircle a (by simp))]
      ring
    have hu2 : y2 * z2 - 1 = 0 := by
      dsimp [y2, z2]
      rw [unit_relation b (hcircle b (by simp))]
      ring
    have hu3 : y3 * z3 - 1 = 0 := by
      dsimp [y3, z3]
      rw [unit_relation c (hcircle c (by simp))]
      ring
    have hu4 : y4 * z4 - 1 = 0 := by
      dsimp [y4, z4]
      rw [unit_relation d (hcircle d (by simp))]
      ring
    have hu5 : y5 * z5 - 1 = 0 := by
      dsimp [y5, z5]
      rw [unit_relation e (hcircle e (by simp))]
      ring
    have hp3 : y1 ^ 3 + y2 ^ 3 + y3 ^ 3 + y4 ^ 3 + y5 ^ 3 = 0 := by
      linear_combination
        ((y1 ^ 2 + y2 ^ 2 + y3 ^ 2 + y4 ^ 2 + y5 ^ 2) -
          (y1 * y2 + y1 * y3 + y1 * y4 + y1 * y5 + y2 * y3 + y2 * y4 +
            y2 * y5 + y3 * y4 + y3 * y5 + y4 * y5)) * hp1 +
        ((3 / 2 : ℂ) * (y1 * y2 * y3 * y4 * y5) * (z1 + z2 + z3 + z4 + z5)) * hzp1 -
        ((3 / 2 : ℂ) * (y1 * y2 * y3 * y4 * y5)) * hzp2 +
        (3 * (-y2 * y3 * y4 * y5 * (z2 + z3 + z4 + z5))) * hu1 +
        (3 * (-y3 * y4 * y5 * (y1 * z3 + y1 * z4 + y1 * z5 + 1))) * hu2 +
        (3 * (-y4 * y5 * (y1 * y2 * z4 + y1 * y2 * z5 + y1 + y2))) * hu3 +
        (3 * (-y5 * (y1 * y2 * y3 * z5 + y1 * y2 + y1 * y3 + y2 * y3))) * hu4 +
        (3 * (-y1 * y2 * y3 - y1 * y2 * y4 - y1 * y3 * y4 - y2 * y3 * y4)) * hu5
    dsimp [y1, y2, y3, y4, y5] at hp3
    simp only [momentSum]
    rw [Finset.sum_insert ha, Finset.sum_insert hb, Finset.sum_insert hc,
      Finset.sum_insert hd, Finset.sum_insert he, Finset.sum_empty, add_zero]
    linear_combination hp3
  have hsix : 6 ∈ harmonicStrength X := hmoment6
  rw [hstrength] at hsix
  norm_num at hsix

example : momentSum ({1, -1} : Finset ℂ) 1 = 0 := by
  norm_num [momentSum]

#print axioms result

end D5.S3.Geometry.MisawaHarmonicStrengthPairRefutation
