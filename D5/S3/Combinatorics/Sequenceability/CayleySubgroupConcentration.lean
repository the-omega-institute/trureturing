/- GID: D5/S3/Combinatorics/Sequenceability/CayleySubgroupConcentration
   generality: G
   mirror-B: none
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Rounded displacement packing and proper stabilizers for Cayley concentration. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Pointwise.Stabilizer
import Mathlib.GroupTheory.Index
import Mathlib.Tactic

/-! Displacement localization underlying the finite-group concentration argument
of Bedert, Bucić, Kravitz, Montgomery and Müyesser, arXiv:2508.18254v1,
Section 4. The integer shell count is rounded explicitly. The stopping condition
for the subsequent descent is a numerical quadratic-form bound, including for
nonsymmetric sets in nonabelian groups. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Sequenceability.CayleySubgroupConcentration

open scoped BigOperators Pointwise

noncomputable section
attribute [local instance] Classical.propDecidable

private def lengthBall {K : Type*} [Fintype K] (D : K → ℝ) (r : ℝ) : Finset K :=
  Finset.univ.filter (fun g => D g ≤ r)

private theorem mem_lengthBall {K : Type*} [Fintype K] (D : K → ℝ) (r : ℝ) (g : K) :
    g ∈ lengthBall D r ↔ D g ≤ r := by
  simp [lengthBall]

private theorem lengthBall_mono {K : Type*} [Fintype K] (D : K → ℝ)
    {r s : ℝ} (hrs : r ≤ s) : lengthBall D r ⊆ lengthBall D s := by
  intro g hg
  exact (mem_lengthBall D s g).mpr (le_trans ((mem_lengthBall D r g).mp hg) hrs)

private theorem rounded_plateau {K : Type*} [Group K] [Fintype K]
    (D : K → ℝ) (hmul : ∀ g h, D (g * h) ≤ D g + D h)
    (hinv : ∀ g, D g⁻¹ = D g)
    (τ : ℝ) (hτ : 0 < τ) (hτone : τ ≤ 1)
    (hlarge : (9 / 10 : ℝ) * τ * Fintype.card K ≤ (lengthBall D (τ / 5)).card) :
    ∃ k : ℕ, 1 ≤ k ∧ (k : ℝ) ≤ 4 / τ ∧
      lengthBall D ((k : ℝ) * (τ / 5)) =
        lengthBall D (((k - 1 : ℕ) : ℝ) * (τ / 5)) := by
  let M : ℕ := ⌊4 / τ⌋₊
  let q : ℕ := (M + 2) / 3
  have ha : 0 < τ / 5 := by positivity
  have hfour : (4 : ℝ) ≤ 4 / τ := (le_div_iff₀ hτ).mpr (by linarith)
  have hM : 4 ≤ M := (Nat.le_floor_iff (by positivity)).mpr hfour
  have hMle : (M : ℝ) ≤ 4 / τ := Nat.floor_le (by positivity)
  have hMlt : 4 / τ < (M : ℝ) + 1 := Nat.lt_floor_add_one (4 / τ)
  have hq : 2 ≤ q := by dsimp [q]; omega
  have hMq : M ≤ 3 * q := by dsimp [q]; omega
  by_contra hplateau
  have hshell (i : Fin q) : ∃ g : K,
      (3 * (i.val : ℝ)) * (τ / 5) < D g ∧
        D g ≤ (3 * (i.val : ℝ) + 1) * (τ / 5) := by
    let k : ℕ := 3 * i.val + 1
    have hk : 1 ≤ k := by omega
    have hkM : k ≤ M := by dsimp [k, q] at *; omega
    have hkbound : (k : ℝ) ≤ 4 / τ := le_trans (by exact_mod_cast hkM) hMle
    have hne : lengthBall D ((k : ℝ) * (τ / 5)) ≠
        lengthBall D (((k - 1 : ℕ) : ℝ) * (τ / 5)) := by
      intro he
      exact hplateau ⟨k, hk, hkbound, he⟩
    have hsub : lengthBall D (((k - 1 : ℕ) : ℝ) * (τ / 5)) ⊆
        lengthBall D ((k : ℝ) * (τ / 5)) :=
      lengthBall_mono D (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le k 1) ha.le)
    obtain ⟨g, hg, hng⟩ := Finset.not_subset.mp
      (show ¬ lengthBall D ((k : ℝ) * (τ / 5)) ⊆
        lengthBall D (((k - 1 : ℕ) : ℝ) * (τ / 5)) from
          fun h => hne (Finset.Subset.antisymm h hsub))
    have hu := (mem_lengthBall D _ g).mp hg
    have hl : (((k - 1 : ℕ) : ℝ) * (τ / 5)) < D g :=
      lt_of_not_ge (fun h => hng ((mem_lengthBall D _ g).mpr h))
    refine ⟨g, ?_, ?_⟩
    · simpa [k, Nat.cast_add, Nat.cast_mul] using hl
    · simpa [k, Nat.cast_add, Nat.cast_mul] using hu
  choose c hc using hshell
  let B := lengthBall D (τ / 5)
  let pack : Fin q × {b // b ∈ B} → K := fun z => c z.1 * z.2.val
  have hreverse (g b : K) : D g ≤ D (g * b) + D b := by
    simpa [mul_assoc, hinv] using hmul (g * b) b⁻¹
  have hseparate (i j : Fin q) (hji : j < i) (b e : {b // b ∈ B}) :
      c i * b.val ≠ c j * e.val := by
    intro heq
    have hb : D b.val ≤ τ / 5 := (mem_lengthBall D _ _).mp b.property
    have he : D e.val ≤ τ / 5 := (mem_lengthBall D _ _).mp e.property
    have hlow := (hc i).1
    have hupp := le_trans (hmul (c j) e.val) (add_le_add (hc j).2 he)
    have hrev := hreverse (c i) b.val
    rw [heq] at hrev
    have hij : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast hji
    nlinarith
  have hpack : Function.Injective pack := by
    rintro ⟨i, b⟩ ⟨j, e⟩ he
    have hij : i = j := by
      rcases lt_trichotomy i j with h | h | h
      · exact False.elim (hseparate j i h e b he.symm)
      · exact h
      · exact False.elim (hseparate i j h b e he)
    subst j
    have hbe : b = e := Subtype.ext (mul_left_cancel he)
    exact Prod.ext rfl hbe
  have hcard : q * B.card ≤ Fintype.card K := by
    simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe] using
      Fintype.card_le_of_injective pack hpack
  have hcardR : (q : ℝ) * (B.card : ℝ) ≤ Fintype.card K := by exact_mod_cast hcard
  have hMqR : (M : ℝ) ≤ 3 * (q : ℝ) := by exact_mod_cast hMq
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hround : 4 < (3 * (q : ℝ) + 1) * τ := by
    have : 4 / τ < 3 * (q : ℝ) + 1 := by linarith
    exact (div_lt_iff₀ hτ).mp this
  have hqtau : (8 / 7 : ℝ) < (q : ℝ) * τ := by nlinarith
  have hn : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hbig := mul_le_mul_of_nonneg_left hlarge (show (0 : ℝ) ≤ q by positivity)
  dsimp [B] at hcardR
  nlinarith

end
end D5.S3.Combinatorics.Sequenceability.CayleySubgroupConcentration
