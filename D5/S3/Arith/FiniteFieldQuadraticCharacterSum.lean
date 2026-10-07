/- GID: D5/S3/Arith/FiniteFieldQuadraticCharacterSum
   generality: G
   mirror-B: D5/B/S3/Arith/FiniteFieldQuadraticCharacterSum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Odd-field shifted quadratic character sum is -1 for nonzero shift. -/

import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

namespace D5.S3.Arith.FiniteFieldQuadraticCharacterSum

open scoped BigOperators

abbrev Conic (F : Type*) [Field F] (a : F) :=
  {p : F × F // p.2 ^ 2 = p.1 ^ 2 - a}

abbrev Hyperbola (F : Type*) [Field F] (a : F) :=
  {p : F × F // p.1 * p.2 = a}

def conicSigmaEquiv {F : Type*} [Field F] (a : F) :
    Conic F a ≃ Σ x : F, {y : F // y ^ 2 = x ^ 2 - a} :=
  { toFun := fun p => ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
    invFun := fun p => ⟨(p.1, p.2.1), p.2.2⟩
    left_inv := by intro p; rfl
    right_inv := by intro p; rfl }

def conicHyperbolaEquiv {F : Type*} [Field F] (hF : ringChar F ≠ 2) (a : F) :
    Conic F a ≃ Hyperbola F a :=
  { toFun := fun p =>
      ⟨(p.1.1 - p.1.2, p.1.1 + p.1.2), by
        calc
          (p.1.1 - p.1.2) * (p.1.1 + p.1.2) = p.1.1 ^ 2 - p.1.2 ^ 2 := by ring
          _ = a := by rw [p.2]; ring⟩
    invFun := fun p =>
      ⟨((p.1.1 + p.1.2) / 2, (p.1.2 - p.1.1) / 2), by
        field_simp [Ring.two_ne_zero hF]
        calc
          (p.1.2 - p.1.1) ^ 2 = (p.1.1 + p.1.2) ^ 2 - 4 * (p.1.1 * p.1.2) := by ring
          _ = (p.1.1 + p.1.2) ^ 2 - 4 * a := by rw [p.2]
          _ = (p.1.1 + p.1.2) ^ 2 - 2 ^ 2 * a := by ring⟩
    left_inv := by
      intro p
      apply Subtype.ext
      apply Prod.ext <;> field_simp [Ring.two_ne_zero hF] <;> ring
    right_inv := by
      intro p
      apply Subtype.ext
      apply Prod.ext <;> field_simp [Ring.two_ne_zero hF] <;> ring }

def hyperbolaNonzeroEquiv {F : Type*} [Field F] {a : F} (ha : a ≠ 0) :
    Hyperbola F a ≃ {u : F // u ≠ 0} :=
  { toFun := fun p =>
      ⟨p.1.1, by
        intro hu
        apply ha
        rw [← p.2, hu, zero_mul]⟩
    invFun := fun u =>
      ⟨(u.1, a / u.1), by
        field_simp [u.2]⟩
    left_inv := by
      intro p
      have hu : p.1.1 ≠ 0 := by
        intro hp
        apply ha
        rw [← p.2, hp, zero_mul]
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · field_simp [hu]
        exact p.2.symm
    right_inv := by
      intro u
      apply Subtype.ext
      rfl }

theorem conic_card_eq_card_field_sub_one {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    (Fintype.card (Conic F a) : ℤ) = Fintype.card F - 1 := by
  classical
  have hnonzero : Fintype.card {u : F // u ≠ 0} = Fintype.card F - 1 := by
    exact Fintype.card_subtype_compl (α := F) (fun u : F => u = 0)
  have hcard : Fintype.card (Conic F a) = Fintype.card {u : F // u ≠ 0} := by
    calc
      Fintype.card (Conic F a) = Fintype.card (Hyperbola F a) :=
        Fintype.card_congr (conicHyperbolaEquiv hF a)
      _ = Fintype.card {u : F // u ≠ 0} :=
        Fintype.card_congr (hyperbolaNonzeroEquiv ha)
  rw [hcard, hnonzero, Nat.cast_sub]
  · norm_num
  · exact Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero

theorem quadraticChar_shift_square_sum {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    ∑ x : F, quadraticChar F (x ^ 2 - a) = -1 := by
  classical
  have hf (x : F) :
      (Fintype.card {y : F // y ^ 2 = x ^ 2 - a} : ℤ) =
        quadraticChar F (x ^ 2 - a) + 1 := by
    simpa [Fintype.card_subtype] using quadraticChar_card_sqrts hF (x ^ 2 - a)
  have hSigma :
      (Fintype.card (Conic F a) : ℤ) =
        ∑ x : F, (Fintype.card {y : F // y ^ 2 = x ^ 2 - a} : ℤ) := by
    rw [Fintype.card_congr (conicSigmaEquiv a), Fintype.card_sigma, Nat.cast_sum]
  have hrel :
      (Fintype.card (Conic F a) : ℤ) =
        Fintype.card F + ∑ x : F, quadraticChar F (x ^ 2 - a) := by
    rw [hSigma]
    simp_rw [hf]
    rw [Finset.sum_add_distrib]
    simp
    ring
  have hC := conic_card_eq_card_field_sub_one hF ha
  linarith

end D5.S3.Arith.FiniteFieldQuadraticCharacterSum
