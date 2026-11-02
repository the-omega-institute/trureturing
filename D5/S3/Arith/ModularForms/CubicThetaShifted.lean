/- GID: D5/S3/Arith/ModularForms/CubicThetaShifted
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/CubicThetaShifted
   mirror-E: none(waiver:formal-affine-lattice-cosets)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Expand]
   utility: none
   digest: Three affine cosets identify the shifted norm theta with three core fibres. -/

import D5.S3.Arith.ModularForms.CubicThetaLattice

/-! The shifted lattice in the Laurent-index-one column of the cube of Jacobi's series. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.ModularForms.CubicThetaShifted

open CubicThetaLattice

def shiftedExponent (p : ℤ × ℤ) : ℤ := eisensteinNorm p - p.1 - p.2

abbrev ShiftedFiber (n : ℕ) := {p : ℤ × ℤ // shiftedExponent p = (n : ℤ)}

theorem shifted_norm (p : ℤ × ℤ) :
    eisensteinNorm (3 * p.1 - 1, 3 * p.2 - 1) = 9 * shiftedExponent p + 3 := by
  dsimp [eisensteinNorm, shiftedExponent]
  ring

theorem shifted_exponent_nonneg (p : ℤ × ℤ) : 0 ≤ shiftedExponent p := by
  have h := norm_nonneg (3 * p.1 - 1, 3 * p.2 - 1)
  rw [shifted_norm] at h
  omega

instance shiftedFiber_finite (n : ℕ) : Finite (ShiftedFiber n) := by
  let f : ShiftedFiber n → NormFiber (9 * n + 3) := fun p =>
    ⟨(3 * p.1.1 - 1, 3 * p.1.2 - 1), by rw [shifted_norm, p.2]; push_cast; rfl⟩
  apply Finite.of_injective f
  intro p q hpq
  have h := congrArg Subtype.val hpq
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  apply Subtype.ext
  exact Prod.ext (by dsimp [f] at hx; omega) (by dsimp [f] at hy; omega)

private def embed (r : Fin 3) (p : ℤ × ℤ) : ℤ × ℤ :=
  if r = 0 then (p.1 - p.2, p.1 + 2 * p.2)
  else if r = 1 then (1 - 2 * p.1 - p.2, p.1 - p.2)
  else (p.1 + 2 * p.2, 1 - 2 * p.1 - p.2)

private def coset (p : ℤ × ℤ) : Fin 3 :=
  ⟨((p.1 - p.2) % 3).toNat, by
    have hn := Int.emod_nonneg (p.1 - p.2) (by norm_num : (3 : ℤ) ≠ 0)
    have hl := Int.emod_lt_of_pos (p.1 - p.2) (by norm_num : (0 : ℤ) < 3)
    omega⟩

private def unembed (p : ℤ × ℤ) : ℤ × ℤ :=
  if coset p = 0 then ((2 * p.1 + p.2) / 3, (p.2 - p.1) / 3)
  else if coset p = 1 then ((1 - p.1 + p.2) / 3, (1 - p.1 - 2 * p.2) / 3)
  else ((2 - p.1 - 2 * p.2) / 3, (2 * p.1 + p.2 - 1) / 3)

private theorem embed_exponent (r : Fin 3) (p : ℤ × ℤ) :
    shiftedExponent (embed r p) = coreExponent p := by
  fin_cases r <;> dsimp [embed, shiftedExponent, coreExponent, eisensteinNorm] <;> ring

private theorem coset_embed (r : Fin 3) (p : ℤ × ℤ) : coset (embed r p) = r := by
  apply Fin.ext
  fin_cases r <;> dsimp [coset, embed] <;> omega

private theorem embed_unembed (p : ℤ × ℤ) : embed (coset p) (unembed p) = p := by
  have hn := Int.emod_nonneg (p.1 - p.2) (by norm_num : (3 : ℤ) ≠ 0)
  have hl := Int.emod_lt_of_pos (p.1 - p.2) (by norm_num : (0 : ℤ) < 3)
  have hc : ((coset p).val : ℤ) = (p.1 - p.2) % 3 := by dsimp [coset]; omega
  have hh := (coset p).isLt
  by_cases h0 : coset p = 0
  · have hv := congrArg Fin.val h0
    apply Prod.ext <;> simp [unembed, embed, h0] <;> omega
  · by_cases h1 : coset p = 1
    · have hv := congrArg Fin.val h1
      apply Prod.ext <;> simp [unembed, embed, h0, h1] <;> omega
    · have hv0 : (coset p).val ≠ 0 := by intro h; exact h0 (Fin.ext h)
      have hv1 : (coset p).val ≠ 1 := by intro h; exact h1 (Fin.ext h)
      apply Prod.ext <;> simp [unembed, embed, h0, h1] <;> omega

private theorem unembed_embed (r : Fin 3) (p : ℤ × ℤ) : unembed (embed r p) = p := by
  unfold unembed
  rw [coset_embed]
  fin_cases r <;> apply Prod.ext <;> dsimp [embed] <;> omega

/-- The three affine cosets are disjoint and exhaust every shifted norm fibre. -/
noncomputable def shiftedCoreEquiv (n : ℕ) : Fin 3 × CoreFiber n ≃ ShiftedFiber n where
  toFun p := ⟨embed p.1 p.2.1, by rw [embed_exponent, p.2.2]⟩
  invFun p := (coset p.1, ⟨unembed p.1, by
    have he := embed_exponent (coset p.1) (unembed p.1)
    rw [embed_unembed, p.2] at he
    exact he.symm⟩)
  left_inv p := by
    apply Prod.ext
    · exact coset_embed p.1 p.2.1
    · apply Subtype.ext
      exact unembed_embed p.1 p.2.1
  right_inv p := by
    apply Subtype.ext
    exact embed_unembed p.1

noncomputable def shiftedTheta : PowerSeries ℚ :=
  PowerSeries.mk fun n => (Nat.card (ShiftedFiber n) : ℚ)

open scoped PowerSeries.WithPiTopology

theorem hasSum_shifted_theta [TopologicalSpace ℚ] :
    HasSum (fun p : ℤ × ℤ => (PowerSeries.X : PowerSeries ℚ) ^
      (shiftedExponent p).toNat) shiftedTheta :=
  hasSum_counted_fibers shiftedExponent shifted_exponent_nonneg shiftedFiber_finite

/-- This exact all-index identity supplies the multiplicity three in the Jacobi cube. -/
theorem shifted_theta_eq_three_core : shiftedTheta = PowerSeries.C 3 * coreTheta := by
  apply PowerSeries.ext
  intro n
  rw [shiftedTheta, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul, coreTheta,
    PowerSeries.coeff_mk, ← Nat.card_congr (shiftedCoreEquiv n)]
  simp [Nat.card_prod]

end D5.S3.Arith.ModularForms.CubicThetaShifted
