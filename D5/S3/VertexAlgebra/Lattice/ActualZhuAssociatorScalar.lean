/- GID: D5/S3/VertexAlgebra/Lattice/ActualZhuAssociatorScalar
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/ActualZhuAssociatorScalar
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed binomial U and V kernels for the original Zhu associator. -/
/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the repository root LICENSE.
Authors: Fedor K. Popov
Source-faithful native port of ZhuUCore.lean and ZhuVCore.lean from
Fedor-Popov/Lean_VOA at 013a799ca834a8a6b3afa8129e3e522025b3f45c.
The kernels are consumed by ActualZhuAssociator, not isolated scalar deliverables.
-/
import D5.S3.VertexAlgebra.Lattice.ActualZhuBinomial
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace D5.S3.VertexAlgebra.Lattice.ActualZhuAssociatorScalar
open scoped BigOperators
open Finset
open private cbz cbz_nat cbz_apply_neg cbz_natCast_eq_choose cbz_lt
  vandermonde_range stepA stepB cbz_vandermonde cbzConvol finsumZ_eq_range_sum
  from D5.S3.VertexAlgebra.Lattice.ActualZhuBinomial
noncomputable section
private abbrev gBinom := StateFieldResidueReconstruction.integerBinomial
private theorem cbz_apply_nonneg (m : ℤ) {k : ℤ} (hk : 0 ≤ k) :
    cbz m k = gBinom m k.toNat := by simp [cbz, hk]
private theorem cbz_convol_support_finite (m n k : ℤ) :
    (Function.support (fun i : ℤ => cbz m i * cbz n (k-i))).Finite := by
  apply Set.Finite.subset (Set.finite_Icc 0 k)
  intro i hi
  rw [Function.mem_support] at hi
  constructor
  · by_contra h; exact hi (by rw [cbz_apply_neg _ (by omega), zero_mul])
  · by_contra h; exact hi (by rw [cbz_apply_neg _ (by omega : k-i<0), mul_zero])
private theorem cbz_upper_neg (m : ℤ) (i : ℕ) :
    cbz (-m - 1) (i : ℤ) = (-1 : ℂ) ^ i * gBinom (m + (i : ℤ)) i := by
  rw [cbz_nat]
  unfold gBinom StateFieldResidueReconstruction.integerBinomial
  have h := Ring.choose_neg (m+1) i
  rw [show -(m+1) = -m-1 by ring,
    show m+1+(i:ℤ)-1 = m+(i:ℤ) by ring] at h
  rw [h, Units.smul_def, smul_eq_mul, Int.cast_mul, Int.cast_negOnePow_natCast]

/-! ## Trinomial revision in the `(a+b, b)` form: `C(K,a)·C(K-a,b) = C(K,a+b)·C(a+b,b)`. -/

/-- Trinomial revision (`K : ℕ`, `a b : ℤ`): `C(K,a)·C(K-a,b) = C(K,a+b)·C(a+b,b)`.
Same shape as `ZhuRes.stepB` but with the kept upper index `a+b` and lower index `b`. -/
private theorem trinomB (K : ℕ) (a b : ℤ) :
    cbz (K : ℤ) a * cbz ((K : ℤ) - a) b = cbz (K : ℤ) (a + b) * cbz (a + b) b := by
  rcases lt_or_ge a 0 with ha | ha
  · -- `a < 0`: `cbz K a = 0`; on the RHS the upper index `a+b` ... handle by sub-cases.
    rw [cbz_apply_neg (K : ℤ) ha, zero_mul]
    rcases lt_or_ge b 0 with hb | hb
    · rw [cbz_apply_neg (a + b) (by omega), mul_zero]
    rcases lt_or_ge (a + b) 0 with hab | hab
    · rw [cbz_apply_neg (K : ℤ) hab, zero_mul]
    · rw [cbz_lt hab (by omega : a + b < b), mul_zero]
  rcases lt_or_ge b 0 with hb | hb
  · -- `b < 0`: `cbz (K-a) b = 0` and `cbz (a+b) b = 0`.
    rw [cbz_apply_neg ((K : ℤ) - a) hb, cbz_apply_neg (a + b) hb, mul_zero, mul_zero]
  -- `0 ≤ a, 0 ≤ b`, so `0 ≤ a + b`.
  rcases lt_or_ge (K : ℤ) (a + b) with hKab | hKab
  · -- `a+b > K`: RHS `cbz K (a+b) = 0`; LHS also 0 (`cbz K a` or `cbz (K-a) b` vanishes).
    rw [cbz_lt (by positivity) hKab, zero_mul]
    rcases lt_or_ge (K : ℤ) a with hKa | hKa
    · rw [cbz_lt (by positivity) hKa, zero_mul]
    · rw [cbz_lt (by omega : 0 ≤ (K : ℤ) - a) (by omega : (K : ℤ) - a < b), mul_zero]
  -- `0 ≤ a, 0 ≤ b, a+b ≤ K`: reduce all to `Nat.choose`.
  obtain ⟨A, rfl⟩ : ∃ A : ℕ, a = (A : ℤ) := ⟨a.toNat, by omega⟩
  obtain ⟨B, rfl⟩ : ∃ B : ℕ, b = (B : ℤ) := ⟨b.toNat, by omega⟩
  have hABK : A + B ≤ K := by exact_mod_cast hKab
  have hAK : A ≤ K := by omega
  rw [show ((K : ℤ) - (A : ℤ)) = ((K - A : ℕ) : ℤ) from by rw [Nat.cast_sub hAK],
      show ((A : ℤ) + (B : ℤ)) = ((A + B : ℕ) : ℤ) from by push_cast; ring,
      cbz_natCast_eq_choose hAK,
      cbz_natCast_eq_choose (by omega : B ≤ K - A),
      cbz_natCast_eq_choose hABK,
      cbz_natCast_eq_choose (by omega : B ≤ A + B),
      ← Nat.cast_mul, ← Nat.cast_mul]
  -- `K.choose A * (K-A).choose B = K.choose (A+B) * (A+B).choose B`.
  congr 1
  have hcm := Nat.choose_mul (n := K) (k := A + B) (s := A) (by omega)
  rw [Nat.add_sub_cancel_left] at hcm
  -- `hcm : K.choose (A+B) * (A+B).choose A = K.choose A * (K-A).choose B`.
  rw [← hcm, ← Nat.choose_symm (by omega : A ≤ A + B), show (A + B) - A = B from by omega]

/-! ## The inner sub-identity (via trinomial revision + Vandermonde, for `t ≤ β+1`). -/

/-- For `t ≤ β+1`:  the inner `i`-sum collapses to a single `cbz`:
`∑_i C(-m-1,i)·C(K, m+1+i)·C(K-m-1-i, β+1-i-t) = C(K, m+β+2-t)`. -/
private theorem inner_collapse (K β : ℕ) (m : ℤ) (t : ℕ) (ht : t ≤ β + 1) :
    ∑ i ∈ Finset.range (β + 2),
        cbz (-m - 1) (i : ℤ) * cbz (K : ℤ) (m + 1 + (i : ℤ))
          * cbz ((K : ℤ) - m - 1 - (i : ℤ)) ((β : ℤ) + 1 - (i : ℤ) - (t : ℤ))
      = cbz (K : ℤ) (m + (β : ℤ) + 2 - (t : ℤ)) := by
  -- Trinomial revision: `C(K, m+1+i)·C(K-(m+1+i), β+1-i-t) = C(K, m+β+2-t)·C(m+β+2-t, β+1-i-t)`.
  -- The kept upper index `a+b = (m+1+i)+(β+1-i-t) = m+β+2-t` is independent of `i`.
  rw [show ∑ i ∈ Finset.range (β + 2),
          cbz (-m - 1) (i : ℤ) * cbz (K : ℤ) (m + 1 + (i : ℤ))
            * cbz ((K : ℤ) - m - 1 - (i : ℤ)) ((β : ℤ) + 1 - (i : ℤ) - (t : ℤ))
        = cbz (K : ℤ) (m + (β : ℤ) + 2 - (t : ℤ))
            * ∑ i ∈ Finset.range (β + 2),
                cbz (-m - 1) (i : ℤ)
                  * cbz (m + (β : ℤ) + 2 - (t : ℤ)) (((β : ℤ) + 1 - (t : ℤ)) - (i : ℤ)) from ?_]
  · -- Vandermonde: `∑_i C(-m-1, i)·C(m+β+2-t, (β+1-t)-i) = C(β+1-t, β+1-t) = 1`.
    have hv := vandermonde_range (-m - 1) (m + (β : ℤ) + 2 - (t : ℤ)) ((β : ℤ) + 1 - (t : ℤ))
      (N := β + 2) (by push_cast; omega)
    rw [show ((-m - 1) + (m + (β : ℤ) + 2 - (t : ℤ))) = (β : ℤ) + 1 - (t : ℤ) from by ring] at hv
    rw [hv, show (β : ℤ) + 1 - (t : ℤ) = (((β + 1 - t : ℕ)) : ℤ) from by
        rw [Nat.cast_sub ht]; push_cast; ring,
      cbz_natCast_eq_choose (le_refl (β + 1 - t)), Nat.choose_self, Nat.cast_one, mul_one]
  · -- the term-wise trinomial rewrite + factoring out the `i`-independent `cbz K (m+β+2-t)`.
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hb := trinomB K (m + 1 + (i : ℤ)) ((β : ℤ) + 1 - (i : ℤ) - (t : ℤ))
    rw [show (K : ℤ) - (m + 1 + (i : ℤ)) = (K : ℤ) - m - 1 - (i : ℤ) from by ring,
      show (m + 1 + (i : ℤ)) + ((β : ℤ) + 1 - (i : ℤ) - (t : ℤ)) = m + (β : ℤ) + 2 - (t : ℤ) from by
        ring] at hb
    rw [show cbz (-m - 1) (i : ℤ) * cbz (K : ℤ) (m + 1 + (i : ℤ))
            * cbz ((K : ℤ) - m - 1 - (i : ℤ)) ((β : ℤ) + 1 - (i : ℤ) - (t : ℤ))
          = cbz (-m - 1) (i : ℤ)
              * (cbz (K : ℤ) (m + 1 + (i : ℤ))
                  * cbz ((K : ℤ) - m - 1 - (i : ℤ)) ((β : ℤ) + 1 - (i : ℤ) - (t : ℤ)))
          from by ring, hb]
    rw [show ((β : ℤ) + 1 - (t : ℤ)) - (i : ℤ) = (β : ℤ) + 1 - (i : ℤ) - (t : ℤ) from by ring]
    ring

/-! ## The main identity. -/

private theorem u_core (K L β : ℕ) (m : ℤ) :
    (∑ i ∈ Finset.range (β + 2),
        ((-1:ℂ)^i * gBinom (m + (i:ℤ)) i)
          * cbz (K:ℤ) (m + 1 + (i:ℤ))
          * cbz ((K:ℤ) + (L:ℤ) - m - 1 - (i:ℤ)) ((β:ℤ) + 1 - (i:ℤ)))
      = ∑ j ∈ Finset.range (β + 2),
          cbz (K:ℤ) (m + 1 + (j:ℤ)) * cbz (L:ℤ) ((β:ℤ) + 1 - (j:ℤ)) := by
  -- Step 1+2: upper negation, then Vandermonde-split the third factor over a fresh index `t`.
  rw [show (∑ i ∈ Finset.range (β + 2),
            ((-1:ℂ)^i * gBinom (m + (i:ℤ)) i)
              * cbz (K:ℤ) (m + 1 + (i:ℤ))
              * cbz ((K:ℤ) + (L:ℤ) - m - 1 - (i:ℤ)) ((β:ℤ) + 1 - (i:ℤ)))
        = ∑ i ∈ Finset.range (β + 2), ∑ t ∈ Finset.range (β + 2),
            cbz (-m - 1) (i:ℤ) * cbz (K:ℤ) (m + 1 + (i:ℤ))
              * (cbz (L:ℤ) (t:ℤ)
                  * cbz ((K:ℤ) - m - 1 - (i:ℤ)) ((β:ℤ) + 1 - (i:ℤ) - (t:ℤ))) from
      Finset.sum_congr rfl (fun i _ => ?_)]
  · -- swap to `t` outer, factor `cbz L t`, collapse the inner `i`-sum via `inner_collapse`.
    rw [Finset.sum_comm]
    rw [show ∑ t ∈ Finset.range (β + 2), ∑ i ∈ Finset.range (β + 2),
              cbz (-m - 1) (i:ℤ) * cbz (K:ℤ) (m + 1 + (i:ℤ))
                * (cbz (L:ℤ) (t:ℤ)
                    * cbz ((K:ℤ) - m - 1 - (i:ℤ)) ((β:ℤ) + 1 - (i:ℤ) - (t:ℤ)))
          = ∑ t ∈ Finset.range (β + 2),
              cbz (L:ℤ) (t:ℤ) * cbz (K:ℤ) (m + (β:ℤ) + 2 - (t:ℤ)) from
        Finset.sum_congr rfl (fun t ht => ?_)]
    · -- RHS reindex `j = β+1-t` (reflect `range (β+2)`).
      rw [← Finset.sum_range_reflect
            (fun j => cbz (K:ℤ) (m + 1 + (j:ℤ)) * cbz (L:ℤ) ((β:ℤ) + 1 - (j:ℤ))) (β + 2)]
      refine Finset.sum_congr rfl (fun t ht => ?_)
      have htβ : t < β + 2 := Finset.mem_range.mp ht
      rw [show ((β + 2 - 1 - t : ℕ) : ℤ) = (β : ℤ) + 1 - (t : ℤ) from by
          rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring]
      rw [show m + 1 + ((β : ℤ) + 1 - (t : ℤ)) = m + (β : ℤ) + 2 - (t : ℤ) from by ring,
        show (β : ℤ) + 1 - ((β : ℤ) + 1 - (t : ℤ)) = (t : ℤ) from by ring]
      ring
    · -- inner `i`-sum collapse (need `t ≤ β+1`).
      have htβ : t ≤ β + 1 := by have := Finset.mem_range.mp ht; omega
      rw [show ∑ i ∈ Finset.range (β + 2),
                cbz (-m - 1) (i:ℤ) * cbz (K:ℤ) (m + 1 + (i:ℤ))
                  * (cbz (L:ℤ) (t:ℤ)
                      * cbz ((K:ℤ) - m - 1 - (i:ℤ)) ((β:ℤ) + 1 - (i:ℤ) - (t:ℤ)))
            = cbz (L:ℤ) (t:ℤ)
                * ∑ i ∈ Finset.range (β + 2),
                    cbz (-m - 1) (i:ℤ) * cbz (K:ℤ) (m + 1 + (i:ℤ))
                      * cbz ((K:ℤ) - m - 1 - (i:ℤ)) ((β:ℤ) + 1 - (i:ℤ) - (t:ℤ)) from by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _ => by ring)]
      rw [inner_collapse K β m t htβ]
  · -- term-wise rewrite for a fixed `i`: upper negation + Vandermonde split.
    rw [show ((-1:ℂ)^i * gBinom (m + (i:ℤ)) i) = cbz (-m - 1) (i:ℤ) from
        (cbz_upper_neg m i).symm]
    have hv := vandermonde_range (L : ℤ) ((K : ℤ) - m - 1 - (i : ℤ)) ((β : ℤ) + 1 - (i : ℤ))
      (N := β + 2) (by push_cast; omega)
    rw [show ((L : ℤ) + ((K : ℤ) - m - 1 - (i : ℤ))) = (K : ℤ) + (L : ℤ) - m - 1 - (i : ℤ) from by
        ring] at hv
    rw [← hv, Finset.mul_sum]

private theorem alt_cbz (n : ℕ) :
    (∑ b ∈ Finset.range (n + 1), (-1 : ℂ) ^ b * cbz (n : ℤ) (b : ℤ))
      = if n = 0 then 1 else 0 := by
  have hcast : (∑ b ∈ Finset.range (n + 1), (-1 : ℂ) ^ b * cbz (n : ℤ) (b : ℤ))
      = ((∑ b ∈ Finset.range (n + 1), ((-1) ^ b * (n.choose b) : ℤ) : ℤ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl (fun b hb => ?_)
    have hbn : b ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    rw [cbz_natCast_eq_choose hbn]
  rw [hcast, Int.alternating_sum_range_choose]
  split <;> simp

/-- The shifted inner alternating sum:
`∑_{a<q+1} (-1)^a · C(q-s, a-s) = (-1)^s · [q = s]` for `s : ℕ`. -/
private theorem inn_alt (q s : ℕ) :
    (∑ a ∈ Finset.range (q + 1), (-1 : ℂ) ^ a * cbz ((q : ℤ) - (s : ℤ)) ((a : ℤ) - (s : ℤ)))
      = (-1 : ℂ) ^ s * (if q = s then 1 else 0) := by
  rcases le_or_gt s q with hsq | hsq
  · -- `s ≤ q`: terms with `a < s` vanish; reindex the rest by `a = s + b`.
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, q = s + m := ⟨q - s, by omega⟩
    rw [show s + m + 1 = s + (m + 1) from by ring, Finset.sum_range_add]
    have hlo : (∑ a ∈ Finset.range s,
          (-1 : ℂ) ^ a * cbz ((↑(s + m) : ℤ) - (s : ℤ)) ((a : ℤ) - (s : ℤ))) = 0 := by
      refine Finset.sum_eq_zero (fun a ha => ?_)
      rw [cbz_apply_neg _ (by have := Finset.mem_range.mp ha; omega), mul_zero]
    rw [hlo, zero_add]
    have hhi : (∑ b ∈ Finset.range (m + 1),
          (-1 : ℂ) ^ (s + b) * cbz ((↑(s + m) : ℤ) - (s : ℤ)) ((↑(s + b) : ℤ) - (s : ℤ)))
        = (-1 : ℂ) ^ s * ∑ b ∈ Finset.range (m + 1), (-1 : ℂ) ^ b * cbz (m : ℤ) (b : ℤ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [show ((↑(s + m) : ℤ) - (s : ℤ)) = (m : ℤ) from by push_cast; ring,
        show ((↑(s + b) : ℤ) - (s : ℤ)) = (b : ℤ) from by push_cast; ring, pow_add]
      ring
    rw [hhi, alt_cbz m]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    · rw [if_neg (by omega : ¬ m = 0), if_neg (by omega : ¬ s + m = s)]
  · -- `s > q`: every term has `a - s < 0`, so `cbz = 0`.
    rw [Finset.sum_eq_zero (fun a ha => by
      rw [cbz_apply_neg _ (by have := Finset.mem_range.mp ha; omega), mul_zero]),
      if_neg (by omega), mul_zero]

/-- The `J`-sum collapse:
`∑_{a<q+1} C(q,a)·(-1)^a·C(a-1,δ) = (-1)^δ · [q ≤ δ]`. -/
private theorem jSum (q δ : ℕ) :
    (∑ a ∈ Finset.range (q + 1),
        cbz (q : ℤ) (a : ℤ) * (-1 : ℂ) ^ a * cbz ((a : ℤ) - 1) (δ : ℤ))
      = (-1 : ℂ) ^ δ * (if q ≤ δ then 1 else 0) := by
  -- Step A: expand `C(a-1,δ)` by the alternating top-row Vandermonde, then swap to `t` outer.
  rw [show (∑ a ∈ Finset.range (q + 1),
            cbz (q : ℤ) (a : ℤ) * (-1 : ℂ) ^ a * cbz ((a : ℤ) - 1) (δ : ℤ))
        = ∑ t ∈ Finset.range (δ + 1), ∑ a ∈ Finset.range (q + 1),
            (-1 : ℂ) ^ t
              * (cbz (q : ℤ) (a : ℤ) * cbz (a : ℤ) ((δ : ℤ) - (t : ℤ)))
              * (-1 : ℂ) ^ a from by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => by
        rw [stepA (a : ℤ) δ, Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring]
  -- Step B: each `t`-term collapses (trinomial revision + `inn_alt`).
  have hterm : ∀ t ∈ Finset.range (δ + 1),
      (∑ a ∈ Finset.range (q + 1),
            (-1 : ℂ) ^ t * (cbz (q : ℤ) (a : ℤ) * cbz (a : ℤ) ((δ : ℤ) - (t : ℤ))) * (-1 : ℂ) ^ a)
        = (-1 : ℂ) ^ t * cbz (q : ℤ) ((δ : ℤ) - (t : ℤ))
            * ((-1 : ℂ) ^ (δ - t) * (if q = δ - t then 1 else 0)) := by
    intro t ht
    have htδ : t ≤ δ := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    rw [show (∑ a ∈ Finset.range (q + 1),
            (-1 : ℂ) ^ t * (cbz (q : ℤ) (a : ℤ) * cbz (a : ℤ) ((δ : ℤ) - (t : ℤ))) * (-1 : ℂ) ^ a)
          = ∑ a ∈ Finset.range (q + 1),
            (-1 : ℂ) ^ t * cbz (q : ℤ) ((δ : ℤ) - (t : ℤ))
              * ((-1 : ℂ) ^ a * cbz ((q : ℤ) - ((δ : ℤ) - (t : ℤ))) ((a : ℤ) - ((δ : ℤ) - (t : ℤ)))) from
        Finset.sum_congr rfl fun a _ => by rw [stepB q (a : ℤ) ((δ : ℤ) - (t : ℤ))]; ring]
    rw [← Finset.mul_sum]
    have hs : ((δ : ℤ) - (t : ℤ)) = ((δ - t : ℕ) : ℤ) := by rw [Nat.cast_sub htδ]
    rw [hs, inn_alt q (δ - t)]
  rw [Finset.sum_congr rfl hterm]
  -- Only the single index `t = δ - q` survives (when `q ≤ δ`).
  by_cases hqδ : q ≤ δ
  · rw [if_pos hqδ, mul_one]
    rw [Finset.sum_eq_single (δ - q)]
    · rw [if_pos (by omega : q = δ - (δ - q))]
      have h1 : ((δ : ℤ) - ((δ - q : ℕ) : ℤ)) = (q : ℤ) := by rw [Nat.cast_sub hqδ]; ring
      rw [h1, show cbz (q : ℤ) (q : ℤ) = 1 from by
        rw [cbz_natCast_eq_choose (le_refl q), Nat.choose_self]; norm_num]
      rw [mul_one, mul_one, ← pow_add]
      congr 1; omega
    · intro t ht htne
      have htδ : t ≤ δ := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
      by_cases hqt : q = δ - t
      · exfalso; apply htne; omega
      · rw [if_neg hqt, mul_zero, mul_zero]
    · intro hmem; exact absurd (Finset.mem_range.mpr (by omega)) hmem
  · rw [if_neg hqδ, mul_zero]
    refine Finset.sum_eq_zero (fun t ht => ?_)
    have htδ : t ≤ δ := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    rw [if_neg (by omega : ¬ q = δ - t), mul_zero, mul_zero]

/-- Truncation: a `jSum`-shaped sum over the larger range `K+1` equals `jSum m δ` when `m ≤ K`
(the extra terms vanish since `C(m, a) = 0` for `a > m`). -/
private theorem jSum_trunc (K m δ : ℕ) (hmK : m ≤ K) :
    (∑ a ∈ Finset.range (K + 1),
        cbz (m : ℤ) (a : ℤ) * (-1 : ℂ) ^ a * cbz ((a : ℤ) - 1) (δ : ℤ))
      = (-1 : ℂ) ^ δ * (if m ≤ δ then 1 else 0) := by
  rw [← jSum m δ]
  refine (Finset.sum_subset
    (Finset.range_subset_range.mpr (by omega : m + 1 ≤ K + 1)) ?_).symm
  intro a _ hanotin
  have : m < a := by rw [Finset.mem_range] at hanotin; omega
  rw [cbz_lt (by positivity) (by exact_mod_cast this), zero_mul, zero_mul]

/-- The inner `a`-collapse `inSum`: for fixed `m : ℤ`,
`∑_{a<K+1} C(K,a)·C(K-a, m-a)·(-1)^δ·C(a-1,δ)·(-1)^a = [0 ≤ m ≤ δ] · C(K,m)`. -/
private theorem inSum (K δ : ℕ) (m : ℤ) :
    (∑ a ∈ Finset.range (K + 1),
        cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) - (a : ℤ)) (m - (a : ℤ))
          * (-1 : ℂ) ^ δ * cbz ((a : ℤ) - 1) (δ : ℤ) * (-1 : ℂ) ^ a)
      = (if 0 ≤ m ∧ m ≤ (δ : ℤ) then cbz (K : ℤ) m else 0) := by
  -- Trinomial revision: `C(K,a)·C(K-a, m-a) = C(K,m)·C(m,a)`; factor out `C(K,m)·(-1)^δ`.
  rw [show (∑ a ∈ Finset.range (K + 1),
            cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) - (a : ℤ)) (m - (a : ℤ))
              * (-1 : ℂ) ^ δ * cbz ((a : ℤ) - 1) (δ : ℤ) * (-1 : ℂ) ^ a)
        = cbz (K : ℤ) m * (-1 : ℂ) ^ δ
            * ∑ a ∈ Finset.range (K + 1),
                cbz m (a : ℤ) * (-1 : ℂ) ^ a * cbz ((a : ℤ) - 1) (δ : ℤ) from by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [show cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) - (a : ℤ)) (m - (a : ℤ))
            = cbz (K : ℤ) m * cbz m (a : ℤ) from (stepB K m (a : ℤ)).symm]
      ring]
  rcases lt_or_ge m 0 with hm0 | hm0
  · rw [cbz_apply_neg (K : ℤ) hm0, if_neg (by omega), zero_mul, zero_mul]
  rcases le_or_gt m (K : ℤ) with hmK | hmK
  · -- `0 ≤ m ≤ K`: the inner sum truncates to `jSum m.toNat δ`.
    obtain ⟨m', rfl⟩ : ∃ m' : ℕ, m = (m' : ℤ) := ⟨m.toNat, by omega⟩
    have hm'K : m' ≤ K := by exact_mod_cast hmK
    rw [jSum_trunc K m' δ hm'K]
    by_cases hm'δ : m' ≤ δ
    · rw [if_pos hm'δ, if_pos ⟨by positivity, by exact_mod_cast hm'δ⟩, mul_one]
      rw [show cbz (K : ℤ) (m' : ℤ) * (-1 : ℂ) ^ δ * (-1 : ℂ) ^ δ
            = cbz (K : ℤ) (m' : ℤ) * ((-1 : ℂ) ^ δ * (-1 : ℂ) ^ δ) from by ring,
        ← pow_add, show δ + δ = 2 * δ from by ring, pow_mul]
      norm_num
    · rw [if_neg hm'δ, if_neg (by omega : ¬ (0 ≤ (m' : ℤ) ∧ (m' : ℤ) ≤ (δ : ℤ))),
        mul_zero, mul_zero]
  · -- `m > K`: `C(K,m) = 0` kills both sides.
    have hz : cbz (K : ℤ) m = 0 := cbz_lt (by positivity) hmK
    rw [hz, zero_mul, zero_mul]
    split <;> simp

/-- Per-`a` dual-index split via the generalized-binomial Vandermonde:
`C(K+L-a, c) = ∑ᶠ i, C(L,i)·C(K-a, c-i)`. -/
private theorem split_a (K L : ℕ) (c : ℤ) (a : ℕ) :
    cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) c
      = ∑ᶠ i : ℤ, cbz (L : ℤ) i * cbz ((K : ℤ) - (a : ℤ)) (c - i) := by
  rw [show (K : ℤ) + (L : ℤ) - (a : ℤ) = (L : ℤ) + ((K : ℤ) - (a : ℤ)) from by ring,
    ← cbz_vandermonde (L : ℤ) ((K : ℤ) - (a : ℤ)) c, cbzConvol]

/-- The V-family scalar identity collapses the signed double residue
into the right-hand convolution for every integer mode. -/
private theorem v_core (K L : ℕ) (γ : ℤ) (δ : ℕ) :
    (∑ a ∈ Finset.range (K + 1),
        cbz (K:ℤ) (a:ℤ)
          * cbz ((K:ℤ) + (L:ℤ) - (a:ℤ)) (γ + 2 + (δ:ℤ) - (a:ℤ))
          * ((-1:ℂ)^δ * gBinom ((a:ℤ) - 1) δ)
          * (-((-1:ℂ)^((a:ℤ) - 1))))
      = ∑ k ∈ Finset.range (δ + 1),
          cbz (L:ℤ) (γ + 2 + (k:ℤ)) * cbz (K:ℤ) ((δ:ℤ) - (k:ℤ)) := by
  -- Step 1: normalize each summand's sign factor and split the dual-index `cbz`.
  rw [show (∑ a ∈ Finset.range (K + 1),
            cbz (K:ℤ) (a:ℤ)
              * cbz ((K:ℤ) + (L:ℤ) - (a:ℤ)) (γ + 2 + (δ:ℤ) - (a:ℤ))
              * ((-1:ℂ)^δ * gBinom ((a:ℤ) - 1) δ)
              * (-((-1:ℂ)^((a:ℤ) - 1))))
        = ∑ a ∈ Finset.range (K + 1),
            ∑ᶠ i : ℤ, cbz (L : ℤ) i
              * (cbz (K:ℤ) (a:ℤ) * cbz ((K:ℤ) - (a:ℤ)) ((γ + 2 + (δ:ℤ) - (a:ℤ)) - i)
                  * (-1:ℂ)^δ * cbz ((a:ℤ) - 1) (δ:ℤ) * (-1:ℂ)^a) from
      Finset.sum_congr rfl fun a _ => by
        -- sign algebra: `gBinom(a-1)δ = cbz(a-1)δ`, `-(-1)^(a-1) = (-1)^a`.
        have hgb : gBinom ((a:ℤ) - 1) δ = cbz ((a:ℤ) - 1) (δ:ℤ) := by
          rw [cbz_apply_nonneg _ (by positivity), Int.toNat_natCast]
        have hsgn : (-((-1:ℂ)^((a:ℤ) - 1))) = (-1:ℂ)^a := by
          rw [zpow_sub₀ (by norm_num : (-1:ℂ) ≠ 0), zpow_natCast]; simp [zpow_one]; ring
        rw [hgb, hsgn, split_a K L (γ + 2 + (δ:ℤ) - (a:ℤ)) a]
        rw [show (cbz (K:ℤ) (a:ℤ)
                  * (∑ᶠ i : ℤ, cbz (L : ℤ) i * cbz ((K:ℤ) - (a:ℤ)) ((γ + 2 + (δ:ℤ) - (a:ℤ)) - i))
                  * ((-1:ℂ)^δ * cbz ((a:ℤ) - 1) (δ:ℤ)) * (-1:ℂ)^a)
              = (cbz (K:ℤ) (a:ℤ) * (-1:ℂ)^δ * cbz ((a:ℤ) - 1) (δ:ℤ) * (-1:ℂ)^a)
                  * (∑ᶠ i : ℤ, cbz (L : ℤ) i * cbz ((K:ℤ) - (a:ℤ)) ((γ + 2 + (δ:ℤ) - (a:ℤ)) - i)) from by
          ring]
        rw [mul_finsum]
        refine finsum_congr fun i => ?_
        ring]
  -- Step 2: swap the finite `a`-sum with the `∑ᶠ i`, then collapse the inner `a`-sum via `inSum`.
  rw [sum_finsum_comm _ _ (fun a _ => ?_)]
  · -- the inner `a`-sum is `inSum K δ (γ+2+δ-i)`.
    rw [show (∑ᶠ i : ℤ, ∑ a ∈ Finset.range (K + 1),
              cbz (L : ℤ) i
                * (cbz (K:ℤ) (a:ℤ) * cbz ((K:ℤ) - (a:ℤ)) ((γ + 2 + (δ:ℤ) - (a:ℤ)) - i)
                    * (-1:ℂ)^δ * cbz ((a:ℤ) - 1) (δ:ℤ) * (-1:ℂ)^a))
          = ∑ᶠ i : ℤ, cbz (L : ℤ) i
              * (if 0 ≤ (γ + 2 + (δ:ℤ) - i) ∧ (γ + 2 + (δ:ℤ) - i) ≤ (δ : ℤ)
                  then cbz (K : ℤ) (γ + 2 + (δ:ℤ) - i) else 0) from
        finsum_congr fun i => by
          rw [← Finset.mul_sum, ← inSum K δ (γ + 2 + (δ:ℤ) - i)]
          refine congrArg _ (Finset.sum_congr rfl fun a _ => ?_)
          rw [show (γ + 2 + (δ:ℤ) - i) - (a:ℤ) = (γ + 2 + (δ:ℤ) - (a:ℤ)) - i from by ring]]
    -- Reindex `i = γ+2+k` (shift), then collapse the `[0,δ]`-supported finsum to the range sum.
    rw [← finsum_comp_equiv (Equiv.addLeft (γ + 2))
        (f := fun i : ℤ => cbz (L : ℤ) i
          * (if 0 ≤ (γ + 2 + (δ:ℤ) - i) ∧ (γ + 2 + (δ:ℤ) - i) ≤ (δ : ℤ)
              then cbz (K : ℤ) (γ + 2 + (δ:ℤ) - i) else 0))]
    simp only [Equiv.coe_addLeft]
    rw [show (∑ᶠ k : ℤ, cbz (L : ℤ) (γ + 2 + k)
              * (if 0 ≤ (γ + 2 + (δ:ℤ) - (γ + 2 + k)) ∧ (γ + 2 + (δ:ℤ) - (γ + 2 + k)) ≤ (δ : ℤ)
                  then cbz (K : ℤ) (γ + 2 + (δ:ℤ) - (γ + 2 + k)) else 0))
          = ∑ᶠ k : ℤ, cbz (L : ℤ) (γ + 2 + k)
              * (if 0 ≤ k ∧ k ≤ (δ : ℤ) then cbz (K : ℤ) ((δ:ℤ) - k) else 0) from
        finsum_congr fun k => by
          rw [show (γ + 2 + (δ:ℤ) - (γ + 2 + k)) = (δ:ℤ) - k from by ring]
          by_cases hk : 0 ≤ k ∧ k ≤ (δ : ℤ)
          · rw [if_pos ⟨by omega, by omega⟩, if_pos hk]
          · rw [if_neg (by omega), if_neg hk]]
    rw [finsumZ_eq_range_sum (N := δ + 1)
        (fun k : ℤ => cbz (L : ℤ) (γ + 2 + k)
          * (if 0 ≤ k ∧ k ≤ (δ : ℤ) then cbz (K : ℤ) ((δ:ℤ) - k) else 0))
        (fun p hp => by rw [if_neg (by omega), mul_zero])
        (fun p hp => by rw [if_neg (by omega), mul_zero])]
    refine Finset.sum_congr rfl fun k hk => ?_
    have : k < δ + 1 := Finset.mem_range.mp hk
    rw [if_pos ⟨by positivity, by exact_mod_cast Nat.lt_succ_iff.mp this⟩]
  · -- finite support of each per-`a` finsum summand.
    apply Set.Finite.subset (cbz_convol_support_finite (L : ℤ) ((K:ℤ) - (a:ℤ))
      (γ + 2 + (δ:ℤ) - (a:ℤ)))
    intro i hi
    rw [Function.mem_support] at hi ⊢
    intro hzero
    apply hi
    have : cbz (L : ℤ) i
            * (cbz (K:ℤ) (a:ℤ) * cbz ((K:ℤ) - (a:ℤ)) ((γ + 2 + (δ:ℤ) - (a:ℤ)) - i)
                * (-1:ℂ)^δ * cbz ((a:ℤ) - 1) (δ:ℤ) * (-1:ℂ)^a)
          = (cbz (L : ℤ) i * cbz ((K:ℤ) - (a:ℤ)) ((γ + 2 + (δ:ℤ) - (a:ℤ)) - i))
              * (cbz (K:ℤ) (a:ℤ) * (-1:ℂ)^δ * cbz ((a:ℤ) - 1) (δ:ℤ) * (-1:ℂ)^a) := by ring
    rw [this, hzero, zero_mul]


#print axioms u_core
#print axioms v_core
end
end D5.S3.VertexAlgebra.Lattice.ActualZhuAssociatorScalar
