/- GID: D5/S3/VertexAlgebra/Lattice/ActualZhuBinomial
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/ActualZhuBinomial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Weighted binomial collapse for the original Zhu right ideal. -/
/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the repository root LICENSE.
Authors: Fedor K. Popov
Source-faithful native port of VOA/Modules/ZhuRingResidue.lean, Lean_VOA
013a799ca834a8a6b3afa8129e3e522025b3f45c. Classical Zhu/Frenkel--Zhu identity.
The generalized coefficients use native Ring.choose; Vandermonde is Mathlib's.
proof_shape: zhu_right_binom: content.
admission_basis: escape-witness.
escape_witness: the alternating-top-row Vandermonde and trinomial revision
collapse the complete weighted commutator row, including negative upper index.
All private helpers are consumed by zhu_right_binom.
-/
import D5.S3.VertexAlgebra.StateFieldResidueReconstruction
import Mathlib.RingTheory.Binomial
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic
import Batteries.Tactic.OpenPrivate
set_option autoImplicit false
namespace D5.S3.VertexAlgebra.Lattice.ActualZhuBinomial
open scoped BigOperators
noncomputable section

private def cbz (m k : ℤ) : ℂ :=
  if 0 ≤ k then StateFieldResidueReconstruction.integerBinomial m k.toNat else 0

private theorem cbz_apply_neg (m : ℤ) {k : ℤ} (hk : k < 0) : cbz m k = 0 := by
  simp [cbz, not_le.mpr hk]

private theorem cbz_nat (m : ℤ) (k : ℕ) : cbz m k =
    StateFieldResidueReconstruction.integerBinomial m k := by simp [cbz]

private theorem cbz_natCast_eq_choose {a k : ℕ} (_hk : k ≤ a) :
    cbz (a : ℤ) k = (a.choose k : ℂ) := by
  simp [cbz, StateFieldResidueReconstruction.integerBinomial, Ring.choose_natCast]

private theorem cbz_lt {m k : ℤ} (hm : 0 ≤ m) (hk : m < k) : cbz m k = 0 := by
  obtain ⟨M,rfl⟩ : ∃ M : ℕ, m = M := ⟨m.toNat, (Int.toNat_of_nonneg hm).symm⟩
  have hk0 : 0 ≤ k := by omega
  obtain ⟨K,rfl⟩ : ∃ K : ℕ, k = K := ⟨k.toNat, (Int.toNat_of_nonneg hk0).symm⟩
  simp [cbz, StateFieldResidueReconstruction.integerBinomial, Ring.choose_natCast,
    Nat.choose_eq_zero_of_lt (show M < K by omega)]

private theorem cbz_zero_left (k : ℤ) : cbz 0 k = if k = 0 then 1 else 0 := by
  by_cases hk : k < 0
  · simp [cbz_apply_neg 0 hk, ne_of_lt hk]
  · obtain ⟨K,rfl⟩ : ∃ K : ℕ, k = K := ⟨k.toNat, by omega⟩
    simp [cbz, StateFieldResidueReconstruction.integerBinomial, Ring.choose_zero_ite]

private theorem cbz_pascal (m k : ℤ) : cbz m k = cbz (m-1) k + cbz (m-1) (k-1) := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · rw [cbz_apply_neg _ hk, cbz_apply_neg _ hk, cbz_apply_neg _ (by omega), add_zero]
  · subst k; simp [cbz, StateFieldResidueReconstruction.integerBinomial, Ring.choose_zero_right]
  · obtain ⟨K,hK⟩ : ∃ K : ℕ, k = (K+1 : ℕ) := ⟨k.toNat-1, by omega⟩
    rw [hK, show ((K+1 : ℕ) : ℤ)-1 = K by omega]
    simp only [cbz_nat, StateFieldResidueReconstruction.integerBinomial]
    have h := Ring.choose_succ_succ (m-1) K
    rw [sub_add_cancel] at h
    rw [h]; push_cast; ring

private theorem cbz_upper_absorption (K : ℕ) (i : ℤ) :
    (i : ℂ) * cbz (K : ℤ) i = (K : ℂ) * cbz ((K : ℤ)-1) (i-1) := by
  rcases lt_trichotomy i 0 with hi | hi | hi
  · rw [cbz_apply_neg _ hi, cbz_apply_neg _ (by omega), mul_zero, mul_zero]
  · subst i; simp [cbz_apply_neg]
  · obtain ⟨j,rfl⟩ : ∃ j : ℕ, i = (j+1 : ℕ) := ⟨i.toNat-1, by omega⟩
    cases K with
    | zero => simp [cbz_zero_left] <;> omega
    | succ K =>
      rw [show (((K+1 : ℕ) : ℤ)-1) = K by omega,
        show (((j+1 : ℕ) : ℤ)-1) = j by omega]
      simp only [cbz, Nat.cast_nonneg, ↓reduceIte, Int.toNat_natCast,
        StateFieldResidueReconstruction.integerBinomial, Ring.choose_natCast, Int.cast_natCast]
      exact_mod_cast (by simpa only [Nat.mul_comm] using (Nat.add_one_mul_choose_eq K j).symm)

private theorem finsumZ_eq_range_sum (F : ℤ → ℂ) {N : ℕ}
    (hlo : ∀ p : ℤ, p < 0 → F p = 0) (hhi : ∀ p : ℤ, (N : ℤ) ≤ p → F p = 0) :
    ∑ᶠ p : ℤ, F p = ∑ i ∈ Finset.range N, F (i : ℤ) := by
  have hsubset : Function.support F ⊆ ↑((Finset.range N).map ⟨(Int.ofNat ·), by
      intro a b h; simpa using h⟩) := by
    intro p hp
    rw [Function.mem_support] at hp
    have hp0 : 0 ≤ p := by by_contra h; exact hp (hlo p (by omega))
    have hpN : p < (N : ℤ) := by by_contra h; exact hp (hhi p (by omega))
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Finset.mem_range,
      Function.Embedding.coeFn_mk]
    exact ⟨p.toNat, by omega, by simp [Int.toNat_of_nonneg hp0]⟩
  rw [finsum_eq_finsetSum_of_support_subset F hsubset, Finset.sum_map]
  rfl

private theorem vandermonde_range (m n k : ℤ) {N : ℕ} (hk : k < (N : ℤ)) :
    ∑ i ∈ Finset.range N, cbz m (i : ℤ) * cbz n (k - (i : ℤ)) = cbz (m + n) k := by
  by_cases hk0 : k < 0
  · rw [cbz_apply_neg _ hk0]
    apply Finset.sum_eq_zero
    intro i _
    rw [cbz_apply_neg n (by omega : k - (i : ℤ) < 0), mul_zero]
  · obtain ⟨K,rfl⟩ : ∃ K : ℕ, k = K := ⟨k.toNat, by omega⟩
    have hKN : K+1 ≤ N := by omega
    rw [← Finset.sum_subset (Finset.range_mono hKN)
      (fun i hi hni => by
        rw [cbz_apply_neg n (by simp only [Finset.mem_range] at hni; omega : (K : ℤ) - (i : ℤ) < 0), mul_zero])]
    have h := Ring.add_choose_eq (R := ℤ) (r := m) (s := n) K (Commute.all m n)
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
    simp only [cbz_nat, StateFieldResidueReconstruction.integerBinomial]
    rw [h, Int.cast_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [show (K : ℤ)-(i : ℤ) = ((K-i : ℕ) : ℤ) by
      rw [Nat.cast_sub (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]]
    simp [cbz_nat, StateFieldResidueReconstruction.integerBinomial]

private def cbzConvol (m n k : ℤ) : ℂ := ∑ᶠ i : ℤ, cbz m i * cbz n (k-i)
private theorem cbz_vandermonde (m n k : ℤ) : cbzConvol m n k = cbz (m+n) k := by
  unfold cbzConvol
  rw [finsumZ_eq_range_sum (N := k.toNat+1) _
    (fun i hi => by rw [cbz_apply_neg _ hi, zero_mul])
    (fun i hi => by rw [cbz_apply_neg n (by omega : k-i < 0), mul_zero])]
  exact vandermonde_range m n k (by omega)

private theorem cbz_neg_one (t : ℕ) : cbz (-1 : ℤ) (t : ℤ) = (-1 : ℂ) ^ t := by
  induction t with
  | zero => simp [cbz, StateFieldResidueReconstruction.integerBinomial]
  | succ n ih =>
    have hp := cbz_pascal (0 : ℤ) ((n : ℤ) + 1)
    rw [show (0 - 1 : ℤ) = -1 from by ring, show ((n : ℤ) + 1 - 1) = (n : ℤ) from by ring,
      cbz_zero_left, if_neg (by omega)] at hp
    have key : cbz (-1 : ℤ) ((n : ℤ) + 1) = -cbz (-1 : ℤ) (n : ℤ) := by linear_combination -hp
    rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 from by push_cast; ring, key, ih, pow_succ]
    ring

/-! ## (A)  `C(p-1, j) = ∑_{t≤j} (-1)^t C(p, j-t)` (Vandermonde with the alternating top row). -/

private theorem stepA (p : ℤ) (j : ℕ) :
    cbz (p - 1) (j : ℤ)
      = ∑ t ∈ Finset.range (j + 1), (-1 : ℂ) ^ t * cbz p ((j : ℤ) - (t : ℤ)) := by
  have hv := vandermonde_range (-1 : ℤ) p (j : ℤ) (N := j + 1) (by push_cast; omega)
  rw [show (-1 + p : ℤ) = p - 1 from by ring] at hv
  rw [← hv]
  exact Finset.sum_congr rfl (fun t _ => by rw [cbz_neg_one t])

/-! ## (B)  Trinomial revision `C(K,p)·C(p,s) = C(K,s)·C(K-s, p-s)`  (`K : ℕ`). -/

private theorem stepB (K : ℕ) (p s : ℤ) :
    cbz (K : ℤ) p * cbz p s = cbz (K : ℤ) s * cbz ((K : ℤ) - s) (p - s) := by
  rcases lt_or_ge s 0 with hs | hs
  · rw [cbz_apply_neg p hs, cbz_apply_neg (K : ℤ) hs, mul_zero, zero_mul]
  rcases lt_or_ge p s with hps | hps
  · rw [cbz_apply_neg ((K : ℤ) - s) (by omega : p - s < 0), mul_zero]
    rcases lt_or_ge p 0 with hp | hp
    · rw [cbz_apply_neg (K : ℤ) hp, zero_mul]
    · rw [cbz_lt hp (by omega : p < s), mul_zero]
  have hp0 : 0 ≤ p := le_trans hs hps
  rcases lt_or_ge (K : ℤ) p with hKp | hKp
  · rw [cbz_lt (by positivity) hKp, zero_mul]
    rcases lt_or_ge (K : ℤ) s with hKs | hKs
    · rw [cbz_lt (by positivity) hKs, zero_mul]
    · rw [cbz_lt (by omega : 0 ≤ (K : ℤ) - s) (by omega : (K : ℤ) - s < p - s), mul_zero]
  obtain ⟨P, rfl⟩ : ∃ P : ℕ, p = (P : ℤ) := ⟨p.toNat, by omega⟩
  obtain ⟨S, rfl⟩ : ∃ S : ℕ, s = (S : ℤ) := ⟨s.toNat, by omega⟩
  have hSP : S ≤ P := by exact_mod_cast hps
  have hPK : P ≤ K := by exact_mod_cast hKp
  have hSK : S ≤ K := le_trans hSP hPK
  rw [show ((K : ℤ) - (S : ℤ)) = ((K - S : ℕ) : ℤ) from by rw [Nat.cast_sub hSK],
      show ((P : ℤ) - (S : ℤ)) = ((P - S : ℕ) : ℤ) from by rw [Nat.cast_sub hSP],
      cbz_natCast_eq_choose hPK, cbz_natCast_eq_choose hSP, cbz_natCast_eq_choose hSK,
      cbz_natCast_eq_choose (Nat.sub_le_sub_right hPK S),
      ← Nat.cast_mul, ← Nat.cast_mul, Nat.choose_mul hSP]

/-! ## (C)  Shifted Vandermonde `∑_p C(a, p-s)·C(M, T-p) = C(a+M, T-s)`. -/

private theorem stepC (a M T s : ℤ) {N : ℕ} (ha : 0 ≤ a) (hs : 0 ≤ s) (hN : a + s < (N : ℤ)) :
    ∑ p ∈ Finset.range N, cbz a ((p : ℤ) - s) * cbz M (T - (p : ℤ)) = cbz (a + M) (T - s) := by
  rw [← finsumZ_eq_range_sum (N := N) (fun p : ℤ => cbz a (p - s) * cbz M (T - p))
      (fun p hp => by rw [cbz_apply_neg a (by omega : p - s < 0), zero_mul])
      (fun p hp => by rw [cbz_lt ha (by omega : a < p - s), zero_mul])]
  rw [← finsum_comp_equiv (Equiv.addRight s)
      (f := fun p : ℤ => cbz a (p - s) * cbz M (T - p))]
  simp only [Equiv.coe_addRight]
  rw [show (∑ᶠ q : ℤ, cbz a (q + s - s) * cbz M (T - (q + s)))
        = ∑ᶠ q : ℤ, cbz a q * cbz M ((T - s) - q) from
      finsum_congr fun q => by
        rw [show q + s - s = q from by ring, show T - (q + s) = (T - s) - q from by ring]]
  rw [← cbzConvol, cbz_vandermonde]

/-! ## The main identity. -/

/-- **The Zhu right-ideal residue identity** (Zhu Thm 2.1.1, the right-ideal coefficient core):
`∑_p C(K,p) C(M, m+3+j-p) C(p-1,j) = ∑_t (-1)^t C(K,j-t) C(K+M-j+t, m+3+t)`.  This is exactly the
generalized-binomial identity making the per-commutator-index term `S_j` of `u * (a∘b)` collapse
into the proved `Pres` residue family. -/
theorem zhu_right_binom (K M j : ℕ) (m : ℤ) :
    ∑ p ∈ Finset.range (K + 1),
        cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (m + 3 + (j : ℤ) - (p : ℤ)) * cbz ((p : ℤ) - 1) (j : ℤ)
      = ∑ t ∈ Finset.range (j + 1),
        (-1 : ℂ) ^ t * cbz (K : ℤ) ((j : ℤ) - (t : ℤ))
          * cbz ((K : ℤ) + (M : ℤ) - (j : ℤ) + (t : ℤ)) (m + 3 + (t : ℤ)) := by
  rw [show (∑ p ∈ Finset.range (K + 1),
            cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (m + 3 + (j : ℤ) - (p : ℤ)) * cbz ((p : ℤ) - 1) (j : ℤ))
        = ∑ p ∈ Finset.range (K + 1), ∑ t ∈ Finset.range (j + 1),
            (-1 : ℂ) ^ t
              * (cbz (K : ℤ) (p : ℤ) * cbz (p : ℤ) ((j : ℤ) - (t : ℤ)))
              * cbz (M : ℤ) (m + 3 + (j : ℤ) - (p : ℤ)) from
      Finset.sum_congr rfl fun p _ => by
        rw [stepA (p : ℤ) j, Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun t ht => ?_
  have htj : (t : ℤ) ≤ (j : ℤ) := by
    have := Finset.mem_range.mp ht; exact_mod_cast Nat.lt_succ_iff.mp this
  rw [show (∑ p ∈ Finset.range (K + 1),
            (-1 : ℂ) ^ t
              * (cbz (K : ℤ) (p : ℤ) * cbz (p : ℤ) ((j : ℤ) - (t : ℤ)))
              * cbz (M : ℤ) (m + 3 + (j : ℤ) - (p : ℤ)))
        = (-1 : ℂ) ^ t * cbz (K : ℤ) ((j : ℤ) - (t : ℤ))
            * ∑ p ∈ Finset.range (K + 1),
                cbz ((K : ℤ) - ((j : ℤ) - (t : ℤ))) ((p : ℤ) - ((j : ℤ) - (t : ℤ)))
                  * cbz (M : ℤ) ((m + 3 + (j : ℤ)) - (p : ℤ)) from by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [stepB K (p : ℤ) ((j : ℤ) - (t : ℤ))]
      ring]
  rcases le_or_gt ((j : ℤ) - (t : ℤ)) (K : ℤ) with hjtK | hjtK
  · rw [stepC ((K : ℤ) - ((j : ℤ) - (t : ℤ))) (M : ℤ) (m + 3 + (j : ℤ)) ((j : ℤ) - (t : ℤ))
          (N := K + 1) (by omega) (by omega) (by push_cast; omega)]
    rw [show ((K : ℤ) - ((j : ℤ) - (t : ℤ))) + (M : ℤ) = (K : ℤ) + (M : ℤ) - (j : ℤ) + (t : ℤ) from by ring,
      show (m + 3 + (j : ℤ)) - ((j : ℤ) - (t : ℤ)) = m + 3 + (t : ℤ) from by ring]
  · rw [cbz_lt (by positivity) hjtK]; ring

end
end D5.S3.VertexAlgebra.Lattice.ActualZhuBinomial
