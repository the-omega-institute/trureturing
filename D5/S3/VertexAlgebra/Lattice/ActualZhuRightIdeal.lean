/- GID: D5/S3/VertexAlgebra/Lattice/ActualZhuRightIdeal
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/ActualZhuRightIdeal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Zhu star preserves the literal full O-space in its right argument. -/
/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the repository root LICENSE.
Authors: Fedor K. Popov
Source-faithful native port of VOA/Modules/ZhuRightIdeal.lean, Lean_VOA
013a799ca834a8a6b3afa8129e3e522025b3f45c; Zhu/Frenkel--Zhu right ideal argument.
Native nonnegative-product finite support supplies one mode-independent cutoff.
proof_shape: star_right_mem_zhuO: content.
admission_basis: escape-witness.
escape_witness: weighted full-state commutator correction is a combination of
higher circles; negative intermediate energy vanishes and finite decomposition
extends the homogeneous result over the complete original carrier and O span.
-/
import D5.S3.VertexAlgebra.Lattice.ActualZhuProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace D5.S3.VertexAlgebra.Lattice.ActualZhuRightIdeal
open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticePositiveEnergy LatticeActualStateFieldCalculus ActualZhuProduct
open scoped BigOperators VertexOperator
open private cbz cbz_nat cbz_apply_neg cbz_lt
  from D5.S3.VertexAlgebra.Lattice.ActualZhuBinomial
open private higherCircle_binomial from D5.S3.VertexAlgebra.Lattice.ActualZhuProduct
open private commutator_evaluated
  from D5.S3.VertexAlgebra.Lattice.NormFourVacuumC2Algebra
noncomputable section
variable {D : LatticeData}

private theorem circle_binomial (D : LatticeData) (M : ℕ) (a b : Carrier D) :
    NormFourZhuFinite.circle D M a b = ∑ i ∈ Finset.range (M+1),
      cbz (M : ℤ) i • mu D a ((i : ℤ)-2) b := by
  simp [NormFourZhuFinite.circle, cbz, StateFieldResidueReconstruction.integerBinomial,
    Ring.choose_natCast]

private theorem negative_grade_zero (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (n : ℤ) (hn : n < 0)
    (a : Carrier D) (ha : a ∈ grade D n) : a = 0 := by
  apply (carrierCoeffEquiv D).injective
  ext x
  simp only [map_zero, Finsupp.zero_apply]
  change (a x.1).coeff x.2 = 0
  apply (mem_grade_iff D n a).mp ha x
  have h := chargeEnergy_nonneg D hD x.1
  dsimp [energy]
  omega

private theorem mode_commutator_uniform (D : LatticeData) (u a : Carrier D) :
    ∃ S : Finset ℕ, ∀ (α β : ℤ) (b : Carrier D),
      mu D u α (mu D a β b) - mu D a β (mu D u α b) =
        ∑ s ∈ S, cbz α s • mu D (mu D u s a) (α+β-s) b := by
  classical
  let S := (nonnegative_products_finite D u a).toFinset
  refine ⟨S, fun α β b => ?_⟩
  rw [commutator_evaluated]
  rw [finsum_eq_sum_of_support_subset (s := S) _ ?_]
  · apply Finset.sum_congr rfl
    intro s _
    simp [commutatorTerm, cbz_nat, mu]
  · intro s hs
    by_contra h
    have hz : mu D u s a = 0 := by
      simpa [S, Function.mem_support] using h
    exact hs (by simp [commutatorTerm, hz])

private theorem rangeSmul_eq_finsumZ (C : ℤ → ℂ) (g : ℤ → Carrier D) (d : ℤ) {N : ℕ}
    (hlo : ∀ p : ℤ, p < 0 → C p = 0) (hhi : ∀ p : ℤ, (N : ℤ) ≤ p → C p = 0) :
    (∑ p ∈ Finset.range N, C (p : ℤ) • g ((p : ℤ) + d)) = ∑ᶠ q : ℤ, C q • g (q + d) := by
  rw [finsum_eq_finsetSum_of_support_subset (fun q : ℤ => C q • g (q + d))
      (s := (Finset.range N).map ⟨(Int.ofNat ·), by intro x y h; simpa using h⟩) ?_]
  · rw [Finset.sum_map]; rfl
  · intro q hq
    rw [Function.mem_support] at hq
    have hC : C q ≠ 0 := fun h => hq (by rw [h, zero_smul])
    have hq0 : 0 ≤ q := by by_contra h; exact hC (hlo q (by omega))
    have hqN : q < (N : ℤ) := by by_contra h; exact hC (hhi q (by omega))
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Finset.mem_range,
      Function.Embedding.coeFn_mk]
    exact ⟨q.toNat, by omega, by simp [Int.toNat_of_nonneg hq0]⟩

/-- Per-`p` reindex of the inner `i`-sum to a `∑ᶠ m` over the mode value (`m = p+i-3-s`). -/
private theorem inner_reindex (D : LatticeData) (M : ℕ) (w b : Carrier D) (s p : ℤ) :
    (∑ i ∈ Finset.range (M + 1), cbz (M : ℤ) (i : ℤ) • mu D w (p + (i : ℤ) - 3 - s) b)
      = ∑ᶠ m : ℤ, cbz (M : ℤ) (m + 3 + s - p) • mu D w m b := by
  rw [show (∑ i ∈ Finset.range (M + 1), cbz (M : ℤ) (i : ℤ) • mu D w (p + (i : ℤ) - 3 - s) b)
        = ∑ i ∈ Finset.range (M + 1),
            cbz (M : ℤ) (i : ℤ) • mu D w ((i : ℤ) + (p - 3 - s)) b from
      Finset.sum_congr rfl fun i _ => by rw [show p + (i : ℤ) - 3 - s = (i : ℤ) + (p - 3 - s) from by ring] ]
  rw [rangeSmul_eq_finsumZ (fun q : ℤ => cbz (M : ℤ) q) (fun q => mu D w q b) (p - 3 - s)
      (fun q hq => cbz_apply_neg (M : ℤ) hq)
      (fun q hq => cbz_lt (by positivity) (by exact_mod_cast hq))]
  rw [← finsum_comp_equiv (Equiv.addRight (p - 3 - s))
      (f := fun m : ℤ => cbz (M : ℤ) (m + 3 + s - p) • mu D w m b)]
  refine finsum_congr fun q => ?_
  simp only [Equiv.coe_addRight]
  rw [show (q + (p - 3 - s)) + 3 + s - p = q from by ring]

/-- If a scalar function `C : ℤ → ℂ` has finite support, so does `m ↦ C m • w₍ₘ₎b`. -/
private theorem smul_support_of_scalar (D : LatticeData) (w b : Carrier D) (C : ℤ → ℂ)
    (hC : (Function.support C).Finite) :
    Function.HasFiniteSupport (fun m : ℤ => C m • mu D w m b) := by
  apply Set.Finite.subset hC
  intro m hm
  rw [Function.mem_support] at hm ⊢
  intro h; apply hm; rw [h, zero_smul]

/-- For `0 ≤ d`, the scalar `m ↦ cbz d (m + e)` has finite support (nonzero only on
`0 ≤ m+e ≤ d`, a finite interval). -/
private theorem cbz_shift_support_fin {d : ℤ} (hd : 0 ≤ d) (e : ℤ) :
    (Function.support (fun m : ℤ => cbz d (m + e))).Finite := by
  apply Set.Finite.subset (Set.finite_Icc (-e) (-e + d))
  intro m hm
  rw [Function.mem_support] at hm
  simp only [Set.mem_Icc]
  constructor
  · by_contra h; exact hm (cbz_apply_neg d (by omega))
  · by_contra h; exact hm (cbz_lt hd (by omega))

/-- The per-`s` scalar coefficient (LHS of `zhu_right_binom` at `j = s`). -/
private def coeffS (K M : ℕ) (s m : ℤ) : ℂ :=
  ∑ p ∈ Finset.range (K + 1),
    cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (m + 3 + s - (p : ℤ)) * cbz ((p : ℤ) - 1) s

/-- `S_s` collapses to the single `∑ᶠ m, coeffS(m) • w₍ₘ₎b`. -/
private theorem S_eq_finsum (D : LatticeData) (K M : ℕ) (w b : Carrier D) (s : ℤ) :
    (∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
        (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ) * cbz ((p : ℤ) - 1) s)
          • mu D w ((p : ℤ) + (i : ℤ) - 3 - s) b)
      = ∑ᶠ m : ℤ, coeffS K M s m • mu D w m b := by
  -- pull the `p`-only scalars out of the inner `i`-sum, then apply `inner_reindex`
  rw [show (∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
            (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ) * cbz ((p : ℤ) - 1) s)
              • mu D w ((p : ℤ) + (i : ℤ) - 3 - s) b)
        = ∑ p ∈ Finset.range (K + 1),
            (cbz (K : ℤ) (p : ℤ) * cbz ((p : ℤ) - 1) s)
              • ∑ᶠ m : ℤ, cbz (M : ℤ) (m + 3 + s - (p : ℤ)) • mu D w m b from
      Finset.sum_congr rfl fun p _ => by
        rw [← inner_reindex D M w b s (p : ℤ), Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]; ring_nf]
  -- push the `p`-scalar into the finsum and swap the finite `p`-sum past `∑ᶠ m`
  rw [show (∑ p ∈ Finset.range (K + 1),
            (cbz (K : ℤ) (p : ℤ) * cbz ((p : ℤ) - 1) s)
              • ∑ᶠ m : ℤ, cbz (M : ℤ) (m + 3 + s - (p : ℤ)) • mu D w m b)
        = ∑ p ∈ Finset.range (K + 1),
            ∑ᶠ m : ℤ,
              (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (m + 3 + s - (p : ℤ)) * cbz ((p : ℤ) - 1) s)
                • mu D w m b from
      Finset.sum_congr rfl fun p _ => by
        have hfin : Function.HasFiniteSupport
            (fun m : ℤ => cbz (M : ℤ) (m + 3 + s - (p : ℤ)) • mu D w m b) :=
          smul_support_of_scalar D w b _
            (Set.Finite.subset (cbz_shift_support_fin (d := (M : ℤ)) (by positivity) (3 + s - (p : ℤ)))
              (fun m hm => by
                rw [Function.mem_support] at hm ⊢
                intro h; apply hm
                rw [show m + 3 + s - (p : ℤ) = m + (3 + s - (p : ℤ)) from by ring]; exact h))
        rw [smul_finsum' (cbz (K : ℤ) (p : ℤ) * cbz ((p : ℤ) - 1) s) hfin]
        refine finsum_congr fun m => ?_
        rw [smul_smul]; ring_nf]
  rw [← finsum_sum_comm (Finset.range (K + 1))
      (fun m p => (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (m + 3 + s - (p : ℤ)) * cbz ((p : ℤ) - 1) s)
        • mu D w m b)
      (fun p _ => ?_)]
  · refine finsum_congr fun m => ?_
    rw [coeffS, Finset.sum_smul]
  · -- finite support of `m ↦ (...)• w₍ₘ₎b` for fixed p
    refine smul_support_of_scalar D w b _ (Set.Finite.subset
      (cbz_shift_support_fin (d := (M : ℤ)) (by positivity) (3 + s - (p : ℤ))) ?_)
    intro m hm
    rw [Function.mem_support] at hm ⊢
    intro h; apply hm
    rw [show (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (m + 3 + s - (p : ℤ)) * cbz ((p : ℤ) - 1) s)
          = (cbz (K : ℤ) (p : ℤ) * cbz ((p : ℤ) - 1) s) * cbz (M : ℤ) (m + (3 + s - (p : ℤ))) from by
        rw [show m + (3 + s - (p : ℤ)) = m + 3 + s - (p : ℤ) from by ring]; ring,
      h, mul_zero]

/-- `higherCircle D Ws w b n` in the mode-value finsum form (`m = r-2-n`). -/
private theorem Pres_eq_finsum (D : LatticeData) (Ws : ℕ) (w b : Carrier D) (n : ℕ) :
    higherCircle D Ws w b n
      = ∑ᶠ m : ℤ, cbz ((Ws : ℤ) + n) (m + 2 + n) • mu D w m b := by
  rw [higherCircle_binomial]
  rw [show (∑ r ∈ Finset.range (Ws + n + 1),
            cbz ((Ws : ℤ) + n) (r : ℤ) • mu D w ((r : ℤ) - 2 - n) b)
        = ∑ r ∈ Finset.range (Ws + n + 1),
            cbz ((Ws : ℤ) + n) (r : ℤ) • mu D w ((r : ℤ) + (-2 - n)) b from
      Finset.sum_congr rfl fun r _ => by rw [show (r : ℤ) - 2 - n = (r : ℤ) + (-2 - n) from by ring] ]
  rw [rangeSmul_eq_finsumZ (fun q : ℤ => cbz ((Ws : ℤ) + n) q) (fun q => mu D w q b) (-2 - n)
      (fun q hq => cbz_apply_neg _ hq)
      (fun q hq => cbz_lt (by positivity) (by omega))]
  rw [← finsum_comp_equiv (Equiv.addRight (-2 - (n : ℤ)))
      (f := fun m : ℤ => cbz ((Ws : ℤ) + n) (m + 2 + n) • mu D w m b)]
  refine finsum_congr fun q => ?_
  simp only [Equiv.coe_addRight]
  rw [show (q + (-2 - (n : ℤ))) + 2 + n = q from by ring]

/-- The per-`s` scalar coefficient (RHS of `zhu_right_binom` at `j = s`). -/
private def coeffP (K M : ℕ) (s : ℕ) (m : ℤ) : ℂ :=
  ∑ t ∈ Finset.range (s + 1),
    (-1 : ℂ) ^ t * cbz (K : ℤ) ((s : ℤ) - (t : ℤ))
      * cbz ((K : ℤ) + (M : ℤ) - (s : ℤ) + (t : ℤ)) (m + 3 + (t : ℤ))

/-- The `Pres`-combination collapses to the single `∑ᶠ m, coeffP(m) • w₍ₘ₎b`.  Here
`w := u₍ₛ₎a ∈ Carrier D_{Ws}` with `Ws = K+M-s-1`. -/
private theorem PresCombo_eq_finsum (D : LatticeData) (K M s Ws : ℕ) (w b : Carrier D)
    (hWs : (Ws : ℤ) = (K : ℤ) + (M : ℤ) - (s : ℤ) - 1) :
    (∑ t ∈ Finset.range (s + 1),
        ((-1 : ℂ) ^ t * cbz (K : ℤ) ((s : ℤ) - (t : ℤ))) • higherCircle D Ws w b (t + 1))
      = ∑ᶠ m : ℤ, coeffP K M s m • mu D w m b := by
  rw [show (∑ t ∈ Finset.range (s + 1),
            ((-1 : ℂ) ^ t * cbz (K : ℤ) ((s : ℤ) - (t : ℤ))) • higherCircle D Ws w b (t + 1))
        = ∑ t ∈ Finset.range (s + 1),
            ∑ᶠ m : ℤ,
              ((-1 : ℂ) ^ t * cbz (K : ℤ) ((s : ℤ) - (t : ℤ))
                * cbz ((K : ℤ) + (M : ℤ) - (s : ℤ) + (t : ℤ)) (m + 3 + (t : ℤ)))
                • mu D w m b from
      Finset.sum_congr rfl fun t _ => by
        rw [Pres_eq_finsum D Ws w b (t + 1), Nat.cast_add, Nat.cast_one]
        have hfin : Function.HasFiniteSupport
            (fun m : ℤ =>
              cbz ((Ws : ℤ) + ((t : ℤ) + 1)) (m + 2 + ((t : ℤ) + 1)) • mu D w m b) :=
          smul_support_of_scalar D w b _
            (Set.Finite.subset
              (cbz_shift_support_fin (d := (Ws : ℤ) + ((t : ℤ) + 1)) (by positivity)
                (2 + ((t : ℤ) + 1)))
              (fun m hm => by
                rw [Function.mem_support] at hm ⊢
                intro h; apply hm
                rw [show m + 2 + ((t : ℤ) + 1) = m + (2 + ((t : ℤ) + 1)) from by ring]; exact h))
        rw [smul_finsum' ((-1 : ℂ) ^ t * cbz (K : ℤ) ((s : ℤ) - (t : ℤ))) hfin]
        refine finsum_congr fun m => ?_
        rw [smul_smul,
          show ((Ws : ℤ) + ((t : ℤ) + 1)) = (K : ℤ) + (M : ℤ) - (s : ℤ) + (t : ℤ) from by
            rw [hWs]; ring,
          show m + 2 + ((t : ℤ) + 1) = m + 3 + (t : ℤ) from by ring,
          mul_assoc] ]
  rw [← finsum_sum_comm (Finset.range (s + 1))
      (fun m t => ((-1 : ℂ) ^ t * cbz (K : ℤ) ((s : ℤ) - (t : ℤ))
          * cbz ((K : ℤ) + (M : ℤ) - (s : ℤ) + (t : ℤ)) (m + 3 + (t : ℤ)))
        • mu D w m b)
      (fun t _ => ?_)]
  · refine finsum_congr fun m => ?_
    rw [coeffP, Finset.sum_smul]
  · -- finite support for fixed `t`
    refine smul_support_of_scalar D w b _ (Set.Finite.subset
      (cbz_shift_support_fin (d := (K : ℤ) + (M : ℤ) - (s : ℤ) + (t : ℤ)) (by omega) (3 + (t : ℤ))) ?_)
    intro m hm
    rw [Function.mem_support] at hm ⊢
    intro h; apply hm
    rw [show ((-1 : ℂ) ^ t * cbz (K : ℤ) ((s : ℤ) - (t : ℤ))
            * cbz ((K : ℤ) + (M : ℤ) - (s : ℤ) + (t : ℤ)) (m + 3 + (t : ℤ)))
          = ((-1 : ℂ) ^ t * cbz (K : ℤ) ((s : ℤ) - (t : ℤ)))
              * cbz ((K : ℤ) + (M : ℤ) - (s : ℤ) + (t : ℤ)) (m + (3 + (t : ℤ))) from by
        rw [show m + (3 + (t : ℤ)) = m + 3 + (t : ℤ) from by ring, mul_assoc],
      h, mul_zero]

/-! ## Step 4: each per-commutator-index term `S_s` lies in `O`. -/

/-- `coeffS = coeffP` (this is exactly `zhu_right_binom`). -/
private theorem coeffS_eq_coeffP (K M s : ℕ) (m : ℤ) : coeffS K M (s : ℤ) m = coeffP K M s m := by
  rw [coeffS, coeffP]
  exact ActualZhuBinomial.zhu_right_binom K M s m

/-- **The per-commutator-index term lies in `O`.**  For `s : ℕ`, `w := u₍ₛ₎a ∈ Carrier D_{K+M-s-1}`,
`S_s := ∑_{p,i} (cbz K p · cbz M i · cbz(p-1,s)) • w₍ₚ₊ᵢ₋₃₋ₛ₎b ∈ ActualZhuFinite.zhuO D`. -/
private theorem S_mem_O (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) {K M : ℕ} {u a : Carrier D}
    (hu : u ∈ grade D (K : ℤ)) (ha : a ∈ grade D (M : ℤ)) (b : Carrier D) (s : ℕ) :
    (∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
        (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ) * cbz ((p : ℤ) - 1) (s : ℤ))
          • mu D (mu D u (s : ℤ) a) ((p : ℤ) + (i : ℤ) - 3 - (s : ℤ)) b) ∈ ActualZhuFinite.zhuO D := by
  set w := mu D u (s : ℤ) a with hw
  have hwmem : w ∈ grade D ((K : ℤ) + (M : ℤ) - (s : ℤ) - 1) := by
    exact positive_actual_mode_grade D hD (K : ℤ) (M : ℤ) (s : ℤ) u a hu ha
  -- collapse the double sum to a single finsum over the mode value
  rw [S_eq_finsum D K M w b (s : ℤ)]
  rcases lt_or_ge ((K : ℤ) + (M : ℤ) - (s : ℤ) - 1) 0 with hneg | hpos
  · -- `w ∈ Carrier D_{<0} = ⊥`, so `w = 0` and the finsum is `0`
    have hwzero := negative_grade_zero D hD _ hneg w hwmem
    rw [show (∑ᶠ m : ℤ, coeffS K M (s : ℤ) m • mu D w m b) = 0 from by
      refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
      simp [hwzero, mu] ]
    exact (ActualZhuFinite.zhuO D).zero_mem
  · -- `Ws := K+M-s-1 : ℕ`; rewrite the finsum as the `Pres`-combination, in `O`
    obtain ⟨Ws, hWs⟩ : ∃ Ws : ℕ, (Ws : ℤ) = (K : ℤ) + (M : ℤ) - (s : ℤ) - 1 :=
      ⟨((K : ℤ) + (M : ℤ) - (s : ℤ) - 1).toNat, by omega⟩
    have hwmem' : w ∈ grade D (Ws : ℤ) := by rwa [hWs]
    rw [show (∑ᶠ m : ℤ, coeffS K M (s : ℤ) m • mu D w m b)
          = ∑ᶠ m : ℤ, coeffP K M s m • mu D w m b from
        finsum_congr fun m => by rw [coeffS_eq_coeffP],
      ← PresCombo_eq_finsum D K M s Ws w b hWs]
    apply Submodule.sum_mem
    intro t _
    exact Submodule.smul_mem _ _ (higherCircle_mem_zhuO D hD hwmem' b (t + 1))

private theorem first_family_mem_O (D : LatticeData) {K M : ℕ} {a : Carrier D}
    (ha : a ∈ grade D (M : ℤ)) (u b : Carrier D) :
    (∑ p ∈ Finset.range (K+1), ∑ i ∈ Finset.range (M+1),
      (cbz (K : ℤ) p * cbz (M : ℤ) i) •
        mu D a ((i : ℤ)-2) (mu D u ((p : ℤ)-1) b)) ∈ ActualZhuFinite.zhuO D := by
  apply Submodule.sum_mem
  intro p _
  have hcircle : NormFourZhuFinite.circle D M a (mu D u ((p : ℤ)-1) b)
      ∈ ActualZhuFinite.zhuO D := Submodule.subset_span ⟨M,a,_,ha,rfl⟩
  have h := (ActualZhuFinite.zhuO D).smul_mem (cbz (K : ℤ) p) hcircle
  simpa only [circle_binomial, Finset.smul_sum, smul_smul] using h

private theorem commutator_family_mem_O (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) {K M : ℕ} {u a : Carrier D}
    (hu : u ∈ grade D (K : ℤ)) (ha : a ∈ grade D (M : ℤ)) (b : Carrier D) :
    (∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
        (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ))
          • (mu D u ((p : ℤ)-1) (mu D a ((i : ℤ)-2) b) - mu D a ((i : ℤ)-2) (mu D u ((p : ℤ)-1) b))) ∈ ActualZhuFinite.zhuO D := by
  obtain ⟨S, hN⟩ := mode_commutator_uniform D u a
  -- expand each bracket and merge the `s`-sum into each `(p,i)` summand
  rw [show (∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
            (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ))
              • (mu D u ((p : ℤ)-1) (mu D a ((i : ℤ)-2) b) - mu D a ((i : ℤ)-2) (mu D u ((p : ℤ)-1) b)))
        = ∑ s ∈ S, ∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
            (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ) * cbz ((p : ℤ) - 1) (s : ℤ))
              • mu D (mu D u (s : ℤ) a) ((p : ℤ) + (i : ℤ) - 3 - (s : ℤ)) b from ?_]
  · apply Submodule.sum_mem
    intro s _
    exact S_mem_O D hD hu ha b s
  · -- the reindexing identity: merge the `s`-sum into each `(p,i)`-summand, then pull `s` out front
    rw [show (∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1),
              (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ))
                • (mu D u ((p : ℤ)-1) (mu D a ((i : ℤ)-2) b) - mu D a ((i : ℤ)-2) (mu D u ((p : ℤ)-1) b)))
          = ∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1), ∑ s ∈ S,
              (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ) * cbz ((p : ℤ) - 1) (s : ℤ))
                • mu D (mu D u (s : ℤ) a) ((p : ℤ) + (i : ℤ) - 3 - (s : ℤ)) b from
        Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun i _ => by
          rw [hN ((p : ℤ) - 1) ((i : ℤ) - 2) b, Finset.smul_sum]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [smul_smul,
            show (p : ℤ) - 1 + ((i : ℤ) - 2) - (s : ℤ) = (p : ℤ) + (i : ℤ) - 3 - (s : ℤ) from by ring] ]
    -- pull the `∑_s` outermost: first swap `i,s` (inner), then `p,s` (outer)
    rw [show (∑ p ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (M + 1), ∑ s ∈ S,
              (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ) * cbz ((p : ℤ) - 1) (s : ℤ))
                • mu D (mu D u (s : ℤ) a) ((p : ℤ) + (i : ℤ) - 3 - (s : ℤ)) b)
          = ∑ p ∈ Finset.range (K + 1), ∑ s ∈ S, ∑ i ∈ Finset.range (M + 1),
              (cbz (K : ℤ) (p : ℤ) * cbz (M : ℤ) (i : ℤ) * cbz ((p : ℤ) - 1) (s : ℤ))
                • mu D (mu D u (s : ℤ) a) ((p : ℤ) + (i : ℤ) - 3 - (s : ℤ)) b from
        Finset.sum_congr rfl fun p _ =>
          Finset.sum_comm (s := Finset.range (M + 1)) (t := S)]
    rw [Finset.sum_comm (s := Finset.range (K + 1)) (t := S)]

/-- The full homogeneous right-argument circle stability, on the literal original O. -/
private theorem homogeneous_circle_mem (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) {K M : ℕ} {u a : Carrier D}
    (hu : u ∈ grade D (K : ℤ)) (ha : a ∈ grade D (M : ℤ)) (b : Carrier D) :
    star D u (NormFourZhuFinite.circle D M a b) ∈ ActualZhuFinite.zhuO D := by
  have hs := star_homogeneous D K u (NormFourZhuFinite.circle D M a b) hu
  have hexpand : star D u (NormFourZhuFinite.circle D M a b) =
      ∑ p ∈ Finset.range (K+1), ∑ i ∈ Finset.range (M+1),
        (cbz (K : ℤ) p * cbz (M : ℤ) i) •
          mu D u ((p : ℤ)-1) (mu D a ((i : ℤ)-2) b) := by
    rw [hs, circle_binomial]
    simp only [mu, map_sum, map_smul, Finset.smul_sum, smul_smul]
    simp [cbz, StateFieldResidueReconstruction.integerBinomial, Ring.choose_natCast]
  rw [hexpand]
  have hfirst := first_family_mem_O (K := K) D ha u b
  have hcomm := commutator_family_mem_O D hD hu ha b
  have h := (ActualZhuFinite.zhuO D).add_mem hfirst hcomm
  convert h using 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← smul_add]
  congr 1
  abel

/-- For every original state u, Zhu star maps the same literal O into O in its right argument. -/
theorem star_right_mem_zhuO (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (u o : Carrier D)
    (ho : o ∈ ActualZhuFinite.zhuO D) : star D u o ∈ ActualZhuFinite.zhuO D := by
  classical
  induction ho using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨M,a,b,ha,rfl⟩ := hz
    rw [← sum_gradeProjections D u, map_sum, LinearMap.sum_apply]
    apply Submodule.sum_mem
    intro k hk
    have hk0 := stateEnergies_nonneg hD u k hk
    have hu := gradeProjection_mem D k u
    have hcast : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk0
    rw [← hcast] at hu
    simpa only [hcast] using homogeneous_circle_mem D hD hu ha b
  | zero => simpa using (ActualZhuFinite.zhuO D).zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using (ActualZhuFinite.zhuO D).add_mem hx hy
  | smul c x _ hx => simpa only [map_smul] using (ActualZhuFinite.zhuO D).smul_mem c hx

#print axioms star_right_mem_zhuO
end
end D5.S3.VertexAlgebra.Lattice.ActualZhuRightIdeal
