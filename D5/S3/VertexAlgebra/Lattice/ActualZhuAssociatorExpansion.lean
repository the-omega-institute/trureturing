/- GID: D5/S3/VertexAlgebra/Lattice/ActualZhuAssociatorExpansion
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/ActualZhuAssociatorExpansion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All-state iterate expansion and finite V tower for the actual Zhu associator. -/
/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the repository root LICENSE.
Authors: Fedor K. Popov
Source-faithful native port of the finite iterate expansion and V-family
regrouping in VOA/Modules/ZhuAssociator.lean from Fedor-Popov/Lean_VOA at
013a799ca834a8a6b3afa8129e3e522025b3f45c.
These private helpers are consumed by ActualZhuAssociator on the original
Carrier and literal ActualZhuFinite.zhuO; no independent novelty is claimed.
-/
import D5.S3.VertexAlgebra.Lattice.ActualZhuRightIdeal
import D5.S3.VertexAlgebra.Lattice.ActualZhuMuIdentity
import D5.S3.VertexAlgebra.Lattice.ActualZhuAssociatorScalar
/-! Finite iterate expansion and the V higher-circle tower on the original carrier. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace D5.S3.VertexAlgebra.Lattice.ActualZhuAssociatorExpansion
open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticePositiveEnergy LatticeActualStateFieldCalculus ActualZhuProduct
open scoped BigOperators VertexOperator
open Classical
open private cbz cbz_nat cbz_apply_neg cbz_natCast_eq_choose cbz_lt
  from D5.S3.VertexAlgebra.Lattice.ActualZhuBinomial
open private gBinom cbz_apply_nonneg u_core v_core
  from D5.S3.VertexAlgebra.Lattice.ActualZhuAssociatorScalar
open private rangeSmul_eq_finsumZ smul_support_of_scalar cbz_shift_support_fin
  Pres_eq_finsum
  from D5.S3.VertexAlgebra.Lattice.ActualZhuRightIdeal
noncomputable section
variable {D : LatticeData}
private theorem cbz_zero (m : ℤ) : cbz m 0 = 1 := by
  simp [cbz, StateFieldResidueReconstruction.integerBinomial]
@[simp] private theorem mu_zero_right (D : LatticeData) (u : Carrier D) (m : ℤ) :
    mu D u m 0 = 0 := by simp [mu]
private theorem regularity (D : LatticeData) (u w : Carrier D) :
    ∃ N : ℤ, ∀ m : ℤ, N ≤ m → mu D u m w = 0 := by
  refine ⟨-((HahnModule.of ℂ).symm (Y D u w)).order, ?_⟩
  intro m hm
  apply VertexOperator.ncoeff_eq_zero_of_lt_order
  omega
private theorem star_homogeneous_cbz (D : LatticeData) {p : ℤ} (hp : 0 ≤ p)
    {u : Carrier D} (hu : u ∈ grade D p) (w : Carrier D) :
    star D u w = ∑ j ∈ Finset.range (p.toNat+1),
      cbz p (j : ℤ) • mu D u ((j : ℤ)-1) w := by
  have hcast : (p.toNat : ℤ) = p := Int.toNat_of_nonneg hp
  rw [← hcast] at hu ⊢
  rw [star_homogeneous D p.toNat u w hu]
  simp only [Int.toNat_natCast]
  apply Finset.sum_congr rfl
  intro j hj
  rw [cbz_natCast_eq_choose (by have := Finset.mem_range.mp hj; omega)]
private theorem iterate_difference_finite (D : LatticeData) (u v w : Carrier D) (r n : ℤ) :
    Function.HasFiniteSupport (fun i : ℕ =>
      ((-1:ℂ)^i * gBinom r i) • (mu D u (r-i) (mu D v (n+i) w) -
        ((-1:ℂ)^r) • mu D v (r+n-i) (mu D u i w))) := by
  obtain ⟨hL,hR,_⟩ := stateField_iterate D u v w r n
  have hh := hL.sub (Function.HasFiniteSupport.smul_right (fun _ : ℕ => (-1:ℂ)^r) hR)
  change Function.HasFiniteSupport (fun i : ℕ =>
    ((-1:ℂ)^i * gBinom r i) • mu D u (r-i) (mu D v (n+i) w) -
      ((-1:ℂ)^r) • (((-1:ℂ)^i * gBinom r i) • mu D v (r+n-i) (mu D u i w))) at hh
  simpa only [smul_sub, smul_smul, mul_comm] using hh

private theorem mode_iterate (D : LatticeData) (u v : Carrier D) (r n : ℤ) (w : Carrier D) :
    mu D (mu D u r v) n w = ∑ᶠ i : ℕ,
      ((-1 : ℂ)^i * gBinom r i) •
        (mu D u (r-i) (mu D v (n+i) w) -
          ((-1 : ℂ)^r) • mu D v (r+n-i) (mu D u i w)) := by
  obtain ⟨hL,hR,he⟩ := stateField_iterate D u v w r n
  change mu D (mu D u r v) n w = _ at he
  have hRS := Function.HasFiniteSupport.smul_right (fun _ : ℕ => (-1:ℂ)^r) hR
  simp only [Pi.smul_def'] at hRS
  rw [he, smul_finsum' _ hR, ← finsum_sub_distrib hL hRS]
  apply finsum_congr
  intro i
  simp only [gBinom, StateFieldResidueReconstruction.integerBinomial, mu, smul_sub, smul_smul]
  congr 1
  ring
private theorem finsum_nat_to_int (F : ℕ → Carrier D) (G : ℤ → Carrier D)
    (hneg : ∀ p : ℤ, p < 0 → G p = 0) (hnat : ∀ n : ℕ, G n = F n) :
    (∑ᶠ n : ℕ, F n) = ∑ᶠ p : ℤ, G p := by
  calc
    (∑ᶠ n : ℕ, F n) = ∑ᶠ n : ℕ, G (n : ℤ) := finsum_congr fun n => (hnat n).symm
    _ = ∑ᶠ p ∈ Set.range (Int.ofNat : ℕ → ℤ), G p :=
      (finsum_mem_range Int.ofNat_injective).symm
    _ = ∑ᶠ p ∈ Set.univ, G p := by
      apply finsum_mem_inter_support_eq'
      intro p hp
      have hp0 : 0 ≤ p := by
        by_contra h
        exact hp (hneg p (by omega))
      simp only [Set.mem_univ, iff_true]
      exact ⟨p.toNat, Int.toNat_of_nonneg hp0⟩
    _ = ∑ᶠ p : ℤ, G p := finsum_mem_univ G
private def Ufam (D : LatticeData) (K L : ℕ) (u v w : (Carrier D)) (Bv : ℕ) : (Carrier D) :=
  ∑ b ∈ Finset.range Bv, ∑ n ∈ Finset.range (b + 1),
    ActualZhuMuIdentity.muCoeff L b n • higherCircle D K u (mu D v (b : ℤ) w) n

/-- The **v-outer (swap) family**: `∑_{a<Bu} ∑_{n=0}^{a} μ(K,a,n) • Pres(v, L, u₍a₎w, n)`. -/
private def Vfam (D : LatticeData) (K L : ℕ) (u v w : (Carrier D)) (Bu : ℕ) : (Carrier D) :=
  ∑ a ∈ Finset.range Bu, ∑ n ∈ Finset.range (a + 1),
    ActualZhuMuIdentity.muCoeff K a n • higherCircle D L v (mu D u (a : ℤ) w) n

/-- The U tower belongs to the original O by higher-circle membership. -/
private theorem Ufam_mem_O (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) {K L : ℕ} {u : (Carrier D)}
    (hu : u ∈ grade D (K : ℤ)) (v w : (Carrier D)) (Bv : ℕ) : Ufam D K L u v w Bv ∈ ActualZhuFinite.zhuO D := by
  refine Submodule.sum_mem _ (fun b _ => Submodule.sum_mem _ (fun n _ => ?_))
  exact Submodule.smul_mem _ _ (higherCircle_mem_zhuO D hD hu (mu D v (b : ℤ) w) n)

/-- The V tower belongs to the original O by higher-circle membership. -/
private theorem Vfam_mem_O (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) {K L : ℕ} {v : (Carrier D)}
    (hv : v ∈ grade D (L : ℤ)) (u w : (Carrier D)) (Bu : ℕ) : Vfam D K L u v w Bu ∈ ActualZhuFinite.zhuO D := by
  refine Submodule.sum_mem _ (fun a _ => Submodule.sum_mem _ (fun n _ => ?_))
  exact Submodule.smul_mem _ _ (higherCircle_mem_zhuO D hD hv (mu D u (a : ℤ) w) n)

/-! ## Finite-sum infrastructure
(general `Finset` sum lemmas used below). -/

/-- Scalar finite support bounds the corresponding state-valued support. -/
private theorem smul_support_of_scalar_gen {ι : Type*} (C : ι → ℂ) (g : ι → (Carrier D))
    (hC : (Function.support C).Finite) :
    Function.HasFiniteSupport (fun x : ι => C x • g x) := by
  apply Set.Finite.subset hC
  intro x hx
  rw [Function.mem_support] at hx ⊢
  intro h; apply hx; rw [h, zero_smul]

/-- Expand the right associated product on two homogeneous inputs. -/
private theorem uvw_expand (D : LatticeData) {K L : ℕ} {u v : (Carrier D)}
    (hu : u ∈ grade D (K : ℤ)) (hv : v ∈ grade D (L : ℤ)) (w : (Carrier D)) :
    star D u (star D v w)
      = ∑ p ∈ Finset.range (K + 1), ∑ c ∈ Finset.range (L + 1),
          (cbz (K : ℤ) (p : ℤ) * cbz (L : ℤ) (c : ℤ))
            • mu D u ((p : ℤ) - 1) (mu D v ((c : ℤ) - 1) w) := by
  rw [star_homogeneous_cbz D (by positivity) hu, show (K : ℤ).toNat + 1 = K + 1 from by simp]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [star_homogeneous_cbz D (by positivity) hv, show (L : ℤ).toNat + 1 = L + 1 from by simp]
  rw [show mu D u ((p : ℤ) - 1) (∑ c ∈ Finset.range (L + 1), cbz (L : ℤ) (c : ℤ) • mu D v ((c : ℤ) - 1) w)
        = ∑ c ∈ Finset.range (L + 1), cbz (L : ℤ) (c : ℤ) • mu D u ((p : ℤ) - 1) (mu D v ((c : ℤ) - 1) w) from by
      rw [mu, map_sum]
      exact Finset.sum_congr rfl fun c _ => by rw [LinearMap.map_smul]; rfl,
    Finset.smul_sum]
  exact Finset.sum_congr rfl fun c _ => by rw [smul_smul]

/-- `u₍ₐ₋₁₎v ∈ (Carrier D)_{K+L-a}` for `a ≤ K` (grade `K+L-a ≥ 0`). -/
private theorem inner_uv_mem (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) {K L : ℕ} {u v : (Carrier D)}
    (hu : u ∈ grade D (K : ℤ)) (hv : v ∈ grade D (L : ℤ)) (a : ℕ) :
    mu D u ((a : ℤ) - 1) v ∈ grade D ((K : ℤ) + (L : ℤ) - (a : ℤ)) := by
  have h := positive_actual_mode_grade D hD (K : ℤ) (L : ℤ) ((a : ℤ)-1) u v hu hv
  rwa [show (K : ℤ) + (L : ℤ) - ((a : ℤ) - 1) - 1 = (K : ℤ) + (L : ℤ) - (a : ℤ) from by ring] at h

/-- **LHS expansion (one step)**: `(u*v)*w = ∑_{a≤K} cbz K a • ((u₍ₐ₋₁₎v) * w)`. -/
private theorem uvw_lhs_step (D : LatticeData) {K : ℕ} {u v : (Carrier D)}
    (hu : u ∈ grade D (K : ℤ)) (w : (Carrier D)) :
    star D (star D u v) w
      = ∑ a ∈ Finset.range (K + 1),
          cbz (K : ℤ) (a : ℤ) • star D (mu D u ((a : ℤ) - 1) v) w := by
  rw [star_homogeneous_cbz D (by positivity) hu, show (K : ℤ).toNat + 1 = K + 1 from by simp]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]

/-! ## `Ufam` as a u-word collection. -/

/-- The net u-word coefficient (residue tower) of `u₍ₘ₎(v₍ᵦ₎w)` in `Ufam`. -/
private def uCoeffTower (K L b : ℕ) (m : ℤ) : ℂ :=
  ∑ k ∈ Finset.range (b + 1), cbz (K : ℤ) (m + 2 + (k : ℤ)) * cbz (L : ℤ) ((b : ℤ) - (k : ℤ))

/-- Per-`b` inner collapse: `∑_{n≤b} μ(L,b,n) • Pres(u,K,v₍b₎w,n) = ∑ᶠ m, uCoeffTower • u₍ₘ₎(v₍b₎w)`. -/
private theorem Ufam_inner (D : LatticeData) (K L b : ℕ) (u v w : (Carrier D)) :
    (∑ n ∈ Finset.range (b + 1), ActualZhuMuIdentity.muCoeff L b n • higherCircle D K u (mu D v (b : ℤ) w) n)
      = ∑ᶠ m : ℤ, uCoeffTower K L b m • mu D u m (mu D v (b : ℤ) w) := by
  -- expand each Pres into a finsum, pull the muCoeff scalar inside
  rw [show (∑ n ∈ Finset.range (b + 1), ActualZhuMuIdentity.muCoeff L b n • higherCircle D K u (mu D v (b : ℤ) w) n)
        = ∑ n ∈ Finset.range (b + 1),
            ∑ᶠ m : ℤ, (ActualZhuMuIdentity.muCoeff L b n * cbz ((K : ℤ) + n) (m + 2 + n))
              • mu D u m (mu D v (b : ℤ) w) from
      Finset.sum_congr rfl fun n _ => by
        rw [Pres_eq_finsum D K u (mu D v (b : ℤ) w) n]
        have hfin : Function.HasFiniteSupport
            (fun m : ℤ => cbz ((K : ℤ) + n) (m + 2 + n) • mu D u m (mu D v (b : ℤ) w)) :=
          smul_support_of_scalar D u (mu D v (b : ℤ) w) _
            (Set.Finite.subset (cbz_shift_support_fin (d := (K : ℤ) + n) (by positivity) (2 + n))
              (fun m hm => by
                rw [Function.mem_support] at hm ⊢
                intro h; apply hm
                rw [show m + 2 + (n : ℤ) = m + (2 + (n : ℤ)) from by ring]; exact h))
        rw [smul_finsum' (ActualZhuMuIdentity.muCoeff L b n) hfin]
        refine finsum_congr fun m => ?_
        rw [smul_smul] ]
  -- swap the finite n-sum past the finsum
  rw [← finsum_sum_comm (Finset.range (b + 1))
      (fun m n => (ActualZhuMuIdentity.muCoeff L b n * cbz ((K : ℤ) + n) (m + 2 + n))
        • mu D u m (mu D v (b : ℤ) w))
      (fun n _ => ?_)]
  · refine finsum_congr fun m => ?_
    rw [← Finset.sum_smul]
    congr 1
    rw [uCoeffTower]
    -- ∑_n μ(L,b,n)·cbz(K+n)(m+2+n) = ∑_k cbz K (m+2+k)·cbz L (b-k)  (mu_identity, s = m+2)
    simpa only [cbz] using (ActualZhuMuIdentity.mu_identity K L b (m+2)).symm
  · -- finite support of m ↦ (μ·cbz)• u₍ₘ₎(...) for fixed n
    refine smul_support_of_scalar D u (mu D v (b : ℤ) w) _ (Set.Finite.subset
      (cbz_shift_support_fin (d := (K : ℤ) + n) (by positivity) (2 + n)) ?_)
    intro m hm
    rw [Function.mem_support] at hm ⊢
    intro h; apply hm
    rw [show (ActualZhuMuIdentity.muCoeff L b n * cbz ((K : ℤ) + n) (m + 2 + n))
          = (ActualZhuMuIdentity.muCoeff L b n) * cbz ((K : ℤ) + n) (m + (2 + (n : ℤ))) from by
        rw [show m + (2 + (n : ℤ)) = m + 2 + (n : ℤ) from by ring], h, mul_zero]

/-- The net v-word coefficient (residue tower) of `v₍ᵧ₎(u₍ₐ₎w)` in `Vfam`. -/
private def vCoeffTower (K L a : ℕ) (γ : ℤ) : ℂ :=
  ∑ k ∈ Finset.range (a + 1), cbz (L : ℤ) (γ + 2 + (k : ℤ)) * cbz (K : ℤ) ((a : ℤ) - (k : ℤ))

/-- Per-`a` inner collapse: `∑_{n≤a} μ(K,a,n) • Pres(v,L,u₍a₎w,n) = ∑ᶠ γ, vCoeffTower • v₍ᵧ₎(u₍ₐ₎w)`. -/
private theorem Vfam_inner (D : LatticeData) (K L a : ℕ) (u v w : (Carrier D)) :
    (∑ n ∈ Finset.range (a + 1), ActualZhuMuIdentity.muCoeff K a n • higherCircle D L v (mu D u (a : ℤ) w) n)
      = ∑ᶠ γ : ℤ, vCoeffTower K L a γ • mu D v γ (mu D u (a : ℤ) w) := by
  simpa only [uCoeffTower, vCoeffTower] using Ufam_inner D L K a v u w

/-! ## LHS expansion via homogeneity + mode_iterate. -/

/-- For `a ≤ K`, expand `(u₍ₐ₋₁₎v)*w` via homogeneity (grade `K+L-a`) and `mode_iterate`,
extending the `r`-range to the fixed `range (K+L+1)` (extra terms vanish via `cbz`). -/
private theorem lhs_per_a (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) {K L : ℕ} {u v : (Carrier D)}
    (hu : u ∈ grade D (K : ℤ)) (hv : v ∈ grade D (L : ℤ)) (w : (Carrier D)) {a : ℕ} (haK : a ≤ K) :
    star D (mu D u ((a : ℤ) - 1) v) w
      = ∑ r ∈ Finset.range (K + L + 1),
          ∑ᶠ i : ℕ, (cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
              * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
            • (mu D u ((a : ℤ) - 1 - (i : ℤ)) (mu D v ((r : ℤ) - 1 + (i : ℤ)) w)
              - ((-1 : ℂ) ^ ((a : ℤ) - 1))
                • mu D v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (mu D u (i : ℤ) w)) := by
  have hmem := inner_uv_mem D hD hu hv a
  rw [star_homogeneous_cbz D (by omega) hmem]
  -- the toNat of K+L-a is K+L-a since a ≤ K
  have htn : ((K : ℤ) + (L : ℤ) - (a : ℤ)).toNat = K + L - a := by
    have : ((K : ℤ) + (L : ℤ) - (a : ℤ)) = ((K + L - a : ℕ) : ℤ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [this, Int.toNat_natCast]
  -- rewrite the range index and apply mode_iterate inside each summand
  rw [show (∑ m ∈ Finset.range (((K : ℤ) + (L : ℤ) - (a : ℤ)).toNat + 1),
            cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (m : ℤ)
              • mu D (mu D u ((a : ℤ) - 1) v) ((m : ℤ) - 1) w)
        = ∑ r ∈ Finset.range (K + L + 1),
            cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
              • mu D (mu D u ((a : ℤ) - 1) v) ((r : ℤ) - 1) w from ?_]
  · -- now expand the composite mode via mode_iterate per r
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [mode_iterate D u v ((a : ℤ) - 1) ((r : ℤ) - 1) w]
    rw [show ((a : ℤ) - 1) + ((r : ℤ) - 1) = ((a : ℤ) - 1) + ((r : ℤ) - 1) from rfl]
    -- distribute the cbz scalar into the finsum
    have hfin : Function.HasFiniteSupport
        (fun i : ℕ => ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i)
          • (mu D u (((a : ℤ) - 1) - (i : ℤ)) (mu D v (((r : ℤ) - 1) + (i : ℤ)) w)
            - ((-1 : ℂ) ^ ((a : ℤ) - 1))
              • mu D v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (mu D u (i : ℤ) w))) := by
      exact iterate_difference_finite D u v w ((a:ℤ)-1) ((r:ℤ)-1)
    rw [smul_finsum' (cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)) hfin]
    refine finsum_congr fun i => ?_
    rw [smul_smul]
  · -- extend the r-range; extra terms r > K+L-a vanish (cbz = 0)
    refine Finset.sum_subset ?_ ?_
    · intro x hx
      rw [Finset.mem_range, htn] at hx
      rw [Finset.mem_range]; omega
    · intro r hr hrni
      have hrlo : (K + L - a) + 1 ≤ r := by
        rw [htn] at hrni; exact Nat.le_of_not_lt (fun h => hrni (Finset.mem_range.mpr h))
      rw [cbz_lt (by omega) (by
        have : ((K + L - a : ℕ) : ℤ) < (r : ℤ) := by exact_mod_cast (by omega : K + L - a < r)
        rw [Nat.cast_sub (by omega)] at this; push_cast at this ⊢; omega :
        ((K : ℤ) + (L : ℤ) - (a : ℤ)) < (r : ℤ)),
        zero_smul]

/-! ## The U-side and V-side of `(u*v)*w`. -/

/-- The **U-side** of `(u*v)*w`: all `u₍ₐ₋₁₋ᵢ₎(v₍ᵣ₋₁₊ᵢ₎w)` terms. -/
private def USide (D : LatticeData) (K L : ℕ) (u v w : (Carrier D)) : (Carrier D) :=
  ∑ a ∈ Finset.range (K + 1), ∑ r ∈ Finset.range (K + L + 1),
    ∑ᶠ i : ℕ, (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
        * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
      • mu D u ((a : ℤ) - 1 - (i : ℤ)) (mu D v ((r : ℤ) - 1 + (i : ℤ)) w)

/-- The **V-side** of `(u*v)*w`: all `v₍ₐ₊ᵣ₋₂₋ᵢ₎(u₍ᵢ₎w)` terms (carrying the sign `(-1)^(a-1)`). -/
private def VSide (D : LatticeData) (K L : ℕ) (u v w : (Carrier D)) : (Carrier D) :=
  ∑ a ∈ Finset.range (K + 1), ∑ r ∈ Finset.range (K + L + 1),
    ∑ᶠ i : ℕ, (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
        * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
      • mu D v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (mu D u (i : ℤ) w)

/-- Finiteness of the per-`(a,r)` u-side `i`-finsum (regularity of `v` on `w`). -/
private theorem uside_fin (D : LatticeData) (K L : ℕ) (u v w : (Carrier D)) (a r : ℕ) :
    Function.HasFiniteSupport (fun i : ℕ =>
      (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
          * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
        • mu D u ((a : ℤ) - 1 - (i : ℤ)) (mu D v ((r : ℤ) - 1 + (i : ℤ)) w)) := by
  have h := (stateField_iterate D u v w ((a:ℤ)-1) ((r:ℤ)-1)).1
  simpa only [mu, gBinom, StateFieldResidueReconstruction.integerBinomial,
    Pi.smul_def', smul_smul, mul_assoc] using
    (Function.HasFiniteSupport.smul_right
      (fun _ : ℕ => cbz (K:ℤ) (a:ℤ) * cbz ((K:ℤ)+(L:ℤ)-(a:ℤ)) (r:ℤ)) h)

/-- Finiteness of the per-`(a,r)` v-side `i`-finsum (regularity of `u` on `w`). -/
private theorem vside_fin (D : LatticeData) (K L : ℕ) (u v w : (Carrier D)) (a r : ℕ) :
    Function.HasFiniteSupport (fun i : ℕ =>
      (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
          * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
        • mu D v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (mu D u (i : ℤ) w)) := by
  have h := (stateField_iterate D u v w ((a:ℤ)-1) ((r:ℤ)-1)).2.1
  simpa only [mu, gBinom, StateFieldResidueReconstruction.integerBinomial,
    Pi.smul_def', smul_smul, mul_assoc, mul_comm, mul_left_comm] using
    (Function.HasFiniteSupport.smul_right
      (fun _ : ℕ => cbz (K:ℤ) (a:ℤ) * cbz ((K:ℤ)+(L:ℤ)-(a:ℤ)) (r:ℤ) *
        ((-1:ℂ)^((a:ℤ)-1))) h)

/-- **Master split**: `(u*v)*w = USide − VSide`. -/
private theorem lhs_split (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) {K L : ℕ} {u v : (Carrier D)}
    (hu : u ∈ grade D (K : ℤ)) (hv : v ∈ grade D (L : ℤ)) (w : (Carrier D)) :
    star D (star D u v) w = USide D K L u v w - VSide D K L u v w := by
  rw [uvw_lhs_step D hu w]
  rw [show (∑ a ∈ Finset.range (K + 1),
            cbz (K : ℤ) (a : ℤ) • star D (mu D u ((a : ℤ) - 1) v) w)
        = ∑ a ∈ Finset.range (K + 1), cbz (K : ℤ) (a : ℤ) •
            (∑ r ∈ Finset.range (K + L + 1),
              ∑ᶠ i : ℕ, (cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
                  * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
                • (mu D u ((a : ℤ) - 1 - (i : ℤ)) (mu D v ((r : ℤ) - 1 + (i : ℤ)) w)
                  - ((-1 : ℂ) ^ ((a : ℤ) - 1))
                    • mu D v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (mu D u (i : ℤ) w))) from
      Finset.sum_congr rfl fun a ha =>
        by rw [lhs_per_a D hD hu hv w (Finset.mem_range.mp ha |> Nat.lt_succ_iff.mp)] ]
  -- distribute and split each summand into u-part minus v-part
  rw [USide, VSide, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r hr => ?_
  -- split the i-finsum: scalar•(uword - sv•vword) = scalar•uword - (scalar·sv)•vword
  rw [smul_finsum' (cbz (K : ℤ) (a : ℤ)) (by
    have hh := Function.HasFiniteSupport.smul_right
      (fun _ : ℕ => cbz ((K:ℤ)+(L:ℤ)-(a:ℤ)) (r:ℤ))
      (iterate_difference_finite D u v w ((a:ℤ)-1) ((r:ℤ)-1))
    simpa only [Pi.smul_def', smul_smul] using hh)]
  rw [show (∑ᶠ i : ℕ, cbz (K : ℤ) (a : ℤ) •
            ((cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
                * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
              • (mu D u ((a : ℤ) - 1 - (i : ℤ)) (mu D v ((r : ℤ) - 1 + (i : ℤ)) w)
                - ((-1 : ℂ) ^ ((a : ℤ) - 1))
                  • mu D v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (mu D u (i : ℤ) w))))
        = ∑ᶠ i : ℕ,
            ((cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
                * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i))
              • mu D u ((a : ℤ) - 1 - (i : ℤ)) (mu D v ((r : ℤ) - 1 + (i : ℤ)) w)
            - (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
                * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
              • mu D v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (mu D u (i : ℤ) w)) from
      finsum_congr fun i => by rw [smul_smul, smul_sub, smul_smul]; ring_nf]
  rw [finsum_sub_distrib (uside_fin D K L u v w a r) (vside_fin D K L u v w a r)]

/-! ## V-side reindex: collect v-words by mode value. -/

/-- Per-`(a,i)` reindex of the `r`-sum to a `∑ᶠ γ` over the v-mode value (`γ = a+r-2-i`). -/
private theorem vside_r_reindex (D : LatticeData) (K L : ℕ) (u v w : (Carrier D)) (a i : ℕ)
    (haK : a ≤ K) :
    (∑ r ∈ Finset.range (K + L + 1),
        cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
          • mu D v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (mu D u (i : ℤ) w))
      = ∑ᶠ γ : ℤ, cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (γ - (a : ℤ) + 2 + (i : ℤ))
          • mu D v γ (mu D u (i : ℤ) w) := by
  rw [show (∑ r ∈ Finset.range (K + L + 1),
            cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
              • mu D v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (mu D u (i : ℤ) w))
        = ∑ r ∈ Finset.range (K + L + 1),
            cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
              • mu D v ((r : ℤ) + ((a : ℤ) - 2 - (i : ℤ))) (mu D u (i : ℤ) w) from
      Finset.sum_congr rfl fun r _ => by
        rw [show ((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ) = (r : ℤ) + ((a : ℤ) - 2 - (i : ℤ)) from by ring] ]
  rw [rangeSmul_eq_finsumZ (fun q : ℤ => cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) q)
      (fun q => mu D v q (mu D u (i : ℤ) w)) ((a : ℤ) - 2 - (i : ℤ))
      (fun q hq => cbz_apply_neg _ hq)
      (fun q hq => cbz_lt (by omega) (by omega))]
  rw [← finsum_comp_equiv (Equiv.addRight ((a : ℤ) - 2 - (i : ℤ)))
      (f := fun γ : ℤ => cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (γ - (a : ℤ) + 2 + (i : ℤ))
        • mu D v γ (mu D u (i : ℤ) w))]
  refine finsum_congr fun q => ?_
  simp only [Equiv.coe_addRight]
  rw [show (q + ((a : ℤ) - 2 - (i : ℤ))) - (a : ℤ) + 2 + (i : ℤ) = q from by ring]

/-- The per-`(γ,i)` v-side coefficient (sum over `a`). -/
private def vSideCoeff (K L : ℕ) (γ : ℤ) (i : ℕ) : ℂ :=
  ∑ a ∈ Finset.range (K + 1),
    cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (γ - (a : ℤ) + 2 + (i : ℤ))
      * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1))

/-- Per-`i` V-side collapse: the `(a,r)` double sum collapses to `∑ᶠ γ, vSideCoeff • v₍ᵧ₎(u₍ᵢ₎w)`. -/
private theorem vside_per_i (D : LatticeData) (K L : ℕ) (u v w : (Carrier D)) (i : ℕ) :
    (∑ a ∈ Finset.range (K + 1), ∑ r ∈ Finset.range (K + L + 1),
        (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
            * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
          • mu D v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (mu D u (i : ℤ) w))
      = ∑ᶠ γ : ℤ, vSideCoeff K L γ i • mu D v γ (mu D u (i : ℤ) w) := by
  -- pull the a-only scalars out of the r-sum and reindex via vside_r_reindex
  rw [show (∑ a ∈ Finset.range (K + 1), ∑ r ∈ Finset.range (K + L + 1),
            (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
                * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
              • mu D v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (mu D u (i : ℤ) w))
        = ∑ a ∈ Finset.range (K + 1),
            (cbz (K : ℤ) (a : ℤ) * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i)
                * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
              • ∑ᶠ γ : ℤ, cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (γ - (a : ℤ) + 2 + (i : ℤ))
                  • mu D v γ (mu D u (i : ℤ) w) from
      Finset.sum_congr rfl fun a ha => by
        rw [← vside_r_reindex D K L u v w a i (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)),
          Finset.smul_sum]
        exact Finset.sum_congr rfl fun r _ => by rw [smul_smul]; ring_nf]
  -- push the a-scalar into each finsum and swap the finite a-sum past ∑ᶠ γ
  rw [show (∑ a ∈ Finset.range (K + 1),
            (cbz (K : ℤ) (a : ℤ) * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i)
                * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
              • ∑ᶠ γ : ℤ, cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (γ - (a : ℤ) + 2 + (i : ℤ))
                  • mu D v γ (mu D u (i : ℤ) w))
        = ∑ a ∈ Finset.range (K + 1),
            ∑ᶠ γ : ℤ,
              (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (γ - (a : ℤ) + 2 + (i : ℤ))
                  * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
                • mu D v γ (mu D u (i : ℤ) w) from
      Finset.sum_congr rfl fun a ha => by
        have haK : a ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        have hfin : Function.HasFiniteSupport
            (fun γ : ℤ => cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (γ - (a : ℤ) + 2 + (i : ℤ))
              • mu D v γ (mu D u (i : ℤ) w)) :=
          smul_support_of_scalar D v (mu D u (i : ℤ) w) _
            (Set.Finite.subset
              (cbz_shift_support_fin (d := (K : ℤ) + (L : ℤ) - (a : ℤ)) (by omega)
                (-(a : ℤ) + 2 + (i : ℤ)))
              (fun γ hγ => by
                rw [Function.mem_support] at hγ ⊢
                intro h; apply hγ
                rwa [show γ + (-(a : ℤ) + 2 + (i : ℤ)) = γ - (a : ℤ) + 2 + (i : ℤ) from by ring] at h))
        rw [smul_finsum' _ hfin]
        refine finsum_congr fun γ => ?_
        rw [smul_smul]; ring_nf]
  rw [← finsum_sum_comm (Finset.range (K + 1))
      (fun γ a => (cbz (K : ℤ) (a : ℤ)
          * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (γ - (a : ℤ) + 2 + (i : ℤ))
          * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
        • mu D v γ (mu D u (i : ℤ) w))
      (fun a ha => ?_)]
  · refine finsum_congr fun γ => ?_
    rw [vSideCoeff, Finset.sum_smul]
  · -- finite support of γ ↦ (...)• v₍ᵧ₎(...) for fixed a
    have haK : a ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    refine smul_support_of_scalar D v (mu D u (i : ℤ) w) _ (Set.Finite.subset
      (cbz_shift_support_fin (d := (K : ℤ) + (L : ℤ) - (a : ℤ)) (by omega)
        (-(a : ℤ) + 2 + (i : ℤ))) ?_)
    intro γ hγ
    rw [Function.mem_support] at hγ ⊢
    intro h; apply hγ
    rw [show (cbz (K : ℤ) (a : ℤ)
            * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (γ - (a : ℤ) + 2 + (i : ℤ))
            * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
          = (cbz (K : ℤ) (a : ℤ) * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i)
              * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
              * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (γ + (-(a : ℤ) + 2 + (i : ℤ))) from by
        rw [show γ + (-(a : ℤ) + 2 + (i : ℤ)) = γ - (a : ℤ) + 2 + (i : ℤ) from by ring]; ring,
      h, mul_zero]

/-- The v-side coefficient equals `-vCoeffTower` (via `v_core`). -/
private theorem vSideCoeff_eq (K L : ℕ) (γ : ℤ) (i : ℕ) :
    vSideCoeff K L γ i = - vCoeffTower K L i γ := by
  rw [vSideCoeff, vCoeffTower]
  rw [← v_core K L γ i]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show γ - (a : ℤ) + 2 + (i : ℤ) = γ + 2 + (i : ℤ) - (a : ℤ) from by ring]
  ring

/-- Finite support in `i` of the r-summed v-side term (for fixed `a`). -/
private theorem vside_a_fin (D : LatticeData) (K L : ℕ) (u v w : (Carrier D)) (a : ℕ) :
    Function.HasFiniteSupport (fun i : ℕ => ∑ r ∈ Finset.range (K + L + 1),
      (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
          * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
        • mu D v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (mu D u (i : ℤ) w)) := by
  obtain ⟨Nu, hNu⟩ := regularity D u w
  apply Set.Finite.subset (Set.finite_Icc (0 : ℕ) Nu.toNat)
  intro i hi
  rw [Function.mem_support] at hi
  simp only [Set.mem_Icc]
  refine ⟨Nat.zero_le _, ?_⟩
  by_contra hbig
  apply hi
  have hNule : Nu ≤ (Nu.toNat : ℤ) := Int.self_le_toNat Nu
  have hi' : (Nu.toNat : ℤ) + 1 ≤ (i : ℤ) := by exact_mod_cast (by omega : Nu.toNat + 1 ≤ i)
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [show mu D u (i : ℤ) w = (0 : (Carrier D)) from hNu _ (by omega)]
  simp

/-- `VSide` as a double finsum over `(i, γ)`. -/
private theorem VSide_eq (D : LatticeData) (K L : ℕ) (u v w : (Carrier D)) :
    VSide D K L u v w
      = ∑ᶠ i : ℕ, ∑ᶠ γ : ℤ, vSideCoeff K L γ i • mu D v γ (mu D u (i : ℤ) w) := by
  rw [VSide]
  -- step 1: per a, swap the r-sum past the i-finsum (innermost)
  rw [show (∑ a ∈ Finset.range (K + 1), ∑ r ∈ Finset.range (K + L + 1),
            ∑ᶠ i : ℕ, (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
                * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
              • mu D v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (mu D u (i : ℤ) w))
        = ∑ a ∈ Finset.range (K + 1),
            ∑ᶠ i : ℕ, ∑ r ∈ Finset.range (K + L + 1),
              (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
                  * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
                • mu D v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (mu D u (i : ℤ) w) from
      Finset.sum_congr rfl fun a _ => by
        rw [← finsum_sum_comm (Finset.range (K + L + 1))
            (fun i r => (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
                * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
              • mu D v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (mu D u (i : ℤ) w))
            (fun r _ => vside_fin D K L u v w a r)] ]
  -- step 2: swap the a-sum past the i-finsum
  rw [← finsum_sum_comm (Finset.range (K + 1))
      (fun i a => ∑ r ∈ Finset.range (K + L + 1),
        (cbz (K : ℤ) (a : ℤ) * cbz ((K : ℤ) + (L : ℤ) - (a : ℤ)) (r : ℤ)
            * ((-1 : ℂ) ^ i * gBinom ((a : ℤ) - 1) i) * ((-1 : ℂ) ^ ((a : ℤ) - 1)))
          • mu D v (((a : ℤ) - 1) + ((r : ℤ) - 1) - (i : ℤ)) (mu D u (i : ℤ) w))
      (fun a _ => vside_a_fin D K L u v w a)]
  -- step 3: apply vside_per_i per i
  refine finsum_congr fun i => ?_
  rw [vside_per_i D K L u v w i]

/-- `Vfam` as a double finsum over `(i, γ)` (extending the `i`-range to all `ℕ`). -/
private theorem Vfam_eq (D : LatticeData) (K L : ℕ) (u v w : (Carrier D)) {Bu : ℕ}
    (hBu : ∀ a : ℕ, Bu ≤ a → mu D u (a : ℤ) w = 0) :
    Vfam D K L u v w Bu
      = ∑ᶠ i : ℕ, ∑ᶠ γ : ℤ, vCoeffTower K L i γ • mu D v γ (mu D u (i : ℤ) w) := by
  rw [Vfam]
  rw [show (∑ a ∈ Finset.range Bu, ∑ n ∈ Finset.range (a + 1),
            ActualZhuMuIdentity.muCoeff K a n • higherCircle D L v (mu D u (a : ℤ) w) n)
        = ∑ a ∈ Finset.range Bu,
            ∑ᶠ γ : ℤ, vCoeffTower K L a γ • mu D v γ (mu D u (a : ℤ) w) from
      Finset.sum_congr rfl fun a _ => Vfam_inner D K L a u v w]
  -- extend the range to all ℕ: terms with i ≥ Bu vanish (u₍ᵢ₎w = 0)
  refine (finsum_eq_finsetSum_of_support_subset _ (s := Finset.range Bu) ?_).symm
  intro i hi
  rw [Function.mem_support] at hi
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hge
  apply hi
  rw [show mu D u (i : ℤ) w = (0 : (Carrier D)) from hBu i (by omega)]
  refine finsum_eq_zero_of_forall_eq_zero fun γ => ?_
  rw [mu_zero_right, smul_zero]

/-- **The v-family matches**: `-VSide = Vfam`. -/
private theorem neg_VSide_eq_Vfam (D : LatticeData) (K L : ℕ) (u v w : (Carrier D)) {Bu : ℕ}
    (hBu : ∀ a : ℕ, Bu ≤ a → mu D u (a : ℤ) w = 0) :
    - VSide D K L u v w = Vfam D K L u v w Bu := by
  rw [VSide_eq, Vfam_eq D K L u v w hBu, ← finsum_neg_distrib]
  refine finsum_congr fun i => ?_
  rw [← finsum_neg_distrib]
  refine finsum_congr fun γ => ?_
  rw [vSideCoeff_eq, neg_smul, neg_neg]

end
end D5.S3.VertexAlgebra.Lattice.ActualZhuAssociatorExpansion
