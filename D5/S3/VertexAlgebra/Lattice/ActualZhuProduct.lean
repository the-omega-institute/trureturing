/- GID: D5/S3/VertexAlgebra/Lattice/ActualZhuProduct
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/ActualZhuProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original-carrier Zhu multiplication and higher circle residues. -/

/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the repository root LICENSE.
Authors: Fedor K. Popov
Source-faithful native port of VOA/Modules/ZhuModule.lean, Lean_VOA
013a799ca834a8a6b3afa8129e3e522025b3f45c; Zhu and Frenkel--Zhu residue argument.
The carrier, energy decomposition, fields, translation and O-space are native.
proof_shape: higherCircle_mem_zhuO: content; star_homogeneous: bind-only.
admission_basis: escape-witness.
escape_witness: state-derivative recursion raises the higher-circle pole order
inside the same literal O; star_homogeneous is consumed by right-argument stability.
-/
import D5.S3.VertexAlgebra.Lattice.ActualZhuFinite
import D5.S3.VertexAlgebra.Lattice.ActualZhuBinomial

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.ActualZhuProduct
open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticePositiveEnergy LatticeSugawaraConformal LatticeActualStateDerivative
open scoped BigOperators VertexOperator DirectSum
open private cbz cbz_apply_neg cbz_nat cbz_natCast_eq_choose cbz_upper_absorption
  from D5.S3.VertexAlgebra.Lattice.ActualZhuBinomial
noncomputable section

private def homogeneousStar (D : LatticeData) (p : ℤ) :
    grade D p →ₗ[ℂ] Module.End ℂ (Carrier D) :=
  ∑ j ∈ Finset.range (p.toNat + 1), (p.toNat.choose j : ℂ) •
    ((LinearMap.proj ((j : ℤ) - 1)).comp
      (VertexOperator.ncoeff.comp ((Y D).comp (grade D p).subtype)))

/-- Bilinear Zhu star on the original full carrier and its original energy decomposition. -/
def star (D : LatticeData) : Carrier D →ₗ[ℂ] Module.End ℂ (Carrier D) :=
  (DirectSum.toModule ℂ ℤ (Module.End ℂ (Carrier D)) (homogeneousStar D)).comp
    (carrierEnergyDecomposition D).toLinearMap

/-- Full finite formula for a homogeneous original state. -/
theorem star_homogeneous (D : LatticeData) (p : ℕ) (a b : Carrier D)
    (ha : a ∈ grade D (p : ℤ)) :
    star D a b = ∑ j ∈ Finset.range (p + 1),
      (p.choose j : ℂ) • mu D a ((j : ℤ) - 1) b := by
  classical
  have he : carrierEnergyDecomposition D a =
      DirectSum.lof ℂ ℤ (fun n => grade D n) (p : ℤ) ⟨a,ha⟩ := by
    apply (carrierEnergyDecomposition D).symm.injective
    simp [carrierEnergyDecomposition]
  change DirectSum.toModule ℂ ℤ (Module.End ℂ (Carrier D)) _
    (carrierEnergyDecomposition D a) b = _
  rw [he, DirectSum.toModule_lof]
  simp [homogeneousStar, mu, LinearMap.sum_apply, Finset.sum_apply]

/-- Higher circles retain the complete shifted binomial row. -/
def higherCircle (D : LatticeData) (M : ℕ) (a b : Carrier D) (n : ℕ) : Carrier D :=
  ∑ i ∈ Finset.range (M + n + 1), ((M + n).choose i : ℂ) •
    mu D a ((i : ℤ) - 2 - n) b

private theorem higherCircle_binomial (D : LatticeData) (M : ℕ) (a b : Carrier D) (n : ℕ) :
    higherCircle D M a b n = ∑ i ∈ Finset.range (M+n+1),
      cbz ((M : ℤ)+n) i • mu D a ((i : ℤ)-2-n) b := by
  unfold higherCircle
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [cbz_nat]
  unfold StateFieldResidueReconstruction.integerBinomial
  have h := Ring.choose_natCast (R := ℤ) (M+n) i
  rw [Nat.cast_add] at h
  exact_mod_cast h.symm

private theorem translation_grade (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (M : ℕ) (a : Carrier D) (ha : a ∈ grade D (M : ℤ)) :
    translation D a ∈ grade D ((M : ℤ)+1) := by
  have hv : vacuum D ∈ grade D 0 := by
    rw [grade_zero D hD]
    exact Submodule.subset_span (Set.mem_singleton _)
  rw [LatticeActualVertexAlgebra.translation_as_mode]
  convert positive_actual_mode_grade D hD (M : ℤ) 0 (-2) a (vacuum D) ha hv using 1 <;>
    congr 1 <;> omega

private theorem derivative_mu (D : LatticeData) (a b : Carrier D) (q : ℤ) :
    mu D (translation D a) q b = -(q : ℂ) • mu D a (q-1) b := by
  exact congrArg (fun f : Module.End ℂ (Carrier D) => f b) (state_derivative_modes D a q)

private theorem pres_coeff_identity (M n : ℕ) (i : ℤ) :
    ((n : ℂ) + 2) * cbz ((M : ℤ) + n + 1) i
      = cbz ((M : ℤ) + n + 1) i * (-((i : ℂ) - 2 - n))
        + ((M : ℂ) + n + 1) * cbz ((M : ℤ) + n) (i - 1) := by
  -- reduces to upper absorption: i·C(M+n+1,i) = (M+n+1)·C(M+n,i-1).
  have hua := cbz_upper_absorption (M + n + 1) i
  rw [show ((((M + n + 1 : ℕ)) : ℤ) - 1) = (M : ℤ) + n from by push_cast; ring,
      show (((M + n + 1 : ℕ)) : ℤ) = (M : ℤ) + n + 1 from by push_cast; ring] at hua
  push_cast at hua ⊢
  linear_combination hua

theorem higherCircle_mem_zhuO (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) {M : ℕ} {a : Carrier D}
    (ha : a ∈ grade D (M : ℤ)) (b : Carrier D) (n : ℕ) : higherCircle D M a b n ∈ ActualZhuFinite.zhuO D := by
  induction n generalizing M a with
  | zero =>
    have he : higherCircle D M a b 0 = NormFourZhuFinite.circle D M a b := by
      simp [higherCircle, NormFourZhuFinite.circle]
    rw [he]
    exact Submodule.subset_span ⟨M,a,b,ha,rfl⟩
  | succ n ih =>
    -- inductive step: (n+2)•Pres(n+1) = G_n + (M+n+1)•Pres(n), with
    --   G_n := Pres (L₋₁a) (M+1) n ∈ O (IH applied to L₋₁a ∈ Carrier D_{M+1}),
    --   Pres a M n ∈ O (IH).
    -- Hence Pres(n+1) = (1/(n+2))•[G_n + (M+n+1)•Pres(n)] ∈ O.
    have haL : translation D a ∈ grade D ((M : ℤ) + 1) := translation_grade D hD M a ha
    -- IH for L₋₁a at level M+1:
    have hG : higherCircle D (M + 1) (translation D a) b n ∈ ActualZhuFinite.zhuO D := by
      have := ih (M := M + 1) (a := translation D a) (by
        rwa [show (((M + 1 : ℕ)) : ℤ) = (M : ℤ) + 1 from by push_cast; ring])
      exact this
    have hP : higherCircle D M a b n ∈ ActualZhuFinite.zhuO D := ih ha
    -- Express G_n with (L₋₁a)₍·₎ expanded to a₍·₎ via smul_L_neg_one.
    -- G_n = ∑_{i∈range(M+n+2)} cbz(M+1+n,i)·(-(i-2-n)) • a₍ᵢ₋₃₋ₙ₎b.
    have hGeq : higherCircle D (M + 1) (translation D a) b n
        = ∑ i ∈ Finset.range (M + n + 2),
            (cbz ((M : ℤ) + n + 1) (i : ℤ) * (-((i : ℂ) - 2 - n)))
              • mu D a ((i : ℤ) - 3 - n) b := by
      rw [higherCircle_binomial]
      rw [show M + 1 + n + 1 = M + n + 2 from by ring]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hcast1 : (((M + 1 : ℕ) : ℤ)) + (n : ℤ) = (M : ℤ) + n + 1 := by push_cast; ring
      rw [hcast1, derivative_mu D a b ((i : ℤ) - 2 - n),
        show ((i : ℤ) - 2 - n - 1) = (i : ℤ) - 3 - n from by ring,
        smul_smul]
      congr 2
      push_cast
      ring
    -- Now the cleared sum identity:
    --   (n+2)•Pres(n+1) = G_n + (M+n+1)•Pres(n)  (all over range(M+n+2), inner mode a₍ᵢ₋₃₋ₙ₎b).
    have hsum : ((n : ℂ) + 2) • higherCircle D M a b (n + 1)
        = higherCircle D (M + 1) (translation D a) b n + ((M : ℂ) + n + 1) • higherCircle D M a b n := by
      rw [hGeq]
      -- expand (n+2)•Pres(n+1)
      have hLHS : ((n : ℂ) + 2) • higherCircle D M a b (n + 1)
          = ∑ i ∈ Finset.range (M + n + 2),
              (((n : ℂ) + 2) * cbz ((M : ℤ) + (n + 1)) (i : ℤ))
                • mu D a ((i : ℤ) - 2 - (n + 1)) b := by
        rw [higherCircle_binomial]
        rw [show M + (n + 1) + 1 = M + n + 2 from by ring, Finset.smul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [smul_smul]
        congr 2 <;> push_cast <;> ring
      -- expand (M+n+1)•Pres(n), reindex k ↦ i-1 onto range(M+n+2).
      have hPn : ((M : ℂ) + n + 1) • higherCircle D M a b n
          = ∑ i ∈ Finset.range (M + n + 2),
              (((M : ℂ) + n + 1) * cbz ((M : ℤ) + n) ((i : ℤ) - 1))
                • mu D a ((i : ℤ) - 3 - n) b := by
        rw [higherCircle_binomial]
        rw [Finset.smul_sum]
        -- shift the index: range(M+n+1) → range(M+n+2) via sum_range_succ' (drop the new bottom i=0).
        rw [Finset.sum_range_succ' (fun i => (((M : ℂ) + n + 1) * cbz ((M : ℤ) + n) ((i : ℤ) - 1))
            • mu D a ((i : ℤ) - 3 - n) b) (M + n + 1)]
        -- bottom i=0 term: cbz(M+n,-1)=0
        rw [show cbz ((M : ℤ) + n) ((0 : ℕ) - 1 : ℤ) = 0 from cbz_apply_neg _ (by norm_num),
          mul_zero, zero_smul, add_zero]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [smul_smul]
        congr 2
        · push_cast; ring_nf
        · push_cast; ring_nf
      rw [hLHS, hPn, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hmode : ((i : ℤ) - 2 - ((n : ℤ) + 1)) = (i : ℤ) - 3 - n := by push_cast; ring
      rw [show ((M : ℤ) + ((n : ℤ) + 1)) = (M : ℤ) + n + 1 from by push_cast; ring, hmode,
        ← add_smul]
      congr 1
      have := pres_coeff_identity M n (i : ℤ)
      push_cast at this ⊢
      linear_combination this
    -- conclude: Pres(n+1) = (1/(n+2))•RHS ∈ O.
    have hne : ((n : ℂ) + 2) ≠ 0 := by
      have : ((n : ℂ) + 2) = ((n + 2 : ℕ) : ℂ) := by push_cast; ring
      rw [this]; exact_mod_cast Nat.succ_ne_zero (n + 1)
    have : higherCircle D M a b (n + 1)
        = (((n : ℂ) + 2)⁻¹) • (higherCircle D (M + 1) (translation D a) b n + ((M : ℂ) + n + 1) • higherCircle D M a b n) := by
      rw [← hsum, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ hG (Submodule.smul_mem _ _ hP))

end
end D5.S3.VertexAlgebra.Lattice.ActualZhuProduct
