/- GID: D5/S3/VertexAlgebra/LatticeBcGhostBrstVacuumSquare
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/LatticeBcGhostBrstVacuumSquare
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual BRST square annihilates every matter vector with ghost vacuum. -/

import D5.S3.VertexAlgebra.LatticeBcGhostBrstCAction
import D5.S3.VertexAlgebra.LatticeSugawaraVirasoro
import D5.S3.VertexAlgebra.BcGhostVacuum
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumSquare

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeSugawaraVirasoro
  LatticeBcGhostBrstCharge LatticeBcGhostBrstCAction BcGhostFockSupport
  BcGhostStressCurrent
open scoped BigOperators TensorProduct VertexOperator

noncomputable section

private def upper (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (u : Carrier D) : ℤ := max 1 (matterCutoff D H u)

private theorem matter_above (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (u : Carrier D) (index : ℤ)
    (hindex : upper D H u < index) : sugawaraMode D H index u = 0 := by
  apply VertexOperator.ncoeff_eq_zero_of_lt_order
  have hcut : matterCutoff D H u < index :=
    lt_of_le_of_lt (le_max_right _ _) hindex
  dsimp [matterCutoff] at hcut
  omega

private theorem c_annihilation (index : ℤ) (hindex : 2 ≤ index) :
    c (K := ℂ) index vacuum = 0 := by
  rw [c, if_neg (by omega : ¬ index ≤ 1)]
  exact annihilate_eq_zero vacuum _ (by simp [occupied, vacuum])

private theorem cc_swap (left right : ℤ) :
    c (K := ℂ) left (c right vacuum) = -c right (c left vacuum) := by
  apply eq_neg_of_add_eq_zero_left
  have hcar := congrArg (fun operator : Module.End ℂ (Fock ℂ) => operator vacuum)
    (c_c (K := ℂ) left right)
  simpa only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply] using hcar

private theorem A_vacuum (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (u : Carrier D) (index : ℤ) :
    A D H index (u ⊗ₜ[ℂ] vacuum) =
      sugawaraMode D H index u ⊗ₜ[ℂ] c (-index) vacuum := by
  by_cases hbranch : -1 ≤ index
  · have hstress := BcGhostVacuum.L_vacuum_annihilation (K := ℂ) index hbranch
    simp [A, N, M, C, G, hbranch, hstress]
  · have hghost := c_annihilation (-index) (by omega)
    simp [A, N, M, C, G, hbranch, hghost]

private theorem Q_vacuum (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (u : Carrier D) (top : ℤ)
    (hcut : ∀ index : ℤ, top < index → sugawaraMode D H index u = 0) :
    Q D H (u ⊗ₜ[ℂ] vacuum) =
      ∑ index ∈ Finset.Icc (-1) top,
        sugawaraMode D H index u ⊗ₜ[ℂ] c (-index) vacuum := by
  change (∑ᶠ index : ℤ, A D H index (u ⊗ₜ[ℂ] vacuum)) = _
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.Icc (-1) top) (by
    intro index hnonzero
    apply Finset.mem_Icc.mpr
    constructor
    · by_contra hlow
      have hghost := c_annihilation (-index) (by omega)
      exact hnonzero (by simp [A_vacuum, hghost])
    · by_contra hhigh
      exact hnonzero (by simp [A_vacuum, hcut index (by omega)]))]
  exact Finset.sum_congr rfl (fun index _ => A_vacuum D H u index)

private theorem cc_vacuum_outside (index mode : ℤ)
    (houtside : index < -1 ∨ 1 - mode < index) :
    c (K := ℂ) (-index) (c (index + mode) vacuum) = 0 := by
  rcases houtside with hlow | hhigh
  · rw [cc_swap, c_annihilation (-index) (by omega), map_zero, neg_zero]
  · rw [c_annihilation (index + mode) (by omega), map_zero]

private theorem V_vacuum (D : LatticeData) (u : Carrier D) (mode : ℤ) :
    V D mode (u ⊗ₜ[ℂ] vacuum) =
      ∑ index ∈ Finset.Icc (-1) (1 - mode),
        (2 * index + mode : ℂ) •
          (u ⊗ₜ[ℂ] c (-index) (c (index + mode) vacuum)) := by
  change (∑ᶠ index : ℤ,
    (2 * index + mode : ℂ) •
      ((C D (-index) * C D (index + mode)) (u ⊗ₜ[ℂ] vacuum))) = _
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.Icc (-1) (1 - mode)) (by
    intro index hnonzero
    by_contra houtside
    change index ∉ (Finset.Icc (-1) (1 - mode) : Finset ℤ) at houtside
    rw [Finset.mem_Icc] at houtside
    have hzero := cc_vacuum_outside index mode (by omega)
    exact hnonzero (by simp [C, Module.End.mul_apply, hzero]))]
  apply Finset.sum_congr rfl
  intro index hindex
  simp [C, Module.End.mul_apply]

private theorem second_matter_bound (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (u : Carrier D) (first : ℤ) (hfirst : first ∈ Finset.Icc (-1) (upper D H u))
    (second : ℤ) (hsecond : upper D H u + 1 < second) :
    sugawaraMode D H second (sugawaraMode D H first u) = 0 := by
  have hfirstlow := (Finset.mem_Icc.mp hfirst).1
  have hsum : upper D H u < second + first := by omega
  have hpositive : 1 ≤ upper D H u := le_max_left _ _
  have hnoncentral : second + first ≠ 0 := by omega
  have hvirasoro := congrArg (fun operator : Module.End ℂ (Carrier D) => operator u)
    (sugawaraMode_virasoro D H hHG hGH second first)
  simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply, RingHom.id_apply, if_neg hnoncentral,
    matter_above D H u second (by omega), map_zero,
    matter_above D H u (second + first) hsum, smul_zero, zero_smul,
    sub_zero, zero_add, add_zero]
    using hvirasoro

private theorem Q_c_vacuum (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (u : Carrier D)
    (first top : ℤ)
    (hcut : ∀ index : ℤ, top < index → sugawaraMode D H index u = 0) :
    Q D H (u ⊗ₜ[ℂ] c (-first) vacuum) =
      (∑ index ∈ Finset.Icc (-1) top,
        sugawaraMode D H index u ⊗ₜ[ℂ] c (-index) (c (-first) vacuum)) -
      (2 : ℂ)⁻¹ •
        (∑ index ∈ Finset.Icc (-1) (first + 1),
          (2 * index - first : ℂ) •
            (u ⊗ₜ[ℂ] c (-index) (c (index - first) vacuum))) := by
  have hcurrent := congrArg (fun operator : Module.End ℂ (State D) =>
      operator (u ⊗ₜ[ℂ] vacuum)) (c_action D H (-first))
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply] at hcurrent
  rw [Q_vacuum D H u top hcut, V_vacuum D u (-first)] at hcurrent
  simp only [C, TensorProduct.map_tmul, LinearMap.id_apply, map_sum,
    Int.cast_neg, sub_neg_eq_add, add_comm 1 first, ← sub_eq_add_neg] at hcurrent
  have hswap :
      (∑ index ∈ Finset.Icc (-1) top,
        sugawaraMode D H index u ⊗ₜ[ℂ]
          c (K := ℂ) (-first) (c (K := ℂ) (-index) (vacuum : Fock ℂ))) =
      -(∑ index ∈ Finset.Icc (-1) top,
        sugawaraMode D H index u ⊗ₜ[ℂ]
          c (K := ℂ) (-index) (c (K := ℂ) (-first) (vacuum : Fock ℂ))) := by
    calc
      _ = ∑ index ∈ Finset.Icc (-1) top,
          -(sugawaraMode D H index u ⊗ₜ[ℂ]
            c (K := ℂ) (-index) (c (K := ℂ) (-first) (vacuum : Fock ℂ))) := by
        apply Finset.sum_congr rfl
        intro index hindex
        rw [cc_swap (-first) (-index)]
        exact TensorProduct.tmul_neg (R := ℂ) (M := Carrier D) (P := Fock ℂ)
          (sugawaraMode D H index u)
          (c (K := ℂ) (-index) (c (K := ℂ) (-first) (vacuum : Fock ℂ)))
      _ = _ := by simp only [Finset.sum_neg_distrib]
  rw [hswap] at hcurrent
  have hsolution := eq_sub_of_add_eq hcurrent
  simpa only [neg_smul, neg_neg, sub_neg_eq_add, sub_eq_add_neg, add_comm] using hsolution

private def matterTerm (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (u : Carrier D) (left right : ℤ) : State D :=
  sugawaraMode D H left (sugawaraMode D H right u) ⊗ₜ[ℂ]
    c (-left) (c (-right) vacuum)

private def bracketTerm (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (u : Carrier D) (left right : ℤ) : State D :=
  ((left - right : ℤ) : ℂ) •
    (sugawaraMode D H (left + right) u ⊗ₜ[ℂ] c (-left) (c (-right) vacuum))

private def triangleTerm (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (u : Carrier D) (total left : ℤ) : State D :=
  ((2 * left - total : ℤ) : ℂ) •
    (sugawaraMode D H total u ⊗ₜ[ℂ] c (-left) (c (left - total) vacuum))

set_option maxHeartbeats 800000 in
private theorem square_expansion (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (u : Carrier D) :
    (Q D H * Q D H) (u ⊗ₜ[ℂ] vacuum) =
      (∑ left ∈ Finset.Icc (-1) (upper D H u + 1),
        ∑ right ∈ Finset.Icc (-1) (upper D H u + 1),
          matterTerm D H u left right) -
      (2 : ℂ)⁻¹ •
        (∑ total ∈ Finset.Icc (-1) (upper D H u),
          ∑ left ∈ Finset.Icc (-1) (total + 1), triangleTerm D H u total left) := by
  rw [Module.End.mul_apply, Q_vacuum D H u (upper D H u) (matter_above D H u), map_sum]
  have haction :
      (∑ first ∈ Finset.Icc (-1) (upper D H u),
        Q D H (sugawaraMode D H first u ⊗ₜ[ℂ] c (-first) vacuum)) =
      ∑ first ∈ Finset.Icc (-1) (upper D H u),
        ((∑ second ∈ Finset.Icc (-1) (upper D H u + 1),
            matterTerm D H u second first) -
          (2 : ℂ)⁻¹ •
            (∑ second ∈ Finset.Icc (-1) (first + 1),
              triangleTerm D H u first second)) := by
    apply Finset.sum_congr rfl
    intro first hfirst
    simpa only [matterTerm, triangleTerm, Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
      using Q_c_vacuum D H (sugawaraMode D H first u) first (upper D H u + 1)
        (second_matter_bound D H hHG hGH u first hfirst)
  rw [haction, Finset.sum_sub_distrib, ← Finset.smul_sum]
  apply congrArg (fun matterRow : State D => matterRow - (2 : ℂ)⁻¹ •
    (∑ total ∈ Finset.Icc (-1) (upper D H u),
      ∑ left ∈ Finset.Icc (-1) (total + 1), triangleTerm D H u total left))
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro left hleft
  apply Finset.sum_subset
  · intro right hright
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hright).1,
      by have hb := (Finset.mem_Icc.mp hright).2; omega⟩
  · intro right hright hnot
    have hrightlow := (Finset.mem_Icc.mp hright).1
    have hrightupper := (Finset.mem_Icc.mp hright).2
    have hhigh : upper D H u < right := by
      by_contra hle
      exact hnot (Finset.mem_Icc.mpr ⟨hrightlow, by omega⟩)
    simp [matterTerm, matter_above D H u right hhigh]

private theorem antisymmetrize (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (u : Carrier D) (indices : Finset ℤ) :
    (∑ left ∈ indices, ∑ right ∈ indices, matterTerm D H u left right) =
      (2 : ℂ)⁻¹ •
        (∑ left ∈ indices, ∑ right ∈ indices,
          ((sugawaraMode D H left * sugawaraMode D H right -
              sugawaraMode D H right * sugawaraMode D H left) u) ⊗ₜ[ℂ]
            c (-left) (c (-right) vacuum)) := by
  have hswap :
      (∑ left ∈ indices, ∑ right ∈ indices,
        sugawaraMode D H right (sugawaraMode D H left u) ⊗ₜ[ℂ]
          c (-left) (c (-right) vacuum)) =
      -(∑ left ∈ indices, ∑ right ∈ indices, matterTerm D H u left right) := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ left ∈ indices, ∑ right ∈ indices, -(matterTerm D H u left right) := by
        apply Finset.sum_congr rfl
        intro left hleft
        apply Finset.sum_congr rfl
        intro right hright
        rw [cc_swap]
        simp only [TensorProduct.tmul_neg, matterTerm]
      _ = _ := by simp only [Finset.sum_neg_distrib]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, TensorProduct.sub_tmul,
    Finset.sum_sub_distrib]
  rw [hswap]
  simp only [matterTerm]
  module

private theorem central_zero (D : LatticeData) (left right : ℤ)
    (hleft : -1 ≤ left) (hright : -1 ≤ right) :
    (if left + right = 0 then (D.rank : ℂ) / 12 * ((left : ℂ) ^ 3 - left) else 0) = 0 := by
  split_ifs with hsum
  · have hcases : left = -1 ∨ left = 0 ∨ left = 1 := by omega
    rcases hcases with hcase | hcase | hcase <;> norm_num [hcase]
  · rfl

private theorem matter_bracket (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (u : Carrier D) (left right : ℤ) (hleft : -1 ≤ left) (hright : -1 ≤ right) :
    ((sugawaraMode D H left * sugawaraMode D H right -
        sugawaraMode D H right * sugawaraMode D H left) u) ⊗ₜ[ℂ]
      c (-left) (c (-right) vacuum) = bracketTerm D H u left right := by
  rw [sugawaraMode_virasoro D H hHG hGH left right,
    central_zero D left right hleft hright, zero_smul, add_zero]
  simp [bracketTerm, TensorProduct.smul_tmul']

set_option maxHeartbeats 800000 in
private theorem square_matter_row (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (u : Carrier D) :
    (∑ left ∈ Finset.Icc (-1) (upper D H u + 1),
      ∑ right ∈ Finset.Icc (-1) (upper D H u + 1), matterTerm D H u left right) =
      (2 : ℂ)⁻¹ •
        (∑ left ∈ Finset.Icc (-1) (upper D H u + 1),
          ∑ right ∈ Finset.Icc (-1) (upper D H u + 1), bracketTerm D H u left right) := by
  rw [antisymmetrize]
  apply congrArg (fun matterRow : State D => (2 : ℂ)⁻¹ • matterRow)
  apply Finset.sum_congr rfl
  intro left hleft
  apply Finset.sum_congr rfl
  intro right hright
  exact matter_bracket D H hHG hGH u left right
    (Finset.mem_Icc.mp hleft).1 (Finset.mem_Icc.mp hright).1

private theorem bracket_outside_triangle (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (u : Carrier D)
    (left right : ℤ) (hleft : -1 ≤ left) (hright : -1 ≤ right)
    (houtside : left + right ∉ Finset.Icc (-1) (upper D H u)) :
    bracketTerm D H u left right = 0 := by
  by_cases hlow : left + right < -1
  · have hleftminus : left = -1 := by omega
    have hrightminus : right = -1 := by omega
    simp [bracketTerm, hleftminus, hrightminus]
  · have hhigh : upper D H u < left + right := by
      by_contra hle
      exact houtside (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    simp [bracketTerm, matter_above D H u (left + right) hhigh]

private theorem square_triangle_bijection (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (u : Carrier D) :
    (∑ left ∈ Finset.Icc (-1) (upper D H u + 1),
      ∑ right ∈ Finset.Icc (-1) (upper D H u + 1), bracketTerm D H u left right) =
      ∑ total ∈ Finset.Icc (-1) (upper D H u),
        ∑ left ∈ Finset.Icc (-1) (total + 1), triangleTerm D H u total left := by
  classical
  let square := (Finset.Icc (-1) (upper D H u + 1)).product
    (Finset.Icc (-1) (upper D H u + 1))
  let surviving := square.filter
    (fun pair : ℤ × ℤ => pair.1 + pair.2 ∈ Finset.Icc (-1) (upper D H u))
  let triangle : Finset (Σ _ : ℤ, ℤ) :=
    (Finset.Icc (-1) (upper D H u)).sigma (fun total => Finset.Icc (-1) (total + 1))
  have hremove :
      (∑ pair ∈ surviving, bracketTerm D H u pair.1 pair.2) =
      ∑ pair ∈ square, bracketTerm D H u pair.1 pair.2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro pair hpair hnot
    have hbounds := Finset.mem_product.mp hpair
    have hsum : pair.1 + pair.2 ∉ Finset.Icc (-1) (upper D H u) := by
      intro hsum
      exact hnot (Finset.mem_filter.mpr ⟨hpair, hsum⟩)
    exact bracket_outside_triangle D H u pair.1 pair.2
      (Finset.mem_Icc.mp hbounds.1).1 (Finset.mem_Icc.mp hbounds.2).1 hsum
  have hreindex :
      (∑ pair ∈ surviving, bracketTerm D H u pair.1 pair.2) =
      ∑ pair ∈ triangle, triangleTerm D H u pair.1 pair.2 := by
    refine Finset.sum_bij
      (fun pair _ => (⟨pair.1 + pair.2, pair.1⟩ : Σ _ : ℤ, ℤ)) ?_ ?_ ?_ ?_
    · intro pair hpair
      have hfiltered := Finset.mem_filter.mp hpair
      have hbounds := Finset.mem_product.mp hfiltered.1
      have hleft := Finset.mem_Icc.mp hbounds.1
      have hright := Finset.mem_Icc.mp hbounds.2
      refine Finset.mem_sigma.mpr ⟨hfiltered.2, ?_⟩
      change pair.1 ∈ Finset.Icc (-1) (pair.1 + pair.2 + 1)
      exact Finset.mem_Icc.mpr ⟨hleft.1, by omega⟩
    · intro first hfirst second hsecond hequal
      have hsum := congrArg (fun pair : Σ _ : ℤ, ℤ => pair.1) hequal
      have hleft := congrArg (fun pair : Σ _ : ℤ, ℤ => pair.2) hequal
      apply Prod.ext <;> dsimp at hsum hleft ⊢ <;> omega
    · intro pair hpair
      have hbounds := Finset.mem_sigma.mp hpair
      have htotal := Finset.mem_Icc.mp hbounds.1
      have hleft := Finset.mem_Icc.mp hbounds.2
      refine ⟨(pair.2, pair.1 - pair.2), ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_product.mpr
          constructor <;> apply Finset.mem_Icc.mpr <;> constructor <;> omega
        · have htotalEq : pair.2 + (pair.1 - pair.2) = pair.1 := by omega
          simpa only [htotalEq] using hbounds.1
      · apply Sigma.ext
        · dsimp
          omega
        · rfl
    · intro pair hpair
      have hcoefficient : pair.1 - pair.2 = 2 * pair.1 - (pair.1 + pair.2) := by omega
      have hmode : -(pair.2) = pair.1 - (pair.1 + pair.2) := by omega
      simp only [bracketTerm, triangleTerm, hcoefficient, hmode]
  calc
    _ = ∑ pair ∈ square, bracketTerm D H u pair.1 pair.2 := by
      symm
      exact Finset.sum_product _ _ _
    _ = ∑ pair ∈ surviving, bracketTerm D H u pair.1 pair.2 := hremove.symm
    _ = ∑ pair ∈ triangle, triangleTerm D H u pair.1 pair.2 := hreindex
    _ = _ := Finset.sum_sigma _ _ _

theorem vacuum_square (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (u : Carrier D) :
    (Q D H * Q D H) (u ⊗ₜ[ℂ] BcGhostFockSupport.vacuum) = 0 := by
  rw [square_expansion D H hHG hGH u, square_matter_row D H hHG hGH u,
    square_triangle_bijection D H u, sub_self]

#print axioms vacuum_square

end

end D5.S3.VertexAlgebra.LatticeBcGhostBrstVacuumSquare
