/- GID: D5/S3/VertexAlgebra/Sectors/LatticeCosetReconstruction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeCosetReconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite native normal-product transport of the transverse creation expansion. -/

import D5.S3.VertexAlgebra.Sectors.LatticeCosetInnerExpansion

/-! Coefficient reconstruction uses native statewise Laurent truncation.
The positive normal-product sum has a finite set of current modes, and each
of those modes has its own field cutoff. No common outer cutoff is assumed.
Native lattice-field conventions follow Bakalov--Kac, math/0402315v1, §4.1. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeCosetReconstruction

open LatticeGeneratingFieldLocality LatticeCosetCompression LatticeCosetTransverse
open LatticeCosetSeparation LatticeCosetCreationSeparation LatticeCosetInnerExpansion
open FieldNormalProduct MvPolynomial
open scoped BigOperators VertexOperator

noncomputable section

open private high_modes_finite map_finsum_linear from D5.S3.VertexAlgebra.Sectors.LatticeCosetFieldSeparation

private theorem finite_rows {V : Type} [AddCommGroup V]
    (f : ℕ → ℕ → V) (hf : Function.HasFiniteSupport (Function.uncurry f)) :
    Function.HasFiniteSupport (fun i => ∑ᶠ j, f i j) := by
  apply (hf.image Prod.fst).subset
  intro i hi
  by_contra hn
  apply hi
  apply finsum_eq_zero_of_forall_eq_zero
  intro j
  by_contra hj
  exact hn ⟨(i,j), hj, rfl⟩

private theorem finite_swap {V : Type} [AddCommGroup V]
    (f : ℕ → ℕ → V) (hf : Function.HasFiniteSupport (Function.uncurry f)) :
    (∑ᶠ i, ∑ᶠ j, f i j) = ∑ᶠ j, ∑ᶠ i, f i j := by
  have hg : Function.HasFiniteSupport (fun ij : ℕ × ℕ => f ij.2 ij.1) :=
    hf.comp_of_injective (Equiv.prodComm ℕ ℕ).injective
  have h₁ : (∑ᶠ ij : ℕ × ℕ, f ij.1 ij.2) = ∑ᶠ i, ∑ᶠ j, f i j :=
    finsum_curry (Function.uncurry f) hf
  have h₂ : (∑ᶠ ij : ℕ × ℕ, f ij.2 ij.1) = ∑ᶠ j, ∑ᶠ i, f i j :=
    finsum_curry (fun ij : ℕ × ℕ => f ij.2 ij.1) hg
  rw [← h₁, ← h₂]
  exact (finsum_comp_equiv (Equiv.prodComm ℕ ℕ)).symm

private theorem native_normal_separation {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (A F : VertexOperator ℂ W) (a f : VertexOperator ℂ V)
    (J : V →ₗ[ℂ] W) (K : ℕ → V →ₗ[ℂ] W)
    (hF : ∀ m g, ((F)[[m]]) (J g) = ∑ᶠ j : ℕ, K j (((f)[[m+j]]) g))
    (hneg : ∀ (i j : ℕ) g, ((A)[[-(i : ℤ)-1]]) (K j g) =
      K j (((a)[[-(i : ℤ)-1]]) g))
    (hpos : ∀ (i : ℕ) g, ((A)[[i]]) (J g) = J (((a)[[i]]) g))
    (m : ℤ) (g : V) :
    (((normalMinusOne A F).1)[[m]]) (J g) =
      ∑ᶠ j : ℕ, K j ((((normalMinusOne a f).1)[[m+j]]) g) := by
  classical
  let neg := fun i j : ℕ => K j (((a)[[-(i : ℤ)-1]]) (((f)[[m+i+j]]) g))
  let pos := fun i j : ℕ => K j (((f)[[m+j-i-1]]) (((a)[[i]]) g))
  have hn : Function.HasFiniteSupport (Function.uncurry neg) := by
    let N : ℕ := (-((HahnModule.of ℂ).symm (f g)).order-m).toNat
    have hz (i j : ℕ) (hij : N ≤ i+j) : ((f)[[m+i+j]]) g = 0 := by
      apply VertexOperator.ncoeff_eq_zero_of_lt_order
      dsimp only [N] at hij
      omega
    apply ((Finset.range N).finite_toSet.prod (Finset.range N).finite_toSet).subset
    rintro ⟨i,j⟩ hij
    change neg i j ≠ 0 at hij
    have hlt : i+j < N := by
      by_contra h
      exact hij (by simp only [neg, hz i j (by omega), map_zero])
    exact ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
  have hp : Function.HasFiniteSupport (Function.uncurry pos) := by
    have hi : Function.HasFiniteSupport (fun i : ℕ => ((a)[[i]]) g) := by
      simpa only [zero_add, LinearMap.id_apply] using
        high_modes_finite a (fun _ => LinearMap.id) 0 g
    have hj (i : ℕ) : Function.HasFiniteSupport (fun j : ℕ =>
        K j (((f)[[m-(i : ℤ)-1+j]]) (((a)[[i]]) g))) :=
      high_modes_finite f K (m-i-1) (((a)[[i]]) g)
    apply (hi.biUnion (fun i _ => (hj i).image (fun j : ℕ => (i,j)))).subset
    rintro ⟨i,j⟩ hij
    change pos i j ≠ 0 at hij
    have hai : ((a)[[i]]) g ≠ 0 := by
      intro hz
      exact hij (by simp only [pos, hz, map_zero])
    have hfj : K j (((f)[[m-(i : ℤ)-1+j]]) (((a)[[i]]) g)) ≠ 0 := by
      simpa only [pos, show m+(j : ℤ)-i-1 = m-i-1+j by omega] using hij
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hai, j, hfj, rfl⟩⟩
  have hleft : (∑ᶠ i : ℕ, ((A)[[-(i : ℤ)-1]]) (((F)[[m+i]]) (J g))) =
      ∑ᶠ j : ℕ, K j (∑ᶠ i : ℕ, ((a)[[-(i : ℤ)-1]]) (((f)[[m+j+i]]) g)) := by
    calc
      _ = ∑ᶠ i : ℕ, ∑ᶠ j : ℕ, neg i j := by
        apply finsum_congr
        intro i
        rw [hF, map_finsum_linear ((A)[[-(i : ℤ)-1]]) _
          (high_modes_finite f K (m+i) g)]
        apply finsum_congr
        intro j
        rw [hneg]
      _ = ∑ᶠ j : ℕ, ∑ᶠ i : ℕ, neg i j := finite_swap neg hn
      _ = _ := by
        apply finsum_congr
        intro j
        rw [map_finsum_linear (K j) _
          (high_modes_finite f (fun i => ((a)[[-(i : ℤ)-1]])) (m+j) g)]
        apply finsum_congr
        intro i
        dsimp only [neg]
        rw [show m+(i : ℤ)+j = m+j+i by omega]
  have hright : (∑ᶠ i : ℕ, ((F)[[m-i-1]]) (((A)[[i]]) (J g))) =
      ∑ᶠ j : ℕ, K j (∑ᶠ i : ℕ, ((f)[[m+j-i-1]]) (((a)[[i]]) g)) := by
    calc
      _ = ∑ᶠ i : ℕ, ∑ᶠ j : ℕ, pos i j := by
        apply finsum_congr
        intro i
        rw [hpos, hF]
        apply finsum_congr
        intro j
        dsimp only [pos]
        rw [show m-(i : ℤ)-1+j = m+j-i-1 by omega]
      _ = ∑ᶠ j : ℕ, ∑ᶠ i : ℕ, pos i j := finite_swap pos hp
      _ = _ := by
        apply finsum_congr
        intro j
        rw [map_finsum_linear (K j) _ (by
          simpa only [zero_add] using high_modes_finite a
            (fun i => ((f)[[m+j-i-1]])) 0 g)]
  have hn' : Function.HasFiniteSupport (fun j =>
      K j (∑ᶠ i : ℕ, ((a)[[-(i : ℤ)-1]]) (((f)[[m+j+i]]) g))) := by
    have h := finite_rows (fun j i => neg i j)
      (hn.comp_of_injective (Equiv.prodComm ℕ ℕ).injective)
    convert h using 1
    funext j
    rw [map_finsum_linear (K j) _
      (high_modes_finite f (fun i => ((a)[[-(i : ℤ)-1]])) (m+j) g)]
    apply finsum_congr
    intro i
    dsimp only [neg]
    rw [show m+(i : ℤ)+j = m+j+i by omega]
  have hp' : Function.HasFiniteSupport (fun j =>
      K j (∑ᶠ i : ℕ, ((f)[[m+j-i-1]]) (((a)[[i]]) g))) := by
    have h := finite_rows (fun j i => pos i j)
      (hp.comp_of_injective (Equiv.prodComm ℕ ℕ).injective)
    convert h using 1
    funext j
    rw [map_finsum_linear (K j) _ (by
      simpa only [zero_add] using high_modes_finite a (fun i => ((f)[[m+j-i-1]])) 0 g)]
  rw [(normalMinusOne A F).2, hleft, hright, ← finsum_add_distrib hn' hp']
  apply finsum_congr
  intro j
  rw [← map_add, (normalMinusOne a f).2]

end
end D5.S3.VertexAlgebra.LatticeCosetReconstruction
