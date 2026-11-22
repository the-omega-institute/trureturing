/- GID: D5/S3/Combinatorics/Matroids/SparsePavingCircuitProduct
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/SparsePavingCircuitProduct
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Two omitted bases impose independent restrictions on the circuit residue module. -/

module

public import D5.S3.Combinatorics.Matroids.CircuitDifferenceBasis
public import D5.S3.Combinatorics.Matroids.CircuitOmittedFaceProduct
public import D5.S3.Combinatorics.Matroids.SparsePavingCircuitCoordinates

/-! The circuit-residue product identity for a sparse pair of omissions. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.SparsePavingCircuitProduct

open Finset CircuitDifferenceBasis CircuitOmittedFaceProduct SparsePavingCircuitCoordinates
open UniformCircuitResidueForms UniformCircuitBasis
open ParallelCircuitObstruction (weightedCircuitResidues)
open RationalJointCircuitImage (RationalResidue)
open Set.powersetCard (ofFinEmbEquiv)
open scoped Matroid

set_option autoImplicit false

variable {I : Type*} [Fintype I] [LinearOrder I]

/-- The product of the circuit residues with zero and two omitted bases is
linearly equivalent to the product for the two single omissions. -/
theorem sparse_paving_residue_product {V : Type*} [Fintype V] (p : V → I)
    (hsurj : Function.Surjective p) (H J : Finset I) {d : ℕ}
    (hd : 1 ≤ d) (hr : d + 2 < Fintype.card I)
    (hH : H.card = d + 2) (hJ : J.card = d + 2) (hsparse : (H ∩ J).card ≤ d)
    (M : Bool → Bool → Matroid I) (hground : ∀ i j, (M i j).E = Set.univ)
    (hbases : ∀ i j (B : Finset I), (M i j).IsBase (B : Set I) ↔ B.card = d + 2 ∧
      (i = true → B ≠ H) ∧ (j = true → B ≠ J)) :
    Nonempty (((weightedCircuitResidues (M false false) p) × (weightedCircuitResidues (M true true) p)) ≃ₗ[ℤ]
      ((weightedCircuitResidues (M true false) p) × (weightedCircuitResidues (M false true) p))) := by
  classical
  let weight (i : I) := (univ.filter fun v => p v = i).card
  have hweight (i : I) : 0 < weight i := by
    obtain ⟨v, hv⟩ := hsurj i
    exact card_pos.mpr ⟨v, mem_filter.mpr ⟨mem_univ _, hv⟩⟩
  obtain ⟨root, hroot, rep, hrep, c, w, hcroot, _, hsep, hcH, hcJ, hcoords, hpos⟩ :=
    exists_two_face_difference_basis H J hd hH hJ hsparse weight hweight
  let F : Set.powersetCard I (d + 1) := ⟨H.erase root, by
    change (H.erase root).card = d + 1
    rw [card_erase_of_mem hroot, hH]; omega⟩
  let G : Set.powersetCard I (d + 1) := ⟨J.erase rep, by
    change (J.erase rep).card = d + 1
    rw [card_erase_of_mem hrep, hJ]; omega⟩
  let standard := Pi.basisFun ℤ I
  let a := sumCovector I
  have ha (i : I) : a (standard i) = 1 := by simp [a, sumCovector, standard, Pi.basisFun_apply]
  let y := ∑ i, weight i • standard i
  have hy : y = fun i => (weight i : ℤ) := by
    funext i
    simp [standard, y, Pi.basisFun_apply, Pi.single_apply, nsmul_eq_mul, mul_ite]
  have hyc : y = ∑ i, w i • c i := by
    rw [hy]
    symm
    simpa only [hcoords, natCast_zsmul] using c.sum_equivFun (fun i => (weight i : ℤ))
  let K := ((insertVector (n := d) (N := RationalResidue) (c root)).ker ⊓
    (insertVector y).ker) ⊓ Submodule.torsionBy ℤ _ (a y)
  have hn : a y = (Fintype.card V : ℤ) := by
    have hcard : Fintype.card V = ∑ i, weight i := by
      simpa only [weight, card_univ] using
        (card_eq_sum_card_fiberwise (s := (univ : Finset V)) (t := (univ : Finset I))
          (f := p) (fun _ _ => mem_univ _))
    rw [hcard, hy, Nat.cast_sum]
    rfl
  let read (T : Set.powersetCard I (d + 1)) : K →ₗ[ℤ] RationalResidue :=
    (LinearMap.proj T).comp ((basisFormEquiv c).symm.toLinearMap.comp K.subtype)
  let P (i j : Bool) : Submodule ℤ K :=
    (if i then (read F).ker else ⊤) ⊓ (if j then (read G).ker else ⊤)
  have eqv (i j : Bool) : Nonempty (weightedCircuitResidues (M i j) p ≃ₗ[ℤ] ↥(P i j)) := by
    let holes : Set (Finset I) := {T | (i = true ∧ T = H) ∨ (j = true ∧ T = J)}
    have hsize (T : Finset I) (hT : T ∈ holes) : T.card = d + 2 := by
      rcases hT with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact hH
      · exact hJ
    have hs : holes.Pairwise (fun T U => (T ∩ U).card + 2 ≤ d + 2) := by
      intro T hT U hU hne
      rcases hT with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rcases hU with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact (hne rfl).elim
      · omega
      · rw [inter_comm]; omega
      · exact (hne rfl).elim
    have hB (T : Finset I) : (M i j).IsBase (T : Set I) ↔ T.card = d + 2 ∧ T ∉ holes := by
      rw [hbases]
      simp only [holes, Set.mem_ofPred_eq, not_or, not_and]
    let center (T : holes) := if T.val = H then root else rep
    have hHne : H ≠ J := by
      intro h
      have hh : (H ∩ J).card = d + 2 := by rw [← h, inter_self, hH]
      omega
    have hcenter (T : holes) : center T ∈ T.val := by
      obtain ⟨T, hT⟩ := T
      rcases hT with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · simpa [center] using hroot
      · simpa [center, hHne.symm] using hrep
    obtain ⟨e⟩ := sparse_paving_pivot_forms_equiv p hr hsize hs (hground i j) hB
      standard a ha root center hcenter
    let tuple (T : holes) (k : Fin (d + 1)) :=
      let S : Set.powersetCard I (d + 1) := ⟨T.val.erase (center T), by
        change (T.val.erase (center T)).card = d + 1
        rw [card_erase_of_mem (hcenter T), hsize T.val T.prop]; omega⟩
      standard (ofFinEmbEquiv.symm S k) - standard (center T)
    have coord (f : K) : (∀ T : holes, f.val (tuple T) = 0) ↔ f ∈ P i j := by
      have hcase (T : holes) :
          f.val (tuple T) = if T.val = H then read F f else read G f := by
        rw [show read F f = f.val (c ∘ ofFinEmbEquiv.symm F) from basisFormEquiv_symm_apply c f.val F,
          show read G f = f.val (c ∘ ofFinEmbEquiv.symm G) from basisFormEquiv_symm_apply c f.val G]
        obtain ⟨T, hT⟩ := T
        rcases hT with ⟨_, hTH⟩ | ⟨_, hTJ⟩
        · subst T
          simp only [ite_true]
          congr 1
          funext k
          have hk : ofFinEmbEquiv.symm F k ∈ H.erase root :=
            (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem F _).mp ⟨k, rfl⟩
          simpa [tuple, center, standard, Function.comp_def] using (hcH _ hk).symm
        · subst T
          simp only [ite_eq_right hHne.symm]
          congr 1
          funext k
          have hk : ofFinEmbEquiv.symm G k ∈ J.erase rep :=
            (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem G _).mp ⟨k, rfl⟩
          simpa [tuple, center, hHne.symm, standard, Function.comp_def] using (hcJ _ hk).symm
      have hp : f ∈ P i j ↔ (i = true → read F f = 0) ∧ (j = true → read G f = 0) := by
        cases i <;> cases j <;> simp [P, Submodule.mem_inf, LinearMap.mem_ker]
      rw [hp]
      constructor
      · intro h
        constructor
        · intro hi
          let T : holes := ⟨H, Or.inl ⟨hi, rfl⟩⟩
          have hh := h T
          rw [hcase T] at hh
          simpa [T] using hh
        · intro hj
          let T : holes := ⟨J, Or.inr ⟨hj, rfl⟩⟩
          have hh := h T
          rw [hcase T] at hh
          simpa [T, hHne.symm] using hh
      · intro h T
        rw [hcase T]
        obtain ⟨T, hT⟩ := T
        rcases hT with ⟨hi, rfl⟩ | ⟨hj, rfl⟩
        · simpa using h.1 hi
        · simpa only [ite_eq_right hHne.symm] using h.2 hj
    have hrootEq : standard root = c root := by rw [hcroot]; simp [standard]
    let ev (T : holes) : Submodule ℤ ((I → ℤ) [⋀^Fin (d + 1)]→ₗ[ℤ] RationalResidue) :=
      (show ((I → ℤ) [⋀^Fin (d + 1)]→ₗ[ℤ] RationalResidue) →ₗ[ℤ] RationalResidue from
        { toFun := fun f => f (tuple T), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }).ker
    let domain := K ⊓ ⨅ T, ev T
    let original := (((insertVector (n := d) (N := RationalResidue) (standard root)).ker ⊓
      (insertVector y).ker) ⊓ Submodule.torsionBy ℤ _ (a y)) ⊓ ⨅ T, ev T
    have hdomain : original = domain := by dsimp only [original, domain, K]; rw [hrootEq]
    have e' : weightedCircuitResidues (M i j) p ≃ₗ[ℤ] ↥domain :=
      e.trans (LinearEquiv.ofEq original domain hdomain)
    let go : ↥domain ≃ₗ[ℤ] ↥(P i j) :=
      { toFun := fun f => ⟨⟨f.val, f.prop.1⟩,
          (coord ⟨f.val, f.prop.1⟩).mp fun T => (Submodule.mem_iInf _).mp f.prop.2 T⟩
        invFun := fun f => ⟨f.val.val, ⟨f.val.prop,
          (Submodule.mem_iInf _).mpr ((coord f.val).mpr f.prop)⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact ⟨e'.trans go⟩
  obtain ⟨empty⟩ := eqv false false
  obtain ⟨first⟩ := eqv true false
  obtain ⟨second⟩ := eqv false true
  obtain ⟨pair⟩ := eqv true true
  have square : Nonempty ((↥K × ↥((read F).ker ⊓ (read G).ker)) ≃ₗ[ℤ]
      (↥(read F).ker × ↥(read G).ker)) := by
    let claim (v : I → ℤ) (n : ℤ) : Prop :=
      let P := ((insertVector (n := d) (N := RationalResidue) (c root)).ker ⊓
        (insertVector v).ker) ⊓ Submodule.torsionBy ℤ _ n
      let coef := fun T : Set.powersetCard I (d + 1) =>
        (LinearMap.proj T).comp ((basisFormEquiv c).symm.toLinearMap.comp P.subtype)
      Nonempty ((↥P × ↥((coef F).ker ⊓ (coef G).ker)) ≃ₗ[ℤ] (↥(coef F).ker × ↥(coef G).ker))
    change claim y (a y)
    rw [hn, hyc]
    exact pivoted_face_product c root w hpos (Fintype.card V) F G (notMem_erase root _) hsep
  obtain ⟨square⟩ := square
  let e₀ := (empty.trans (LinearEquiv.ofEq _ (⊤ : Submodule ℤ K) (by simp [P]))).trans Submodule.topEquiv
  let e₁ := first.trans (LinearEquiv.ofEq _ (read F).ker (by simp [P]))
  let e₂ := second.trans (LinearEquiv.ofEq _ (read G).ker (by simp [P]))
  exact ⟨(e₀.prodCongr pair).trans (square.trans (e₁.symm.prodCongr e₂.symm))⟩

end D5.S3.Combinatorics.Matroids.SparsePavingCircuitProduct
