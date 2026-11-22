/- GID: D5/S3/Combinatorics/Matroids/SunflowerCircuitResidueProduct
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/SunflowerCircuitResidueProduct
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: The residue product for adding one omitted base to a common-element sunflower. -/

module

public import D5.S3.Combinatorics.Matroids.CircuitDifferenceBasis
public import D5.S3.Combinatorics.Matroids.SparsePavingCircuitCoordinates
public import D5.S3.Combinatorics.Matroids.SunflowerPivotProduct

/-! Residues in simultaneous difference coordinates around the common element. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.SunflowerCircuitResidueProduct

open Finset UniformCircuitResidueForms UniformCircuitBasis SparsePavingCircuitCoordinates
open CircuitDifferenceBasis SunflowerPivotProduct
open ParallelCircuitObstruction (weightedCircuitResidues)
open RationalJointCircuitImage (RationalResidue)
open Set.powersetCard (ofFinEmbEquiv)
open scoped Matroid

set_option autoImplicit false

private theorem pivot_residue_equiv {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V]
    (p : V → I) {d : ℕ} (hr : d + 2 < Fintype.card I)
    (holes : Set (Finset I)) (hs : ∀ H ∈ holes, H.card = d + 2)
    (hsparse : holes.Pairwise (fun H J => (H ∩ J).card + 2 ≤ d + 2))
    (root : I) (hroot : ∀ H ∈ holes, root ∈ H)
    (M : Matroid I) (hground : M.E = Set.univ)
    (hbases : ∀ T : Finset I, M.IsBase (T : Set I) ↔ T.card = d + 2 ∧ T ∉ holes)
    (c : Module.Basis I ℤ (I → ℤ)) (hcroot : c root = Pi.single root 1)
    (hc : ∀ i ≠ root, c i = Pi.single i 1 - Pi.single root 1) :
    let a := sumCovector I
    let weight (i : I) := (univ.filter fun v => p v = i).card
    let y := ∑ i, weight i • Pi.single i (1 : ℤ)
    let K := ((insertVector (n := d) (N := RationalResidue) (c root)).ker ⊓ (insertVector y).ker) ⊓
      Submodule.torsionBy ℤ _ (a y)
    let read := fun F : Set.powersetCard I (d + 1) =>
      (LinearMap.proj F).comp ((basisFormEquiv (N := RationalResidue) c).symm.toLinearMap.comp K.subtype)
    let face (T : holes) : Set.powersetCard I (d + 1) := ⟨T.val.erase root, by
      change (T.val.erase root).card = d + 1
      rw [card_erase_of_mem (hroot T.val T.prop), hs T.val T.prop]
      omega⟩
    Nonempty (weightedCircuitResidues M p ≃ₗ[ℤ]
      ↥(⨅ T : holes, (read (face T)).ker)) := by
  classical
  intro a weight y K read face
  let standard := Pi.basisFun ℤ I
  have hstandard (i : I) : standard i = Pi.single i (1 : ℤ) := by
    funext j
    simp [standard, Pi.basisFun_apply, Pi.single_apply, eq_comm]
  have ha (i : I) : a (standard i) = 1 := by simp [a, sumCovector, standard, Pi.basisFun_apply]
  obtain ⟨e⟩ := sparse_paving_pivot_forms_equiv p hr hs hsparse hground hbases
    standard a ha root (fun _ => root) (fun T => hroot T.val T.prop)
  let tuple (T : holes) (j : Fin (d + 1)) := c (ofFinEmbEquiv.symm (face T) j)
  let standardTuple (T : holes) (j : Fin (d + 1)) :=
    standard (ofFinEmbEquiv.symm (face T) j) - standard root
  let eval (v : Fin (d + 1) → I → ℤ) :
      ((I → ℤ) [⋀^Fin (d + 1)]→ₗ[ℤ] RationalResidue) →ₗ[ℤ] RationalResidue :=
    { toFun := fun f => f v, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let original := K ⊓ ⨅ T, (eval (tuple T)).ker
  have ht (T : holes) (j : Fin (d + 1)) :
      standard (ofFinEmbEquiv.symm (face T) j) - standard root = tuple T j := by
    have hj : ofFinEmbEquiv.symm (face T) j ∈ T.val.erase root :=
      (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem (face T) _).mp ⟨j, rfl⟩
    change standard (ofFinEmbEquiv.symm (face T) j) - standard root =
      c (ofFinEmbEquiv.symm (face T) j)
    rw [hc _ (ne_of_mem_erase hj), hstandard, hstandard]
  have e' : weightedCircuitResidues M p ≃ₗ[ℤ] ↥original := by
    let z := ∑ i, weight i • standard i
    let K₀ := ((insertVector (n := d) (N := RationalResidue) (standard root)).ker ⊓
      (insertVector z).ker) ⊓ Submodule.torsionBy ℤ _ (a z)
    let domain := K₀ ⊓ ⨅ T, (eval (standardTuple T)).ker
    have e₀ : weightedCircuitResidues M p ≃ₗ[ℤ] ↥domain := e
    have hK : K₀ = K := by simp only [K₀, z, K, y, hstandard, hcroot]
    have hmap : (⨅ T, (eval (standardTuple T)).ker) = ⨅ T, (eval (tuple T)).ker :=
      iInf_congr fun T => congrArg (fun v => (eval v).ker) (funext (ht T))
    have hdomain : domain = original := by simp only [domain, original, hK, hmap]
    exact e₀.trans (LinearEquiv.ofEq _ _ hdomain)
  have hread (f : K) (T : holes) : eval (tuple T) f.val = read (face T) f :=
    (basisFormEquiv_symm_apply c f.val (face T)).symm
  let move : ↥original ≃ₗ[ℤ] ↥(⨅ T : holes, (read (face T)).ker) :=
    { toFun := fun f => ⟨⟨f.val, f.prop.1⟩, (Submodule.mem_iInf _).mpr fun T =>
        (hread ⟨f.val, f.prop.1⟩ T).symm.trans ((Submodule.mem_iInf _).mp f.prop.2 T)⟩
      invFun := fun f => ⟨f.val.val, f.val.prop, (Submodule.mem_iInf _).mpr fun T =>
        (hread f.val T).trans ((Submodule.mem_iInf _).mp f.prop T)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact ⟨e'.trans move⟩

/-- The residue modules for a sunflower and the uniform core have the same
product as the residue modules for a subfamily and its one omitted petal. -/
theorem sunflower_residue_product {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V]
    (p : V → I) (hp : Function.Surjective p) {d : ℕ} (hd : 1 ≤ d)
    (hr : d + 2 < Fintype.card I) (root : I)
    (H : Finset I) (previous : Finset (Finset I)) (hnew : H ∉ previous)
    (hsize : ∀ T ∈ insert H previous, T.card = d + 2)
    (hroot : ∀ T ∈ insert H previous, root ∈ T)
    (hdisjoint : (↑(insert H previous) : Set (Finset I)).Pairwise
      (fun F G => Disjoint (F.erase root) (G.erase root)))
    (M : Bool → Bool → Matroid I) (hground : ∀ i j, (M i j).E = Set.univ)
    (hbases : ∀ i j (B : Finset I), (M i j).IsBase (B : Set I) ↔
      B.card = d + 2 ∧ (i = true → B ∉ previous) ∧ (j = true → B ≠ H)) :
    Nonempty ((weightedCircuitResidues (M false false) p × weightedCircuitResidues (M true true) p) ≃ₗ[ℤ]
      (weightedCircuitResidues (M true false) p × weightedCircuitResidues (M false true) p)) := by
  classical
  let family := insert H previous
  let H₀ : family := ⟨H, mem_insert_self _ _⟩
  let face (T : family) : Set.powersetCard I (d + 1) := ⟨T.val.erase root, by
    change (T.val.erase root).card = d + 1
    rw [card_erase_of_mem (hroot T.val T.prop), hsize T.val T.prop]; omega⟩
  have face_inj : Function.Injective face := by
    intro T U he
    apply Subtype.ext
    have h : T.val.erase root = U.val.erase root := congrArg Subtype.val he
    have hi : insert root (T.val.erase root) = insert root (U.val.erase root) := congrArg (insert root) h
    rwa [insert_erase (hroot T.val T.prop), insert_erase (hroot U.val U.prop)] at hi
  let oldFaces := previous.attach.image (fun T => face ⟨T.val, mem_insert_of_mem T.prop⟩)
  have mem_oldFaces (F : Set.powersetCard I (d + 1)) :
      F ∈ oldFaces ↔ ∃ T : previous, face ⟨T.val, mem_insert_of_mem T.prop⟩ = F := by
    simp [oldFaces, mem_image]
  have freshFace : face H₀ ∉ oldFaces := by
    intro hf
    obtain ⟨T, he⟩ := (mem_oldFaces _).mp hf
    have h : T.val = H := congrArg Subtype.val (face_inj he)
    exact hnew (h ▸ T.prop)
  have face_pair : (↑(insert (face H₀) oldFaces) : Set (Set.powersetCard I (d + 1))).Pairwise
      (fun F G => Disjoint F.val G.val) := by
    intro F hF G hG hne
    have lift (U : Set.powersetCard I (d + 1)) (hU : U ∈ insert (face H₀) oldFaces) :
        ∃ T : family, face T = U := by
      rcases mem_insert.mp hU with rfl | hU
      · exact ⟨H₀, rfl⟩
      · obtain ⟨T, hT⟩ := (mem_oldFaces _).mp hU
        exact ⟨⟨T.val, mem_insert_of_mem T.prop⟩, hT⟩
    obtain ⟨T, rfl⟩ := lift F hF
    obtain ⟨U, rfl⟩ := lift G hG
    exact hdisjoint T.prop U.prop (fun he => hne (congrArg face (Subtype.ext he)))
  have hcard : (face H₀).val.card = d + 1 := (face H₀).prop
  obtain ⟨q, hq⟩ := card_pos.mp (show 0 < (face H₀).val.card by omega)
  have hqr : q ≠ root := ne_of_mem_erase hq
  obtain ⟨c, hcroot, hc, hcoords⟩ := exists_difference_basis {q} root q (by simp [Ne.symm hqr]) (by simp)
  have hc' (i : I) (hi : i ≠ root) : c i = Pi.single i 1 - Pi.single root 1 := by
    simpa using hc i hi
  let weight (i : I) := (univ.filter fun v => p v = i).card
  let w (i : I) := if i = root then ∑ j, weight j else weight i
  have weight_pos (i : I) : 0 < weight i := by
    obtain ⟨v, hv⟩ := hp i
    exact card_pos.mpr ⟨v, mem_filter.mpr ⟨mem_univ _, hv⟩⟩
  have w_pos (i : I) : 0 < w i := by
    by_cases hi : i = root
    · simp only [w, hi, ite_true]
      exact (weight_pos root).trans_le (single_le_sum (fun j _ => Nat.zero_le (weight j)) (mem_univ root))
    · simpa [w, hi] using weight_pos i
  let a := sumCovector I
  let y := ∑ i, weight i • Pi.single i (1 : ℤ)
  have hy (i : I) : y i = (weight i : ℤ) := by
    simp [y, Pi.single_apply, nsmul_eq_mul, mul_ite]
  have hyc : y = ∑ i, w i • c i := by
    have h (i : I) : c.equivFun y i = (w i : ℤ) := by
      rw [hcoords]
      simp only [hy, ← Nat.cast_sum, sum_singleton]
      by_cases hi : i = q
      · subst i
        simp [w]
      · simp [w, hi]
    simpa only [h, natCast_zsmul] using (c.sum_equivFun y).symm
  let K := ((insertVector (n := d) (N := RationalResidue) (c root)).ker ⊓ (insertVector y).ker) ⊓
    Submodule.torsionBy ℤ _ (a y)
  let read := fun F : Set.powersetCard I (d + 1) =>
    (LinearMap.proj F).comp ((basisFormEquiv (N := RationalResidue) c).symm.toLinearMap.comp K.subtype)
  let old := ⨅ F : oldFaces, (read F.val).ker
  let Q (i j : Bool) : Submodule ℤ K :=
    (if i then old else ⊤) ⊓ (if j then (read (face H₀)).ker else ⊤)
  have eqv (i j : Bool) : Nonempty (weightedCircuitResidues (M i j) p ≃ₗ[ℤ] ↥(Q i j)) := by
    let holes : Set (Finset I) := {T | (i = true ∧ T ∈ previous) ∨ (j = true ∧ T = H)}
    have hin (T : holes) : T.val ∈ family := by
      rcases T.prop with ⟨_, h⟩ | ⟨_, h⟩
      · exact mem_insert_of_mem h
      · simp [h, family]
    have hsparse : holes.Pairwise (fun T U => (T ∩ U).card + 2 ≤ d + 2) := by
      intro T hT U hU hne
      have hd' := hdisjoint (hin ⟨T, hT⟩) (hin ⟨U, hU⟩) hne
      have hsub : T ∩ U ⊆ {root} := by
        intro x hx
        by_contra h
        have hxr : x ≠ root := fun he => h (mem_singleton.mpr he)
        exact Finset.disjoint_left.mp hd' (mem_erase.mpr ⟨hxr, (mem_inter.mp hx).1⟩)
          (mem_erase.mpr ⟨hxr, (mem_inter.mp hx).2⟩)
      have hb := card_le_card hsub
      rw [card_singleton] at hb
      omega
    have hbase (T : Finset I) : (M i j).IsBase (T : Set I) ↔ T.card = d + 2 ∧ T ∉ holes := by
      rw [hbases]
      simp only [holes, Set.mem_ofPred_eq, not_or, not_and]
    obtain ⟨e⟩ := pivot_residue_equiv p hr holes (fun T hT => hsize T (hin ⟨T, hT⟩))
      hsparse root (fun T hT => hroot T (hin ⟨T, hT⟩)) (M i j) (hground i j) hbase c hcroot hc'
    let domain : Submodule ℤ K := ⨅ T : holes, (read (face ⟨T.val, hin T⟩)).ker
    have e' : weightedCircuitResidues (M i j) p ≃ₗ[ℤ] ↥domain := e
    have memQ (f : K) : f ∈ Q i j ↔
        (i = true → ∀ F : oldFaces, read F.val f = 0) ∧ (j = true → read (face H₀) f = 0) := by
      cases i <;> cases j <;> simp [Q, old, Submodule.mem_iInf, LinearMap.mem_ker]
    have hQ : domain = Q i j := by
      ext f
      rw [memQ]
      change (f ∈ ⨅ T : holes, (read (face ⟨T.val, hin T⟩)).ker) ↔ _
      simp only [Submodule.mem_iInf, LinearMap.mem_ker]
      constructor
      · intro h
        refine ⟨fun hi F => ?_, fun hj => ?_⟩
        · obtain ⟨T, hT⟩ := (mem_oldFaces F.val).mp F.prop
          exact hT ▸ h ⟨T.val, Or.inl ⟨hi, T.prop⟩⟩
        · exact h ⟨H, Or.inr ⟨hj, rfl⟩⟩
      · intro h T
        obtain ⟨T, hT⟩ := T
        rcases hT with ⟨hi, hT⟩ | ⟨hj, rfl⟩
        · exact h.1 hi ⟨face ⟨T, mem_insert_of_mem hT⟩, (mem_oldFaces _).mpr ⟨⟨T, hT⟩, rfl⟩⟩
        · exact h.2 hj
    exact ⟨e'.trans (LinearEquiv.ofEq _ _ hQ)⟩
  have square : Nonempty ((↥K × ↥(old ⊓ (read (face H₀)).ker)) ≃ₗ[ℤ] (↥old × ↥(read (face H₀)).ker)) := by
    let claim (z : I → ℤ) (n : ℤ) : Prop :=
      let P := ((insertVector (n := d) (N := RationalResidue) (c root)).ker ⊓ (insertVector z).ker) ⊓
        Submodule.torsionBy ℤ _ n
      let atFace := fun F : Set.powersetCard I (d + 1) =>
        (LinearMap.proj F).comp ((basisFormEquiv (N := RationalResidue) c).symm.toLinearMap.comp P.subtype)
      let base := ⨅ F : oldFaces, (atFace F.val).ker
      Nonempty ((↥P × ↥(base ⊓ (atFace (face H₀)).ker)) ≃ₗ[ℤ] (↥base × ↥(atFace (face H₀)).ker))
    change claim y (a y)
    generalize a y = n
    rw [hyc]
    exact sunflower_pivot_product hd c root w w_pos n (face H₀) oldFaces freshFace
      (by intro F hF; rcases mem_insert.mp hF with rfl | hF
          · exact notMem_erase _ _
          · obtain ⟨T, rfl⟩ := (mem_oldFaces _).mp hF
            exact notMem_erase _ _) face_pair
  obtain ⟨empty⟩ := eqv false false
  obtain ⟨prior⟩ := eqv true false
  obtain ⟨single⟩ := eqv false true
  obtain ⟨all⟩ := eqv true true
  obtain ⟨square⟩ := square
  let e₀ := (empty.trans (LinearEquiv.ofEq _ (⊤ : Submodule ℤ K) (by simp [Q]))).trans Submodule.topEquiv
  let e₁ := prior.trans (LinearEquiv.ofEq _ old (by simp [Q]))
  let e₂ := single.trans (LinearEquiv.ofEq _ (read (face H₀)).ker (by simp [Q]))
  exact ⟨(e₀.prodCongr all).trans (square.trans (e₁.symm.prodCongr e₂.symm))⟩

end D5.S3.Combinatorics.Matroids.SunflowerCircuitResidueProduct
