/- GID: D5/S3/Combinatorics/Matroids/PuncturedCircuitInvariantFactors
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/PuncturedCircuitInvariantFactors
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Cyclic factors of the joint lifting obstruction after omitting one uniform basis. -/

module

public import D5.S3.Combinatorics.Matroids.PuncturedCircuitCoordinates
public import D5.S3.Combinatorics.Matroids.PuncturedCircuitSplit
public import D5.S3.Combinatorics.Matroids.PuncturedCircuitWeightBasis

/-! The exact joint lifting obstruction of a parallel expansion with one omitted core basis. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.PuncturedCircuitInvariantFactors

open Finset
open scoped Matroid
open PuncturedCircuitCoordinateCount PuncturedCircuitCoordinates PuncturedCircuitResiduePairs
open PuncturedCircuitSplit PuncturedCircuitWeightBasis UniformCircuitResidueForms
open RankTwoCircuitInvariantFactors (ResidueTorsion residueTorsion_equiv_zmod)
open ParallelCircuitObstruction (parallel_lifting_obstruction weightedCircuitResidues)
open JointCircuitLiftingObstruction (JointSaturatedImage JointImageInSaturation)
open RationalJointCircuitImage (RationalResidue)
open UniformCircuitBasis (sumCovector)
open Set.powersetCard (ofFinEmbEquiv)

set_option autoImplicit false

variable {I : Type*} [Fintype I] [LinearOrder I]

private lemma gcd_after_partition (weight : I → ℕ) (H : Finset I) (j : I) (hj : j ∈ H)
    (n : ℕ) (hn : n = ∑ i, weight i) :
    n.gcd (((H.erase j).gcd weight).gcd ((univ \ H).gcd weight)) = univ.gcd weight := by
  let tail := (univ : Finset I).erase j
  have hjoin : H.erase j ∪ (univ \ H) = tail := by
    ext i
    by_cases h : i ∈ H
    · simp [tail, h]
    · have hne : i ≠ j := fun he => h (he.symm ▸ hj)
      simp [tail, h, hne]
  have hgcd : tail.gcd weight = ((H.erase j).gcd weight).gcd ((univ \ H).gcd weight) := by
    rw [← hjoin, gcd_union]
    rfl
  have hsplit : n = weight j + ∑ i ∈ tail, weight i := by
    rw [hn]
    change (∑ i, weight i) = weight j + ∑ i ∈ (univ : Finset I).erase j, weight i
    rw [add_comm]
    exact (sum_erase_add _ weight (mem_univ j)).symm
  rw [← hgcd]
  apply Nat.dvd_antisymm
  · apply Finset.dvd_gcd
    intro i _
    by_cases he : i = j
    · subst i
      have hdTail : n.gcd (tail.gcd weight) ∣ ∑ i ∈ tail, weight i :=
        dvd_sum fun i hi => (Nat.gcd_dvd_right _ _).trans (gcd_dvd hi)
      have hd := Nat.dvd_sub (Nat.gcd_dvd_left n (tail.gcd weight)) hdTail
      have heq : n - (∑ i ∈ tail, weight i) = weight j := by
        rw [hsplit, Nat.add_sub_cancel]
      rwa [heq] at hd
    · exact (Nat.gcd_dvd_right _ _).trans (gcd_dvd (by simp [tail, he]))
  · exact Nat.dvd_gcd
      (hn ▸ dvd_sum (fun i _ => gcd_dvd (mem_univ i)))
      (Finset.dvd_gcd fun i _ => gcd_dvd (mem_univ i))

private def assembleFamilies {A B J G R Q : Type*} [AddCommGroup G] [AddCommGroup R]
    [AddCommGroup Q] :
    ((A → G) × (B → R) × ((J → G × R) × Q)) ≃ₗ[ℤ]
      ((A ⊕ J → G) × (B ⊕ J → R) × Q) where
  toFun f := (Sum.elim f.1 (fun j => (f.2.2.1 j).1),
    Sum.elim f.2.1 (fun j => (f.2.2.1 j).2), f.2.2.2)
  invFun f := (fun a => f.1 (Sum.inl a), (fun b => f.2.1 (Sum.inl b)),
    (fun j => (f.1 (Sum.inr j), f.2.1 (Sum.inr j))), f.2.2)
  left_inv f := rfl
  right_inv f := by
    apply Prod.ext
    · funext j
      cases j <;> rfl
    · apply Prod.ext
      · funext j
        cases j <;> rfl
      · rfl
  map_add' f g := by
    apply Prod.ext
    · funext j
      cases j <;> rfl
    · apply Prod.ext
      · funext j
        cases j <;> rfl
      · rfl
  map_smul' t f := by
    apply Prod.ext
    · funext j
      cases j <;> rfl
    · apply Prod.ext
      · funext j
        cases j <;> rfl
      · rfl

/-- Removing one basis from a rank-`r+2` uniform core exchanges one factor of
each uniform order for a factor of order the gcd of the total size and all
class sizes outside the omitted basis. -/
theorem punctured_lifting_obstruction_invariant_factors
    {V : Type*} [Fintype V] [LinearOrder V] {S : Matroid I} {H : Finset I} {r : ℕ}
    (hH : H.card = r + 2) (hr : r + 2 < Fintype.card I) (hground : S.E = Set.univ)
    (hbases : ∀ B : Finset I, S.IsBase (B : Set I) ↔ B.card = r + 2 ∧ B ≠ H)
    (p : V → I) (hsurj : Function.Surjective p) (horder : ∀ ⦃a b⦄, p a < p b → a < b) :
    let n := Fintype.card V
    let weight := fun i => (univ.filter fun x => p x = i).card
    let g := univ.gcd weight
    let q := n.gcd ((univ \ H).gcd weight)
    Nonempty ((JointSaturatedImage (S.comap p) ⧸ JointImageInSaturation (S.comap p)) ≃ₗ[ℤ]
      ((Fin (((Fintype.card I - 2).choose r) - 1) → ZMod g) ×
       (Fin (((Fintype.card I - 2).choose (r + 1)) - 1) → ZMod n) × ZMod q)) := by
  classical
  dsimp only
  let weight := fun i => (univ.filter fun x => p x = i).card
  let n := Fintype.card V
  let g := univ.gcd weight
  have hw (i : I) : 0 < weight i := by
    obtain ⟨x, hx⟩ := hsurj i
    exact card_pos.mpr ⟨x, mem_filter.mpr ⟨mem_univ _, hx⟩⟩
  obtain ⟨j, hj⟩ := card_pos.mp (show 0 < H.card by omega)
  let _ : Nonempty V := ⟨(hsurj j).choose⟩
  have hn : 0 < n := Fintype.card_pos
  have hind (i : I) : S.IsNonloop i := by
    apply Matroid.indep_singleton.mp
    rw [← coe_singleton, independent_iff hH hr hbases]
    exact ⟨by simp, fun he => by have := congrArg card he; simp at this; omega⟩
  obtain ⟨obstruction, _⟩ := parallel_lifting_obstruction hsurj horder (fun a => hind (p a))
  have hInside : (H.erase j).Nonempty := card_pos.mp (by rw [card_erase_of_mem hj]; omega)
  have hOutside : (univ \ H).Nonempty := by
    obtain ⟨i, _, hi⟩ := exists_mem_notMem_of_card_lt_card
      (show H.card < (univ : Finset I).card by simpa [hH] using hr)
    exact ⟨i, mem_sdiff.mpr ⟨mem_univ _, hi⟩⟩
  obtain ⟨b, z, w, hz, hwH, hpivot, hbasis, hzero⟩ :=
    exists_punctured_weight_basis H j hj hInside hOutside weight hw
  have hjz : j ≠ z := (mem_erase.mp hz).1.symm
  have hjw : j ≠ w := fun h => hwH (h ▸ hj)
  have hzw : z ≠ w := fun h => hwH (h ▸ mem_of_mem_erase hz)
  let u := (H.erase j).gcd weight
  let v := (univ \ H).gcd weight
  have hpos (A : Finset I) (hA : A.Nonempty) : 0 < A.gcd weight := by
    obtain ⟨i, hi⟩ := hA
    refine Nat.pos_of_ne_zero fun hz => (hw i).ne' ?_
    exact Nat.zero_dvd.mp (hz ▸ (gcd_dvd (f := weight) hi))
  let J₀ : PairIndex j z w r := ⟨⟨(H.erase j).erase z, by
      change ((H.erase j).erase z).card = r
      rw [card_erase_of_mem hz, card_erase_of_mem hj, hH]; omega⟩,
    fun h => notMem_erase j H (mem_of_mem_erase h), notMem_erase _ _,
    fun h => hwH (mem_of_mem_erase (mem_of_mem_erase h))⟩
  have hJ : insert z J₀.val.val = H.erase j := insert_erase hz
  let standard := Pi.basisFun ℤ I
  let a := sumCovector I
  let y := ∑ i, (univ.filter fun x => p x = i).card • standard i
  have ha (i : I) : a (standard i) = 1 := by simp [a, sumCovector, standard, Pi.basisFun]
  have hy : y = (fun i => (weight i : ℤ)) := by
    funext i
    simp [standard, y, weight, Pi.basisFun, Pi.single_apply, nsmul_eq_mul, mul_ite]
  have hcard : n = ∑ i, weight i := by
    simpa only [weight, card_univ] using
      (card_eq_sum_card_fiberwise (s := (univ : Finset V)) (t := (univ : Finset I))
        (f := p) (fun _ _ => mem_univ _))
  have hay : a y = (n : ℤ) := by
    change (∑ i, y i) = (n : ℤ)
    rw [hy, hcard, Nat.cast_sum]
  have hpivot' : standard j = b j := by
    rw [hpivot]
    simp [standard, Pi.basisFun]
  have hwy : y = (weight j : ℤ) • b j + (u • b z + v • b w) := by
    rw [hy, hbasis, add_assoc]
    simp only [natCast_zsmul]
    rfl
  let Tail : Set.powersetCard I (r + 1) := ⟨H.erase j, by
    change (H.erase j).card = r + 1
    rw [card_erase_of_mem hj, hH]; omega⟩
  let labels := ofFinEmbEquiv.symm Tail
  let e : Fin (r + 1) ≃ (H.erase j : Finset I) := Equiv.ofBijective
    (fun i => ⟨labels i, (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem Tail _).mp
      ⟨i, rfl⟩⟩)
    ⟨fun _ _ h => labels.injective (congrArg Subtype.val h),
      fun x => by
        obtain ⟨i, hi⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem Tail _).mpr x.prop
        exact ⟨i, Subtype.ext hi⟩⟩
  let Alt := (I → ℤ) [⋀^Fin (r + 1)]→ₗ[ℤ] RationalResidue
  have hcoordinate (f : Alt) :
      formCoordinates standard f (H.erase j) = 0 ↔ formCoordinates b f (insert z J₀.val.val) = 0 := by
    rw [hJ]
    have ht : (H.erase j).card = r + 1 := Tail.prop
    rw [formCoordinates, dite_eq_left ht, formCoordinates, dite_eq_left ht,
      basisFormEquiv_symm_apply, basisFormEquiv_symm_apply]
    change f (fun i => standard (labels i)) = 0 ↔ f (fun i => b (labels i)) = 0
    have he (i : Fin (r + 1)) : (e i : I) = labels i := rfl
    simpa only [standard, Pi.basisFun_apply, he] using hzero e f
  obtain ⟨pivot⟩ := punctured_pivot_forms_equiv p hH hr hground hbases standard a ha j hj
  let P := (((insertVector (N := RationalResidue) (n := r) (standard j)).ker ⊓
    (insertVector y).ker) ⊓ Submodule.torsionBy ℤ Alt (a y))
  let readout : P →ₗ[ℤ] RationalResidue := (coefficient standard (H.erase j)).comp P.subtype
  have contract (f : Alt) (hf : f.curryLeft (b j) = 0) :
      f.curryLeft y = f.curryLeft (u • b z + v • b w) := by
    rw [hwy, map_add, map_zsmul, hf, smul_zero, zero_add]
  let K := puncturedForms b j z w n u v J₀
  have hk (f : Alt) :
      ((f.curryLeft (standard j) = 0 ∧ f.curryLeft y = 0) ∧ a y • f = 0) ∧
      formCoordinates standard f (H.erase j) = 0 ↔ f ∈ K := by
    change _ ↔ ((f.curryLeft (b j) = 0 ∧ f.curryLeft (u • b z + v • b w) = 0) ∧
      (n : ℤ) • f = 0) ∧ formCoordinates b f (insert z J₀.val.val) = 0
    rw [hpivot', hay, hcoordinate]
    constructor
    · rintro ⟨⟨⟨hj', hy'⟩, hn'⟩, hz'⟩
      exact ⟨⟨⟨hj', (contract f hj').symm.trans hy'⟩, hn'⟩, hz'⟩
    · rintro ⟨⟨⟨hj', hy'⟩, hn'⟩, hz'⟩
      exact ⟨⟨⟨hj', (contract f hj').trans hy'⟩, hn'⟩, hz'⟩
  let adapt : readout.ker ≃ₗ[ℤ] K :=
    { toFun := fun f => ⟨f.val.val, (hk f.val.val).mp ⟨f.val.prop, f.prop⟩⟩
      invFun := fun f => ⟨⟨f.val, ((hk f.val).mpr f.prop).1⟩, ((hk f.val).mpr f.prop).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  obtain ⟨split⟩ := punctured_forms_equiv b j z w hjz hjw hzw n u v J₀
  obtain ⟨pairs⟩ := punctured_pairs_equiv J₀ n u v (hpos _ hInside) (hpos _ hOutside)
  let A := BothIndex j z w (r + 1) ⊕ {J : PairIndex j z w r // J ≠ J₀}
  let B := NeitherIndex j z w (r + 1) ⊕ {J : PairIndex j z w r // J ≠ J₀}
  have hcounts := card_after_omitting_pair j z w hjz hjw hzw r J₀
  have hg : n.gcd (u.gcd v) = g := gcd_after_partition weight H j hj n hcard
  have hq : 0 < n.gcd v := Nat.gcd_pos_of_pos_left v hn
  obtain ⟨eg⟩ := residueTorsion_equiv_zmod g (hpos _ ⟨j, mem_univ j⟩).ne'
  obtain ⟨en⟩ := residueTorsion_equiv_zmod n hn.ne'
  obtain ⟨eq⟩ := residueTorsion_equiv_zmod (n.gcd v) hq.ne'
  let eG := (LinearEquiv.ofEq _ _ (congrArg ResidueTorsion hg)).trans eg
  let finishG := (LinearEquiv.piCongrRight fun _ : A => eG).trans
    (LinearEquiv.piCongrLeft' ℤ (fun _ : A => ZMod g)
      (Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card.symm.trans hcounts.1)))
  let finishN := (LinearEquiv.piCongrRight fun _ : B => en).trans
    (LinearEquiv.piCongrLeft' ℤ (fun _ : B => ZMod n)
      (Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card.symm.trans hcounts.2)))
  let keepBoth := LinearEquiv.refl ℤ (BothIndex j z w (r + 1) → ResidueTorsion (n.gcd (u.gcd v)))
  let keepNeither := LinearEquiv.refl ℤ (NeitherIndex j z w (r + 1) → ResidueTorsion n)
  let pairFinish := keepBoth.prodCongr (keepNeither.prodCongr pairs)
  have pivot' : weightedCircuitResidues S p ≃ₗ[ℤ] readout.ker := pivot
  exact ⟨obstruction.trans (pivot'.trans (adapt.trans (split.trans (pairFinish.trans
    (assembleFamilies.trans (finishG.prodCongr (finishN.prodCongr eq)))))))⟩

end D5.S3.Combinatorics.Matroids.PuncturedCircuitInvariantFactors
