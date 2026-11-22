/- GID: D5/S3/Combinatorics/Matroids/PrivatePairCircuitInvariantFactors
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/PrivatePairCircuitInvariantFactors
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Independent cyclic factor replacement for omissions with private pairs and a common pivot. -/

import D5.S3.Combinatorics.Matroids.PrivatePairCircuitResidueProduct
import D5.S3.Combinatorics.Matroids.PuncturedCircuitInvariantFactors
import D5.S3.Combinatorics.Matroids.UniformCircuitInvariantFactors
import D5.S3.FiniteGroups.Modules.FiniteModuleProductCancellation

/-! Cyclic factors of the lifting obstruction for overlapping omissions with private pairs. -/

namespace D5.S3.Combinatorics.Matroids.PrivatePairCircuitInvariantFactors

open Finset SparsePavingCircuitCoordinates PrivatePairCircuitResidueProduct PrivatePairOmissionFamily
open PuncturedCircuitInvariantFactors UniformCircuitInvariantFactors
open ParallelCircuitObstruction (parallel_lifting_obstruction weightedCircuitResidues)
open JointCircuitLiftingObstruction (JointSaturatedImage JointImageInSaturation)
open D5.S3.FiniteGroups.FiniteModuleProductCancellation (finite_prod_cancel)
open scoped Matroid

set_option autoImplicit false

private abbrev Families (X Y : Type*) (a b : ℕ) := (Fin a → X) × (Fin b → Y)

private theorem interior_choose_ge (k j : ℕ) (hj : 0 < j) (hjk : j < k) :
    k ≤ k.choose j := by
  induction k generalizing j with
  | zero => omega
  | succ k ih =>
      by_cases hfirst : j = 1
      · simp [hfirst]
      by_cases hlast : j = k
      · subst j
        rw [Nat.choose_succ_self_right]
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
      rw [Nat.choose_succ_succ]
      have hp : 0 < k.choose j := Nat.choose_pos (by omega)
      have hge : k ≤ k.choose j.succ := ih j.succ (by omega) (by omega)
      omega

private theorem family_multiplicity_bounds {k d : ℕ} {family : Finset (Finset (Fin (k + 2)))}
    (hd : 1 ≤ d) (hr : d < k) (hsize : ∀ H ∈ family, H.card = d + 2)
    (hprivate : HasPrivatePairs family) :
    family.card ≤ k.choose d ∧ family.card ≤ k.choose (d + 1) := by
  classical
  by_cases hempty : family = ∅
  · simp [hempty]
  obtain ⟨H, hH⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  let rest := family.erase H
  have privatePoint (G : rest) : ∃ i ∈ G.val, ∀ U ∈ family, U ≠ G.val → i ∉ U := by
    obtain ⟨i, hi, _, _, _, h⟩ := hprivate G.val (mem_of_mem_erase G.prop)
    exact ⟨i, hi, fun U hU hne => (h U hU hne).1⟩
  choose point hpoint hout using privatePoint
  let target := (univ : Finset (Fin (k + 2))) \ H
  let inject : rest → target := fun G =>
    ⟨point G, mem_sdiff.mpr ⟨mem_univ _, hout G H hH (ne_of_mem_erase G.prop).symm⟩⟩
  have hinj : Function.Injective inject := by
    intro G U he
    apply Subtype.ext
    by_contra hne
    have h : point G = point U := congrArg Subtype.val he
    exact hout G U.val (mem_of_mem_erase U.prop) (fun he' => hne he'.symm)
      (h ▸ hpoint U)
  have hle := Fintype.card_le_of_injective inject hinj
  simp only [Fintype.card_coe] at hle
  have hrest : rest.card = family.card - 1 := card_erase_of_mem hH
  have htarget : target.card = k - d := by
    simp [target, card_sdiff_of_subset (subset_univ H), hsize H hH]
  have hpos : 0 < family.card := card_pos.mpr ⟨H, hH⟩
  have hcard : family.card ≤ k := by omega
  refine ⟨hcard.trans (interior_choose_ge k d (by omega) hr), ?_⟩
  by_cases hlast : d + 1 = k
  · rw [hlast, Nat.choose_self]
    by_contra hn
    have hrestpos : 0 < rest.card := by omega
    obtain ⟨G, hG⟩ := card_pos.mp hrestpos
    have hG' := mem_erase.mp hG
    obtain ⟨i, hi, j, hj, hij, houtside⟩ := hprivate G hG'.2
    have hiH := (houtside H hH hG'.1.symm).1
    have hjH := (houtside H hH hG'.1.symm).2
    have hsub : ({i, j} : Finset (Fin (k + 2))) ⊆ target := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact mem_sdiff.mpr ⟨mem_univ _, hiH⟩
      · exact mem_sdiff.mpr ⟨mem_univ _, hjH⟩
    have hcardTwo := card_le_card hsub
    simp [hij, htarget] at hcardTwo
    omega
  · exact hcard.trans (interior_choose_ge k (d + 1) (by omega) (by omega))

private def splitRow {W : Type*} [AddCommGroup W] {m : ℕ} (hm : 0 < m) :
    (Fin m → W) ≃ₗ[ℤ] (Fin (m - 1) → W) × W :=
  (LinearEquiv.piCongrLeft' ℤ (fun _ : Fin m => W) (finCongr (by omega))).trans
    ((Fin.consLinearEquiv ℤ (fun _ : Fin (m - 1 + 1) => W)).symm.trans
      (LinearEquiv.prodComm ℤ W (Fin (m - 1) → W)))

private def splitFamilies {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Families X Y a b ≃ₗ[ℤ] Families X Y (a - 1) (b - 1) × (X × Y) :=
  ((splitRow (W := X) ha).prodCongr (splitRow (W := Y) hb)).trans
    (LinearEquiv.prodProdProdComm ℤ _ _ _ _)

private theorem cancelStep {X Y A B T : Type*} [AddCommGroup X] [AddCommGroup Y]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup T]
    [Finite X] [Finite Y] [Finite A] [Finite B] {a b t : ℕ} (ha : t < a) (hb : t < b)
    (e : (Families X Y a b × T) ≃ₗ[ℤ]
      ((Families X Y (a - t) (b - t) × A) × (Families X Y (a - 1) (b - 1) × B))) :
    Nonempty (T ≃ₗ[ℤ] (Families X Y (a - t - 1) (b - t - 1) × (A × B))) := by
  let C := Families X Y (a - t - 1) (b - t - 1)
  let D := Families X Y (a - 1) (b - 1)
  let reorder : (((C × (X × Y)) × A) × (D × B)) ≃ₗ[ℤ] ((C × (A × B)) × (D × (X × Y))) :=
    { toFun := fun x => ((x.1.1.1, x.1.2, x.2.2), x.2.1, x.1.1.2)
      invFun := fun x => (((x.1.1, x.2.2), x.1.2.1), x.2.1, x.1.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let splitOld := splitFamilies (X := X) (Y := Y)
    (show 0 < a - t by omega) (show 0 < b - t by omega)
  let splitFull := splitFamilies (X := X) (Y := Y) (show 0 < a by omega) (show 0 < b by omega)
  let _ : Finite T := Finite.of_injective (fun x : T => e (0, x))
    (fun _ _ h => (Prod.mk.inj (e.injective h)).2)
  exact finite_prod_cancel ((LinearEquiv.prodComm ℤ T _).trans
    (e.trans (((splitOld.prodCongr (LinearEquiv.refl ℤ A)).prodCongr (LinearEquiv.refl ℤ _)).trans
      (reorder.trans ((LinearEquiv.refl ℤ (C × (A × B))).prodCongr splitFull.symm)))))

private def insertPetal {I : Type*} [DecidableEq I] (q : Finset I → ℕ)
    {H : Finset I} {old : Finset (Finset I)} (hfresh : H ∉ old) :
    ((∀ T : old, ZMod (q T.val)) × ZMod (q H)) ≃ₗ[ℤ] (∀ T : ↥(insert H old), ZMod (q T.val)) := by
  classical
  let singleton := ({H} : Set (Finset I))
  let single : (∀ T : singleton, ZMod (q T.val)) ≃ₗ[ℤ] ZMod (q H) :=
    { toFun := fun f => f ⟨H, rfl⟩
      invFun := fun z T => by rw [Set.mem_singleton_iff.mp T.prop]; exact z
      left_inv := by
        intro f
        funext T
        have h : T = ⟨H, rfl⟩ := Subtype.ext (Set.mem_singleton_iff.mp T.prop)
        subst T
        rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hdis : Disjoint (↑old : Set (Finset I)) singleton := by
    simpa [singleton, Set.disjoint_singleton_right] using hfresh
  let index : old ⊕ singleton ≃ ↥(insert H old) := (Equiv.Set.union hdis).symm.trans
    (Set.equivOfEq (by ext T; simp [singleton]))
  let ξ (T : ↥(insert H old)) := ZMod (q T.val)
  exact ((LinearEquiv.refl ℤ (∀ T : old, ZMod (q T.val))).prodCongr single.symm).trans
    ((LinearEquiv.sumPiEquivProdPi ℤ old singleton (fun T => ξ (index T))).symm.trans
      (LinearEquiv.piCongrLeft ℤ ξ index))

/-- For omissions with a common element and private pairs, each petal removes one
copy of each uniform cyclic order and adds its own gcd factor. -/
theorem private_pair_lifting_obstruction_invariant_factors {V : Type*} [Fintype V] [LinearOrder V]
    {k d : ℕ} {S : Matroid (Fin (k + 2))} (hd : 1 ≤ d) (hr : d < k)
    (root : Fin (k + 2)) (family : Finset (Finset (Fin (k + 2))))
    (hsize : ∀ H ∈ family, H.card = d + 2) (hroot : ∀ H ∈ family, root ∈ H)
    (hprivate : HasPrivatePairs family)
    (hbases : ∀ B : Finset (Fin (k + 2)), S.IsBase (B : Set (Fin (k + 2))) ↔
      B.card = d + 2 ∧ B ∉ family)
    (p : V → Fin (k + 2)) (hp : Function.Surjective p) (horder : ∀ ⦃x y⦄, p x < p y → x < y) :
    let n := Fintype.card V
    let weight (i : Fin (k + 2)) := (univ.filter fun v => p v = i).card
    let g := univ.gcd weight
    let q (H : Finset (Fin (k + 2))) := n.gcd ((univ \ H).gcd weight)
    Nonempty ((JointSaturatedImage (S.comap p) ⧸ JointImageInSaturation (S.comap p)) ≃ₗ[ℤ]
      (((Fin (k.choose d - family.card) → ZMod g) × (Fin (k.choose (d + 1) - family.card) → ZMod n)) ×
        (∀ T : family, ZMod (q T.val)))) := by
  classical
  intro n weight g q
  let I := Fin (k + 2)
  let obs (M : Matroid I) := JointSaturatedImage (M.comap p) ⧸ JointImageInSaturation (M.comap p)
  let α := k.choose d
  let β := k.choose (d + 1)
  obtain ⟨ha, hb⟩ := family_multiplicity_bounds hd hr hsize hprivate
  have hr' : d + 2 < Fintype.card I := by simp [I]; omega
  have hk : Fintype.card (Fin (k + 2)) - 2 = k := by simp
  have sparse (A : Finset (Finset I)) (hA : A ⊆ family) :
      (↑A : Set (Finset I)).Pairwise (fun H J => (H ∩ J).card + 2 ≤ d + 2) := by
    intro F hF G hG hne
    have bound := hprivate.inter_card_add_two_le (hA hF) (hA hG) hne
    exact bound.trans (hsize F (hA hF)).le
  have makeCore (A : Finset (Finset I)) (hA : A ⊆ family) : ∃ M : Matroid I, M.E = Set.univ ∧
      ∀ B : Finset I, M.IsBase (B : Set I) ↔ B.card = d + 2 ∧ B ∉ A :=
    exists_sparse_paving_core (holes := (↑A : Set (Finset I))) hr' (by omega) (sparse A hA)
  let _ : Nonempty V := ⟨(hp 0).choose⟩
  have hn : 0 < n := Fintype.card_pos
  have hg : 0 < g := by
    obtain ⟨v, hv⟩ := hp 0
    have hw : 0 < weight 0 := card_pos.mpr ⟨v, mem_filter.mpr ⟨mem_univ _, hv⟩⟩
    exact Nat.pos_of_ne_zero fun h => hw.ne' (Nat.zero_dvd.mp (h ▸ gcd_dvd (f := weight) (mem_univ 0)))
  let _ : NeZero n := ⟨hn.ne'⟩
  let _ : NeZero g := ⟨hg.ne'⟩
  let _ (H : Finset I) : NeZero (q H) := ⟨(Nat.gcd_pos_of_pos_left _ hn).ne'⟩
  have lift (A : Finset (Finset I)) (hA : A ⊆ family) {M : Matroid I}
      (hM : ∀ B : Finset I, M.IsBase (B : Set I) ↔ B.card = d + 2 ∧ B ∉ A) :
      Nonempty (obs M ≃ₗ[ℤ] weightedCircuitResidues M p) := by
    have nonloop (i : I) : M.IsNonloop i := by
      apply Matroid.indep_singleton.mp
      rw [← coe_singleton, indep_iff_card_and_allowed (holes := (↑A : Set (Finset I))) hr'
        (fun H hH => hsize H (hA hH)) (sparse A hA) hM]
      have hcard : ({i} : Finset I).card < d + 2 := by simp
      exact ⟨hcard.le, fun h => (hsize _ (hA h)).not_lt hcard⟩
    obtain ⟨e, _⟩ := parallel_lifting_obstruction hp horder (fun v => nonloop (p v))
    exact ⟨e⟩
  obtain ⟨uniform, huniform, hbaseUniform⟩ := makeCore ∅ (empty_subset _)
  obtain ⟨full⟩ := uniform_lifting_obstruction_invariant_factors
    (fun B => by simpa using hbaseUniform B) p hp horder
  have uniformFactors : obs uniform ≃ₗ[ℤ] Families (ZMod g) (ZMod n) α β := full
  obtain ⟨liftUniform⟩ := lift ∅ (empty_subset _) hbaseUniform
  let factors (A : Finset (Finset I)) :=
    Families (ZMod g) (ZMod n) (α - A.card) (β - A.card) × (∀ H : A, ZMod (q H.val))
  have calcFactors (A : Finset (Finset I)) (hA : A ⊆ family) (N : Matroid I)
      (hBase : ∀ B : Finset I, N.IsBase (B : Set I) ↔ B.card = d + 2 ∧ B ∉ A) :
      Nonempty (obs N ≃ₗ[ℤ] factors A) := by
    induction A using Finset.induction_on generalizing N with
    | empty =>
      obtain ⟨e⟩ := uniform_lifting_obstruction_invariant_factors
        (fun B => by simpa using hBase B) p hp horder
      have trivialFactor : (∀ H : (∅ : Finset (Finset I)), ZMod (q H.val)) ≃ₗ[ℤ] PUnit.{1} :=
        LinearEquiv.ofSubsingleton _ _
      let drop : (Families (ZMod g) (ZMod n) α β × PUnit.{1}) ≃ₗ[ℤ]
          Families (ZMod g) (ZMod n) α β :=
        LinearEquiv.prodUnique
      let finish := drop.symm.trans
        ((LinearEquiv.refl ℤ _).prodCongr trivialFactor.symm)
      have base : obs N ≃ₗ[ℤ] Families (ZMod g) (ZMod n) α β := e
      exact ⟨base.trans finish⟩
    | @insert H old fresh ih =>
      have hold : old ⊆ family := subset_trans (subset_insert _ _) hA
      have hH : H ∈ family := hA (mem_insert_self _ _)
      have hs : ({H} : Finset (Finset I)) ⊆ family := singleton_subset_iff.mpr hH
      obtain ⟨prior, hprior, hbasePrior⟩ := makeCore old hold
      obtain ⟨single, hsingle, hbaseSingle⟩ := makeCore {H} hs
      obtain ⟨priorFactors⟩ := ih hold prior hbasePrior
      have hbaseOne (B : Finset I) : single.IsBase (B : Set I) ↔ B.card = d + 2 ∧ B ≠ H := by
        simpa only [mem_singleton] using hbaseSingle B
      obtain ⟨one⟩ := punctured_lifting_obstruction_invariant_factors
        (hsize H hH) hr' hsingle hbaseOne p hp horder
      let ix := LinearEquiv.piCongrLeft' ℤ
        (fun _ : Fin ((Fintype.card (Fin (k + 2)) - 2).choose d - 1) => ZMod g)
        (finCongr (congrArg (fun j => j.choose d - 1) hk))
      let iy := LinearEquiv.piCongrLeft' ℤ
        (fun _ : Fin ((Fintype.card (Fin (k + 2)) - 2).choose (d + 1) - 1) => ZMod n)
        (finCongr (congrArg (fun j => j.choose (d + 1) - 1) hk))
      have one' : obs single ≃ₗ[ℤ] ((Fin (α - 1) → ZMod g) × (Fin (β - 1) → ZMod n) × ZMod (q H)) :=
        one.trans (ix.prodCongr (iy.prodCongr (LinearEquiv.refl ℤ _)))
      let oneFactors := one'.trans (LinearEquiv.prodAssoc ℤ _ _ _).symm
      let M (i j : Bool) := match i, j with
        | false, false => uniform
        | true, false => prior
        | false, true => single
        | true, true => N
      have hBM (i j : Bool) (B : Finset I) : (M i j).IsBase (B : Set I) ↔
          B.card = d + 2 ∧ (i = true → B ∉ old) ∧ (j = true → B ≠ H) := by
        cases i <;> cases j <;>
          simp [M, hbaseUniform, hbasePrior, hbaseOne, hBase, and_comm]
      obtain ⟨square⟩ := private_pair_residue_product p hp hd hr' root H old fresh
        (fun T hT => hsize T (hA hT)) (fun T hT => hroot T (hA hT)) (hprivate.mono hA) M hBM
      obtain ⟨liftPrior⟩ := lift old hold hbasePrior
      obtain ⟨liftSingle⟩ := lift {H} hs hbaseSingle
      obtain ⟨liftAll⟩ := lift (insert H old) hA hBase
      let productEquiv := (liftUniform.prodCongr liftAll).trans
        (square.trans (liftPrior.symm.prodCongr liftSingle.symm))
      have hcard := card_le_card hA
      rw [card_insert_of_notMem fresh] at hcard
      have hα : old.card < α := by dsimp [α]; omega
      have hβ : old.card < β := by dsimp [β]; omega
      obtain ⟨e⟩ := cancelStep hα hβ ((uniformFactors.symm.prodCongr (LinearEquiv.refl ℤ _)).trans
        (productEquiv.trans (priorFactors.prodCongr oneFactors)))
      let e' := e.trans ((LinearEquiv.refl ℤ _).prodCongr (insertPetal q fresh))
      change Nonempty (obs N ≃ₗ[ℤ]
        (Families (ZMod g) (ZMod n) (α - (insert H old).card) (β - (insert H old).card) ×
          (∀ T : ↥(insert H old), ZMod (q T.val))))
      rw [card_insert_of_notMem fresh, Nat.sub_add_eq, Nat.sub_add_eq]
      exact ⟨e'⟩
  exact calcFactors family Subset.rfl S hbases

end D5.S3.Combinatorics.Matroids.PrivatePairCircuitInvariantFactors
