/- GID: D5/S3/Topology/TauCeti/Algebra/Homology/OrderedCechCover
   generality: G
   mirror-B: D5/B/S3/Topology/TauCeti/Algebra/Homology/OrderedCechCover
   mirror-E: none(waiver:abstract-chain-contraction)
   anchors: []
   utility: none
   digest: The actual ordered free cover augmentation has a chosen-vertex chain contraction. -/


import D5.S3.Topology.TauCeti.Algebra.BigOperators.AlternatingSum
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.BigOperators

/-!
# The ordered free complex of a set cover

Source adaptation of TauCetiProject/TauCeti at revision
`580580ea8726c50dcf98e199fa0a7caef5a74302`, files
`TauCeti/Algebra/Homology/OrderedCech.lean`,
`TauCeti/Algebra/Homology/OrderedCech/Cover.lean`, and the insertion-sign
identity in `TauCeti/Data/Finset/Basic.lean`.
Modifications: native imports and coproduct interfaces; only the free-cover
complex is retained; finite-set deletion is transported to the existing
`TauCeti.sum_neg_one_pow_smul_sum_neg_one_pow_smul_eq_zero` supplier.
The full Apache-2.0 license is in
`docs/reports/licenses/tauceti-sphere-port-LICENSE.txt`.
-/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
public section

noncomputable section
open CategoryTheory Limits Opposite Finset
universe w v u
namespace TauCeti.OrderedCover

section Enumeration
variable {ι : Type w} [LinearOrder ι]
private lemma erase_enumeration {s : Finset ι} {n : ℕ} (hs : #s = n + 1) (i : Fin (n + 1)) :
    (s.erase (s.orderEmbOfFin hs i)).orderEmbOfFin
      (by rw [card_erase_of_mem (orderEmbOfFin_mem s hs i), hs]; omega) =
    (Fin.succAboveOrderEmb i).trans (s.orderEmbOfFin hs) := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro j
  apply mem_erase.mpr
  constructor
  · exact fun h ↦ Fin.succAbove_ne i j ((s.orderEmbOfFin hs).injective h)
  · exact orderEmbOfFin_mem s hs _

private lemma rank_enumeration {s : Finset ι} {n : ℕ} (hs : #s = n) (i : Fin n) :
    #{a ∈ s | a < s.orderEmbOfFin hs i} = (i : ℕ) := by
  have himage : (Finset.Iio i).image (s.orderEmbOfFin hs) =
      {a ∈ s | a < s.orderEmbOfFin hs i} := by
    ext a
    simp only [mem_image, Finset.mem_Iio, mem_filter]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨orderEmbOfFin_mem s hs j, (s.orderEmbOfFin hs).lt_iff_lt.mpr hj⟩
    · intro ha
      let j := (s.orderIsoOfFin hs).symm ⟨a, ha.1⟩
      have hj : s.orderEmbOfFin hs j = a :=
        congrArg Subtype.val ((s.orderIsoOfFin hs).apply_symm_apply ⟨a, ha.1⟩)
      refine ⟨j, ?_, hj⟩
      apply (s.orderEmbOfFin hs).lt_iff_lt.mp
      rw [hj]
      exact ha.2
  rw [← himage, card_image_of_injective _ (s.orderEmbOfFin hs).injective, Fin.card_Iio]

private lemma signed_sum_reindex {G : Type v} [AddCommGroup G] {s : Finset ι} {n : ℕ} (hs : #s = n)
    (f : ι → G) :
    ∑ a : s, ((-1 : ℤ) ^ #{b ∈ s | b < a.1}) • f a.1 =
      ∑ i : Fin n, ((-1 : ℤ) ^ (i : ℕ)) • f (s.orderEmbOfFin hs i) := by
  symm
  apply Fintype.sum_equiv (s.orderIsoOfFin hs).toEquiv
  intro i
  change ((-1 : ℤ) ^ (i : ℕ)) • f (s.orderEmbOfFin hs i) =
    ((-1 : ℤ) ^ #{b ∈ s | b < s.orderEmbOfFin hs i}) • f (s.orderEmbOfFin hs i)
  rw [rank_enumeration hs i]


private lemma double_deletion {s : Finset ι} {n : ℕ} (hs : #s = n + 3)
    (i j : Fin (n + 2)) (hij : i ≤ j) :
    (s.erase (s.orderEmbOfFin hs j.succ)).erase
      ((s.erase (s.orderEmbOfFin hs j.succ)).orderEmbOfFin
        (by rw [card_erase_of_mem (orderEmbOfFin_mem s hs _), hs]; omega) i) =
    (s.erase (s.orderEmbOfFin hs i.castSucc)).erase
      ((s.erase (s.orderEmbOfFin hs i.castSucc)).orderEmbOfFin
        (by rw [card_erase_of_mem (orderEmbOfFin_mem s hs _), hs]; omega) j) := by
  rw [erase_enumeration (by omega), erase_enumeration (by omega)]
  change (s.erase (s.orderEmbOfFin hs j.succ)).erase
      (s.orderEmbOfFin hs (j.succ.succAbove i)) =
    (s.erase (s.orderEmbOfFin hs i.castSucc)).erase
      (s.orderEmbOfFin hs (i.castSucc.succAbove j))
  rw [Fin.succAbove_succ_of_le _ _ hij, Fin.succAbove_castSucc_of_le _ _ hij,
    erase_right_comm]

end Enumeration

private theorem neg_one_pow_card_filter_lt_mul_insert {α R : Type*} [LinearOrder α] [Monoid R]
    [HasDistribNeg R]
    {s : Finset α} {c k : α} (hc : c ∉ s) (hk : k ∈ s) :
    (-1 : R) ^ ({j ∈ s | j < c}).card * (-1) ^ ({j ∈ insert c s | j < k}).card =
      -((-1) ^ ({j ∈ s | j < k}).card * (-1) ^ ({j ∈ s.erase k | j < c}).card) := by
  have hck : c ≠ k := fun h ↦ hc (h ▸ hk)
  rcases hck.lt_or_gt with h | h
  · have hcs : c ∉ {j ∈ s | j < k} := by simp [hc]
    have hkc : k ∉ {j ∈ s | j < c} := by simp [h.not_gt]
    simp only [filter_insert, h, ↓reduceIte, card_insert_of_notMem hcs, filter_erase,
      erase_eq_of_notMem hkc, pow_succ]
    simp [← pow_add, add_comm]
  · have hkc : k ∈ {j ∈ s | j < c} := mem_filter.2 ⟨hk, h⟩
    simp only [filter_insert, h.not_gt, ↓reduceIte, filter_erase, ← card_erase_add_one hkc,
      pow_succ]
    simp [← pow_add, add_comm]

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C]
  {ι : Type w} {A : Type w} (R : C) (P : ι → Set A)

def freeFunctor : (Finset ι)ᵒᵖ ⥤ C :=
  { obj s := {a : A // ∀ i ∈ s.unop, a ∈ P i}
    map f := TypeCat.ofHom fun a ↦ ⟨a.1, fun i hi ↦ a.2 i (leOfHom f.unop hi)⟩ } ⋙
    sigmaConst.obj R

private def pointι {s : Finset ι} (a : A) (ha : ∀ i ∈ s, a ∈ P i) :
    R ⟶ (freeFunctor R P).obj (op s) :=
  Sigma.ι (fun _ : {a : A // ∀ i ∈ s, a ∈ P i} ↦ R) ⟨a, ha⟩

@[reassoc (attr := simp)]
private lemma pointι_map {s t : Finset ι} (f : op s ⟶ op t) (a : A)
    (ha : ∀ i ∈ s, a ∈ P i) :
    pointι R P a ha ≫ (freeFunctor R P).map f =
      pointι R P a (fun i hi ↦ ha i (leOfHom f.unop hi)) :=
  (Sigma.ι_comp_map' _ _ _).trans (Category.id_comp _)

variable [Preadditive C] [LinearOrder ι]

private abbrev X (p : ℕ) : C :=
  ∐ fun s : {s : Finset ι // #s = p + 1} ↦ (freeFunctor R P).obj (op s.1)

private def single (p : ℕ) (s : Finset ι) (a : A) (ha : ∀ i ∈ s, a ∈ P i) : R ⟶ X R P p :=
  if hs : #s = p + 1 then pointι R P a ha ≫
    Sigma.ι (fun t : {t : Finset ι // #t = p + 1} ↦ (freeFunctor R P).obj (op t.1)) ⟨s, hs⟩ else 0

private def d (p : ℕ) : X R P (p + 1) ⟶ X R P p :=
  Sigma.desc fun s ↦ ∑ i ∈ s.1, ((-1 : ℤ) ^ #{j ∈ s.1 | j < i}) •
    (if hs : #(s.1.erase i) = p + 1 then
      (freeFunctor R P).map (homOfLE (s.1.erase_subset i)).op ≫
        Sigma.ι (fun t : {t : Finset ι // #t = p + 1} ↦ (freeFunctor R P).obj (op t.1)) ⟨s.1.erase i, hs⟩
     else 0)

private def epsilon0 : X R P 0 ⟶ ∐ fun _ : A ↦ R :=
  Sigma.desc fun _ ↦ Sigma.desc fun a ↦ Sigma.ι (fun _ : A ↦ R) a.1

@[reassoc (attr := simp)]
private lemma single_epsilon0 {s : Finset ι} (hs : #s = 0 + 1) (a : A)
    (ha : ∀ i ∈ s, a ∈ P i) :
    single R P 0 s a ha ≫ epsilon0 R P = Sigma.ι (fun _ : A ↦ R) a := by
  unfold single
  rw [dite_eq_left hs]
  unfold epsilon0
  rw [Category.assoc, Sigma.ι_comp_desc]
  exact Sigma.ι_comp_desc _ _

private def vertex (hP : ⋃ i, P i = Set.univ) (a : A) : ι :=
  (Set.mem_iUnion.1 (hP ▸ Set.mem_univ a)).choose

private lemma mem_vertex (hP : ⋃ i, P i = Set.univ) (a : A) : a ∈ P (vertex P hP a) :=
  (Set.mem_iUnion.1 (hP ▸ Set.mem_univ a)).choose_spec

private def section0 (hP : ⋃ i, P i = Set.univ) : (∐ fun _ : A ↦ R) ⟶ X R P 0 :=
  Sigma.desc fun a ↦ single R P 0 {vertex P hP a} a (by simpa using mem_vertex P hP a)

private lemma section0_epsilon0 (hP : ⋃ i, P i = Set.univ) :
    section0 R P hP ≫ epsilon0 R P = 𝟙 _ := by
  apply Sigma.hom_ext
  intro a
  simp [section0]

private def H (hP : ⋃ i, P i = Set.univ) (p j : ℕ) : X R P p ⟶ X R P j :=
  Sigma.desc fun s ↦ Sigma.desc fun a ↦
    ((-1 : ℤ) ^ #{k ∈ s.1 | k < vertex P hP a.1}) •
      single R P j (insert (vertex P hP a.1) s.1) a.1
        ((forall_mem_insert _ _ _).2 ⟨mem_vertex P hP a.1, a.2⟩)

private lemma single_H (hP : ⋃ i, P i = Set.univ) {p : ℕ} (j : ℕ)
    {s : Finset ι} (hs : #s = p + 1) (a : A) (ha : ∀ i ∈ s, a ∈ P i) :
    single R P p s a ha ≫ H R P hP p j =
      ((-1 : ℤ) ^ #{k ∈ s | k < vertex P hP a}) •
        single R P j (insert (vertex P hP a) s) a
          ((forall_mem_insert _ _ _).2 ⟨mem_vertex P hP a, ha⟩) := by
  unfold single
  rw [dite_eq_left hs]
  unfold H
  rw [Category.assoc, Sigma.ι_comp_desc]
  exact Sigma.ι_comp_desc _ _

private lemma single_H_of_mem (hP : ⋃ i, P i = Set.univ) {p : ℕ}
    {s : Finset ι} (hs : #s = p + 1) (a : A) (ha : ∀ i ∈ s, a ∈ P i)
    (hc : vertex P hP a ∈ s) :
    single R P p s a ha ≫ H R P hP p (p + 1) = 0 := by
  rw [single_H R P hP _ hs a ha]
  have hcard : #(insert (vertex P hP a) s) ≠ p + 1 + 1 := by
    rw [insert_eq_of_mem hc, hs]; omega
  simp [single, hcard]


private lemma single_congr {p : ℕ} {s t : Finset ι} (a : A)
    (ha : ∀ i ∈ s, a ∈ P i) (e : s = t) :
    single R P p s a ha = single R P p t a (e ▸ ha) := by
  subst e
  rfl

private lemma single_d {p : ℕ} {s : Finset ι} (hs : #s = p + 1 + 1) (a : A)
    (ha : ∀ i ∈ s, a ∈ P i) :
    single R P (p + 1) s a ha ≫ d R P p =
      ∑ i ∈ s, ((-1 : ℤ) ^ #{j ∈ s | j < i}) •
        single R P p (s.erase i) a (fun j hj ↦ ha j (mem_of_mem_erase hj)) := by
  unfold single
  rw [dite_eq_left hs]
  unfold d
  rw [Category.assoc, Sigma.ι_comp_desc, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hcard : #(s.erase i) = p + 1 := by rw [card_erase_of_mem hi, hs]; omega
  rw [Preadditive.comp_zsmul, dite_eq_left hcard, ← Category.assoc, pointι_map]
  rw [dite_eq_left hcard]

private def coneFace (hP : ⋃ i, P i = Set.univ) (p : ℕ) (s : Finset ι) (a : A)
    (ha : ∀ i ∈ s, a ∈ P i) : R ⟶ X R P p :=
  ∑ k ∈ s, ((-1 : ℤ) ^ #{j ∈ s | j < k} * (-1) ^ #{j ∈ s.erase k | j < vertex P hP a}) •
    single R P p (insert (vertex P hP a) (s.erase k)) a
      ((forall_mem_insert _ _ _).2 ⟨mem_vertex P hP a, fun j hj ↦ ha j (mem_of_mem_erase hj)⟩)

private lemma single_H_d_of_notMem (hP : ⋃ i, P i = Set.univ) {p : ℕ} {s : Finset ι}
    (hs : #s = p + 1) (a : A) (ha : ∀ i ∈ s, a ∈ P i) (hc : vertex P hP a ∉ s) :
    single R P p s a ha ≫ H R P hP p (p + 1) ≫ d R P p =
      single R P p s a ha - coneFace R P hP p s a ha := by
  rw [← Category.assoc, single_H R P hP _ hs, Preadditive.zsmul_comp,
    single_d R P (by rw [card_insert_of_notMem hc, hs]), sum_insert hc, smul_add, coneFace,
    sub_eq_add_neg, ← sum_neg_distrib, Finset.smul_sum,
    single_congr R P a _ (erase_insert hc), smul_smul, filter_insert]
  simp only [lt_irrefl, ↓reduceIte]
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]
  congr 1
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hck : vertex P hP a ≠ k := fun h ↦ hc (h ▸ hk)
  rw [smul_smul, neg_one_pow_card_filter_lt_mul_insert hc hk, neg_smul,
    single_congr R P a _ (erase_insert_of_ne hck)]


private lemma hom_ext {p : ℕ} {Y : C} {f g : X R P p ⟶ Y}
    (h : ∀ (s : Finset ι) (_ : #s = p + 1) (a : A) (ha : ∀ i ∈ s, a ∈ P i),
      single R P p s a ha ≫ f = single R P p s a ha ≫ g) : f = g := by
  refine Sigma.hom_ext _ _ fun s ↦ Sigma.hom_ext _ _ fun a ↦ ?_
  simpa only [single, dite_eq_left s.2, pointι, Category.assoc] using h s.1 s.2 a.1 a.2

private lemma d_squared (n : ℕ) : d R P (n + 1) ≫ d R P n = 0 := by
  apply hom_ext R P
  intro s hs a ha
  rw [← Category.assoc, single_d R P hs, Preadditive.sum_comp]
  simp_rw [Preadditive.zsmul_comp]
  have expand : (∑ i ∈ s, ((-1 : ℤ) ^ #{j ∈ s | j < i}) •
      (single R P (n + 1) (s.erase i) a (fun j hj ↦ ha j (mem_of_mem_erase hj)) ≫ d R P n)) =
      ∑ i ∈ s, ((-1 : ℤ) ^ #{j ∈ s | j < i}) •
        ∑ k ∈ s.erase i, ((-1 : ℤ) ^ #{j ∈ s.erase i | j < k}) •
          single R P n ((s.erase i).erase k) a
            (fun j hj ↦ ha j (mem_of_mem_erase (mem_of_mem_erase hj))) := by
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [single_d R P (by rw [card_erase_of_mem hi, hs]; omega)]
  rw [expand, comp_zero, ← sum_coe_sort]
  rw [signed_sum_reindex hs (fun i ↦
    ∑ k ∈ s.erase i, ((-1 : ℤ) ^ #{j ∈ s.erase i | j < k}) •
      single R P n ((s.erase i).erase k) a
        (fun j hj ↦ ha j (mem_of_mem_erase (mem_of_mem_erase hj))))]
  have inner (i : Fin (n + 3)) :
      ∑ k ∈ s.erase (s.orderEmbOfFin hs i),
        ((-1 : ℤ) ^ #{j ∈ s.erase (s.orderEmbOfFin hs i) | j < k}) •
          single R P n ((s.erase (s.orderEmbOfFin hs i)).erase k) a
            (fun j hj ↦ ha j (mem_of_mem_erase (mem_of_mem_erase hj))) =
      ∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k : ℕ)) •
          single R P n ((s.erase (s.orderEmbOfFin hs i)).erase
            ((s.erase (s.orderEmbOfFin hs i)).orderEmbOfFin
              (by rw [card_erase_of_mem (orderEmbOfFin_mem s hs i), hs]; omega) k)) a
            (fun j hj ↦ ha j (mem_of_mem_erase (mem_of_mem_erase hj))) := by
    rw [← sum_coe_sort]
    exact signed_sum_reindex _ (fun k ↦
      single R P n ((s.erase (s.orderEmbOfFin hs i)).erase k) a
        (fun j hj ↦ ha j (mem_of_mem_erase (mem_of_mem_erase hj))))
  simp_rw [inner]
  apply TauCeti.sum_neg_one_pow_smul_sum_neg_one_pow_smul_eq_zero
  intro i j hij
  exact single_congr R P a _ (double_deletion hs i j hij)

end TauCeti.OrderedCover
