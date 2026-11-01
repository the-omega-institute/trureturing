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

@[simp]
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
        Sigma.ι (fun t : {t : Finset ι // #t = p + 1} ↦ (freeFunctor R P).obj (op t.1))
          ⟨s.1.erase i, hs⟩
     else 0)

private def epsilon0 : X R P 0 ⟶ ∐ fun _ : A ↦ R :=
  Sigma.desc fun _ ↦ Sigma.desc fun a ↦ Sigma.ι (fun _ : A ↦ R) a.1

omit [LinearOrder ι] in
@[simp]
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

omit [LinearOrder ι] in
private lemma mem_vertex (hP : ⋃ i, P i = Set.univ) (a : A) : a ∈ P (vertex P hP a) :=
  (Set.mem_iUnion.1 (hP ▸ Set.mem_univ a)).choose_spec

private def section0 (hP : ⋃ i, P i = Set.univ) : (∐ fun _ : A ↦ R) ⟶ X R P 0 :=
  Sigma.desc fun a ↦ single R P 0 {vertex P hP a} a (by simpa using mem_vertex P hP a)

omit [LinearOrder ι] in
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


omit [LinearOrder ι] in
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


omit [LinearOrder ι] in
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


private lemma single_d_H (hP : ⋃ i, P i = Set.univ) {p : ℕ} {s : Finset ι}
    (hs : #s = p + 1 + 1) (a : A) (ha : ∀ i ∈ s, a ∈ P i) :
    single R P (p + 1) s a ha ≫ d R P p ≫ H R P hP p (p + 1) =
      coneFace R P hP (p + 1) s a ha := by
  rw [← Category.assoc, single_d R P hs, Preadditive.sum_comp, coneFace]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [Preadditive.zsmul_comp,
    single_H R P hP _ (by rw [card_erase_of_mem hk, hs]; rfl), smul_smul]

private lemma coneFace_of_mem (hP : ⋃ i, P i = Set.univ) {p : ℕ} {s : Finset ι}
    (hs : #s = p + 1) (a : A) (ha : ∀ i ∈ s, a ∈ P i) (hc : vertex P hP a ∈ s) :
    coneFace R P hP p s a ha = single R P p s a ha := by
  rw [coneFace, sum_eq_single (vertex P hP a)]
  · rw [single_congr R P a _ (insert_erase hc), filter_erase,
      erase_eq_of_notMem (by simp), ← pow_add, ← two_mul, pow_mul,
      neg_one_sq, one_pow, one_smul]
  · intro k hk hkc
    have hcard : #(insert (vertex P hP a) (s.erase k)) ≠ p + 1 := by
      rw [insert_eq_of_mem (mem_erase.2 ⟨Ne.symm hkc, hc⟩), card_erase_of_mem hk, hs]
      omega
    simp [single, hcard]
  · exact fun h ↦ (h hc).elim

private lemma coneFace_zero (hP : ⋃ i, P i = Set.univ) {s : Finset ι}
    (hs : #s = 0 + 1) (a : A) (ha : ∀ i ∈ s, a ∈ P i) :
    coneFace R P hP 0 s a ha =
      single R P 0 {vertex P hP a} a (by simpa using mem_vertex P hP a) := by
  obtain ⟨i, rfl⟩ := card_eq_one.1 hs
  simp [coneFace, filter_singleton]

/-- The ordered free Čech complex, with its actual intersection-inclusion differential. -/
abbrev complex : ChainComplex C ℕ := ChainComplex.of (X R P) (d R P) (d_squared R P)

private lemma boundary_epsilon0 : d R P 0 ≫ epsilon0 R P = 0 := by
  apply hom_ext R P
  intro s hs a ha
  rw [← Category.assoc, single_d R P hs, Preadditive.sum_comp]
  simp_rw [Preadditive.zsmul_comp]
  rw [← sum_coe_sort]
  have heq : (∑ i : s, ((-1 : ℤ) ^ #{j ∈ s | j < i.1}) •
      (single R P 0 (s.erase i.1) a (fun j hj ↦ ha j (mem_of_mem_erase hj)) ≫ epsilon0 R P)) =
      ∑ i : s, ((-1 : ℤ) ^ #{j ∈ s | j < i.1}) • Sigma.ι (fun _ : A ↦ R) a := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [single_epsilon0 R P (by rw [card_erase_of_mem i.2, hs])]
  rw [heq, signed_sum_reindex hs (fun _ ↦ Sigma.ι (fun _ : A ↦ R) a)]
  simp [Fin.sum_univ_succ]

variable [HasZeroObject C]

/-- The augmentation is independently defined by sending each degree-zero point to itself. -/
def augmentation : complex R P ⟶ (ChainComplex.single₀ C).obj (∐ fun _ : A ↦ R) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨epsilon0 R P, by
    change ChainComplex.of.d (X R P) (d R P) 1 0 ≫ epsilon0 R P = 0
    exact (congrArg (fun f ↦ f ≫ epsilon0 R P)
      (ChainComplex.of_d (X R P) (d R P) (0 : ℕ))).trans (boundary_epsilon0 R P)⟩

private def section_ (hP : ⋃ i, P i = Set.univ) :
    (ChainComplex.single₀ C).obj (∐ fun _ : A ↦ R) ⟶ complex R P :=
  (ChainComplex.fromSingle₀Equiv _ _).symm (section0 R P hP)

private lemma augmentation_f_zero : (augmentation R P).f 0 = epsilon0 R P :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

private lemma section_f_zero (hP : ⋃ i, P i = Set.univ) :
    (section_ R P hP).f 0 = section0 R P hP :=
  ChainComplex.fromSingle₀Equiv_symm_apply_f_zero _

private lemma section_f_succ (hP : ⋃ i, P i = Set.univ) (n : ℕ) :
    (section_ R P hP).f (n + 1) = 0 :=
  ChainComplex.fromSingle₀Equiv_symm_apply_f_succ _ _

private lemma section_augmentation (hP : ⋃ i, P i = Set.univ) :
    section_ R P hP ≫ augmentation R P = 𝟙 _ := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
    augmentation_f_zero, section_f_zero]
  exact section0_epsilon0 R P hP

private lemma id_sub_augmentation_section (hP : ⋃ i, P i = Set.univ) :
    𝟙 _ - augmentation R P ≫ section_ R P hP =
      Homotopy.nullHomotopicMap' (C := complex R P) (D := complex R P)
        (fun i j (_ : (ComplexShape.down ℕ).Rel j i) ↦ H R P hP i j) := by
  ext (_ | p) : 1
  · rw [Homotopy.nullHomotopicMap'_f_of_not_rel_left (ComplexShape.down_mk 1 0 rfl)
      (fun l h ↦ by simp at h)]
    change (𝟙 _ - augmentation R P ≫ section_ R P hP).f 0 =
      H R P hP 0 1 ≫ ChainComplex.of.d (X R P) (d R P) 1 0
    erw [ChainComplex.of_d (X R P) (d R P) 0]
    apply hom_ext R P
    intro s hs a ha
    simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f,
      HomologicalComplex.comp_f, Preadditive.comp_sub, Category.comp_id,
      augmentation_f_zero, section_f_zero]
    rw [← Category.assoc, single_epsilon0 R P hs, section0, Sigma.ι_comp_desc,
      ← coneFace_zero R P hP hs a ha]
    by_cases hc : vertex P hP a ∈ s
    · rw [coneFace_of_mem R P hP hs a ha hc, sub_self, ← Category.assoc,
        single_H_of_mem R P hP hs a ha hc, zero_comp]
    · rw [single_H_d_of_notMem R P hP hs a ha hc]
  · rw [Homotopy.nullHomotopicMap'_f (ComplexShape.down_mk (p + 2) (p + 1) rfl)
      (ComplexShape.down_mk (p + 1) p rfl)]
    change (𝟙 _ - augmentation R P ≫ section_ R P hP).f (p + 1) =
      ChainComplex.of.d (X R P) (d R P) (p + 1) p ≫ H R P hP p (p + 1) +
        H R P hP (p + 1) (p + 2) ≫
          ChainComplex.of.d (X R P) (d R P) (p + 2) (p + 1)
    erw [ChainComplex.of_d (X R P) (d R P) p,
      ChainComplex.of_d (X R P) (d R P) (p + 1)]
    apply hom_ext R P
    intro s hs a ha
    simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f,
      HomologicalComplex.comp_f, section_f_succ,
      comp_zero, sub_zero, Category.comp_id, Preadditive.comp_add, single_d_H R P hP hs a ha]
    by_cases hc : vertex P hP a ∈ s
    · rw [coneFace_of_mem R P hP hs a ha hc, ← Category.assoc,
        single_H_of_mem R P hP hs a ha hc, zero_comp, add_zero]
    · rw [single_H_d_of_notMem R P hP hs a ha hc, add_sub_cancel]

/-- The same actual augmentation has the explicit chosen-vertex chain-homotopy inverse. -/
theorem augmentation_homotopy_equiv (hP : ⋃ i, P i = Set.univ) :
    ∃ E : HomotopyEquiv (complex R P) ((ChainComplex.single₀ C).obj (∐ fun _ : A ↦ R)),
      E.hom = augmentation R P := by
  refine ⟨{
    hom := augmentation R P
    inv := section_ R P hP
    homotopyHomInvId := (Homotopy.equivSubZero.symm
      ((Homotopy.ofEq (id_sub_augmentation_section R P hP)).trans
        (Homotopy.nullHomotopy' _))).symm
    homotopyInvHomId := Homotopy.ofEq (section_augmentation R P hP) }, rfl⟩

/-! ### Functoriality in the covered basis

These maps use the same coefficient object `R` on every basis element.
In particular, using them for singular simplices does not replace `R` by
the free object on the simplices.
-/

variable {B D : Type w} {P : ι → Set A} {Q : ι → Set B} {T : ι → Set D}

/-- The actual inclusion of a covered basis element in a degree of the complex. -/
def basisι {p : ℕ} (s : Finset ι) (hs : #s = p + 1)
    (a : A) (ha : ∀ i ∈ s, a ∈ P i) : R ⟶ (complex R P).X p :=
  single R P p s a ha

lemma basisι_eq {p : ℕ} (s : Finset ι) (hs : #s = p + 1)
    (a : A) (ha : ∀ i ∈ s, a ∈ P i) :
    basisι R s hs a ha =
      Sigma.ι (fun _ : {a : A // ∀ i ∈ s, a ∈ P i} => R) ⟨a, ha⟩ ≫
        Sigma.ι (fun t : {t : Finset ι // #t = p + 1} =>
          (freeFunctor R P).obj (op t.val)) ⟨s, hs⟩ := by
  simp only [basisι, single, dite_eq_left hs, pointι]

@[reassoc]
lemma basisι_d {p : ℕ} (s : Finset ι) (hs : #s = p + 2)
    (a : A) (ha : ∀ i ∈ s, a ∈ P i) :
    basisι R s hs a ha ≫ (complex R P).d (p + 1) p =
      ∑ i : s, ((-1 : ℤ) ^ #{j ∈ s | j < i.1}) •
        basisι R (s.erase i.1) (by rw [card_erase_of_mem i.2, hs]; omega)
          a (fun j hj ↦ ha j (mem_of_mem_erase hj)) := by
  change single R P (p + 1) s a ha ≫
    ChainComplex.of.d (X R P) (d R P) (p + 1) p = _
  rw [ChainComplex.of_d, single_d R P hs, ← sum_coe_sort]
  rfl

@[ext]
lemma basis_hom_ext {p : ℕ} {Y : C} {f g : (complex R P).X p ⟶ Y}
    (h : ∀ (s : Finset ι) (hs : #s = p + 1) (a : A)
      (ha : ∀ i ∈ s, a ∈ P i), basisι R s hs a ha ≫ f = basisι R s hs a ha ≫ g) :
    f = g :=
  hom_ext R P h

private def mapX (f : A → B) (hf : ∀ i a, a ∈ P i → f a ∈ Q i) (p : ℕ) :
    (complex R P).X p ⟶ (complex R Q).X p :=
  Sigma.desc fun s ↦ Sigma.desc fun a ↦
    pointι R Q (f a.1) (fun i hi ↦ hf i a.1 (a.2 i hi)) ≫
      Sigma.ι (fun t : {t : Finset ι // #t = p + 1} ↦ (freeFunctor R Q).obj (op t.1)) s

@[reassoc]
private lemma single_mapX (f : A → B) (hf : ∀ i a, a ∈ P i → f a ∈ Q i)
    {p : ℕ} {s : Finset ι} (hs : #s = p + 1) (a : A)
    (ha : ∀ i ∈ s, a ∈ P i) :
    single R P p s a ha ≫ mapX R f hf p =
      single R Q p s (f a) (fun i hi ↦ hf i a (ha i hi)) := by
  simp only [single, dite_eq_left hs, mapX, pointι, Category.assoc,
    Sigma.ι_comp_desc]

private lemma mapX_comm (f : A → B) (hf : ∀ i a, a ∈ P i → f a ∈ Q i) (p : ℕ) :
    mapX R f hf (p + 1) ≫ d R Q p = d R P p ≫ mapX R f hf p := by
  apply hom_ext R P
  intro s hs a ha
  rw [← Category.assoc, single_mapX R f hf hs, single_d R Q hs,
    ← Category.assoc, single_d R P hs, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Preadditive.zsmul_comp,
    single_mapX R f hf (by rw [card_erase_of_mem hi, hs]; omega)]

/-- A function of covered bases induces the actual ordered chain map. -/
def map (f : A → B) (hf : ∀ i a, a ∈ P i → f a ∈ Q i) :
    complex R P ⟶ complex R Q :=
  ChainComplex.ofHom (mapX R f hf) (fun p => by
    simpa only [complex, ChainComplex.of_d] using mapX_comm R f hf p)

@[reassoc (attr := simp)]
lemma basisι_map (f : A → B) (hf : ∀ i a, a ∈ P i → f a ∈ Q i)
    {p : ℕ} (s : Finset ι) (hs : #s = p + 1) (a : A)
    (ha : ∀ i ∈ s, a ∈ P i) :
    basisι R s hs a ha ≫ (map R f hf).f p =
      basisι R s hs (f a) (fun i hi ↦ hf i a (ha i hi)) :=
  single_mapX R f hf hs a ha

@[simp]
lemma map_id : map R (id : A → A) (P := P) (Q := P) (fun _ _ h ↦ h) = 𝟙 _ := by
  ext p : 1
  apply basis_hom_ext R
  intro s hs a ha
  simp

@[simp]
lemma map_comp (f : A → B) (g : B → D)
    (hf : ∀ i a, a ∈ P i → f a ∈ Q i) (hg : ∀ i b, b ∈ Q i → g b ∈ T i) :
    map R (g ∘ f) (fun i a ha ↦ hg i (f a) (hf i a ha)) =
      map R f hf ≫ map R g hg := by
  ext p : 1
  apply basis_hom_ext R
  intro s hs a ha
  simp

@[reassoc (attr := simp)]
lemma basisι_augmentation (s : Finset ι) (hs : #s = 1) (a : A)
    (ha : ∀ i ∈ s, a ∈ P i) :
    basisι R s hs a ha ≫ (augmentation R P).f 0 = Sigma.ι (fun _ : A ↦ R) a := by
  exact (congrArg (fun f ↦ single R P 0 s a ha ≫ f)
    (augmentation_f_zero R P)).trans (single_epsilon0 R P hs a ha)

end TauCeti.OrderedCover
