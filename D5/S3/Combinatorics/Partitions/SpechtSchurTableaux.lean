/- GID: D5/S3/Combinatorics/Partitions/SpechtSchurTableaux
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/SpechtSchurTableaux
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Selected tableau and Schur suppliers for the ordinary Specht Frobenius comparison. -/

/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license. Authors: The Tau Ceti contributors.
Selected declarations from TauCeti 5a01f5fe3621126cccf9ba22e700493cbc7b7156.
Namespaces and root references adapted to the existing D5 source chain.
License, selection, consumers and retirement:
Library/FiniteGroups/tauceti2026spechtpolytabloids.md.
Unfinished escape audit: https://github.com/the-omega-institute/trureturing/issues/24542.
-/
import D5.S3.Combinatorics.Partitions.SpechtTableauInvolution
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

namespace D5.S3.Combinatorics.Partitions.SpechtPolytabloid
noncomputable section
open scoped BigOperators

namespace TauCeti

open _root_.YoungDiagram (ofPartition card_ofPartition)

open Finset MvPolynomial

namespace BoundedSSYT

variable {N : ℕ} {μ : YoungDiagram}

private theorem support_content_subset_range (T : BoundedSSYT N μ) :
    ↑(SemistandardYoungTableau.content T.1).support ⊆ Set.range (Fin.val : Fin N → ℕ) := by
  intro x hx
  simp only [Finset.mem_coe, SemistandardYoungTableau.support_content, Finset.mem_image] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  exact ⟨⟨_, entry_lt T ((_root_.YoungDiagram.mem_cells _).mp hc)⟩, rfl⟩

noncomputable def weight (T : BoundedSSYT N μ) : Fin N →₀ ℕ :=
  Finsupp.comapDomain Fin.val (SemistandardYoungTableau.content T.1) Fin.val_injective.injOn

@[simp]
theorem weight_apply (T : BoundedSSYT N μ) (i : Fin N) :
    weight T i = SemistandardYoungTableau.content T.1 i :=
  Finsupp.comapDomain_apply _ _ _ _

theorem mapDomain_weight (T : BoundedSSYT N μ) :
    Finsupp.mapDomain Fin.val (weight T) = SemistandardYoungTableau.content T.1 :=
  Finsupp.mapDomain_comapDomain _ Fin.val_injective _ (support_content_subset_range T)

theorem sum_weight (T : BoundedSSYT N μ) : ∑ i, weight T i = μ.card := by
  simp only [weight_apply]
  rw [Fin.sum_univ_eq_sum_range fun i => SemistandardYoungTableau.content T.1 i]
  exact SemistandardYoungTableau.sum_content_eq_card fun c hc =>
    entry_lt T ((_root_.YoungDiagram.mem_cells _).mp hc)

private theorem lt_of_content_eq {T : _root_.SemistandardYoungTableau μ} {d : Fin N →₀ ℕ}
    (h : ⇑(SemistandardYoungTableau.content T) = ⇑(Finsupp.mapDomain Fin.val d))
    {i c : ℕ} (hic : (i, c) ∈ μ) : T i c < N := by
  by_contra hlt
  have hmem : SemistandardYoungTableau.content T (T i c) ≠ 0 := by
    rw [← Finsupp.mem_support_iff, SemistandardYoungTableau.support_content]
    exact Finset.mem_image.mpr ⟨(i, c), (_root_.YoungDiagram.mem_cells _).mpr hic, rfl⟩
  refine hmem ((congrFun h (T i c)).trans (Finsupp.mapDomain_of_notMem_range _ _ ?_))
  rintro ⟨y, hy⟩
  exact hlt (hy ▸ y.isLt)

private theorem weight_eq_of_content_eq (T : BoundedSSYT N μ) {d : Fin N →₀ ℕ}
    (h : ⇑(SemistandardYoungTableau.content T.1) = ⇑(Finsupp.mapDomain Fin.val d)) :
    weight T = d := by
  ext i
  rw [weight_apply, congrFun h i, Finsupp.mapDomain_apply_of_injective Fin.val_injective]

private noncomputable def weightFiberEquivContentFiber (N : ℕ) (μ : YoungDiagram)
    (d : Fin N →₀ ℕ) :
    {T : BoundedSSYT N μ // weight T = d} ≃
      {T : _root_.SemistandardYoungTableau μ //
        ⇑(SemistandardYoungTableau.content T) = ⇑(Finsupp.mapDomain Fin.val d)} where
  toFun T := ⟨T.1.1, by rw [← mapDomain_weight T.1, T.2]⟩
  invFun T := ⟨⟨T.1, fun _ _ hic => lt_of_content_eq T.2 hic⟩, weight_eq_of_content_eq _ T.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_weight_eq (d : Fin N →₀ ℕ) :
    Nat.card {T : BoundedSSYT N μ // weight T = d}
      = diagramKostkaNumber μ (Finsupp.mapDomain Fin.val d) :=
  (Nat.card_congr (weightFiberEquivContentFiber N μ d)).trans (diagramKostkaNumber_def _ _).symm

end BoundedSSYT

variable (N : ℕ) (R : Type*) [CommSemiring R] (μ : YoungDiagram)

noncomputable def diagramSchurPoly : MvPolynomial (Fin N) R :=
  ∑ T : BoundedSSYT N μ, monomial (BoundedSSYT.weight T) 1

theorem diagramSchurPoly_eq_sum :
    diagramSchurPoly N R μ = ∑ T : BoundedSSYT N μ, monomial (BoundedSSYT.weight T) 1 :=
  (rfl)

variable {N R μ}

theorem coeff_diagramSchurPoly (d : Fin N →₀ ℕ) :
    (diagramSchurPoly N R μ).coeff d
      = (diagramKostkaNumber μ (Finsupp.mapDomain Fin.val d) : R) := by
  classical
  rw [diagramSchurPoly]
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_boole, ← BoundedSSYT.card_weight_eq d, Nat.card_eq_fintype_card,
    Fintype.card_subtype]

theorem eval_diagramSchurPoly (y : Fin N → R) :
    eval y (diagramSchurPoly N R μ)
      = ∑ T : BoundedSSYT N μ, ∏ i, y i ^ BoundedSSYT.weight T i := by
  rw [diagramSchurPoly, map_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [eval_monomial, one_mul]
  exact Finsupp.prod_fintype _ _ fun _ => pow_zero _

@[simp] theorem eval_one_diagramSchurPoly_eq_card_boundedSSYT (N : ℕ) (μ : YoungDiagram) :
    eval (fun _ : Fin N => (1 : R)) (diagramSchurPoly N R μ) =
      (Nat.card (BoundedSSYT N μ) : R) := by
  rw [eval_diagramSchurPoly]
  simp only [one_pow, prod_const_one, sum_const, card_univ, Nat.card_eq_fintype_card,
    nsmul_eq_mul, mul_one]
theorem map_diagramSchurPoly {S : Type*} [CommSemiring S] (f : R →+* S) :
    MvPolynomial.map f (diagramSchurPoly N R μ) = diagramSchurPoly N S μ := by
  ext d
  rw [MvPolynomial.coeff_map, coeff_diagramSchurPoly, coeff_diagramSchurPoly, map_natCast]

theorem diagramSchurPoly_eq_zero_of_lt_colLen (h : N < μ.colLen 0) :
    diagramSchurPoly N R μ = 0 := by
  have := BoundedSSYT.isEmpty_of_lt_colLen h
  simp [diagramSchurPoly]

@[simp]
theorem diagramSchurPoly_bot : diagramSchurPoly N R (⊥ : YoungDiagram) = 1 := by
  have hw : BoundedSSYT.weight (default : BoundedSSYT N (⊥ : YoungDiagram)) = 0 := by
    ext i
    rw [BoundedSSYT.weight_apply, Finsupp.coe_zero, Pi.zero_apply,
      SemistandardYoungTableau.content_apply]
    simp
  rw [diagramSchurPoly, Finset.univ_unique, Finset.sum_singleton, hw, monomial_zero']
  exact map_one C

variable (N μ)

variable {N μ}

theorem mapDomain_rowLenWeight (h : μ.colLen 0 ≤ N) :
    ⇑(Finsupp.mapDomain Fin.val (rowLenWeight N μ)) = μ.rowLen := by
  funext j
  by_cases hj : j < N
  · exact Finsupp.mapDomain_apply_of_injective Fin.val_injective _ (⟨j, hj⟩ : Fin N)
  · have hzero : μ.rowLen j = 0 := by
      by_contra hne
      exact hj (lt_of_lt_of_le (_root_.YoungDiagram.mem_iff_lt_colLen.mp
        (_root_.YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero hne))) h)
    rw [hzero]
    refine Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨y, hy⟩
    exact hj (hy ▸ y.isLt)

theorem coeff_diagramSchurPoly_rowLenWeight (h : μ.colLen 0 ≤ N) :
    (diagramSchurPoly N R μ).coeff (rowLenWeight N μ) = 1 := by
  rw [coeff_diagramSchurPoly, mapDomain_rowLenWeight h, diagramKostkaNumber_rowLen, Nat.cast_one]

theorem diagramSchurPoly_ne_zero [Nontrivial R] (h : μ.colLen 0 ≤ N) :
    diagramSchurPoly N R μ ≠ 0 := by
  intro hz
  have h1 := coeff_diagramSchurPoly_rowLenWeight (R := R) h
  rw [hz] at h1
  simp at h1

theorem diagramSchurPoly_eq_zero_iff [Nontrivial R] :
    diagramSchurPoly N R μ = 0 ↔ N < μ.colLen 0 :=
  ⟨fun h => not_le.mp fun hle => diagramSchurPoly_ne_zero hle h,
    diagramSchurPoly_eq_zero_of_lt_colLen⟩

theorem isHomogeneous_diagramSchurPoly : (diagramSchurPoly N R μ).IsHomogeneous μ.card :=
  IsHomogeneous.sum _ _ _ fun T _ =>
    isHomogeneous_monomial _ ((Finsupp.degree_eq_sum _).trans (BoundedSSYT.sum_weight T))

section Partition

variable {n : ℕ} (μ ν : n.Partition)

end Partition

section Alphabet

variable {σ : Type*} [Fintype σ] {n : ℕ}

noncomputable def schurPoly (σ : Type*) [Fintype σ] (R : Type*) [CommSemiring R] {n : ℕ}
    (μ : n.Partition) : MvPolynomial σ R :=
  rename (Fintype.equivFin σ).symm (diagramSchurPoly (Fintype.card σ) R (ofPartition μ))

theorem schurPoly_eq_rename (μ : n.Partition) :
    schurPoly σ R μ
      = rename (Fintype.equivFin σ).symm (diagramSchurPoly (Fintype.card σ) R (ofPartition μ)) :=
  (rfl)

variable (μ ν : n.Partition)

theorem coeff_schurPoly_mapDomain (d : Fin (Fintype.card σ) →₀ ℕ) :
    (schurPoly σ R μ).coeff (Finsupp.mapDomain (Fintype.equivFin σ).symm d)
      = (diagramKostkaNumber (ofPartition μ) (Finsupp.mapDomain Fin.val d) : R) := by
  rw [schurPoly, MvPolynomial.coeff_rename_mapDomain _ (Fintype.equivFin σ).symm.injective,
    coeff_diagramSchurPoly]

theorem coeff_schurPoly (d : σ →₀ ℕ) :
    (schurPoly σ R μ).coeff d
      = (diagramKostkaNumber (ofPartition μ)
          (Finsupp.mapDomain (fun x => (Fintype.equivFin σ x : ℕ)) d) : R) := by
  have hd : Finsupp.mapDomain (Fintype.equivFin σ).symm
      (Finsupp.mapDomain (Fintype.equivFin σ) d) = d := by
    rw [← Finsupp.mapDomain_comp]
    simp
  conv_lhs => rw [← hd]
  rw [coeff_schurPoly_mapDomain, ← Finsupp.mapDomain_comp]
  rfl

theorem coeff_schurPoly_partWeight (h : (ofPartition ν).colLen 0 ≤ Fintype.card σ) :
    (schurPoly σ R μ).coeff (partWeight σ ν) = (kostkaNumber μ ν : R) := by
  rw [partWeight, coeff_schurPoly_mapDomain, mapDomain_rowLenWeight h, kostkaNumber_def]

theorem schurPoly_eq_zero_iff [Nontrivial R] :
    schurPoly σ R μ = 0 ↔ Fintype.card σ < (ofPartition μ).colLen 0 := by
  rw [schurPoly, map_eq_zero_iff _ (rename_injective _ (Fintype.equivFin σ).symm.injective),
    diagramSchurPoly_eq_zero_iff]

theorem isHomogeneous_schurPoly : (schurPoly σ R μ).IsHomogeneous n := by
  have h := isHomogeneous_diagramSchurPoly (N := Fintype.card σ) (R := R) (μ := ofPartition μ)
  rw [card_ofPartition μ] at h
  rw [schurPoly]
  exact h.rename_isHomogeneous

end Alphabet

end TauCeti

namespace TauCeti

open MvPolynomial

namespace BoundedSSYT

variable {N : ℕ} {μ : YoungDiagram}

def benderKnuth (T : BoundedSSYT N μ) {a b : Fin N} (hab : (b : ℕ) = (a : ℕ) + 1) :
    BoundedSSYT N μ :=
  ⟨T.1.benderKnuth (a : ℕ), fun i j hij => by
    rcases SemistandardYoungTableau.benderKnuth_apply_eq_or T.1 (a : ℕ) i j with h | h | h
    · rw [h]; exact T.2 i j hij
    · rw [h]; exact a.isLt
    · rw [h, ← hab]; exact b.isLt⟩

@[simp]
theorem benderKnuth_benderKnuth (T : BoundedSSYT N μ) {a b : Fin N}
    (hab : (b : ℕ) = (a : ℕ) + 1) : (T.benderKnuth hab).benderKnuth hab = T :=
  Subtype.ext (SemistandardYoungTableau.benderKnuth_benderKnuth T.1 (a : ℕ))

theorem benderKnuth_involutive (N : ℕ) (μ : YoungDiagram) {a b : Fin N}
    (hab : (b : ℕ) = (a : ℕ) + 1) :
    Function.Involutive fun T : BoundedSSYT N μ => T.benderKnuth hab :=
  fun T => benderKnuth_benderKnuth T hab

private theorem val_swap {a b i : Fin N} :
    ((Equiv.swap a b i : Fin N) : ℕ) = Equiv.swap (a : ℕ) (b : ℕ) (i : ℕ) := by
  rcases eq_or_ne i a with rfl | hia
  · rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
  rcases eq_or_ne i b with rfl | hib
  · rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
  · rw [Equiv.swap_apply_of_ne_of_ne hia hib,
      Equiv.swap_apply_of_ne_of_ne (fun h => hia (Fin.ext h)) (fun h => hib (Fin.ext h))]

theorem weight_benderKnuth (T : BoundedSSYT N μ) {a b : Fin N} (hab : (b : ℕ) = (a : ℕ) + 1)
    (i : Fin N) : weight (T.benderKnuth hab) i = weight T (Equiv.swap a b i) := by
  rw [weight_apply, weight_apply, val_swap, hab]
  exact SemistandardYoungTableau.content_benderKnuth T.1 (a : ℕ) (i : ℕ)

theorem mapDomain_weight_swap (T : BoundedSSYT N μ) {a b : Fin N}
    (hab : (b : ℕ) = (a : ℕ) + 1) :
    Finsupp.mapDomain (Equiv.swap a b) (weight T) = weight (T.benderKnuth hab) := by
  ext i
  rw [← Finsupp.equivMapDomain_eq_mapDomain, Finsupp.equivMapDomain_apply, Equiv.symm_swap,
    weight_benderKnuth]

end BoundedSSYT

variable {R : Type*} [CommSemiring R]

theorem rename_swap_diagramSchurPoly {N : ℕ} (R : Type*) [CommSemiring R] (μ : YoungDiagram)
    {a b : Fin N} (hab : (b : ℕ) = (a : ℕ) + 1) :
    rename (Equiv.swap a b) (diagramSchurPoly N R μ) = diagramSchurPoly N R μ := by
  calc rename (Equiv.swap a b) (diagramSchurPoly N R μ)
      = ∑ T : BoundedSSYT N μ, monomial (BoundedSSYT.weight (T.benderKnuth hab)) (1 : R) := by
        rw [diagramSchurPoly_eq_sum, map_sum]
        exact Finset.sum_congr rfl fun T _ => by
          rw [rename_monomial, BoundedSSYT.mapDomain_weight_swap T hab]
    _ = ∑ T : BoundedSSYT N μ, monomial (BoundedSSYT.weight T) (1 : R) :=
        Fintype.sum_bijective _ (BoundedSSYT.benderKnuth_involutive N μ hab).bijective _ _
          fun _ => rfl
    _ = diagramSchurPoly N R μ := (diagramSchurPoly_eq_sum N R μ).symm

theorem isSymmetric_diagramSchurPoly (N : ℕ) (R : Type*) [CommSemiring R] (μ : YoungDiagram) :
    (diagramSchurPoly N R μ).IsSymmetric := by
  intro e
  match N with
  | 0 =>
    rw [Subsingleton.elim e 1]
    simp
  | M + 1 =>
    have hmem : e ∈ Submonoid.closure
        (Set.range fun i : Fin M => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      trivial
    induction hmem using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact rename_swap_diagramSchurPoly R μ (by simp)
    | one => simp
    | mul x y _ _ hx hy =>
      rw [Equiv.Perm.coe_mul, ← rename_rename, hy, hx]

@[simp]
theorem rename_diagramSchurPoly {M N : ℕ} (μ : YoungDiagram) (e : Fin M ≃ Fin N) :
    rename e (diagramSchurPoly M R μ) = diagramSchurPoly N R μ := by
  have h : M = N := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst M
  exact isSymmetric_diagramSchurPoly N R μ e

private theorem isSymmetric_rename {σ τ : Type*} {p : MvPolynomial τ R} (hp : p.IsSymmetric)
    (e : τ ≃ σ) : (rename e p).IsSymmetric := by
  intro f
  have hcomp : (⇑f ∘ ⇑e) = ⇑e ∘ ⇑(e.trans (f.trans e.symm)) := funext fun t => by simp
  rw [rename_rename, hcomp, ← rename_rename, hp]

theorem schurPoly_isSymmetric {σ : Type*} [Fintype σ] {n : ℕ} (μ : n.Partition) :
    (schurPoly σ R μ).IsSymmetric := by
  rw [schurPoly_eq_rename]
  exact isSymmetric_rename (isSymmetric_diagramSchurPoly _ _ _) _

end TauCeti

namespace TauCeti

open Finset MvPolynomial

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {n : ℕ}

variable (R : Type*) [CommSemiring R]

variable (μ : n.Partition)

@[simp]
theorem coeff_schurPoly_eq_kostkaNumber {d : σ →₀ ℕ} (h : d.degree = n) :
    (schurPoly σ R μ).coeff d = (kostkaNumber μ (weightPartition d h) : R) := by
  obtain ⟨e, he⟩ := exists_perm_mapDomain_eq_partWeight d h
  have hsymm : (schurPoly σ R μ).coeff (Finsupp.mapDomain e d) = (schurPoly σ R μ).coeff d := by
    conv_lhs => rw [← schurPoly_isSymmetric (R := R) μ e]
    exact coeff_rename_mapDomain _ e.injective _ _
  rw [← hsymm, he, coeff_schurPoly_partWeight μ _
    (by rw [YoungDiagram.colLen_zero_ofPartition]; exact card_parts_weightPartition_le d h)]

theorem schurPoly_eq_sum_kostkaNumber_smul_msymm :
    schurPoly σ R μ = ∑ ν : n.Partition, (kostkaNumber μ ν : R) • msymm σ R ν := by
  ext d
  rw [coeff_sum]
  simp only [coeff_smul, smul_eq_mul]
  by_cases hd : d.degree = n
  · rw [coeff_schurPoly_eq_kostkaNumber R μ hd, Finset.sum_eq_single (weightPartition d hd)]
    · rw [coeff_msymm R _ hd, ite_eq_left rfl, mul_one]
    · exact fun ν _ hne => by
        rw [coeff_msymm R ν hd, ite_eq_right fun hw => hne hw.symm, mul_zero]
    · exact fun hmem => absurd (Finset.mem_univ _) hmem
  · rw [(isHomogeneous_schurPoly (σ := σ) (R := R) μ).coeff_eq_zero hd]
    exact (Finset.sum_eq_zero fun ν _ => by
      rw [coeff_msymm_eq_zero_of_degree_ne R ν hd, mul_zero]).symm

end TauCeti

end
end D5.S3.Combinatorics.Partitions.SpechtPolytabloid
