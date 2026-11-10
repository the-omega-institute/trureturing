/- GID: D5/S3/HomologicalAlgebra/EilenbergZilber/SpecialContraction
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/EilenbergZilber/SpecialContraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Structural cancellation for the recursive normalized Eilenberg–Mac Lane homotopy. -/

import D5.S3.HomologicalAlgebra.EilenbergZilber.BisimplicialNormalized

/-! # Special contractions of the bisimplicial Eilenberg–Zilber homotopy -/

noncomputable section

open CategoryTheory
open AlgebraicTopology AlgebraicTopology.DoldKan CategoryTheory.Limits
open scoped Simplicial

namespace D5.S3.HomologicalAlgebra.EilenbergZilber
namespace BisimplicialObject

/-- An adjacent pair identified by a simplex map. -/
private def Repeats {n : ℕ} {a : SimplexCategory} (f : (⦋n⦌ : SimplexCategory) ⟶ a)
    (i : Fin n) : Prop :=
  f.toOrderHom i.castSucc = f.toOrderHom i.succ

private lemma Repeats.comp {n : ℕ} {a b : SimplexCategory}
    {f : (⦋n⦌ : SimplexCategory) ⟶ a} {i : Fin n} (h : Repeats f i) (g : a ⟶ b) :
    Repeats (f ≫ g) i := by
  exact congrArg g.toOrderHom h

private lemma hLetter_fst_val (n : ℕ) (r : Fin (n + 1)) (ν : Shuffle r.val (n - r.val))
    (i : Fin (n + 1)) :
    ((hLetter n r ν).fst.toOrderHom i : ℕ) =
      (ν.1 (i.cast (by have := r.isLt; omega))).1.val := by
  simp only [hLetter, SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply, val_eqToHom_apply]
  change (ν.1 _).1.val = (ν.1 _).1.val
  congr 2
  apply congrArg (fun j => ν.1 j)
  exact Fin.ext (val_eqToHom_apply _ _)

private lemma hLetter_snd_val (n : ℕ) (r : Fin (n + 1)) (ν : Shuffle r.val (n - r.val))
    (i : Fin (n + 1)) :
    ((hLetter n r ν).snd.toOrderHom i : ℕ) =
      r.val + (ν.1 (i.cast (by have := r.isLt; omega))).2.val := by
  simp only [hLetter, SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply, val_eqToHom_apply]
  change r.val + (ν.1 _).2.val = r.val + (ν.1 _).2.val
  congr 3
  apply congrArg (fun j => ν.1 j)
  exact Fin.ext (val_eqToHom_apply _ _)

/-- A repeat before the split in the first input coordinate, or at or after the
split in the second, forces a common repeat in this shuffle summand. -/
private lemma hLetter_common_repeat {n : ℕ} {a b : SimplexCategory}
    (f : (⦋n⦌ : SimplexCategory) ⟶ a) (g : (⦋n⦌ : SimplexCategory) ⟶ b)
    (r : Fin (n + 1)) (ν : Shuffle r.val (n - r.val))
    (h : (∃ j : Fin n, j.val < r.val ∧ Repeats f j) ∨
         (∃ k : Fin n, r.val ≤ k.val ∧ Repeats g k)) :
    ∃ i : Fin n, Repeats ((hLetter n r ν).fst ≫ f) i ∧
      Repeats ((hLetter n r ν).snd ≫ g) i := by
  have hr := r.isLt
  rcases h with ⟨j, hj, hfj⟩ | ⟨k, hk, hgk⟩
  · obtain ⟨i, hi₀, hi₁, hi₂⟩ := Shuffle.exists_fst_step ν j.val (by omega)
    let t : Fin n := i.cast (by omega)
    have hc : t.castSucc.cast (by omega) = i.castSucc := Fin.ext rfl
    have hs : t.succ.cast (by omega) = i.succ := Fin.ext rfl
    have e₀ : (hLetter n r ν).fst.toOrderHom t.castSucc = j.castSucc := by
      apply Fin.ext
      rw [hLetter_fst_val, hc]
      exact hi₀
    have e₁ : (hLetter n r ν).fst.toOrderHom t.succ = j.succ := by
      apply Fin.ext
      rw [hLetter_fst_val, hs]
      exact hi₁
    have e₂ : Repeats (hLetter n r ν).snd t := by
      apply Fin.ext
      rw [hLetter_snd_val, hLetter_snd_val, hc, hs, hi₂]
    refine ⟨t, ?_, e₂.comp g⟩
    change f.toOrderHom ((hLetter n r ν).fst.toOrderHom t.castSucc) =
      f.toOrderHom ((hLetter n r ν).fst.toOrderHom t.succ)
    rw [e₀, e₁]
    exact hfj
  · have hk' := k.isLt
    obtain ⟨i, hi₀, hi₁, hi₂⟩ := Shuffle.exists_snd_step ν (k.val - r.val) (by omega)
    let t : Fin n := i.cast (by omega)
    have hc : t.castSucc.cast (by omega) = i.castSucc := Fin.ext rfl
    have hs : t.succ.cast (by omega) = i.succ := Fin.ext rfl
    have e₀ : (hLetter n r ν).snd.toOrderHom t.castSucc = k.castSucc := by
      apply Fin.ext
      rw [hLetter_snd_val, hc, hi₀]
      change r.val + (k.val - r.val) = k.val
      omega
    have e₁ : (hLetter n r ν).snd.toOrderHom t.succ = k.succ := by
      apply Fin.ext
      rw [hLetter_snd_val, hs, hi₁]
      change r.val + (k.val - r.val + 1) = k.val + 1
      omega
    have e₂ : Repeats (hLetter n r ν).fst t := by
      apply Fin.ext
      rw [hLetter_fst_val, hLetter_fst_val, hc, hs, hi₂]
    refine ⟨t, e₂.comp f, ?_⟩
    change g.toOrderHom ((hLetter n r ν).snd.toOrderHom t.castSucc) =
      g.toOrderHom ((hLetter n r ν).snd.toOrderHom t.succ)
    rw [e₀, e₁]
    exact hgk

private lemma isNorm_single_of_repeat {s n : ℕ} (l : OpLetter s n) (c : ℤ)
    (i : Fin n) (hf : Repeats l.fst i) (hg : Repeats l.snd i) :
    IsNorm (Finsupp.single l c) := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    let k : OpLetter s n :=
      ⟨SimplexCategory.δ i.castSucc ≫ l.fst, SimplexCategory.δ i.castSucc ≫ l.snd⟩
    have e : (⟨SimplexCategory.σ i, SimplexCategory.σ i⟩ : OpLetter n (n + 1)).compLetter k = l := by
      cases l
      simp only [OpLetter.compLetter, k, OpLetter.mk.injEq, Category.assoc]
      exact ⟨(factor_through_σ i _ hf).symm, (factor_through_σ i _ hg).symm⟩
    have hn := IsNorm.diagDegen (SimplexCategory.σ i) (sigma_not_mono i) (Finsupp.single k c)
    rwa [DerivedOp.single_comp_single, e, mul_one] at hn

private lemma isNorm_sum {s n : ℕ} {ι : Type*} (t : Finset ι) (f : ι → DerivedOp s n)
    (h : ∀ i ∈ t, IsNorm (f i)) : IsNorm (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using IsNorm.zero
  | @insert a t ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a t)).add
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- For an ordered pair of separate repeats, every split meets at least one
repeat, hence every term of the composite has a diagonal degeneracy. -/
private lemma hOp_comp_ordered_repeat {s n : ℕ} (l : OpLetter s n) (c : ℤ)
    (j k : Fin n) (hjk : j ≤ k) (hf : Repeats l.fst j) (hg : Repeats l.snd k) :
    IsNorm ((hOp n).comp (Finsupp.single l c)) := by
  let comp : DerivedOp n n →+ DerivedOp s n :=
    { toFun M := M.comp (Finsupp.single l c)
      map_zero' := DerivedOp.zero_comp _
      map_add' M N := DerivedOp.add_comp M N _ }
  change IsNorm (comp (hOp n))
  rw [hOp, map_sum]
  refine isNorm_sum _ _ fun r _ => ?_
  rw [map_sum]
  refine isNorm_sum _ _ fun ν _ => ?_
  change IsNorm (DerivedOp.comp (Finsupp.single (hLetter n r ν) ν.sign) (Finsupp.single l c))
  rw [DerivedOp.single_comp_single]
  have H := hLetter_common_repeat l.fst l.snd r ν
  have h : (∃ i : Fin n, i.val < r.val ∧ Repeats l.fst i) ∨
      (∃ i : Fin n, r.val ≤ i.val ∧ Repeats l.snd i) := by
    by_cases hj : j.val < r.val
    · exact Or.inl ⟨j, hj, hf⟩
    · exact Or.inr ⟨k, by have : j.val ≤ k.val := hjk; omega, hg⟩
  obtain ⟨i, hi, hi'⟩ := H h
  exact isNorm_single_of_repeat _ _ i hi hi'

end BisimplicialObject
end D5.S3.HomologicalAlgebra.EilenbergZilber
