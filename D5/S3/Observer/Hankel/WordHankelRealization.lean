/- GID: D5/S3/Observer/Hankel/WordHankelRealization
   generality: G
   mirror-B: D5/B/S3/Observer/Hankel/WordHankelRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Word residual rank is the attained minimum matrix dimension; full-rank blocks recover every word. -/

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Hankel.WordHankelRealization

open Module
open scoped Matrix

universe u v t
variable {K : Type u} {Alphabet : Type v} [Field K] [Fintype Alphabet]

/-- The response remaining after reading a prefix. -/
def residual (f : List Alphabet → K) (u : List Alphabet) : List Alphabet → K :=
  fun v => f (u ++ v)

/-- The span uses every finite word, including the empty word. -/
def residualSpace (f : List Alphabet → K) : Submodule K (List Alphabet → K) :=
  Submodule.span K (Set.range (residual f))

private def residualState (f : List Alphabet → K) (u : List Alphabet) : residualSpace f :=
  ⟨residual f u, Submodule.subset_span ⟨u, rfl⟩⟩

private def shiftLinear (a : Alphabet) : (List Alphabet → K) →ₗ[K] (List Alphabet → K) where
  toFun g v := g (a :: v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem shift_residual (f : List Alphabet → K) (u : List Alphabet) (a : Alphabet) :
    shiftLinear a (residual f u) = residual f (u ++ [a]) := by
  funext v
  simp [shiftLinear, residual, List.append_assoc]

private theorem shift_mem (f : List Alphabet → K) (a : Alphabet)
    {g : List Alphabet → K} (hg : g ∈ residualSpace f) :
    shiftLinear a g ∈ residualSpace f := by
  have invariant : residualSpace f ≤ (residualSpace f).comap (shiftLinear a) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨u, rfl⟩
    change shiftLinear a (residual f u) ∈ residualSpace f
    rw [shift_residual]
    exact Submodule.subset_span ⟨u ++ [a], rfl⟩
  exact invariant hg

/-- Domain restriction precedes codomain restriction to the invariant residual space. -/
def canonicalShift (f : List Alphabet → K) (a : Alphabet) :
    residualSpace f →ₗ[K] residualSpace f :=
  ((shiftLinear a).domRestrict (residualSpace f)).codRestrict (residualSpace f)
    (fun g => shift_mem f a g.property)

private theorem fold_state (f : List Alphabet → K) (w : List Alphabet)
    (g : residualSpace f) (v : List Alphabet) :
    (w.foldl (fun x a => canonicalShift f a x) g).val v = g.val (w ++ v) := by
  induction w generalizing g with
  | nil => rfl
  | cons a w ih =>
      rw [List.foldl_cons, ih]
      rfl

/-- The product preserves the order of letters, without commuting their matrices. -/
def wordProduct {d : ℕ} (A : Alphabet → Matrix (Fin d) (Fin d) K) :
    List Alphabet → Matrix (Fin d) (Fin d) K
  | [] => 1
  | a :: w => A a * wordProduct A w

private theorem wordProduct_append {d : ℕ} (A : Alphabet → Matrix (Fin d) (Fin d) K)
    (u v : List Alphabet) : wordProduct A (u ++ v) = wordProduct A u * wordProduct A v := by
  induction u with
  | nil => simp [wordProduct]
  | cons a u ih => simp only [List.cons_append, wordProduct, ih, Matrix.mul_assoc]

/-- Row initial state, letter matrices, column readout; dimension zero is allowed. -/
structure MatrixRealization (f : List Alphabet → K) (d : ℕ) where
  alpha : Fin d → K
  A : Alphabet → Matrix (Fin d) (Fin d) K
  beta : Fin d → K
  correct : ∀ w, f w = (alpha ᵥ* wordProduct A w) ⬝ᵥ beta

private def semantics {d : ℕ} (A : Alphabet → Matrix (Fin d) (Fin d) K)
    (beta : Fin d → K) : (Fin d → K) →ₗ[K] (List Alphabet → K) where
  toFun x w := (x ᵥ* wordProduct A w) ⬝ᵥ beta
  map_add' x y := by
    funext w
    simp only [Matrix.add_vecMul, add_dotProduct, Pi.add_apply]
  map_smul' c x := by
    funext w
    simp only [Matrix.smul_vecMul, smul_dotProduct, Pi.smul_apply, RingHom.id_apply]

private theorem residualSpace_le_range {f : List Alphabet → K} {d : ℕ}
    (R : MatrixRealization f d) : residualSpace f ≤ LinearMap.range (semantics R.A R.beta) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨u, rfl⟩
  refine ⟨R.alpha ᵥ* wordProduct R.A u, ?_⟩
  funext v
  change ((R.alpha ᵥ* wordProduct R.A u) ᵥ* wordProduct R.A v) ⬝ᵥ R.beta = f (u ++ v)
  rw [R.correct, wordProduct_append, Matrix.vecMul_vecMul]

private theorem finite_and_lower_bound {f : List Alphabet → K} {d : ℕ}
    (R : MatrixRealization f d) :
    FiniteDimensional K (residualSpace f) ∧ finrank K (residualSpace f) ≤ d := by
  have hle := residualSpace_le_range R
  refine ⟨Submodule.finiteDimensional_of_le hle, ?_⟩
  calc
    finrank K (residualSpace f) ≤ finrank K (LinearMap.range (semantics R.A R.beta)) :=
      Submodule.finrank_mono hle
    _ ≤ finrank K (Fin d → K) := (semantics R.A R.beta).finrank_range_le
    _ = d := by simp

private def basisLetters {f : List Alphabet → K} {d : ℕ}
    (b : Basis (Fin d) K (residualSpace f)) (a : Alphabet) : Matrix (Fin d) (Fin d) K :=
  (LinearMap.toMatrix b b (canonicalShift f a))ᵀ

private theorem basis_step {f : List Alphabet → K} {d : ℕ}
    (b : Basis (Fin d) K (residualSpace f)) (g : residualSpace f) (a : Alphabet) :
    b.equivFun (canonicalShift f a g) = b.equivFun g ᵥ* basisLetters b a := by
  rw [basisLetters, Matrix.vecMul_transpose]
  simpa only [Basis.equivFun_apply] using
    (LinearMap.toMatrix_mulVec_repr b b (canonicalShift f a) g).symm

private theorem basis_word {f : List Alphabet → K} {d : ℕ}
    (b : Basis (Fin d) K (residualSpace f)) (w : List Alphabet) (g : residualSpace f) :
    b.equivFun (w.foldl (fun x a => canonicalShift f a x) g) =
      b.equivFun g ᵥ* wordProduct (basisLetters b) w := by
  induction w generalizing g with
  | nil => simp [wordProduct]
  | cons a w ih =>
      rw [List.foldl_cons, ih, basis_step, Matrix.vecMul_vecMul, wordProduct]

private theorem basis_evaluate {f : List Alphabet → K} {d : ℕ}
    (b : Basis (Fin d) K (residualSpace f)) (g : residualSpace f) (v : List Alphabet) :
    g.val v = b.equivFun g ⬝ᵥ (fun i => (b i).val v) := by
  have h := congrArg (fun x : residualSpace f => x.val v) (b.sum_equivFun g)
  simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul, dotProduct] using h.symm

private def realizationInBasis (f : List Alphabet → K) {d : ℕ}
    (b : Basis (Fin d) K (residualSpace f)) : MatrixRealization f d where
  alpha := b.equivFun (residualState f [])
  A := basisLetters b
  beta := fun i => (b i).val []
  correct w := by
    have hs : (w.foldl (fun x a => canonicalShift f a x) (residualState f [])).val [] = f w := by
      rw [fold_state]
      simp [residualState, residual]
    rw [← hs, basis_evaluate b, basis_word]

/-- The finite residual carrier supplies a realization of exactly its own dimension. -/
def canonicalMatrixRealization (f : List Alphabet → K) [FiniteDimensional K (residualSpace f)] :
    MatrixRealization f (finrank K (residualSpace f)) :=
  realizationInBasis f (Module.finBasis K (residualSpace f))

/-- Finite realizability, the bound for every model, and attainment at the residual rank. -/
theorem finite_hankel_realization (f : List Alphabet → K) :
    (FiniteDimensional K (residualSpace f) ↔ ∃ d, Nonempty (MatrixRealization f d)) ∧
    (∀ d, MatrixRealization f d → finrank K (residualSpace f) ≤ d) ∧
    (FiniteDimensional K (residualSpace f) →
      Nonempty (MatrixRealization f (finrank K (residualSpace f)))) := by
  have attained : FiniteDimensional K (residualSpace f) →
      Nonempty (MatrixRealization f (finrank K (residualSpace f))) := by
    intro hf
    letI : FiniteDimensional K (residualSpace f) := hf
    exact ⟨canonicalMatrixRealization f⟩
  refine ⟨⟨?_, ?_⟩, (fun _ R => (finite_and_lower_bound R).2), attained⟩
  · intro hf
    exact ⟨finrank K (residualSpace f), attained hf⟩
  · rintro ⟨d, ⟨R⟩⟩
    exact (finite_and_lower_bound R).1

/-- Independent functions on an arbitrary set have a nonsingular square evaluation block. -/
theorem finite_evaluation_separation {T : Type t} {r : ℕ} (hr : 0 < r)
    (g : Fin r → T → K) (hg : LinearIndependent K g) :
    ∃ t : Fin r → T, IsUnit (Matrix.of (fun i j => g i (t j))).det := by
  classical
  let W := Submodule.span K (Set.range g)
  let b : Basis (Fin r) K W := Basis.span hg
  letI : FiniteDimensional K W := Module.Finite.of_basis b
  let E : T → Module.Dual K W := fun t =>
    { toFun := fun x => x.val t
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hspan : Submodule.span K (Set.range E) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro x hx
    have hx' : ∃ t, x.val t ≠ 0 := by
      by_contra! h
      apply hx
      apply Subtype.ext
      exact funext h
    obtain ⟨t, ht⟩ := hx'
    exact ⟨E t, ⟨t, rfl⟩, ht⟩
  have hdim : finrank K (Submodule.span K (Set.range E)) = r := by
    rw [hspan, finrank_top, Subspace.dual_finrank_eq, Module.finrank_eq_card_basis b]
    simp
  obtain ⟨q, hq, _, hqi⟩ := Submodule.exists_fun_fin_finrank_span_eq K (Set.range E)
  let e : Fin r ≃ Fin (finrank K (Submodule.span K (Set.range E))) :=
    (finCongr hdim).symm
  choose t ht using fun i : Fin r => hq (e i)
  have hi : LinearIndependent K (fun i => E (t i)) := by
    have hfamily : (fun i => E (t i)) = q ∘ e := funext ht
    rw [hfamily]
    exact hqi.comp e e.injective
  have hm := hi.map' b.dualBasis.equivFun.toLinearMap
    (LinearMap.ker_eq_bot.mpr b.dualBasis.equivFun.injective)
  have hmap : b.dualBasis.equivFun.toLinearMap ∘ (fun i => E (t i)) =
      (Matrix.of (fun i j => g i (t j))).col := by
    funext j i
    change b.dualBasis.equivFun (E (t j)) i = g i (t j)
    rw [Basis.dualBasis_equivFun]
    change ((Basis.span hg i : W) : T → K) (t j) = g i (t j)
    exact congrArg (fun x : T → K => x (t j)) (Basis.coe_span_apply hg i)
  have hcols : LinearIndependent K (Matrix.of (fun i j => g i (t j))).col := by
    rwa [hmap] at hm
  exact ⟨t, (Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_cols_iff_isUnit.mp hcols)⟩

/-- Prefix by suffix evaluations of the complete word response. -/
def block {r : ℕ} (f : List Alphabet → K) (p s : Fin r → List Alphabet) : Matrix (Fin r) (Fin r) K :=
  fun i j => f (p i ++ s j)

/-- Insert one letter between each chosen prefix and suffix. -/
def shiftedBlock {r : ℕ} (f : List Alphabet → K) (p s : Fin r → List Alphabet) (a : Alphabet) :
    Matrix (Fin r) (Fin r) K := fun i j => f (p i ++ [a] ++ s j)

private def evaluateAt {r : ℕ} (s : Fin r → List Alphabet) :
    (List Alphabet → K) →ₗ[K] (Fin r → K) :=
  LinearMap.pi (fun j => LinearMap.proj (s j))

private theorem selected_independent {r : ℕ} (f : List Alphabet → K)
    (p s : Fin r → List Alphabet) (hH : IsUnit (block f p s).det) :
    LinearIndependent K (fun i => residualState f (p i)) := by
  have hi : LinearIndependent K (fun i => residual f (p i)) :=
    LinearIndependent.of_comp (evaluateAt s)
      (by
        have hrows : (evaluateAt s) ∘ (fun i => residual f (p i)) =
            (block f p s).row := by
          funext i j
          rfl
        rw [hrows]
        exact Matrix.linearIndependent_rows_iff_isUnit.mpr
          ((Matrix.isUnit_iff_isUnit_det _).mpr hH))
  exact LinearIndependent.of_comp (residualSpace f).subtype hi

private def selectedBasis {r : ℕ} (f : List Alphabet → K)
    [FiniteDimensional K (residualSpace f)] (hglobal : finrank K (residualSpace f) = r)
    (p s : Fin r → List Alphabet) (hH : IsUnit (block f p s).det) :
    Basis (Fin r) K (residualSpace f) :=
  basisOfLinearIndependentOfCardEqFinrank' (fun i => residualState f (p i))
    (selected_independent f p s hH) (by simpa using hglobal.symm)

private theorem selectedBasis_apply {r : ℕ} (f : List Alphabet → K)
    [FiniteDimensional K (residualSpace f)] (hglobal : finrank K (residualSpace f) = r)
    (p s : Fin r → List Alphabet) (hH : IsUnit (block f p s).det) (i : Fin r) :
    selectedBasis f hglobal p s hH i = residualState f (p i) := by
  simp [selectedBasis]

private theorem selected_coordinates {r : ℕ} (f : List Alphabet → K)
    [FiniteDimensional K (residualSpace f)] (hglobal : finrank K (residualSpace f) = r)
    (p s : Fin r → List Alphabet) (hH : IsUnit (block f p s).det) (g : residualSpace f) :
    (selectedBasis f hglobal p s hH).equivFun g =
      (fun j => g.val (s j)) ᵥ* (block f p s)⁻¹ := by
  let b := selectedBasis f hglobal p s hH
  have he : b.equivFun g ᵥ* block f p s = (fun j => g.val (s j)) := by
    funext j
    simpa only [Matrix.vecMul, block, b, selectedBasis_apply, residualState, residual] using
      (basis_evaluate b g (s j)).symm
  calc
    b.equivFun g = (b.equivFun g ᵥ* block f p s) ᵥ* (block f p s)⁻¹ := by
      rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hH, Matrix.vecMul_one]
    _ = _ := by rw [he]

/-- Recovery consumes the dimension of the entire residual space, before constructing correctness. -/
def recoveredRealization {r : ℕ} (f : List Alphabet → K)
    (hfinite : FiniteDimensional K (residualSpace f))
    (hglobal : finrank K (residualSpace f) = r)
    (p s : Fin r → List Alphabet) (hH : IsUnit (block f p s).det) : MatrixRealization f r := by
  letI : FiniteDimensional K (residualSpace f) := hfinite
  let b := selectedBasis f hglobal p s hH
  let R := realizationInBasis f b
  have ha : R.alpha = (fun j => f (s j)) ᵥ* (block f p s)⁻¹ := by
    simpa only [R, realizationInBasis, residualState, residual, List.nil_append] using
      selected_coordinates f hglobal p s hH (residualState f [])
  have hb : R.beta = (fun i => f (p i)) := by
    funext i
    simp only [R, realizationInBasis, b, selectedBasis_apply, residualState,
      residual, List.append_nil]
  have hA : R.A = fun a => shiftedBlock f p s a * (block f p s)⁻¹ := by
    funext a i
    change (LinearMap.toMatrix b b (canonicalShift f a))ᵀ i = _
    rw [LinearMap.toMatrix_transpose_apply, ← Basis.equivFun_apply]
    rw [selected_coordinates]
    have hrow : (fun j => (canonicalShift f a (b i)).val (s j)) =
        shiftedBlock f p s a i := by
      funext j
      rw [show b i = residualState f (p i) from selectedBasis_apply f hglobal p s hH i]
      change f (p i ++ (a :: s j)) = f ((p i ++ [a]) ++ s j)
      rw [List.append_assoc]
      rfl
    rw [hrow, Matrix.mul_apply_eq_vecMul]
  refine ⟨(fun j => f (s j)) ᵥ* (block f p s)⁻¹,
    (fun a => shiftedBlock f p s a * (block f p s)⁻¹), (fun i => f (p i)), ?_⟩
  intro w
  rw [← ha, ← hA, ← hb]
  exact R.correct w

private theorem exists_full_rank_block (f : List Alphabet → K)
    (hfinite : FiniteDimensional K (residualSpace f)) {r : ℕ}
    (hr : 0 < r) (hglobal : finrank K (residualSpace f) = r) :
    ∃ p s : Fin r → List Alphabet, IsUnit (block f p s).det := by
  letI : FiniteDimensional K (residualSpace f) := hfinite
  letI : FiniteDimensional K (Submodule.span K (Set.range (residual f))) := hfinite
  obtain ⟨q, hq, _, hqi⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq K (Set.range (residual f))
  let e : Fin r ≃ Fin (finrank K (residualSpace f)) := (finCongr hglobal).symm
  choose p hp using fun i : Fin r => hq (e i)
  have hi : LinearIndependent K (fun i => residual f (p i)) := by
    have hfamily : (fun i => residual f (p i)) = q ∘ e := funext hp
    rw [hfamily]
    exact hqi.comp e e.injective
  obtain ⟨s, hs⟩ := finite_evaluation_separation hr (fun i => residual f (p i)) hi
  exact ⟨p, s, hs⟩

/-- Every invertible block of full global rank yields the stated minimal all-word model;
some such prefix and suffix families exist. -/
theorem full_rank_block_recovery {r : ℕ} (hr : 0 < r) (f : List Alphabet → K)
    (hfinite : FiniteDimensional K (residualSpace f))
    (hglobal : finrank K (residualSpace f) = r) :
    (∀ (p s : Fin r → List Alphabet), IsUnit (block f p s).det →
      (∀ w, f w =
      (((fun j => f (s j)) ᵥ* (block f p s)⁻¹) ᵥ*
        wordProduct (fun a => shiftedBlock f p s a * (block f p s)⁻¹) w) ⬝ᵥ
          (fun i => f (p i))) ∧
      (∀ d, MatrixRealization f d → r ≤ d)) ∧
    (∃ p' s' : Fin r → List Alphabet, IsUnit (block f p' s').det) := by
  refine ⟨?_, exists_full_rank_block f hfinite hr hglobal⟩
  intro p s hH
  refine ⟨(recoveredRealization f hfinite hglobal p s hH).correct, ?_⟩
  intro d R
  rw [← hglobal]
  exact (finite_and_lower_bound R).2

end D5.S3.Observer.Hankel.WordHankelRealization
