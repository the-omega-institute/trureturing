/- GID: D5/S3/Quantum/Algebra/GenericMatrixIrreducibility
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/GenericMatrixIrreducibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Generic determinant and characteristic polynomial irreducibility in every positive size. -/

/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic

/-!
The determinant proof below is transplanted from the clean Apache-2.0 release of
mathlib-initiative/Etingof-RepresentationTheory-draft1, revision
c6d86a8bd52065aafb8251fa1cdcd55b609743ef, file
clean-code/release/RepresentationTheory/AuxiliaryMatrixDeterminantIrreducibility.lean.
Full license and NOTICE: docs/reports/generic-matrix-suppliers/.
Retire the transplanted determinant proof when this repository's own pinned
Mathlib contains an equivalent positive-size complex generic determinant theorem;
then replace its live uses by direct applications of that pinned declaration.
The characteristic-polynomial bridge following it is local content.
-/

open MvPolynomial Matrix Finset

namespace D5.S3.Quantum.Algebra.GenericMatrixIrreducibility

private noncomputable def genMatrix (m : ℕ) :
    Matrix (Fin m) (Fin m) (MvPolynomial (Fin m × Fin m) ℂ) :=
  of fun i j => X (i, j)

@[simp] private lemma genMatrix_apply (m : ℕ) (i j : Fin m) :
    genMatrix m i j = X (i, j) := rfl

private lemma submatrix_eq_rename (n : ℕ) (c : Fin (n + 2)) :
    det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove c)) =
    rename (Prod.map Fin.succ (Fin.succAbove c)) (det (genMatrix (n + 1))) := by
  rw [AlgHom.map_det]
  congr 1
  ext i j
  simp [genMatrix_apply, submatrix_apply, AlgHom.mapMatrix_apply, rename_X]

private lemma submatrix_vars_fst_ne_zero (n : ℕ) (c : Fin (n + 2))
    {v : Fin (n + 2) × Fin (n + 2)}
    (hv : v ∈ (det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove c))).vars) :
    v.1 ≠ 0 := by
  rw [submatrix_eq_rename] at hv
  obtain ⟨⟨a, b⟩, _, hab⟩ := mem_vars_rename _ _ hv
  exact hab ▸ Fin.succ_ne_zero a

private lemma minor00_eq_rename (n : ℕ) :
    det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0)) =
    rename (Prod.map Fin.succ Fin.succ) (det (genMatrix (n + 1))) := by
  have := submatrix_eq_rename n 0
  simp only [Fin.succAbove_zero] at this ⊢
  exact this

private lemma minor00_ne_zero (n : ℕ) :
    det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0)) ≠ 0 := by
  rw [minor00_eq_rename]
  exact (rename_injective _
    (Prod.map_injective.mpr ⟨Fin.succ_injective _, Fin.succ_injective _⟩)).ne
    (det_mvPolynomialX_ne_zero (Fin (n + 1)) ℂ)

private lemma minor00_vars (n : ℕ) :
    ((0 : Fin (n + 2)), (0 : Fin (n + 2))) ∉
    (det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0))).vars := by
  intro h
  exact absurd rfl (submatrix_vars_fst_ne_zero n 0 h)

private lemma rest_vars (n : ℕ) :
    ((0 : Fin (n + 2)), (0 : Fin (n + 2))) ∉
    (∑ j : Fin (n + 1),
      (-1 : MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℂ) ^ ((j : ℕ) + 1) *
      X ((0 : Fin (n + 2)), j.succ) *
      det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove j.succ))).vars := by
  intro h
  have h' := vars_sum_subset (Finset.univ) _ h
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at h'
  obtain ⟨j, hj⟩ := h'

  have hj' := vars_mul _ _ hj
  simp only [Finset.mem_union] at hj'
  rcases hj' with hj' | hj'
  ·
    have hj'' := vars_mul _ _ hj'
    simp only [Finset.mem_union] at hj''
    rcases hj'' with hj'' | hj''
    ·
      exact absurd (vars_pow _ _ hj'') (by simp)
    ·
      rw [vars_X] at hj''
      simp only [Finset.mem_singleton] at hj''
      exact absurd (congr_arg Prod.snd hj'').symm (Fin.succ_ne_zero j)
  ·
    exact absurd rfl (submatrix_vars_fst_ne_zero n j.succ hj')

private lemma vars_subset_vars_mul_left {σ : Type*} {R : Type*} [CommSemiring R]
    [NoZeroDivisors R] {a b : MvPolynomial σ R} (ha : a ≠ 0) (hb : b ≠ 0) :
    a.vars ⊆ (a * b).vars := by
  classical
  intro x hx
  simp only [vars_def] at hx ⊢
  rw [Multiset.mem_toFinset] at hx ⊢
  rw [← Multiset.count_pos] at hx ⊢
  rw [← degreeOf_def] at hx ⊢
  have := degreeOf_mul_eq ha hb (n := x)
  omega

private lemma rename_irreducible {σ τ : Type*} [DecidableEq σ] [DecidableEq τ]
    {f : σ → τ} (hf : Function.Injective f)
    {p : MvPolynomial σ ℂ} (hp : Irreducible p) :
    Irreducible (rename f p) := by
  constructor
  ·
    intro h
    exact hp.1 ((killCompl_rename_app hf p) ▸ h.map (killCompl hf).toRingHom)
  ·
    intro a b hab
    have hne : rename f p ≠ 0 := (rename_injective f hf).ne hp.ne_zero
    have ha : a ≠ 0 := left_ne_zero_of_mul (hab ▸ hne)
    have hb : b ≠ 0 := right_ne_zero_of_mul (hab ▸ hne)

    have hvars_rfp : ∀ x ∈ (rename f p).vars, x ∈ Set.range f := by
      intro x hx
      obtain ⟨y, _, rfl⟩ := mem_vars_rename f p hx
      exact Set.mem_range_self y

    have hvars_a : ↑a.vars ⊆ Set.range f := by
      intro x hx
      exact hvars_rfp x (hab ▸ vars_subset_vars_mul_left ha hb hx)
    have hvars_b : ↑b.vars ⊆ Set.range f := by
      intro x hx
      exact hvars_rfp x (hab ▸ mul_comm a b ▸ vars_subset_vars_mul_left hb ha hx)

    obtain ⟨a', rfl⟩ := exists_rename_eq_of_vars_subset_range a f hf hvars_a
    obtain ⟨b', rfl⟩ := exists_rename_eq_of_vars_subset_range b f hf hvars_b

    rw [← map_mul] at hab
    have hab' : p = a' * b' := (rename_injective f hf) hab

    exact (hp.isUnit_or_isUnit hab').imp (·.map (rename f).toRingHom) (·.map (rename f).toRingHom)

set_option maxHeartbeats 800000 in

private lemma minor00_isRelPrime (n : ℕ) (ih' : Irreducible (det (genMatrix (n + 1)))) :
    IsRelPrime
      (det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0)))
      (∑ j : Fin (n + 1),
        (-1 : MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℂ) ^ ((j : ℕ) + 1) *
        X ((0 : Fin (n + 2)), j.succ) *
        det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove j.succ))) := by

  have hf_irr : Irreducible (det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0))) := by
    rw [minor00_eq_rename]
    exact rename_irreducible (Prod.map_injective.mpr
      ⟨Fin.succ_injective _, Fin.succ_injective _⟩) ih'

  rw [hf_irr.isRelPrime_iff_not_dvd]

  have hf1_irr : Irreducible (det ((genMatrix (n + 2)).submatrix Fin.succ
      (Fin.succAbove (1 : Fin (n + 2))))) := by
    rw [submatrix_eq_rename]
    exact rename_irreducible (Prod.map_injective.mpr
      ⟨Fin.succ_injective _, Fin.succAbove_right_injective⟩) ih'

  let φ : (Fin (n + 2) × Fin (n + 2)) → MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℂ :=
    fun v => if v.1 = 0 then (if v.2 = 1 then 1 else 0) else X v

  have aeval_X_id : ∀ (p : MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℂ),
      aeval (X : _ → MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℂ) p = p := by
    have : aeval (X : _ → MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℂ) = AlgHom.id ℂ _ := by
      ext i; simp
    intro p; rw [this]; simp

  have hφ_fix_minor : ∀ (c : Fin (n + 2)),
      aeval φ (det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove c))) =
      det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove c)) := by
    intro c
    have hφ_eq : ∀ v ∈ (det ((genMatrix (n + 2)).submatrix Fin.succ
        (Fin.succAbove c))).vars, φ v = X v := by
      intro v hv
      simp only [φ, if_neg (submatrix_vars_fst_ne_zero n c hv)]
    rw [show aeval φ (det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove c))) =
      aeval X (det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove c))) from
      MvPolynomial.eval₂Hom_congr' rfl (fun i hi _ => hφ_eq i hi) rfl]
    exact aeval_X_id _

  have hφ_X : ∀ j : Fin (n + 1),
      φ ((0 : Fin (n + 2)), j.succ) = if j = 0 then 1 else 0 := by
    intro j
    simp only [φ, ite_true]
    rcases Decidable.eq_or_ne j 0 with rfl | hj
    · simp [show Fin.succ (0 : Fin (n + 1)) = (1 : Fin (n + 2)) from rfl]
    · simp [show Fin.succ j ≠ (1 : Fin (n + 2)) from by
        rwa [show (1 : Fin (n + 2)) = Fin.succ 0 from rfl, Ne, Fin.succ_inj], hj]

  intro ⟨q, hq⟩

  have hφ_rest : aeval φ (∑ j : Fin (n + 1),
      (-1 : MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℂ) ^ ((j : ℕ) + 1) *
      X ((0 : Fin (n + 2)), j.succ) *
      det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove j.succ))) =
      -det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove (1 : Fin (n + 2)))) := by
    simp only [map_sum, map_mul, map_pow, map_neg, map_one, aeval_X, hφ_fix_minor, hφ_X]
    rw [Fin.sum_univ_succ]
    simp

  have hdvd : det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0)) ∣
      det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 1)) := by
    have h1 : aeval φ (det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0))) ∣
        aeval φ (∑ j : Fin (n + 1),
          (-1 : MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℂ) ^ ((j : ℕ) + 1) *
          X ((0 : Fin (n + 2)), j.succ) *
          det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove j.succ))) :=
      (aeval φ).toRingHom.map_dvd ⟨q, hq⟩
    rw [hφ_fix_minor 0, hφ_rest] at h1
    exact dvd_neg.mp h1

  have hassoc := hf_irr.associated_of_dvd hf1_irr hdvd

  obtain ⟨u, hu⟩ := hassoc

  have hmem : ((1 : Fin (n + 2)), (1 : Fin (n + 2))) ∈
      (det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0))).vars := by

    by_contra habs
    let g₁ : Fin (n + 2) × Fin (n + 2) → ℂ := fun ⟨i, j⟩ => if i = j then 1 else 0
    let g₂ : Fin (n + 2) × Fin (n + 2) → ℂ := Function.update g₁ (1, 1) 0
    have hag : ∀ i ∈ (det ((genMatrix (n + 2)).submatrix Fin.succ
        (Fin.succAbove 0))).vars, g₁ i = g₂ i := by
      intro i hi
      exact (Function.update_of_ne (ne_of_mem_of_not_mem hi habs) _ _).symm

    have heq : MvPolynomial.eval g₁
          (det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0))) =
        MvPolynomial.eval g₂
          (det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0))) :=
      MvPolynomial.eval₂Hom_congr' rfl (fun i hi _ => hag i hi) rfl

    have hev1 : MvPolynomial.eval g₁
        (det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0))) = 1 := by
      rw [show MvPolynomial.eval g₁ (det ((genMatrix (n + 2)).submatrix Fin.succ
        (Fin.succAbove 0))) = det ((MvPolynomial.eval g₁).mapMatrix
        ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0))) from
        RingHom.map_det _ _]
      have : (MvPolynomial.eval g₁).mapMatrix
          ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0)) =
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
        ext i j
        simp [RingHom.mapMatrix_apply, Matrix.map_apply, submatrix_apply, genMatrix_apply,
          MvPolynomial.eval_X, g₁, Fin.succAbove_zero, Fin.succ_inj, one_apply]
      rw [this, det_one]

    have hev0 : MvPolynomial.eval g₂
        (det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0))) = 0 := by
      rw [show MvPolynomial.eval g₂ (det ((genMatrix (n + 2)).submatrix Fin.succ
        (Fin.succAbove 0))) = det ((MvPolynomial.eval g₂).mapMatrix
        ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0))) from
        RingHom.map_det _ _]
      apply det_eq_zero_of_row_eq_zero (0 : Fin (n + 1))
      intro j

      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, submatrix_apply,
        genMatrix_apply, MvPolynomial.eval_X, Fin.succAbove_zero]

      simp only [g₂, g₁, Function.update_apply]
      simp only [Prod.mk.injEq, show (1 : Fin (n + 2)) = Fin.succ 0 from rfl, Fin.succ_inj]
      split
      · simp
      · next h =>
        simp only [not_and] at h
        simp [Ne.symm (h trivial)]
    exact absurd (hev1.symm.trans (heq.trans hev0)) one_ne_zero
  have hnotmem : ((1 : Fin (n + 2)), (1 : Fin (n + 2))) ∉
      (det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove (1 : Fin (n + 2))))).vars := by
    rw [submatrix_eq_rename]
    intro h
    obtain ⟨⟨a, b⟩, _, hab⟩ := mem_vars_rename _ _ h
    simp only [Prod.map, Prod.mk.injEq] at hab
    exact absurd hab.2 (Fin.succAbove_ne 1 b)

  have hmem' : ((1 : Fin (n + 2)), (1 : Fin (n + 2))) ∈
      (det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 1))).vars :=
    hu ▸ vars_subset_vars_mul_left hf_irr.ne_zero (Units.ne_zero u) hmem
  exact hnotmem hmem'

/-- For every positive natural index, the determinant of the associated auxiliary matrix is irreducible. -/
theorem det_generic_irreducible (n : ℕ) (hn : 0 < n) :
    Irreducible (det (mvPolynomialX (Fin n) (Fin n) ℂ)) := by
  change Irreducible (det (genMatrix n))
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>

      have hdet : det (genMatrix 1) = X ((0 : Fin 1), (0 : Fin 1)) := by
        unfold genMatrix; rw [det_fin_one]; rfl
      rw [hdet]
      exact irreducible_of_totalDegree_eq_one
        (totalDegree_X _)
        (fun x hx => isUnit_of_dvd_one (by
          have := hx (Finsupp.single ((0 : Fin 1), (0 : Fin 1)) 1)
          simpa [coeff_X] using this))
    | succ n =>

      have ih' := ih (by omega)

      suffices heq : det (genMatrix (n + 2)) =
          det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0)) *
          X ((0 : Fin (n + 2)), (0 : Fin (n + 2))) +
          (∑ j : Fin (n + 1),
            (-1 : MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℂ) ^ ((j : ℕ) + 1) *
            X ((0 : Fin (n + 2)), j.succ) *
            det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove j.succ))) by
        rw [heq]
        exact irreducible_mul_X_add _ _ _
          (minor00_ne_zero n)
          (minor00_vars n)
          (rest_vars n)
          (minor00_isRelPrime n ih')

      rw [det_succ_row_zero, Fin.sum_univ_succ]
      simp only [genMatrix_apply, Fin.val_zero, pow_zero, one_mul]
      congr 1
      · ring

/-- The characteristic polynomial of the full generic complex matrix remains
irreducible over the fraction field of its exact coefficient ring. -/
theorem charpoly_generic_irreducible_fractionRing (n : ℕ) (hn : 0 < n) :
    Irreducible ((charpoly (mvPolynomialX (Fin n) (Fin n) ℂ)).map
      (algebraMap (MvPolynomial (Fin n × Fin n) ℂ)
        (FractionRing (MvPolynomial (Fin n × Fin n) ℂ)))) := by
  classical
  let R := MvPolynomial (Fin n × Fin n) ℂ
  let Y := mvPolynomialX (Fin n) (Fin n) ℂ
  let ψ : R →+* Polynomial R := MvPolynomial.eval₂Hom
    (Polynomial.C.comp MvPolynomial.C)
    (fun ij => (if ij.1 = ij.2 then Polynomial.X else 0) -
      Polynomial.C (MvPolynomial.X ij))
  let φ : Polynomial R →+* Polynomial R := Polynomial.eval₂RingHom ψ Polynomial.X
  have hφX : φ Polynomial.X = Polynomial.X := by simp [φ]
  have hφC (c : ℂ) : φ (Polynomial.C (MvPolynomial.C c)) =
      Polynomial.C (MvPolynomial.C c) := by simp [φ, ψ]
  have hφV (ij : Fin n × Fin n) : φ (Polynomial.C (MvPolynomial.X ij)) =
      (if ij.1 = ij.2 then Polynomial.X else 0) -
        Polynomial.C (MvPolynomial.X ij) := by simp [φ, ψ]
  have hinv : φ.comp φ = RingHom.id (Polynomial R) := by
    ext c ij
    · simp [RingHom.comp_apply, hφC]
    · simp only [RingHom.comp_apply, RingHom.id_apply, hφV, map_sub]
      split <;> simp_all
    · simp [RingHom.comp_apply, hφX]
  have invol : Function.Involutive φ := fun p => DFunLike.congr_fun hinv p
  let e : Polynomial R ≃+* Polynomial R := RingEquiv.ofBijective φ invol.bijective
  have hdet : Irreducible (Polynomial.C (det Y)) :=
    (Polynomial.prime_C_iff.2 (det_generic_irreducible n hn).prime).irreducible
  have hedet : e (Polynomial.C (det Y)) = charpoly Y := by
    change φ (Polynomial.C (det Y)) = det (charmatrix Y)
    rw [← RingHom.comp_apply, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.comp_apply,
      Y, mvPolynomialX_apply, hφV, charmatrix_apply, diagonal_apply]
  have hchar : Irreducible (charpoly Y) := hedet ▸ hdet.map e.toMulEquiv
  exact ((charpoly_monic Y).irreducible_iff_irreducible_map_fraction_map
    (K := FractionRing R)).1 hchar

end D5.S3.Quantum.Algebra.GenericMatrixIrreducibility
