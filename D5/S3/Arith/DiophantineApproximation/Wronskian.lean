/- GID: D5/S3/Arith/DiophantineApproximation/Wronskian
   generality: G
   mirror-B: D5/B/S3/Arith/DiophantineApproximation/Wronskian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A linearly independent polynomial family has nonzero Hasse-Wronskian determinant. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.RingTheory.Polynomial.Wronskian
public import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Data.ZMod.Basic

-- Used only by the acceptance criteria.

@[expose] public section

noncomputable section

namespace Polynomial

variable {R : Type*} [CommSemiring R] {ι : Type*}

variable {S : Type*} [CommRing S] {n : ℕ}

/-- The **Hasse–Wronskian matrix**: the entry `(i, j)` is the `i`-th Hasse derivative of `ψ j`. -/
def hasseWronskianMatrix (ψ : Fin n → S[X]) : Matrix (Fin n) (Fin n) S[X] :=
  .of fun i j ↦ hasseDeriv i (ψ j)

/-- The **Hasse–Wronskian** of a family of polynomials, the determinant of
`hasseWronskianMatrix`. It differs from `wronskianDet` by the factor `∏ i, i !`. -/
def hasseWronskianDet (ψ : Fin n → S[X]) : S[X] := (hasseWronskianMatrix ψ).det

variable {K : Type*} [Field K]

/-- **Echelon basis.** A linearly independent family of polynomials over a field spans the same
space as a family with pairwise distinct degrees: one element of each degree occurring in the span
already spans it, so there are at least `n` such degrees. -/
theorem exists_natDegree_injective {n : ℕ} {ψ : Fin n → K[X]} (hψ : LinearIndependent K ψ) :
    ∃ g : Fin n → K[X], (∀ i, g i ∈ Submodule.span K (Set.range ψ)) ∧ (∀ i, g i ≠ 0) ∧
      Function.Injective fun i ↦ (g i).natDegree := by
  classical
  set V : Submodule K K[X] := Submodule.span K (Set.range ψ) with hV
  obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ f ∈ V, f.natDegree ≤ B := by
    refine ⟨Finset.univ.sup fun j ↦ (ψ j).natDegree, fun f hf ↦ ?_⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hf
    refine natDegree_sum_le_of_forall_le _ _ fun j _ ↦ ?_
    rw [smul_eq_C_mul]
    exact (natDegree_C_mul_le _ _).trans
      (Finset.le_sup (f := fun j ↦ (ψ j).natDegree) (Finset.mem_univ j))
  set D : Finset ℕ := (Finset.range (B + 1)).filter
    (fun m ↦ ∃ f ∈ V, f ≠ 0 ∧ f.natDegree = m) with hD
  have hex : ∀ m : ℕ, ∃ f : K[X], m ∈ D → (f ∈ V ∧ f ≠ 0 ∧ f.natDegree = m) := by
    intro m
    by_cases hm : m ∈ D
    · obtain ⟨f, hf1, hf2, hf3⟩ := (Finset.mem_filter.mp hm).2
      exact ⟨f, fun _ ↦ ⟨hf1, hf2, hf3⟩⟩
    · exact ⟨0, fun h ↦ absurd h hm⟩
  choose g hg using hex
  have hmemD : ∀ f ∈ V, f ≠ 0 → f.natDegree ∈ D := fun f hf hf0 ↦
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hB f hf)), f, hf, hf0, rfl⟩
  have hspan : ∀ m : ℕ, ∀ f ∈ V, f.natDegree = m → f ∈ Submodule.span K (g '' ↑D) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro f hf hfdeg
      rcases eq_or_ne f 0 with rfl | hf0
      · exact Submodule.zero_mem _
      have hmD : m ∈ D := hfdeg ▸ hmemD f hf hf0
      obtain ⟨hgV, hg0, hgdeg⟩ := hg m hmD
      set c : K := f.leadingCoeff / (g m).leadingCoeff with hc
      have hcne : c ≠ 0 :=
        div_ne_zero (leadingCoeff_ne_zero.mpr hf0) (leadingCoeff_ne_zero.mpr hg0)
      have hmem : C c * g m ∈ Submodule.span K (g '' ↑D) := by
        rw [← smul_eq_C_mul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, hmD, rfl⟩)
      have hCmemV : C c * g m ∈ V := by
        rw [← smul_eq_C_mul]; exact Submodule.smul_mem _ _ hgV
      have hdeg : (f - C c * g m).degree < f.degree := by
        refine degree_sub_lt_left ?_ hf0 ?_
        · rw [degree_C_mul hcne, degree_eq_natDegree hf0, degree_eq_natDegree hg0, hfdeg, hgdeg]
        · rw [leadingCoeff_mul, leadingCoeff_C, hc,
            div_mul_cancel₀ _ (leadingCoeff_ne_zero.mpr hg0)]
      rcases eq_or_ne (f - C c * g m) 0 with h0 | h0
      · rw [sub_eq_zero] at h0
        exact h0 ▸ hmem
      · have hlt : (f - C c * g m).natDegree < m := by
          have h := natDegree_lt_natDegree h0 hdeg
          rwa [hfdeg] at h
        have hsub := ih _ hlt (f - C c * g m) (Submodule.sub_mem _ hf hCmemV) rfl
        have hfeq : f = (f - C c * g m) + C c * g m := by ring
        rw [hfeq]
        exact Submodule.add_mem _ hsub hmem
  have hcard : n ≤ D.card := by
    have h1 : Module.finrank K V = n := by
      rw [hV, finrank_span_eq_card hψ, Fintype.card_fin]
    have : FiniteDimensional K (Submodule.span K ((D.image g : Finset K[X]) : Set K[X])) :=
      FiniteDimensional.span_of_finite _ (Finset.finite_toSet _)
    have h2 : V ≤ Submodule.span K ((D.image g : Finset K[X]) : Set K[X]) := by
      intro f hf
      refine Submodule.span_mono ?_ (hspan _ f hf rfl)
      rintro x ⟨m, hm, rfl⟩
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
    calc n = Module.finrank K V := h1.symm
      _ ≤ Module.finrank K (Submodule.span K ((D.image g : Finset K[X]) : Set K[X])) :=
          Submodule.finrank_mono h2
      _ ≤ (D.image g).card := finrank_span_finset_le_card _
      _ ≤ D.card := Finset.card_image_le
  obtain ⟨t, htD, htcard⟩ := Finset.exists_subset_card_eq hcard
  have hmem : ∀ i : Fin n, ((t.orderIsoOfFin htcard i : ℕ)) ∈ D :=
    fun i ↦ htD (t.orderIsoOfFin htcard i).2
  refine ⟨fun i ↦ g (t.orderIsoOfFin htcard i), fun i ↦ (hg _ (hmem i)).1,
    fun i ↦ (hg _ (hmem i)).2.1, fun i₁ i₂ h ↦ ?_⟩
  have h1 := (hg _ (hmem i₁)).2.2
  have h2 := (hg _ (hmem i₂)).2.2
  exact (t.orderIsoOfFin htcard).injective (Subtype.ext (by rw [← h1, ← h2]; exact h))

/-- **The hard half.** Over a field of characteristic zero the Hasse–Wronskian of a linearly
independent family is not the zero polynomial: pass to a family with pairwise distinct degrees,
whose Wronskian has a nonzero top coefficient. -/
theorem hasseWronskianDet_ne_zero [CharZero K] {n : ℕ} {ψ : Fin n → K[X]}
    (hψ : LinearIndependent K ψ) : hasseWronskianDet ψ ≠ 0 := by
  classical
  obtain ⟨g, hgV, hg0, hginj⟩ := exists_natDegree_injective hψ
  have hgdet : hasseWronskianDet g ≠ 0 := by
    have hchoose : (Matrix.of fun (i j : Fin n) ↦
        (((g j).natDegree.choose (i : ℕ) : ℕ) : K)).det ≠ 0 := by
      let d : Fin n → ℕ := fun j ↦ (g j).natDegree
      have hv : (Matrix.vandermonde fun j : Fin n ↦ (d j : K)).det ≠ 0 :=
        Matrix.det_vandermonde_ne_zero_iff.mpr (Nat.cast_injective.comp hginj)
      have he := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
        (fun j : Fin n ↦ (d j : K)) (fun i : Fin n ↦ descPochhammer K i)
        (fun i ↦ descPochhammer_natDegree K i) (fun i ↦ monic_descPochhammer K i)
      have hscale : (Matrix.of fun i j : Fin n ↦ (descPochhammer K j).eval (d i : K)).det =
          (∏ i : Fin n, ((i : ℕ).factorial : K)) *
            (Matrix.of fun i j : Fin n ↦ (((d i).choose (j : ℕ) : ℕ) : K)).det := by
        have hmat : (Matrix.of fun i j : Fin n ↦ (descPochhammer K j).eval (d i : K)) =
            (Matrix.of fun i j : Fin n ↦ ((j : ℕ).factorial : K) *
              (((d i).choose (j : ℕ) : ℕ) : K)) := by
          ext i j
          simp only [Matrix.of_apply, descPochhammer_eval_eq_descFactorial,
            Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
        rw [hmat]
        exact Matrix.det_mul_row (fun i : Fin n ↦ ((i : ℕ).factorial : K))
          (Matrix.of fun i j : Fin n ↦ (((d i).choose (j : ℕ) : ℕ) : K))
      intro hzero
      have htranspose :
          (Matrix.of fun i j : Fin n ↦ (((d i).choose (j : ℕ) : ℕ) : K)).det = 0 := by
        rw [show (Matrix.of fun i j : Fin n ↦ (((d i).choose (j : ℕ) : ℕ) : K)) =
          Matrix.transpose (Matrix.of fun i j : Fin n ↦ (((d j).choose (i : ℕ) : ℕ) : K)) from rfl,
          Matrix.det_transpose, hzero]
      exact hv (he.trans (hscale.trans (by rw [htranspose, mul_zero])))
    intro h
    have hco : (hasseWronskianDet g).coeff
        ((∑ i, (g i).natDegree) - ∑ i : Fin n, (i : ℕ))
        = (∏ i, (g i).leadingCoeff) *
          (Matrix.of fun (i j : Fin n) ↦
            (((g j).natDegree.choose (i : ℕ) : ℕ) : K)).det := by
      have hprod (s : Finset (Fin n)) (f : Fin n → K[X]) (m : Fin n → ℕ)
          (h : ∀ i ∈ s, (f i).natDegree ≤ m i) :
          (∏ i ∈ s, f i).coeff (∑ i ∈ s, m i) = ∏ i ∈ s, (f i).coeff (m i) := by
        classical
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s ha ih =>
            rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha,
              Polynomial.coeff_mul_add_eq_of_natDegree_le (h a (Finset.mem_insert_self a s))
                ((Polynomial.natDegree_prod_le s f).trans (Finset.sum_le_sum fun i hi ↦
                  h i (Finset.mem_insert_of_mem hi))),
              ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)]
      have hderiv (τ : Equiv.Perm (Fin n)) :
          (∏ i, hasseDeriv (τ i : ℕ) (g i)).coeff
            ((∑ i, (g i).natDegree) - ∑ i : Fin n, (i : ℕ))
            = (∏ i, (g i).leadingCoeff) *
              ∏ i, (((g i).natDegree.choose (τ i : ℕ) : ℕ) : K) := by
        classical
        by_cases hgood : ∀ i, (τ i : ℕ) ≤ (g i).natDegree
        · have hsum : ∑ i, ((g i).natDegree - (τ i : ℕ))
              = (∑ i, (g i).natDegree) - ∑ i : Fin n, (i : ℕ) := by
            have h1 : (∑ i, ((g i).natDegree - (τ i : ℕ))) + ∑ i, ((τ i : ℕ))
                = ∑ i, (g i).natDegree := by
              rw [← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl fun i _ ↦ Nat.sub_add_cancel (hgood i)
            have h2 : ∑ i, ((τ i : ℕ)) = ∑ i : Fin n, (i : ℕ) := Equiv.sum_comp τ fun i ↦ (i : ℕ)
            omega
          rw [← hsum, hprod _ _ _ fun i _ ↦ natDegree_hasseDeriv_le _ _,
            ← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun i _ ↦ ?_
          rw [hasseDeriv_coeff, Nat.sub_add_cancel (hgood i), coeff_natDegree, mul_comm]
        · simp only [not_forall, not_le] at hgood
          obtain ⟨i₀, hi₀⟩ := hgood
          have h1 : hasseDeriv (τ i₀ : ℕ) (g i₀) = 0 := hasseDeriv_eq_zero_of_lt_natDegree _ _ hi₀
          have h2 : (((g i₀).natDegree.choose (τ i₀ : ℕ) : ℕ) : K) = 0 := by
            rw [Nat.choose_eq_zero_of_lt hi₀, Nat.cast_zero]
          rw [Finset.prod_eq_zero (Finset.mem_univ i₀) h1, coeff_zero,
            show (∏ i, (((g i).natDegree.choose (τ i : ℕ) : ℕ) : K)) = 0 from
              Finset.prod_eq_zero (Finset.mem_univ i₀) h2, mul_zero]
      classical
      rw [hasseWronskianDet, Matrix.det_apply', finsetSum_coeff, Matrix.det_apply', Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ ↦ ?_
      have hc : ((Equiv.Perm.sign τ : ℤ) : K[X]) = C ((Equiv.Perm.sign τ : ℤ) : K) := by simp
      simp only [hasseWronskianMatrix, Matrix.of_apply]
      rw [hc, coeff_C_mul, hderiv]
      ring
    rw [h, coeff_zero] at hco
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ ↦ leadingCoeff_ne_zero.mpr (hg0 i))
      hchoose hco.symm
  choose M hM using fun i ↦ (Submodule.mem_span_range_iff_exists_fun K).mp (hgV i)
  have hmat : hasseWronskianMatrix g
      = hasseWronskianMatrix ψ * Matrix.of fun k i ↦ C (M i k) := by
    refine Matrix.ext fun i j ↦ ?_
    rw [Polynomial.hasseWronskianMatrix, Matrix.of_apply, ← hM j, map_sum, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k _ ↦ by
      rw [Polynomial.hasseWronskianMatrix, Matrix.of_apply, map_smul, smul_eq_C_mul, mul_comm]
      rfl
  intro h
  refine hgdet ?_
  rw [hasseWronskianDet, hmat, Matrix.det_mul, ← hasseWronskianDet, h, zero_mul]

end Polynomial

end

end
