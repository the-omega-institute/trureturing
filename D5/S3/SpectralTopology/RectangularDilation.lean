/- GID: D5/S3/SpectralTopology/RectangularDilation
   generality: G
   mirror-B: D5/B/S3/SpectralTopology/RectangularDilation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Spectrum]
   utility: none
   digest: Positive ordered second eigenvalues of unequal Hermitian block dilations. -/

module
public import D5.S3.Quantum.Matrix.LinGProperty.ArithmeticBound
public import Mathlib.Tactic

/-! Zero padding preserves the positive ordered prefix, with characteristic-polynomial multiplicity. -/
@[expose] public section
noncomputable section
namespace D5.S3.SpectralTopology.RectangularDilation
open Matrix
open scoped BigOperators

private theorem positive_second_filter_iff (l : List ℝ) (hs : l.Pairwise (· ≥ ·))
    (x : ℝ) (hx : 0 < x) :
    (l.filter fun y => decide (0 < y))[1]? = some x ↔ l[1]? = some x := by
  cases l with
  | nil => simp
  | cons a l =>
    rcases List.pairwise_cons.mp hs with ⟨ha, hs⟩
    by_cases hapos : 0 < a
    · cases l with
      | nil => simp
      | cons b l =>
        rcases List.pairwise_cons.mp hs with ⟨hb, hs⟩
        by_cases hbpos : 0 < b
        · simp [hapos, hbpos]
        · have hf : (l.filter fun y => decide (0 < y)) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro y hy
            simpa using (not_lt.mpr (le_trans (hb y hy) (le_of_not_gt hbpos)))
          simp [hapos, hbpos, hf]
          intro h; subst b; exact (hbpos hx).elim
    · have hf : (l.filter fun y => decide (0 < y)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro y hy
        simpa using (not_lt.mpr (le_trans (ha y hy) (le_of_not_gt hapos)))
      simp only [List.filter_cons, decide_eq_false hapos, Bool.false_eq_true, ↓reduceIte, hf]
      simp only [List.getElem?_nil, reduceCtorEq, false_iff]
      intro h
      have hm : x ∈ l := List.mem_of_getElem? h
      exact (not_lt.mpr (le_trans (ha x hm) (le_of_not_gt hapos))) hx

private theorem second_eq_of_positive_roots
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (ha : 1 < Fintype.card ι) (hb : 1 < Fintype.card κ)
    (hr : (A.charpoly.roots.map Complex.re).filter (0 < ·) =
      (B.charpoly.roots.map Complex.re).filter (0 < ·))
    (hp : 0 < hA.eigenvalues₀ ⟨1,ha⟩) :
    hB.eigenvalues₀ ⟨1,hb⟩ = hA.eigenvalues₀ ⟨1,ha⟩ := by
  have hAr : A.charpoly.roots.map Complex.re = (List.ofFn hA.eigenvalues₀ : Multiset ℝ) := by
    rw [hA.roots_charpoly_eq_eigenvalues₀, Multiset.map_map]
    simp only [Function.comp_def, Complex.ofReal_re, Fin.univ_val_map]
  have hBr : B.charpoly.roots.map Complex.re = (List.ofFn hB.eigenvalues₀ : Multiset ℝ) := by
    rw [hB.roots_charpoly_eq_eigenvalues₀, Multiset.map_map]
    simp only [Function.comp_def, Complex.ofReal_re, Fin.univ_val_map]
  rw [hAr, hBr] at hr
  have hl : (List.ofFn hA.eigenvalues₀).filter (fun y => decide (0 < y)) =
      (List.ofFn hB.eigenvalues₀).filter (fun y => decide (0 < y)) := by
    apply List.Perm.eq_of_pairwise' (r := (· ≥ ·))
      ((hA.eigenvalues₀_antitone.sortedGE_ofFn.pairwise).filter _)
      ((hB.eigenvalues₀_antitone.sortedGE_ofFn.pairwise).filter _)
    exact Multiset.coe_eq_coe.mp hr
  have hget : (List.ofFn hA.eigenvalues₀)[1]? = some (hA.eigenvalues₀ ⟨1,ha⟩) := by simp [ha]
  have hpos := (positive_second_filter_iff _ hA.eigenvalues₀_antitone.sortedGE_ofFn.pairwise _ hp).mpr hget
  rw [hl] at hpos
  have hout := (positive_second_filter_iff _ hB.eigenvalues₀_antitone.sortedGE_ofFn.pairwise _ hp).mp hpos
  simpa [hb] using hout

private theorem second_eq_of_charpoly_padding
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (ha : 1 < Fintype.card ι) (hb : 1 < Fintype.card κ) (q : ℕ)
    (hr : B.charpoly = A.charpoly * Polynomial.X ^ q)
    (hp : 0 < hA.eigenvalues₀ ⟨1,ha⟩) :
    hB.eigenvalues₀ ⟨1,hb⟩ = hA.eigenvalues₀ ⟨1,ha⟩ := by
  apply second_eq_of_positive_roots A B hA hB ha hb _ hp
  rw [hr, Polynomial.roots_mul
    (mul_ne_zero (charpoly_monic A).ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)),
    Polynomial.roots_X_pow, Multiset.map_add, Multiset.filter_add]
  simp

end D5.S3.SpectralTopology.RectangularDilation
