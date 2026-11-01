/- GID: D5/S3/SpectralTopology/RectangularDilation
   generality: G
   mirror-B: D5/B/S3/SpectralTopology/RectangularDilation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Spectrum]
   utility: none
   digest: Positive ordered second eigenvalues of unequal Hermitian block dilations. -/

import D5.S3.Quantum.Matrix.LinGProperty.ArithmeticBound
import Mathlib.Tactic

/-! Zero padding preserves the positive ordered prefix, with characteristic-polynomial multiplicity. -/
noncomputable section
namespace D5.S3.SpectralTopology.RectangularDilation
open Matrix
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem positive_second_filter_iff (l : List ℝ) (hs : l.Pairwise (· ≥ ·))
    (x : ℝ) (hx : 0 < x) :
    (l.filter fun y => decide (0 < y))[1]? = some x ↔ l[1]? = some x := by
  cases l with
  | nil => simp
  | cons a l =>
    rcases List.pairwise_cons.mp hs with ⟨ha, hs⟩
    by_cases hapos : 0 < a
    · cases l with
      | nil => simp [hapos]
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
    simp only [Function.comp_def, Fin.univ_val_map]
    rfl
  have hBr : B.charpoly.roots.map Complex.re = (List.ofFn hB.eigenvalues₀ : Multiset ℝ) := by
    rw [hB.roots_charpoly_eq_eigenvalues₀, Multiset.map_map]
    simp only [Function.comp_def, Fin.univ_val_map]
    rfl
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

/-- Unequal blocks retain their positive second ordered eigenvalue, with algebraic multiplicity. -/
theorem unequal_dilation_second
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (B : Matrix ι κ ℂ) (ha : 1 < Fintype.card ι)
    (hP : (fromBlocks 0 B Bᴴ (0 : Matrix κ κ ℂ)).IsHermitian)
    (hp : 0 < (isHermitian_mul_conjTranspose_self B).eigenvalues₀ ⟨1,ha⟩) :
    hP.eigenvalues₀ ⟨1, by simp only [Fintype.card_sum]; omega⟩ =
      Real.sqrt ((isHermitian_mul_conjTranspose_self B).eigenvalues₀ ⟨1,ha⟩) := by
  let T := ι ⊕ κ
  let X : Matrix T T ℂ := fromBlocks 0 B 0 0
  let G : Matrix T T ℂ := fromBlocks (B * Bᴴ) 0 0 0
  have hG : G.IsHermitian := (isHermitian_mul_conjTranspose_self B).fromBlocks (by simp) isHermitian_zero
  have hXX : X * Xᴴ = G := by
    dsimp [X, G]
    rw [fromBlocks_conjTranspose, fromBlocks_multiply]
    simp
  have hn : 1 < Fintype.card T := by dsimp [T]; simp only [Fintype.card_sum]; omega
  have hg := second_eq_of_charpoly_padding (B * Bᴴ) G
    (isHermitian_mul_conjTranspose_self B) hG ha hn (Fintype.card κ)
    (by
      dsimp [G]
      rw [charpoly_fromBlocks_zero₁₂, charpoly_zero]) hp
  let e := Fintype.equivFin T
  let Y : Matrix (Fin (Fintype.card T)) (Fin (Fintype.card T)) ℂ := X.reindex e e
  have hYY : Y * Yᴴ = G.reindex e e := by
    rw [show Yᴴ = Xᴴ.reindex e e by exact conjTranspose_reindex e e X]
    change X.submatrix e.symm e.symm * Xᴴ.submatrix e.symm e.symm = _
    rw [submatrix_mul_equiv, hXX]
    rfl
  have hYG := isHermitian_mul_conjTranspose_self Y
  have hy := second_eq_of_charpoly_padding G (Y * Yᴴ) hG hYG hn
    (by simpa only [Fintype.card_fin] using hn) 0
    (by rw [hYY, charpoly_reindex]; simp) (hg.symm ▸ hp)
  have hyval : hYG.eigenvalues₀ ⟨1, by simpa only [Fintype.card_fin] using hn⟩ =
      (isHermitian_mul_conjTranspose_self B).eigenvalues₀ ⟨1,ha⟩ := hy.trans hg
  let D : Matrix (T ⊕ T) (T ⊕ T) ℂ := fromBlocks 0 X Xᴴ 0
  have hD : D.IsHermitian := isHermitian_zero.fromBlocks rfl isHermitian_zero
  let F := fromBlocks 0 Y Yᴴ (0 : Matrix (Fin (Fintype.card T)) (Fin (Fintype.card T)) ℂ)
  have hF : F.IsHermitian := isHermitian_zero.fromBlocks rfl isHermitian_zero
  have hFval := Quantum.Matrix.LinGProperty.dilation_eigenvalues Y hF
    (⟨1, by simpa only [Fintype.card_fin] using hn⟩ : Fin (Fintype.card (Fin (Fintype.card T))))
  rw [← Quantum.Schatten.singularValuesSorted_conjTranspose Y,
    Quantum.Schatten.singularValuesSorted_eq_sqrt_eigenvalues_zero] at hFval
  simp only [conjTranspose_conjTranspose] at hFval
  rw [hyval] at hFval
  have hFD : F.charpoly = D.charpoly := by
    have heq : D.reindex (Equiv.sumCongr e e) (Equiv.sumCongr e e) = F := by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;>
        simp [D, F, Y, Matrix.reindex_apply, Matrix.submatrix_apply,
          fromBlocks, conjTranspose_reindex]
    rw [← heq, charpoly_reindex]
  have hd := second_eq_of_charpoly_padding F D hF hD
    (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)
    (by simp only [Fintype.card_sum]; omega) 0 (by rw [hFD]; simp)
    (hFval.symm ▸ Real.sqrt_pos.mpr hp)
  have hdval : hD.eigenvalues₀ ⟨1, by simp only [Fintype.card_sum]; omega⟩ =
      Real.sqrt ((isHermitian_mul_conjTranspose_self B).eigenvalues₀ ⟨1,ha⟩) := hd.trans hFval
  let E : (ι ⊕ κ) ⊕ (κ ⊕ ι) ≃ T ⊕ T := {
    toFun := fun z => match z with
      | .inl (.inl i) => .inl (.inl i)
      | .inl (.inr j) => .inr (.inr j)
      | .inr (.inl j) => .inl (.inr j)
      | .inr (.inr i) => .inr (.inl i)
    invFun := fun z => match z with
      | .inl (.inl i) => .inl (.inl i)
      | .inl (.inr j) => .inr (.inl j)
      | .inr (.inl i) => .inr (.inr i)
      | .inr (.inr j) => .inl (.inr j)
    left_inv := by intro z; rcases z with (i | j) | (j | i) <;> rfl
    right_inv := by intro z; rcases z with (i | j) | (i | j) <;> rfl }
  have hperm : D.reindex E.symm E.symm =
      fromBlocks (fromBlocks 0 B Bᴴ (0 : Matrix κ κ ℂ)) 0 0
        (0 : Matrix (κ ⊕ ι) (κ ⊕ ι) ℂ) := by
    ext i j
    rcases i with (i | i) | (i | i) <;> rcases j with (j | j) | (j | j) <;>
      simp [D, X, E, Matrix.reindex_apply, Matrix.submatrix_apply, fromBlocks,
        conjTranspose_apply]
  have hchar : D.charpoly = (fromBlocks 0 B Bᴴ (0 : Matrix κ κ ℂ)).charpoly *
      Polynomial.X ^ Fintype.card (κ ⊕ ι) := by
    rw [← charpoly_reindex E.symm D, hperm, charpoly_fromBlocks_zero₁₂, charpoly_zero]
  have hr : (D.charpoly.roots.map Complex.re).filter (0 < ·) =
      ((fromBlocks 0 B Bᴴ (0 : Matrix κ κ ℂ)).charpoly.roots.map Complex.re).filter (0 < ·) := by
    rw [hchar, Polynomial.roots_mul (mul_ne_zero
      (charpoly_monic _).ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)),
      Polynomial.roots_X_pow, Multiset.map_add, Multiset.filter_add]
    simp
  have hout := second_eq_of_positive_roots D _ hD hP
    (by simp only [Fintype.card_sum]; omega)
    (by simp only [Fintype.card_sum]; omega) hr (hdval.symm ▸ Real.sqrt_pos.mpr hp)
  exact hout.trans hdval

theorem eigenvalues_ofReal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (hC : (A.map Complex.ofReal).IsHermitian) :
    hC.eigenvalues₀ = hA.eigenvalues₀ := by
  apply List.ofFn_inj.mp
  rw [← hC.sort_roots_charpoly_eq_eigenvalues₀,
    ← hA.sort_roots_charpoly_eq_eigenvalues₀]
  have hr : (A.map Complex.ofReal).charpoly.roots =
      A.charpoly.roots.map (algebraMap ℝ ℂ) := by
    rw [show A.map Complex.ofReal = A.map (algebraMap ℝ ℂ) from rfl,
      charpoly_map]
    exact ((charpoly_monic A).roots_map_of_card_eq_natDegree (algebraMap ℝ ℂ)
      (Polynomial.splits_iff_card_roots.mp hA.splits_charpoly)).symm
  rw [hr, Multiset.map_map]
  rfl

/-- The real unequal-block identity uses the ordinary real ordered spectra. -/
theorem unequal_real_dilation_second
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (B : Matrix ι κ ℝ) (ha : 1 < Fintype.card ι)
    (hP : (fromBlocks 0 B B.transpose (0 : Matrix κ κ ℝ)).IsHermitian)
    (hp : 0 < (isHermitian_mul_conjTranspose_self B).eigenvalues₀ ⟨1, ha⟩) :
    hP.eigenvalues₀ ⟨1, by simp only [Fintype.card_sum]; omega⟩ =
      Real.sqrt ((isHermitian_mul_conjTranspose_self B).eigenvalues₀ ⟨1, ha⟩) := by
  let C := B.map Complex.ofReal
  have hCG : C * Cᴴ = (B * Bᴴ).map Complex.ofReal := by
    rw [show Cᴴ = Bᴴ.map Complex.ofReal from by
      ext i j; simp [C, conjTranspose_apply]]
    exact (Matrix.map_mul (f := algebraMap ℝ ℂ) (L := B) (M := Bᴴ)).symm
  have hGram : (isHermitian_mul_conjTranspose_self C).eigenvalues₀ =
      (isHermitian_mul_conjTranspose_self B).eigenvalues₀ := by
    have transfer (M : Matrix ι ι ℂ) (he : M = (B * Bᴴ).map Complex.ofReal)
        (hM : M.IsHermitian) : hM.eigenvalues₀ =
          (isHermitian_mul_conjTranspose_self B).eigenvalues₀ := by
      subst M
      exact eigenvalues_ofReal _ _ hM
    exact transfer _ hCG _
  let P := fromBlocks 0 B B.transpose (0 : Matrix κ κ ℝ)
  have hPC : fromBlocks 0 C Cᴴ (0 : Matrix κ κ ℂ) = P.map Complex.ofReal := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [P, C, fromBlocks, conjTranspose_apply]
  have hH := hP.map Complex.ofReal (by intro x; simp)
  have hD : (fromBlocks 0 C Cᴴ (0 : Matrix κ κ ℂ)).IsHermitian := by rw [hPC]; exact hH
  have he := unequal_dilation_second C ha hD (by rw [hGram]; exact hp)
  have hEV := eigenvalues_ofReal P hP hH
  rw [hGram] at he
  simpa only [hPC, hEV] using he

end D5.S3.SpectralTopology.RectangularDilation
