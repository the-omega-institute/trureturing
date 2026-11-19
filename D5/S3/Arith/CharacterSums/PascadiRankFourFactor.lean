/- GID: D5/S3/Arith/CharacterSums/PascadiRankFourFactor
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiRankFourFactor
   mirror-E: none(waiver:rank-four-root-relevant-factor)
   anchors: []
   utility: none
   digest: Common value and derivative congruences force a root-relevant primitive factor in rank four. -/

import D5.S3.Arith.Lattices.CofactorKernel
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Determinants and cofactors for finite families with a common value and derivative. -/

open Matrix Polynomial
open scoped BigOperators Nat

namespace D5.S3.Arith.CharacterSums.PrimeCube

open D5.S3.Arith.Lattices.CofactorKernel (cofactor det_topRow cofactor_mul_right_cross augment)

noncomputable section

private theorem independent_rows {ι κ : Type*} [Finite ι] [Fintype κ]
    (A : Matrix ι κ ℚ) (k : ℕ) (hk : A.rank = k) :
    ∃ e : Fin k → ι, Function.Injective e ∧ LinearIndependent ℚ (A.row ∘ e) := by
  classical
  obtain ⟨τ, f, hf, hspan, hli⟩ := exists_linearIndependent' ℚ A.row
  letI : Finite τ := Finite.of_injective f hf
  letI : Fintype τ := Fintype.ofFinite τ
  have hc : Fintype.card τ = k := by
    rw [← finrank_span_eq_card hli, hspan, ← A.rank_eq_finrank_span_row, hk]
  let g : Fin k ≃ τ := (Fintype.equivFinOfCardEq hc).symm
  exact ⟨f ∘ g, hf.comp g.injective, (linearIndependent_equiv g).mpr hli⟩

private theorem det_height {k : ℕ} (M : Matrix (Fin k) (Fin k) ℤ) (H : Fin k → ℝ)
    (h : ∀ i j, |(M i j : ℝ)| ≤ H j) :
    |(M.det : ℝ)| ≤ (k ! : ℕ) * ∏ j, H j := by
  classical
  let v : AbsoluteValue ℤ ℝ := (AbsoluteValue.abs : AbsoluteValue ℝ ℝ).comp
    (f := Int.castRingHom ℝ) (Int.cast_injective (α := ℝ))
  change v M.det ≤ _
  calc
    _ = v (∑ σ : Equiv.Perm (Fin k), Equiv.Perm.sign σ • ∏ j, M (σ j) j) :=
      congrArg v (Matrix.det_apply M)
    _ ≤ ∑ σ : Equiv.Perm (Fin k), v (Equiv.Perm.sign σ • ∏ j, M (σ j) j) :=
      v.sum_le _ _
    _ = ∑ σ : Equiv.Perm (Fin k), ∏ j, v (M (σ j) j) := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [v.map_units_int_smul, v.map_prod]
    _ ≤ ∑ _σ : Equiv.Perm (Fin k), ∏ j, H j := by
      gcongr with σ _ j _
      exact h _ _
    _ = _ := by simp [Fintype.card_perm, nsmul_eq_mul]

private theorem det_dvd_columns {k : ℕ} (M : Matrix (Fin k) (Fin k) ℤ)
    (d : Fin k → ℤ) (h : ∀ i j, d j ∣ M i j) :
    (∏ j, d j) ∣ M.det := by
  choose c hc using h
  refine ⟨(Matrix.of c).det, ?_⟩
  have he : M = Matrix.of (fun i j => d j * c i j) := Matrix.ext hc
  rw [he]
  exact Matrix.det_mul_row d (Matrix.of c)

private theorem eq_zero_of_dvd_of_abs_lt {d x : ℤ} (hd : d ∣ x)
    (hx : |(x : ℝ)| < (d : ℝ)) : x = 0 := by
  by_contra hn
  exact (not_le_of_gt hx) (by exact_mod_cast Int.le_abs_of_dvd hn hd)

private def congruenceBasis (β lam δ : ℤ) : Matrix (Fin 5) (Fin 5) ℤ :=
  !![1, 0, 0, 0, 0;
     β, 1, 0, 0, 0;
     β^2, 2*β, 1, 0, 0;
     -lam, -δ, 0, 1, 0;
     -lam*β, -lam-δ*β, 0, 0, 1]

private theorem congruenceBasis_det (β lam δ : ℤ) : (congruenceBasis β lam δ).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · norm_num [congruenceBasis, Fin.prod_univ_succ]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | contradiction | rfl | exact (by decide : ¬ _ ) hij

private def columnHeights (I J : ℝ) : Fin 5 → ℝ :=
  ![I^2, 2*I*J, J^2, 3*I, 3*J]

private theorem five_rows_det_zero (M : Matrix (Fin 5) (Fin 5) ℤ)
    (I J : ℝ) (p β lam δ : ℤ)
    (h : ∀ i j, |(M i j : ℝ)| ≤ columnHeights I J j)
    (h0 : ∀ i, p^3 ∣ (M * congruenceBasis β lam δ) i 0)
    (h1 : ∀ i, p ∣ (M * congruenceBasis β lam δ) i 1)
    (hgap : 2160*(I*J)^4 < (p : ℝ)^4) : M.det = 0 := by
  let v : Fin 5 → ℤ := ![p^3, p, 1, 1, 1]
  have hd := det_dvd_columns (M * congruenceBasis β lam δ) v (by
    intro i j
    fin_cases j <;> first | exact h0 i | exact h1 i | exact one_dvd _)
  have hv : ∏ j, v j = p^4 := by
    simp [v, Fin.prod_univ_succ]
    ring
  rw [hv, Matrix.det_mul, congruenceBasis_det, mul_one] at hd
  apply eq_zero_of_dvd_of_abs_lt hd
  have hb := det_height M (columnHeights I J) h
  have hprod : (5 ! : ℝ) * ∏ j, columnHeights I J j = 2160*(I*J)^4 := by
    norm_num [columnHeights, Fin.prod_univ_succ]
    ring
  norm_num at hb hprod
  rw [hprod] at hb
  simpa only [Int.cast_pow] using hb.trans_lt hgap

private theorem cofactor_four_nonzero (M : Matrix (Fin 4) (Fin 5) ℤ)
    (h : LinearIndependent ℚ (M.map (Int.castRingHom ℚ)).row) : cofactor M ≠ 0 := by
  classical
  let A := M.map (Int.castRingHom ℚ)
  have hr : Aᵀ.rank = 4 := by simpa only [Matrix.rank_transpose, Fintype.card_fin] using h.rank_matrix
  obtain ⟨e, he, hii⟩ := independent_rows Aᵀ 4 hr
  have hns : ¬ Function.Surjective e := by
    intro hs
    have := Fintype.card_le_of_surjective e hs
    norm_num at this
  obtain ⟨j, hj⟩ := not_forall.mp hns
  have hj' (i : Fin 4) : e i ≠ j := fun h => hj ⟨i, h⟩
  let f : Fin 4 → Fin 4 := fun i => (finSuccAboveEquiv j).symm ⟨e i, hj' i⟩
  have hf (i : Fin 4) : j.succAbove (f i) = e i :=
    congrArg Subtype.val ((finSuccAboveEquiv j).apply_symm_apply ⟨e i, hj' i⟩)
  have hfi : Function.Injective f := by
    intro i i' hh
    apply he
    simpa only [hf] using congrArg j.succAbove hh
  let ef := Equiv.ofBijective f ⟨hfi, Finite.injective_iff_surjective.mp hfi⟩
  have hminor : LinearIndependent ℚ ((A.submatrix id j.succAbove)ᵀ).row := by
    apply (linearIndependent_equiv ef).mp
    convert hii using 1
    ext i k
    exact congrArg (A k) (hf i)
  have hdet : (A.submatrix id j.succAbove).det ≠ 0 := by
    rw [← Matrix.det_transpose]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.linearIndependent_row_iff_isUnit.mp hminor)).ne_zero
  intro hz
  have hc := congrFun hz j
  change (-1 : ℤ) ^ (j : ℕ) * (M.submatrix id j.succAbove).det = 0 at hc
  have hi := (mul_eq_zero.mp hc).resolve_left (pow_ne_zero _ (by decide))
  apply hdet
  have hm := congrArg (Int.castRingHom ℚ) hi
  rwa [RingHom.map_det, map_zero] at hm

private theorem cofactor_height_four (M : Matrix (Fin 4) (Fin 5) ℤ) (I J : ℝ)
    (h : ∀ i j, |(M i j : ℝ)| ≤ columnHeights I J j) (j : Fin 5) :
    |((cofactor M j : ℤ) : ℝ)| ≤ 24 * ∏ k : Fin 4, columnHeights I J (j.succAbove k) := by
  simp only [cofactor, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, abs_mul,
    abs_pow, abs_neg, abs_one, one_pow, one_mul]
  simpa [Nat.factorial] using det_height (M.submatrix id j.succAbove) _ (fun i k => h i (j.succAbove k))

private theorem cofactor_four_small (M : Matrix (Fin 4) (Fin 5) ℤ) (I J : ℝ)
    (hI : 1 ≤ I) (hJ : 1 ≤ J)
    (h : ∀ i j, |(M i j : ℝ)| ≤ columnHeights I J j) (j : Fin 5) :
    |((cofactor M j : ℤ) : ℝ)| ≤ 2160*(I*J)^4 := by
  have hH (k : Fin 5) : 1 ≤ columnHeights I J k := by
    fin_cases k <;> simp only [columnHeights, Matrix.cons_val, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.isValue]
    · exact one_le_pow₀ hI
    · change 1 ≤ 2*I*J
      calc
        1 ≤ (2 : ℝ) := by norm_num
        _ = 2*(1*1) := by ring
        _ ≤ 2*(I*J) := by gcongr
        _ = _ := by ring
    · exact one_le_pow₀ hJ
    · change 1 ≤ 3*I; linarith
    · change 1 ≤ 3*J; linarith
  have hprod : 120 * ∏ k, columnHeights I J k = 2160*(I*J)^4 := by
    norm_num [columnHeights, Fin.prod_univ_succ]
    ring
  calc
    _ ≤ 24 * ∏ k : Fin 4, columnHeights I J (j.succAbove k) :=
      cofactor_height_four M I J h j
    _ ≤ 120 * ∏ k, columnHeights I J k := by
      rw [Fin.prod_univ_succAbove _ j, ← mul_assoc]
      apply mul_le_mul_of_nonneg_right
      · nlinarith only [hH j]
      · exact Finset.prod_nonneg fun k _ => zero_le_one.trans (hH (j.succAbove k))
    _ = _ := hprod

private theorem transformed_cofactor_dvd (M : Matrix (Fin 4) (Fin 5) ℤ) (p : ℤ)
    (h0 : ∀ i, p^3 ∣ M i 0) (h1 : ∀ i, p ∣ M i 1) :
    p ∣ cofactor M 0 ∧ p^3 ∣ cofactor M 1 ∧
    p^4 ∣ cofactor M 2 ∧ p^4 ∣ cofactor M 3 ∧ p^4 ∣ cofactor M 4 := by
  let v : Fin 5 → ℤ := ![p^3,p,1,1,1]
  have hv (i : Fin 4) (j : Fin 5) : v j ∣ M i j := by
    fin_cases j <;> first | exact h0 i | exact h1 i | exact one_dvd _
  have hd (j : Fin 5) : (∏ k : Fin 4, v (j.succAbove k)) ∣ cofactor M j :=
    dvd_mul_of_dvd_right (det_dvd_columns (M.submatrix id j.succAbove)
      (v ∘ j.succAbove) (fun i k => hv i (j.succAbove k))) _
  constructor
  · simpa [v, Fin.prod_univ_succ, Fin.succAbove] using hd 0
  constructor
  · simpa [v, Fin.prod_univ_succ, Fin.succAbove] using hd 1
  have he : p^3*p = p^4 := by ring
  exact ⟨by simpa [v, Fin.prod_univ_succ, Fin.succAbove, he] using hd 2,
    by simpa [v, Fin.prod_univ_succ, Fin.succAbove, he] using hd 3,
    by simpa [v, Fin.prod_univ_succ, Fin.succAbove, he] using hd 4⟩

private theorem scroll_minors (M : Matrix (Fin 4) (Fin 5) ℤ)
    (p β lam δ : ℤ) (I J : ℝ)
    (h : ∀ i j, |(M i j : ℝ)| ≤ columnHeights I J j)
    (h0 : ∀ i, p^3 ∣ (M * congruenceBasis β lam δ) i 0)
    (h1 : ∀ i, p ∣ (M * congruenceBasis β lam δ) i 1)
    (hg₂ : 233280*(I*J)^6 < (p : ℝ)^5)
    (hg₃ : 93312*(I*J)^6*J < (p : ℝ)^5) :
    let U := cofactor M
    let w := cofactor (M * congruenceBasis β lam δ)
    U 0 = w 0 ∧ U 1 = β*w 0+w 1 ∧ U 2 = β^2*w 0+2*β*w 1+w 2 ∧
    U 3 = -lam*w 0-δ*w 1+w 3 ∧ U 4 = -lam*β*w 0+(-lam-δ*β)*w 1+w 4 ∧
    U 0*U 2 = U 1^2 ∧ U 0*U 4 = U 1*U 3 := by
  dsimp only
  let U := cofactor M
  let w := cofactor (M * congruenceBasis β lam δ)
  have ht : congruenceBasis β lam δ *ᵥ w = U := by
    rw [show w = cofactor (M * congruenceBasis β lam δ) from rfl,
      cofactor_mul_right_cross, congruenceBasis_det, one_smul]
  have ht' (j : Fin 5) := (congrFun ht j).symm
  have hU0 : U 0 = w 0 := by
    simpa [congruenceBasis, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using ht' 0
  have hU1 : U 1 = β*w 0+w 1 := by
    simpa [congruenceBasis, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using ht' 1
  have hU2 : U 2 = β^2*w 0+2*β*w 1+w 2 := by
    simpa [congruenceBasis, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, add_assoc] using ht' 2
  have hU3 : U 3 = -lam*w 0-δ*w 1+w 3 := by
    simpa [congruenceBasis, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, sub_eq_add_neg,
      add_assoc] using ht' 3
  have hU4 : U 4 = -lam*β*w 0+(-lam-δ*β)*w 1+w 4 := by
    simpa [congruenceBasis, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, add_assoc] using ht' 4
  obtain ⟨d0, d1, d2, d3, d4⟩ : p ∣ w 0 ∧ p^3 ∣ w 1 ∧
      p^4 ∣ w 2 ∧ p^4 ∣ w 3 ∧ p^4 ∣ w 4 :=
    transformed_cofactor_dvd _ p h0 h1
  have he₂ : U 0*U 2-U 1^2 = w 0*w 2-w 1^2 := by rw [hU0,hU1,hU2]; ring
  have he₃ : U 0*U 4-U 1*U 3 = δ*w 1^2+w 0*w 4-β*w 0*w 3-w 1*w 3 := by
    rw [hU0,hU1,hU3,hU4]
    ring
  have hd₂ : p^5 ∣ U 0*U 2-U 1^2 := by
    rw [he₂]
    obtain ⟨a, ha⟩ := d0
    obtain ⟨b, hb⟩ := d1
    obtain ⟨c, hc⟩ := d2
    exact ⟨a*c-p*b^2, by rw [ha,hb,hc]; ring⟩
  have hd₃ : p^5 ∣ U 0*U 4-U 1*U 3 := by
    rw [he₃]
    obtain ⟨a, ha⟩ := d0
    obtain ⟨b, hb⟩ := d1
    obtain ⟨c, hc⟩ := d3
    obtain ⟨d, hd⟩ := d4
    exact ⟨δ*p*b^2+a*d-β*a*c-p^2*b*c, by rw [ha,hb,hc,hd]; ring⟩
  have hh0 : |((U 0 : ℤ) : ℝ)| ≤ 432*I^2*J^4 := by
    convert cofactor_height_four M I J h 0 using 1 <;>
      norm_num [columnHeights, Fin.prod_univ_succ, Fin.succAbove] <;> ring
  have hh1 : |((U 1 : ℤ) : ℝ)| ≤ 216*I^3*J^3 := by
    convert cofactor_height_four M I J h 1 using 1 <;>
      norm_num [columnHeights, Fin.prod_univ_succ, Fin.succAbove] <;> ring
  have hh2 : |((U 2 : ℤ) : ℝ)| ≤ 432*I^4*J^2 := by
    convert cofactor_height_four M I J h 2 using 1 <;>
      norm_num [columnHeights, Fin.prod_univ_succ, Fin.succAbove] <;> ring
  have hh3 : |((U 3 : ℤ) : ℝ)| ≤ 144*I^3*J^4 := by
    convert cofactor_height_four M I J h 3 using 1 <;>
      norm_num [columnHeights, Fin.prod_univ_succ, Fin.succAbove] <;> ring
  have hh4 : |((U 4 : ℤ) : ℝ)| ≤ 144*I^4*J^3 := by
    convert cofactor_height_four M I J h 4 using 1 <;>
      norm_num [columnHeights, Fin.prod_univ_succ, Fin.succAbove] <;> ring
  have hb₂ : |((U 0*U 2-U 1^2 : ℤ) : ℝ)| ≤ 233280*(I*J)^6 := by
    push_cast
    calc
      _ ≤ |((U 0 : ℤ) : ℝ)| * |((U 2 : ℤ) : ℝ)| + |((U 1 : ℤ) : ℝ)|^2 := by
        simpa only [abs_mul, ← abs_pow] using abs_sub (((U 0 : ℤ) : ℝ)*((U 2 : ℤ) : ℝ)) (((U 1 : ℤ) : ℝ)^2)
      _ ≤ (432*I^2*J^4)*(432*I^4*J^2)+(216*I^3*J^3)^2 := by gcongr
      _ = _ := by ring
  have hb₃ : |((U 0*U 4-U 1*U 3 : ℤ) : ℝ)| ≤ 93312*(I*J)^6*J := by
    push_cast
    calc
      _ ≤ |((U 0 : ℤ) : ℝ)| * |((U 4 : ℤ) : ℝ)| + |((U 1 : ℤ) : ℝ)| * |((U 3 : ℤ) : ℝ)| := by
        simpa only [abs_mul] using abs_sub (((U 0 : ℤ) : ℝ)*((U 4 : ℤ) : ℝ)) (((U 1 : ℤ) : ℝ)*((U 3 : ℤ) : ℝ))
      _ ≤ (432*I^2*J^4)*(144*I^4*J^3)+(216*I^3*J^3)*(144*I^3*J^4) := by
        gcongr
        exact (abs_nonneg _).trans hh1
      _ = _ := by ring
  exact ⟨hU0,hU1,hU2,hU3,hU4,
    sub_eq_zero.mp (eq_zero_of_dvd_of_abs_lt hd₂ (by simpa using hb₂.trans_lt hg₂)),
    sub_eq_zero.mp (eq_zero_of_dvd_of_abs_lt hd₃ (by simpa using hb₃.trans_lt hg₃))⟩

private theorem integral_scroll_parameter (u v w : ℤ) (hu : u ≠ 0)
    (hscroll : u*w = v^2) :
    let θ : ℚ := (v : ℚ)/u
    let a : ℤ := θ.den
    let n := θ.num
    0 < a ∧ IsCoprime a n ∧ (n : ℚ)/(a : ℚ) = θ ∧
      ∃ d : ℤ, u = d*a^2 ∧ v = d*a*n ∧ w = d*n^2 := by
  dsimp only
  let θ : ℚ := (v : ℚ)/u
  let a : ℤ := θ.den
  let n := θ.num
  have ha : 0 < a := Int.natCast_pos.mpr θ.den_pos
  have hn : IsCoprime a n := by
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    simpa [a, n, Int.gcd, Nat.gcd_comm] using θ.reduced.gcd_eq_one
  have hθ : (n : ℚ)/(a : ℚ) = θ := by simpa [a,n] using θ.num_div_den
  have huQ : (u : ℚ) ≠ 0 := by exact_mod_cast hu
  have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hv : a*v = u*n := by
    have he := (div_eq_div_iff haQ huQ).mp hθ
    exact_mod_cast (show (a : ℚ)*(v : ℚ) = (u : ℚ)*(n : ℚ) by linear_combination -he)
  have hww : a^2*w = u*n^2 := by
    apply mul_left_cancel₀ hu
    linear_combination a^2*hscroll + (a*v+u*n)*hv
  have hd : a^2 ∣ u := (hn.pow_left.pow_right).dvd_of_dvd_mul_right ⟨w, by rw [hww, mul_comm]⟩
  obtain ⟨d, hd⟩ := hd
  have hdu : u = d*a^2 := by simpa [mul_comm] using hd
  refine ⟨ha, hn, hθ, d, hdu, ?_, ?_⟩
  · apply mul_left_cancel₀ ha.ne'
    rw [hdu] at hv
    linear_combination hv
  · apply mul_left_cancel₀ (pow_ne_zero 2 ha.ne')
    rw [hdu] at hww
    linear_combination hww

/-- The exact three height gaps bound the rank by four. In rank four the
primitive factor has positive leading coefficient, reduces to a linear factor
at the common residue, and vanishes at a rational point where the baseline
linear polynomial is nonzero. -/
theorem rank_four_root_relevant_factor {ι : Type*} [Finite ι]
    (A : Matrix ι (Fin 5) ℤ) (p : ℕ) (hp : p.Prime)
    (β lam δ : ℤ) (I J : ℝ) (hJI : J ≤ I) (hJ : 1 ≤ J)
    (hq : ∀ i, |(A i 0 : ℝ)| ≤ I^2)
    (hr : ∀ i, |(A i 1 : ℝ)| ≤ 2*I*J)
    (hs : ∀ i, |(A i 2 : ℝ)| ≤ J^2)
    (hl : ∀ i, |(A i 3 : ℝ)| ≤ 3*I)
    (hm : ∀ i, |(A i 4 : ℝ)| ≤ 3*J)
    (hval : ∀ i, (p : ℤ)^3 ∣ A i 0 + A i 1*β + A i 2*β^2 - lam*(A i 3 + A i 4*β))
    (hder : ∀ i, (p : ℤ) ∣ A i 1 + 2*A i 2*β - lam*A i 4 - δ*(A i 3 + A i 4*β))
    (hg₁ : 2160*(I*J)^4 < (p : ℝ)^4)
    (hg₂ : 233280*(I*J)^6 < (p : ℝ)^5)
    (hg₃ : 93312*(I*J)^6*J < (p : ℝ)^5) :
    (A.map (Int.castRingHom ℚ)).rank ≤ 4 ∧
    ((A.map (Int.castRingHom ℚ)).rank = 4 → ∀ base : ι,
      IsUnit ((A base 3 + A base 4*β : ℤ) : ZMod p) →
      ∃ a n : ℤ, 0 < a ∧ Int.gcd a n = 1 ∧ ¬ (p : ℤ) ∣ a ∧ (p : ℤ) ∣ a*β-n ∧
        a*A base 3+n*A base 4 ≠ 0 ∧
        let f : ℤ[X] := C a * X - C n
        Irreducible f ∧ f.IsPrimitive ∧
        ∀ i, f ∣
          (C (A base 3) + C (A base 4)*X) *
            (C (A i 0) + C (A i 1)*X + C (A i 2)*X^2) -
          (C (A i 3) + C (A i 4)*X) *
            (C (A base 0) + C (A base 1)*X + C (A base 2)*X^2)) := by
  classical
  let T := congruenceBasis β lam δ
  let Aℚ := A.map (Int.castRingHom ℚ)
  letI : Fact p.Prime := ⟨hp⟩
  have hpZ : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  have hH (i : ι) (j : Fin 5) : |(A i j : ℝ)| ≤ columnHeights I J j := by
    fin_cases j <;> first | exact hq i | exact hr i | exact hs i | exact hl i | exact hm i
  have hT0 (i : ι) : (p : ℤ)^3 ∣ (A*T) i 0 := by
    convert hval i using 1
    simp [T, congruenceBasis, Matrix.mul_apply, Fin.sum_univ_succ]
    ring
  have hT1 (i : ι) : (p : ℤ) ∣ (A*T) i 1 := by
    convert hder i using 1
    simp [T, congruenceBasis, Matrix.mul_apply, Fin.sum_univ_succ]
    ring
  have hdet (e : Fin 5 → ι) : (A.submatrix e id).det = 0 :=
    five_rows_det_zero _ I J p β lam δ (fun i j => hH (e i) j)
      (fun i => hT0 (e i)) (fun i => hT1 (e i)) hg₁
  refine ⟨?_, ?_⟩
  · by_contra! hrank
    change 4 < Aℚ.rank at hrank
    have hr5 : Aℚ.rank = 5 :=
      le_antisymm (Aℚ.rank_le_card_width.trans_eq (Fintype.card_fin 5)) (by omega)
    obtain ⟨e, _, he⟩ := independent_rows Aℚ 5 hr5
    have hunit := Matrix.linearIndependent_row_iff_isUnit.mp
      (show LinearIndependent ℚ ((A.submatrix e id).map (Int.castRingHom ℚ)).row from he)
    have hn := ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero
    apply hn
    change ((Int.castRingHom ℚ).mapMatrix (A.submatrix e id)).det = 0
    rw [← RingHom.map_det, hdet e, map_zero]
  · intro h4 base hbase
    obtain ⟨e, _, he⟩ := independent_rows Aℚ 4 h4
    let M : Matrix (Fin 4) (Fin 5) ℤ := A.submatrix e id
    let U := cofactor M
    let w := cofactor (M*T)
    have hn : U ≠ 0 := cofactor_four_nonzero M he
    have hrow (i : ι) : ∑ j, A i j * U j = 0 := by
      rw [← det_topRow M (A i)]
      rw [show (augment M).updateRow 0 (A i) = A.submatrix (Fin.cases i e) id from ?_,
        hdet]
      ext j k
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [Matrix.submatrix_apply]
      · simp [Matrix.submatrix_apply, M, Matrix.updateRow_ne (Fin.succ_ne_zero j)]
    have hM (i : Fin 4) (j : Fin 5) : |(M i j : ℝ)| ≤ columnHeights I J j := hH (e i) j
    have hz0 (i : Fin 4) : (p : ℤ)^3 ∣ (M*T) i 0 := hT0 (e i)
    have hz1 (i : Fin 4) : (p : ℤ) ∣ (M*T) i 1 := hT1 (e i)
    obtain ⟨hU0,hU1,hU2,hU3,hU4,hscroll₂,hscroll₄⟩ :
        U 0 = w 0 ∧ U 1 = β*w 0+w 1 ∧ U 2 = β^2*w 0+2*β*w 1+w 2 ∧
        U 3 = -lam*w 0-δ*w 1+w 3 ∧ U 4 = -lam*β*w 0+(-lam-δ*β)*w 1+w 4 ∧
        U 0*U 2 = U 1^2 ∧ U 0*U 4 = U 1*U 3 :=
      scroll_minors M p β lam δ I J hM hz0 hz1 hg₂ hg₃
    obtain ⟨_,_,hw2,hw3,hw4⟩ : (p : ℤ) ∣ w 0 ∧ (p : ℤ)^3 ∣ w 1 ∧
        (p : ℤ)^4 ∣ w 2 ∧ (p : ℤ)^4 ∣ w 3 ∧ (p : ℤ)^4 ∣ w 4 :=
      transformed_cofactor_dvd (M*T) p hz0 hz1
    have hsmall (j : Fin 5) : |((U j : ℤ) : ℝ)| < (p : ℝ)^4 :=
      (cofactor_four_small M I J (hJ.trans hJI) hJ hM j).trans_lt hg₁
    have hno (h0 : (p : ℤ)^4 ∣ U 0) (h1 : (p : ℤ)^4 ∣ U 1) : False := by
      have d0 : (p : ℤ)^4 ∣ w 0 := by rwa [← hU0]
      have d1 : (p : ℤ)^4 ∣ w 1 := by
        rw [hU1] at h1
        exact (dvd_add_right (dvd_mul_of_dvd_right d0 β)).mp h1
      apply hn
      funext j
      change U j = 0
      apply eq_zero_of_dvd_of_abs_lt (d := (p : ℤ)^4) _ (by push_cast; exact hsmall j)
      fin_cases j
      · exact h0
      · exact h1
      · change (p : ℤ)^4 ∣ U 2
        rw [hU2]
        exact (dvd_add (dvd_mul_of_dvd_right d0 _) (dvd_mul_of_dvd_right d1 _)).add hw2
      · change (p : ℤ)^4 ∣ U 3
        rw [hU3]
        exact (dvd_sub (dvd_mul_of_dvd_right d0 _) (dvd_mul_of_dvd_right d1 _)).add hw3
      · change (p : ℤ)^4 ∣ U 4
        rw [hU4]
        exact (dvd_add (dvd_mul_of_dvd_right d0 _) (dvd_mul_of_dvd_right d1 _)).add hw4
    have hu0 : U 0 ≠ 0 := by
      intro h0
      have h1 : U 1 = 0 := by simpa only [h0, zero_mul, eq_comm (a := (0 : ℤ)), pow_eq_zero_iff (by decide : 2 ≠ 0)] using hscroll₂
      exact hno (h0 ▸ dvd_zero _) (h1 ▸ dvd_zero _)
    obtain ⟨ha, hcop, hθ, d, hd0, hd1, hd2⟩ :=
      integral_scroll_parameter (U 0) (U 1) (U 2) hu0 hscroll₂
    let θ : ℚ := ((U 1 : ℤ) : ℚ)/((U 0 : ℤ) : ℚ)
    let a : ℤ := θ.den
    let n := θ.num
    change 0 < a at ha
    change IsCoprime a n at hcop
    change (n : ℚ)/(a : ℚ) = θ at hθ
    change U 0 = d*a^2 at hd0
    change U 1 = d*a*n at hd1
    change U 2 = d*n^2 at hd2
    have hprec : w 2 = d*(n-a*β)^2 := by
      linear_combination -hU2 - β^2*hU0 + 2*β*hU1 + hd2 - 2*β*hd1 + β^2*hd0
    have hrel : (p : ℤ) ∣ n-a*β := by
      by_contra hbad
      rw [hprec] at hw2
      have hsd := hpZ.pow_dvd_of_dvd_mul_right 4 ((fun h => hbad (hpZ.dvd_of_dvd_pow h))) hw2
      exact hno (by rw [hd0]; exact dvd_mul_of_dvd_left hsd _) (by rw [hd1]; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hsd a) n)
    have hna : ¬ (p : ℤ) ∣ a := by
      intro hpa
      have hpn := (dvd_sub_left (dvd_mul_of_dvd_left hpa β)).mp hrel
      exact hpZ.not_isUnit (IsCoprime.isUnit_of_dvd' hcop hpa hpn)
    have hbaseline : a*A base 3+n*A base 4 ≠ 0 := by
      intro hz
      have hdiv : (p : ℤ) ∣ a*(A base 3+A base 4*β) := by
        convert dvd_sub (show (p : ℤ) ∣ a*A base 3+n*A base 4 from hz ▸ dvd_zero _)
          (dvd_mul_of_dvd_left hrel (A base 4)) using 1 <;> ring
      have hL := (hpZ.dvd_or_dvd hdiv).resolve_left hna
      exact hbase.ne_zero ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hL)
    let f : ℤ[X] := C a * X - C n
    have hprim : f.IsPrimitive := by
      apply isPrimitive_iff_isUnit_of_C_dvd.mpr
      intro c hc
      have hc0 := (C_dvd_iff_dvd_coeff _ _).mp hc 0
      have hc1 := (C_dvd_iff_dvd_coeff _ _).mp hc 1
      exact IsCoprime.isUnit_of_dvd' hcop
        (by simpa only [f, coeff_sub, coeff_C_mul, coeff_X_one, mul_one,
          coeff_C, if_neg (by decide : (1 : ℕ) ≠ 0), sub_zero] using hc1)
        (by simpa [f, coeff_C_mul] using hc0)
    have hf : f.map (Int.castRingHom ℚ) = C (a : ℚ) * (X - C θ) := by
      have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
      have hmul : (a : ℚ)*θ = n := by
        rw [← hθ]
        field_simp
      simp only [f, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_X, Int.coe_castRingHom, mul_sub, ← C_mul, hmul]
    have hfUnit : IsUnit (C (a : ℚ) : ℚ[X]) := isUnit_C.mpr
      (isUnit_iff_ne_zero.mpr (by exact_mod_cast ha.ne'))
    have hfirr : Irreducible f := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mpr (by
      rw [hf, irreducible_isUnit_mul hfUnit]
      exact irreducible_X_sub_C θ)
    refine ⟨a,n,ha,Int.isCoprime_iff_gcd_eq_one.mp hcop,hna,dvd_sub_comm.mp hrel,
      hbaseline,hfirr,hprim,?_⟩
    intro i
    apply (IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast _ _ hprim).mpr
    rw [hf, IsUnit.mul_left_dvd hfUnit, dvd_iff_isRoot]
    let ζ : ℚ := ((U 3 : ℤ) : ℚ)/((U 0 : ℤ) : ℚ)
    have hUQ : ((U 0 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hu0
    have hc2 : ((U 2 : ℤ) : ℚ)/((U 0 : ℤ) : ℚ) = θ^2 := by
      have he : ((U 0 : ℤ) : ℚ)*((U 2 : ℤ) : ℚ) = ((U 1 : ℤ) : ℚ)^2 := by exact_mod_cast hscroll₂
      dsimp [θ]
      field_simp
      linear_combination he
    have hc4 : ((U 4 : ℤ) : ℚ)/((U 0 : ℤ) : ℚ) = θ*ζ := by
      have he : ((U 0 : ℤ) : ℚ)*((U 4 : ℤ) : ℚ) = ((U 1 : ℤ) : ℚ)*((U 3 : ℤ) : ℚ) := by exact_mod_cast hscroll₄
      dsimp [θ,ζ]
      field_simp
      linear_combination he
    have heval (j : ι) : (A j 0 : ℚ)+(A j 1 : ℚ)*θ+(A j 2 : ℚ)*θ^2 +
        ζ*((A j 3 : ℚ)+(A j 4 : ℚ)*θ) = 0 := by
      have hh : ∑ k, (A j k : ℚ)*((U k : ℤ) : ℚ) = 0 := by exact_mod_cast hrow j
      have hh' : (A j 0 : ℚ)*((U 0 : ℤ) : ℚ) + ((A j 1 : ℚ)*((U 1 : ℤ) : ℚ) +
          ((A j 2 : ℚ)*((U 2 : ℤ) : ℚ) + ((A j 3 : ℚ)*((U 3 : ℤ) : ℚ) +
          (A j 4 : ℚ)*((U 4 : ℤ) : ℚ)))) = 0 := by
        rw [Fin.sum_univ_five] at hh
        simpa only [add_assoc] using hh
      calc
        _ = ((A j 0 : ℚ)*((U 0 : ℤ) : ℚ)+(A j 1 : ℚ)*((U 1 : ℤ) : ℚ)+
            (A j 2 : ℚ)*((U 2 : ℤ) : ℚ)+(A j 3 : ℚ)*((U 3 : ℤ) : ℚ)+(A j 4 : ℚ)*((U 4 : ℤ) : ℚ))/((U 0 : ℤ) : ℚ) := by
          rw [← hc2, mul_comm (A j 4 : ℚ) θ, mul_add, ← mul_assoc ζ θ,
            mul_comm ζ θ, ← hc4]
          dsimp [θ,ζ]
          field_simp
          <;> ring
        _ = 0 := by rw [show _ + _ + _ + _ + _ = (0 : ℚ) by linear_combination hh', zero_div]
    simp only [IsRoot, eval_map, eval₂_sub, eval₂_mul, eval₂_add, eval₂_C, eval₂_X,
      eval₂_pow, Int.coe_castRingHom]
    linear_combination ((A base 3 : ℚ)+(A base 4 : ℚ)*θ)*heval i -
      ((A i 3 : ℚ)+(A i 4 : ℚ)*θ)*heval base

end
end D5.S3.Arith.CharacterSums.PrimeCube
