/- GID: D5/S3/Quantum/AURICOmega/RationalGramCospectralFourCoordinates
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/RationalGramCospectralFourCoordinates
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The exact four-coordinate criterion for both cospectral rational Gram families. -/

import D5.S3.Quantum.AURICOmega.RationalGramCospectral

namespace D5.S3.Quantum.AURICOmega.RationalGramCospectralFourCoordinates

set_option autoImplicit false

open Matrix
open D5.S3.Quantum.AURICOmega.RationalGramCospectral

local notation "GramMatrix" => Matrix (Fin 4) (Fin 4) ℚ

private theorem matching_unit_axes_fit (t s : ℚ) (hs : s ≠ 0)
    (h : 1 + 4*t = s^2) (n : ℕ) :
    RealizableIn (pairedEdges t) n ↔ RealizableIn (diagonal ![1,1,2*(1-2*t),2*(1-2*t)]) n := by
  refine (fits_congr _ _ aCongr aCongrInv aCongr_mul_inv (decompose_first t) n).trans ?_
  apply diag_scaling ![1,(2*s)⁻¹,1/2,1/2]
  · intro i
    fin_cases i <;> simp [hs]
  · intro i
    fin_cases i <;> simp [h] <;> field_simp <;> ring

private theorem same_thresholds_of_square_eigenvalue (t s : ℚ) (hs : s ≠ 0)
    (h : 1 + 4*t = s^2) (n : ℕ) :
    RealizableIn (pairedEdges t) n ↔ RealizableIn (triangleBlock t) n := by
  let b := 2 * (1-2*t)
  have hb : s^2 + b = 3 := by
    dsimp [b]
    linear_combination -h
  have matching : RealizableIn (pairedEdges t) n ↔
      RealizableIn (diagonal ![1, 1, b, b]) n := matching_unit_axes_fit t s hs h n
  have triangle : RealizableIn (triangleBlock t) n ↔ RealizableIn (diagonal ![3,1,b,3*b]) n := by
    refine (fits_congr _ _ bBasis bInv bBasis_mul_inv (decompose_second t) n).trans ?_
    apply diag_scaling ![s⁻¹,1,1,1]
    · intro i
      fin_cases i <;> simp [hs]
    · intro i
      fin_cases i <;> simp [b,h] <;> field_simp <;> ring
  have hb' : b = 3 - s^2 := by linear_combination hb
  refine matching.trans ((fits_congr _ _ (P := !![s,0,0,b; 0,1,0,0; 1,0,0,-s; 0,0,1,0])
    (Q := !![s/3,0,b/3,0; 0,1,0,0; 0,0,0,1; 1/3,0,-s/3,0]) ?_ ?_ n).trans triangle.symm)
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, hb'] <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, diagonal_apply, hb'] <;> ring

private theorem matching_diagonal_in_four (b : ℚ) :
    RealizableIn (diagonal ![1,1,b,b]) 4 ↔ ∃ x y : ℚ, x^2+y^2=b := by
  constructor
  · rintro ⟨X,hX⟩
    have entry (i j : Fin 4) : X i ⬝ᵥ X j = (diagonal ![1,1,b,b] : GramMatrix) i j :=
      congrFun (congrFun hX i) j
    let earlier : Fin 2 → Fin 4 → ℚ := ![X 0,X 1]
    let standard : Fin 2 → Fin 4 → ℚ := ![![1,0,0,0],![0,1,0,0]]
    have e0 := entry 0 0
    have e1 := entry 0 1
    have e2 := entry 1 0
    have e3 := entry 1 1
    have he (i j : Fin 2) : earlier i ⬝ᵥ earlier j = standard i ⬝ᵥ standard j := by
      norm_num [diagonal_apply,dotProduct,Fin.sum_univ_succ] at e0 e1 e2 e3
      fin_cases i <;> fin_cases j <;>
        norm_num [earlier,standard,dotProduct,Fin.sum_univ_succ] <;> assumption
    obtain ⟨f,hfit,hf⟩ := fin_frame_isometry earlier standard he
    let z := f (X 2)
    have align (i : Fin 2) : standard i ⬝ᵥ z = earlier i ⬝ᵥ X 2 := by
      rw [← hfit i,show z = f (X 2) from rfl,hf]
    have hz0 : standard 0 ⬝ᵥ z = 0 := (align 0).trans (by simpa [earlier,diagonal_apply] using entry 0 2)
    have hz1 : standard 1 ⬝ᵥ z = 0 := (align 1).trans (by simpa [earlier,diagonal_apply] using entry 1 2)
    have hn : z ⬝ᵥ z = b := (hf _ _).trans (by simpa [diagonal_apply] using entry 2 2)
    norm_num [standard,dotProduct,Fin.sum_univ_succ] at hz0 hz1 hn
    rw [hz0,hz1] at hn
    exact ⟨z 2,z 3,by simpa [pow_two] using hn⟩
  · rintro ⟨x,y,rfl⟩
    refine ⟨!![1,0,0,0;0,1,0,0;0,0,x,y;0,0,-y,x], ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply,Matrix.transpose_apply,Matrix.diagonal_apply,Fin.sum_univ_succ] <;> ring

private theorem square_of_gram_determinant (G : GramMatrix) (hG : RealizableIn G 4) :
    IsSquare G.det := by
  obtain ⟨X,hX⟩ := hG
  have hh := congrArg Matrix.det hX
  rw [Matrix.det_mul,Matrix.det_transpose] at hh
  exact ⟨X.det,hh.symm⟩

private theorem four_coordinate_criterion_nondegenerate (t : ℚ)
    (ha : 1+4*t ≠ 0) (hb : 1-2*t ≠ 0) :
    (RealizableIn (pairedEdges t) 4 ↔
      ∃ s x y : ℚ, 1+4*t=s^2 ∧ 2*(1-2*t)=x^2+y^2) ∧
    (RealizableIn (triangleBlock t) 4 ↔
      ∃ s x y : ℚ, 1+4*t=s^2 ∧ 2*(1-2*t)=x^2+y^2) := by
  have hpol := spectrum_and_thresholds.1.2 t
  have hdet : (pairedEdges t).det = (1+4*t)*(1-2*t)^2 := by
    have he := congrArg (Polynomial.eval (0 : ℚ)) hpol.2
    simp [Matrix.eval_charpoly, Matrix.det_neg, Fintype.card_fin] at he
    linear_combination he
  have hsame : (pairedEdges t).det = (triangleBlock t).det := by
    simpa [Matrix.eval_charpoly, Matrix.det_neg, Fintype.card_fin] using
      congrArg (Polynomial.eval (0 : ℚ)) hpol.1
  have eigen_square (h : IsSquare (pairedEdges t).det) : ∃ s : ℚ, 1+4*t=s^2 := by
    obtain ⟨d,hd⟩ := h
    refine ⟨d/(1-2*t),?_⟩
    rw [hdet,← sq] at hd
    rw [div_pow,←hd,mul_div_cancel_right₀ _ (pow_ne_zero 2 hb)]
  have matching : RealizableIn (pairedEdges t) 4 ↔
      ∃ s x y : ℚ, 1+4*t=s^2 ∧ 2*(1-2*t)=x^2+y^2 := by
    constructor
    · intro h
      obtain ⟨s,hs⟩ := eigen_square (square_of_gram_determinant _ h)
      have hne : s ≠ 0 := by
        intro hz
        apply ha
        simp [hs,hz]
      obtain ⟨x,y,hxy⟩ := (matching_diagonal_in_four _).mp ((matching_unit_axes_fit t s hne hs 4).mp h)
      exact ⟨s,x,y,hs,hxy.symm⟩
    · rintro ⟨s,x,y,hs,hxy⟩
      have hne : s ≠ 0 := by
        intro hz
        apply ha
        simp [hs,hz]
      exact (matching_unit_axes_fit t s hne hs 4).mpr
        ((matching_diagonal_in_four _).mpr ⟨x,y,hxy.symm⟩)
  refine ⟨matching,?_⟩
  constructor
  · intro h
    obtain ⟨s,hs⟩ := eigen_square (hsame ▸ square_of_gram_determinant _ h)
    have hne : s ≠ 0 := by
      intro hz
      apply ha
      simp [hs,hz]
    exact matching.mp ((same_thresholds_of_square_eigenvalue t s hne hs 4).mpr h)
  · intro h
    obtain ⟨s,x,y,hs,hxy⟩ := h
    have hne : s ≠ 0 := by
      intro hz
      apply ha
      simp [hs,hz]
    exact (same_thresholds_of_square_eigenvalue t s hne hs 4).mp (matching.mpr ⟨s,x,y,hs,hxy⟩)

private theorem left_endpoint_matching (n : ℕ) :
    RealizableIn (pairedEdges (-(1/4))) n ↔ RealizableIn (diagonal ![1,0,3,3]) n := by
  refine (fits_congr _ _ aCongr aCongrInv aCongr_mul_inv (decompose_first _) n).trans ?_
  apply diag_scaling ![1, 1, 1/2, 1/2]
  · intro i
    fin_cases i <;> norm_num
  · intro i
    fin_cases i <;> norm_num

private theorem left_endpoint_triangle (n : ℕ) :
    RealizableIn (triangleBlock (-(1/4))) n ↔ RealizableIn (diagonal ![0,1,3,1]) n := by
  refine (fits_congr _ _ bBasis bInv bBasis_mul_inv (decompose_second _) n).trans ?_
  apply diag_scaling ![1, 1, 1, 1/3]
  · intro i
    fin_cases i <;> norm_num
  · intro i
    fin_cases i <;> norm_num

private theorem no_norm_three_under_unit_and_three (z : Fin 4 → ℚ)
    (h0 : (![1,0,0,0] : Fin 4 → ℚ) ⬝ᵥ z = 0)
    (h1 : (![0,1,1,1] : Fin 4 → ℚ) ⬝ᵥ z = 0) :
    z ⬝ᵥ z ≠ 3 := by
  intro hn
  norm_num [dotProduct, Fin.sum_univ_succ] at h0 h1 hn
  have hz3 : z 3 = -z 1 - z 2 := by linear_combination h1
  rw [h0,hz3] at hn
  apply modular_ternary_rational_descent 3 1 1 2 (by decide) (by decide) (by decide)
    (z 2) (2 * z 1 + z 2) 0
  norm_num
  linear_combination 2*hn

private theorem three_not_two_rational_squares (x y : ℚ) : x ^ 2 + y ^ 2 ≠ 3 := by
  simpa using three_not_five_sq_add_two_sq 0 x y

private theorem no_norm_three_under_two_units (z : Fin 4 → ℚ)
    (h0 : (![1,0,0,0] : Fin 4 → ℚ) ⬝ᵥ z = 0)
    (h1 : (![0,1,0,0] : Fin 4 → ℚ) ⬝ᵥ z = 0) :
    z ⬝ᵥ z ≠ 3 := by
  intro hn
  norm_num [dotProduct, Fin.sum_univ_succ] at h0 h1 hn
  rw [h0,h1] at hn
  exact three_not_two_rational_squares (z 2) (z 3) (by simpa [pow_two] using hn)

private theorem left_endpoint_matching_not_four : ¬ RealizableIn (pairedEdges (-(1/4))) 4 := by
  intro he
  obtain ⟨X,hX⟩ := (left_endpoint_matching 4).mp he
  have entry (i j : Fin 4) : X i ⬝ᵥ X j = (diagonal ![1,0,3,3] : GramMatrix) i j :=
    congrFun (congrFun hX i) j
  let earlier : Fin 2 → Fin 4 → ℚ := ![X 0,X 2]
  let standard : Fin 2 → Fin 4 → ℚ := ![![1,0,0,0],![0,1,1,1]]
  have e0 := entry 0 0
  have e1 := entry 0 2
  have e2 := entry 2 0
  have e3 := entry 2 2
  have hgram (i j : Fin 2) : earlier i ⬝ᵥ earlier j = standard i ⬝ᵥ standard j := by
    norm_num [diagonal_apply, dotProduct, Fin.sum_univ_succ] at e0 e1 e2 e3
    fin_cases i <;> fin_cases j <;>
      norm_num [earlier, standard, dotProduct, Fin.sum_univ_succ] <;> assumption
  obtain ⟨f,hfit,hf⟩ := fin_frame_isometry earlier standard hgram
  have aligned (i : Fin 2) : standard i ⬝ᵥ f (X 3) = earlier i ⬝ᵥ X 3 := by
    rw [← hfit i,hf]
  exact no_norm_three_under_unit_and_three (f (X 3))
    ((aligned 0).trans (by simpa [earlier,diagonal_apply] using entry 0 3))
    ((aligned 1).trans (by simpa [earlier,diagonal_apply] using entry 2 3))
    ((hf _ _).trans (by simpa [diagonal_apply] using entry 3 3))

private theorem left_endpoint_triangle_not_four : ¬ RealizableIn (triangleBlock (-(1/4))) 4 := by
  intro he
  obtain ⟨X,hX⟩ := (left_endpoint_triangle 4).mp he
  have entry (i j : Fin 4) : X i ⬝ᵥ X j = (diagonal ![0,1,3,1] : GramMatrix) i j :=
    congrFun (congrFun hX i) j
  let earlier : Fin 2 → Fin 4 → ℚ := ![X 1,X 3]
  let standard : Fin 2 → Fin 4 → ℚ := ![![1,0,0,0],![0,1,0,0]]
  have e0 := entry 1 1
  have e1 := entry 1 3
  have e2 := entry 3 1
  have e3 := entry 3 3
  have hgram (i j : Fin 2) : earlier i ⬝ᵥ earlier j = standard i ⬝ᵥ standard j := by
    norm_num [diagonal_apply, dotProduct, Fin.sum_univ_succ] at e0 e1 e2 e3
    fin_cases i <;> fin_cases j <;>
      norm_num [earlier, standard, dotProduct, Fin.sum_univ_succ] <;> assumption
  obtain ⟨f,hfit,hf⟩ := fin_frame_isometry earlier standard hgram
  have aligned (i : Fin 2) : standard i ⬝ᵥ f (X 2) = earlier i ⬝ᵥ X 2 := by
    rw [← hfit i,hf]
  exact no_norm_three_under_two_units (f (X 2))
    ((aligned 0).trans (by simpa [earlier,diagonal_apply] using entry 1 2))
    ((aligned 1).trans (by simpa [earlier,diagonal_apply] using entry 3 2))
    ((hf _ _).trans (by simpa [diagonal_apply] using entry 2 2))

private theorem thresholds_at_left_endpoint (n : ℕ) :
    (RealizableIn (pairedEdges (-(1/4))) n ↔ 5 ≤ n) ∧
    (RealizableIn (triangleBlock (-(1/4))) n ↔ 5 ≤ n) := by
  constructor
  · refine ⟨fun h => ?_, fun hn => ?_⟩
    · by_contra hn
      exact left_endpoint_matching_not_four (fits_mono (by omega) h)
    · apply fits_mono hn
      apply (left_endpoint_matching 5).mpr
      refine ⟨!![1,0,0,0,0; 0,0,0,0,0; 0,1,1,1,0; 0,1,-1,0,1], ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.diagonal_apply, Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_succ]
  · refine ⟨fun h => ?_, fun hn => ?_⟩
    · by_contra hn
      exact left_endpoint_triangle_not_four (fits_mono (by omega) h)
    · apply fits_mono hn
      apply (left_endpoint_triangle 5).mpr
      refine ⟨!![0,0,0,0,0; 1,0,0,0,0; 0,0,1,1,1; 0,1,0,0,0], ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.diagonal_apply, Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem right_endpoint_matching (n : ℕ) :
    RealizableIn (pairedEdges (1/2)) n ↔ RealizableIn (diagonal ![1,3,0,0]) n := by
  refine (fits_congr _ _ aCongr aCongrInv aCongr_mul_inv (decompose_first _) n).trans ?_
  apply diag_scaling ![1,1/2,1,1]
  · intro i
    fin_cases i <;> norm_num
  · intro i
    fin_cases i <;> norm_num

private theorem right_endpoint_triangle (n : ℕ) :
    RealizableIn (triangleBlock (1/2)) n ↔ RealizableIn (diagonal ![1,1,0,0]) n := by
  refine (fits_congr _ _ bBasis bInv bBasis_mul_inv (decompose_second _) n).trans ?_
  apply diag_scaling ![1/3,1,1,1]
  · intro i
    fin_cases i <;> norm_num
  · intro i
    fin_cases i <;> norm_num

private theorem right_endpoint_matching_not_three :
    ¬ RealizableIn (pairedEdges (1/2)) 3 := by
  intro h
  obtain ⟨X,hX⟩ := (right_endpoint_matching 3).mp h
  have entry (i j : Fin 4) : X i ⬝ᵥ X j = (diagonal ![1,3,0,0] : GramMatrix) i j :=
    congrFun (congrFun hX i) j
  let b : Fin 3 → ℚ := ![1,0,0]
  have hb : X 0 ⬝ᵥ X 0 = b ⬝ᵥ b := by
    have h0 := entry 0 0
    norm_num [diagonal_apply, dotProduct, Fin.sum_univ_succ, b] at h0 ⊢
    exact h0
  obtain ⟨f, hfit, hf, _⟩ := RationalGramOddPrime.rational_reflection_with_fixed_vectors (X 0) b hb
  let y := f (X 1)
  have hz : b ⬝ᵥ y = 0 := by
    rw [← hfit, show y = f (X 1) from rfl, hf]
    simpa [diagonal_apply] using entry 0 1
  have hn : y ⬝ᵥ y = 3 := (hf _ _).trans (by simpa [diagonal_apply] using entry 1 1)
  norm_num [dotProduct, Fin.sum_univ_succ,b] at hz hn
  rw [hz] at hn
  exact three_not_two_rational_squares (y 1) (y 2) (by simpa [pow_two] using hn)

private theorem right_endpoint_triangle_not_one :
    ¬ RealizableIn (triangleBlock (1/2)) 1 := by
  intro h
  obtain ⟨X,hX⟩ := (right_endpoint_triangle 1).mp h
  have entry (i j : Fin 4) : X i ⬝ᵥ X j = (diagonal ![1,1,0,0] : GramMatrix) i j :=
    congrFun (congrFun hX i) j
  have h0 := entry 0 0
  have h1 := entry 1 1
  have h01 := entry 0 1
  norm_num [dotProduct, Fin.sum_univ_succ,diagonal_apply] at h0 h1 h01
  rcases h01 with hz | hz
  · simp [hz] at h0
  · simp [hz] at h1

private theorem thresholds_at_right_endpoint (n : ℕ) :
    (RealizableIn (pairedEdges (1/2)) n ↔ 4 ≤ n) ∧
    (RealizableIn (triangleBlock (1/2)) n ↔ 2 ≤ n) := by
  constructor
  · refine ⟨fun h => ?_, fun hn => ?_⟩
    · by_contra hn
      exact right_endpoint_matching_not_three (fits_mono (by omega) h)
    · apply fits_mono hn
      apply (right_endpoint_matching 4).mpr
      refine ⟨!![1,0,0,0;0,1,1,1;0,0,0,0;0,0,0,0], ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.diagonal_apply, Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_succ]
  · refine ⟨fun h => ?_, fun hn => ?_⟩
    · by_contra hn
      exact right_endpoint_triangle_not_one (fits_mono (by omega) h)
    · apply fits_mono hn
      apply (right_endpoint_triangle 2).mpr
      refine ⟨!![1,0;0,1;0,0;0,0], ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.diagonal_apply, Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Both spectra families admit four coordinates under the same rational norm criterion. -/
theorem four_coordinate_criterion (t : ℚ) :
    (RealizableIn (pairedEdges t) 4 ↔
      t = 1/2 ∨ ∃ s x y : ℚ, 1 + 4*t = s^2 ∧ 2*(1-2*t) = x^2+y^2) ∧
    (RealizableIn (triangleBlock t) 4 ↔
      t = 1/2 ∨ ∃ s x y : ℚ, 1 + 4*t = s^2 ∧ 2*(1-2*t) = x^2+y^2) := by
  by_cases hright : t = 1/2
  · subst t
    exact ⟨iff_of_true ((thresholds_at_right_endpoint 4).1.mpr (by decide)) (Or.inl rfl),
      iff_of_true ((thresholds_at_right_endpoint 4).2.mpr (by decide)) (Or.inl rfl)⟩
  · by_cases hleft : t = -(1/4)
    · subst t
      have no_witness : ¬ (∃ s x y : ℚ, 1 + 4 * (-(1/4)) = s^2 ∧
          2*(1-2*(-(1/4))) = x^2+y^2) := by
        rintro ⟨_, x, y, _, h⟩
        exact three_not_two_rational_squares x y (by norm_num at h; exact h.symm)
      exact ⟨iff_of_false (fun hf => (by decide : ¬ 5 ≤ (4 : ℕ))
          ((thresholds_at_left_endpoint 4).1.mp hf)) (fun h => h.elim hright no_witness),
        iff_of_false (fun hf => (by decide : ¬ 5 ≤ (4 : ℕ))
          ((thresholds_at_left_endpoint 4).2.mp hf)) (fun h => h.elim hright no_witness)⟩
    · have ha : 1 + 4*t ≠ 0 := by
        intro he
        apply hleft
        linear_combination he / 4
      have hb : 1 - 2*t ≠ 0 := by
        intro he
        apply hright
        linear_combination -he / 2
      have rewrite_square :
          (∃ s x y : ℚ, 1 + 4*t = s^2 ∧ 2*(1-2*t) = x^2+y^2) ↔
          (t = 1/2 ∨ ∃ s x y : ℚ, 1 + 4*t = s^2 ∧
            2*(1-2*t) = x^2+y^2) := by
        constructor
        · exact Or.inr
        · intro h
          exact h.resolve_left hright
      exact ⟨(four_coordinate_criterion_nondegenerate t ha hb).1.trans rewrite_square,
        (four_coordinate_criterion_nondegenerate t ha hb).2.trans rewrite_square⟩

end D5.S3.Quantum.AURICOmega.RationalGramCospectralFourCoordinates
