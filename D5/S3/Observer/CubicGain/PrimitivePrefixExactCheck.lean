import D5.S3.Observer.CubicGain.PrimitivePrefix
import Mathlib.Tactic
open D5.S3.Observer.CubicGain
open D5.S3.Observer.CubicGain.CommonWordSensitivity
open D5.S3.Observer.CubicGain.PrimitivePrefix
open scoped Matrix

private def zeroWords : Fin 3 → List Bool :=
  ![[false,true],[true,false],[true]]

private def interiorWords : Fin 3 → List Bool :=
  ![[true,false,true,false,true,false,true,false,true,false,true,false,false,true],
    [false,true,true,false,true,false],
    [true,true,false,true,false,true,false,true,false]]

private theorem zeroInhabited : OrientedKernel (endpoint zeroWords) !![1,0;0,0] := by
  have hv (X : Mat) : prefixValue (endpoint zeroWords) X =
      ![X 1 0,X 0 1+X 1 0+X 1 1,X 0 1+2*X 1 0] := by
    ext i
    fin_cases i <;> norm_num [prefixValue,endpoint,zeroWords,futureProduct,
      actionM,actionJ,Matrix.trace,Matrix.diag,Matrix.mul_apply,Fin.sum_univ_two] <;> ring
  refine ⟨?_,by norm_num [Matrix.det_fin_two],?_,?_⟩
  · intro h
    have he := congrArg (fun X : Mat => X 0 0) h
    norm_num at he
  · intro X
    rw [hv]
    constructor
    · intro h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      have h2 := congrFun h 2
      simp at h0 h1 h2
      have hq : X 0 1=0 := by linarith
      have hs : X 1 1=0 := by linarith
      refine ⟨X 0 0,?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hq,hs,h0]
    · rintro ⟨v,rfl⟩
      ext i
      fin_cases i <;> simp
  · intro S hS _
    have he : polar S !![1,0;0,0] = S 1 1 := by
      simp [polar,Matrix.det_fin_two,Matrix.add_apply]
      <;> ring
    rw [he]
    exact hS 1 1

private theorem interiorInhabited :
    OrientedKernel (endpoint interiorWords) !![6,-1;-30,5] := by
  have hv (X : Mat) : prefixValue (endpoint interiorWords) X =
      ![6*X 0 0+6*X 0 1+X 1 0,
        12*X 0 0+32*X 0 1+2*X 1 0+4*X 1 1,
        31*X 0 0+141*X 0 1+5*X 1 0+21*X 1 1] := by
    ext i
    fin_cases i <;> norm_num [prefixValue,endpoint,interiorWords,futureProduct,
      actionM,actionJ,Matrix.trace,Matrix.diag,Matrix.mul_apply,Fin.sum_univ_two] <;> ring
  refine ⟨?_,by norm_num [Matrix.det_fin_two],?_,?_⟩
  · intro h
    have he := congrArg (fun X : Mat => X 0 0) h
    norm_num at he
  · intro X
    rw [hv]
    constructor
    · intro h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      have h2 := congrFun h 2
      simp at h0 h1 h2
      refine ⟨X 0 0/6,?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;> linarith
    · rintro ⟨v,rfl⟩
      ext i
      fin_cases i <;> simp <;> ring
  · intro S hS _
    have he : polar S !![6,-1;-30,5] =
        5*S 0 0+30*S 0 1+S 1 0+6*S 1 1 := by
      simp [polar,Matrix.det_fin_two,Matrix.add_apply]
      <;> ring
    rw [he]
    linarith [hS 0 0,hS 0 1,hS 1 0,hS 1 1]

example : OrientedKernel (endpoint zeroWords) (signedMatrix 1 0 1 0) := by
  apply (whole_word_primitive_representation _ _).mpr
  have hr := ((whole_word_primitive_representation _ _).mp zeroInhabited).1
  refine ⟨hr,1,0,1,0,1,![0,0,1,1],?_,by norm_num,by simp,?_⟩
  · norm_num [PrimitiveParameters]
  · constructor
    · rfl
    · intro i
      ext j
      fin_cases i <;> fin_cases j <;>
        norm_num [endpoint,zeroWords,futureProduct,actionM,actionJ,
          Matrix.mulVec,Matrix.mul_apply,dotProduct,Fin.sum_univ_two]

example : OrientedKernel (endpoint interiorWords) (signedMatrix 1 5 6 1) := by
  apply (whole_word_primitive_representation _ _).mpr
  have hr := ((whole_word_primitive_representation _ _).mp interiorInhabited).1
  refine ⟨hr,1,5,6,1,1,![0,1,2,6],?_,by norm_num,by simp,?_⟩
  · norm_num [PrimitiveParameters]
  · constructor
    · rfl
    · intro i
      ext j
      fin_cases i <;> fin_cases j <;>
        norm_num [endpoint,interiorWords,futureProduct,actionM,actionJ,
          Matrix.mulVec,Matrix.mul_apply,dotProduct,Fin.sum_univ_two]

example : endpoint interiorWords 1 = !![7,1;6,1] ∧
    endpoint interiorWords 2 = !![13,2;32,5] ∧
    endpoint interiorWords 3 = !![32,5;141,22] ∧
    (
      !![(6:ℝ),6,1;12,32,2;31,141,5]
    ).det = -20 := by
  norm_num [endpoint,interiorWords,futureProduct,actionM,actionJ,
    Matrix.mul_apply,Fin.sum_univ_two,Matrix.det_fin_three]

example : endpoint zeroWords 1 = !![1,1;0,1] ∧
    endpoint zeroWords 2 = !![1,1;1,2] ∧
    endpoint zeroWords 3 = !![1,2;1,1] ∧
    (!![(0:ℝ),1,0;1,1,1;1,2,0]).det = 1 := by
  norm_num [endpoint,zeroWords,futureProduct,actionM,actionJ,
    Matrix.mul_apply,Fin.sum_univ_two,Matrix.det_fin_three]




example (A B : Mat)
    (hA : ∀ i j, 0 ≤ A i j ∧ ∃ z : ℤ, A i j = (z:ℝ))
    (hAd : A.det=1 ∨ A.det = -1)
    (hB : ∀ i j, 0 ≤ B i j ∧ ∃ z : ℤ, B i j = (z:ℝ))
    (hBd : B.det=1 ∨ B.det = -1) :
    (∃ u : List Bool, futureProduct u*A = B) ↔
      ∀ i j, 0 ≤ (B*A⁻¹) i j := by
  classical
  have hunit : IsUnit A.det := by rcases hAd with h | h <;> simp [h]
  constructor
  · rintro ⟨u,hu⟩
    have he : B*A⁻¹ = futureProduct u := by
      rw [← hu,Matrix.mul_nonsing_inv_cancel_right _ hunit]
    rw [he]
    exact fun i j => ((legal_matrix_monoid _).mp ⟨u,rfl⟩).1 i j |>.1
  · intro hnonneg
    choose Z hZ using fun i j => (hA i j).2
    choose Y hY using fun i j => (hB i j).2
    have hi : ∃ K : Matrix (Fin 2) (Fin 2) ℤ,
        A⁻¹ = K.map (Int.castRingHom ℝ) := by
      rcases hAd with h | h
      · refine ⟨!![Z 1 1,-Z 0 1;-Z 1 0,Z 0 0],?_⟩
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.inv_def,h,Ring.inverse_eq_inv,Matrix.adjugate_fin_two,hZ]
      · refine ⟨!![-Z 1 1,Z 0 1;Z 1 0,-Z 0 0],?_⟩
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.inv_def,h,Ring.inverse_eq_inv,Matrix.adjugate_fin_two,hZ]
    obtain ⟨K,hK⟩ := hi
    have hYr : B = Y.map (Int.castRingHom ℝ) := by ext i j; exact hY i j
    have he : B*A⁻¹ = ((Y : Matrix (Fin 2) (Fin 2) ℤ)*K).map (Int.castRingHom ℝ) := by
      rw [hYr,hK,Matrix.map_mul]
    have hd : (B*A⁻¹).det=1 ∨ (B*A⁻¹).det = -1 := by
      rw [Matrix.det_mul,Matrix.det_nonsing_inv,Ring.inverse_eq_inv]
      rcases hAd with ha | ha <;> rcases hBd with hb | hb <;> simp [ha,hb]
    have hwhole : (∀ i j, 0 ≤ (B*A⁻¹) i j ∧ ∃ z : ℤ,
        (B*A⁻¹) i j = (z:ℝ)) ∧
        ((B*A⁻¹).det=1 ∨ (B*A⁻¹).det = -1) := by
      refine ⟨?_,hd⟩
      intro i j
      exact ⟨hnonneg i j,((Y : Matrix (Fin 2) (Fin 2) ℤ)*K) i j,by rw [he]; rfl⟩
    obtain ⟨u,hu⟩ := (legal_matrix_monoid _).mpr hwhole
    refine ⟨u,?_⟩
    rw [hu,Matrix.nonsing_inv_mul_cancel_right _ hunit]
