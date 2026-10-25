import CFMPNormalizedInverseCore306Transient
import D5.S3.Geometry.Hyperideal.TwoLengthAngleSum
import D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface
import D5.S3.Geometry.Hyperideal.LengthGramBody
import D5.S3.Geometry.Hyperideal.S4OppositePairAction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Matrix.Normed

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology Matrix
open Set Filter
open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
open D5.S3.Geometry.Hyperideal.TwoLengthAngleSum
open D5.S3.Geometry.Hyperideal.FourCycleCurvature (frame)

namespace CFMPGenuineLengthNeighborhood435Transient

def sourceCosine (l : Fin 6 → ℝ) (q : Fin 6) : ℝ :=
  rawCos (fun i => Real.cosh (l i)) q

def genuine (l : Fin 6 → ℝ) : Prop :=
  (∀ i, 0 < l i) ∧ ∀ q, -1 < sourceCosine l q ∧ sourceCosine l q < 1

theorem sourceCosine_continuousAt (l : Fin 6 → ℝ) (hl : ∀ i, 0 < l i)
    (q : Fin 6) : ContinuousAt (fun p => sourceCosine p q) l := by
  have hcosh (i : Fin 6) : 1 < Real.cosh (l i) :=
    Real.one_lt_cosh.mpr (hl i).ne'
  have hleft : 0 < rad (Real.cosh (l (frame q 0)))
      (Real.cosh (l (frame q 1))) (Real.cosh (l (frame q 5))) :=
    rad_positive _ _ _ (hcosh _) (hcosh _) (hcosh _)
  have hright : 0 < rad (Real.cosh (l (frame q 0)))
      (Real.cosh (l (frame q 2))) (Real.cosh (l (frame q 4))) :=
    rad_positive _ _ _ (hcosh _) (hcosh _) (hcosh _)
  have hn : Continuous (fun p : Fin 6 → ℝ =>
      numerator (Real.cosh (p (frame q 0))) (Real.cosh (p (frame q 1)))
        (Real.cosh (p (frame q 2))) (Real.cosh (p (frame q 3)))
        (Real.cosh (p (frame q 4))) (Real.cosh (p (frame q 5)))) := by
    unfold numerator
    fun_prop
  have hL : Continuous (fun p : Fin 6 → ℝ =>
      Real.sqrt (rad (Real.cosh (p (frame q 0)))
        (Real.cosh (p (frame q 1))) (Real.cosh (p (frame q 5))))) := by
    unfold rad
    fun_prop
  have hR : Continuous (fun p : Fin 6 → ℝ =>
      Real.sqrt (rad (Real.cosh (p (frame q 0)))
        (Real.cosh (p (frame q 2))) (Real.cosh (p (frame q 4))))) := by
    unfold rad
    fun_prop
  exact (hn.continuousAt.div hL.continuousAt (Real.sqrt_pos.mpr hleft).ne').div
    hR.continuousAt (Real.sqrt_pos.mpr hright).ne'

theorem genuine_open : IsOpen {l : Fin 6 → ℝ | genuine l} := by
  apply isOpen_iff_mem_nhds.mpr
  intro l hl
  have hlength : ∀ᶠ p in 𝓝 l, ∀ i, 0 < p i :=
    Filter.eventually_all.mpr (fun i =>
      (continuous_apply i).continuousAt.eventually (Ioi_mem_nhds (hl.1 i)))
  have hcosine : ∀ᶠ p in 𝓝 l, ∀ q,
      -1 < sourceCosine p q ∧ sourceCosine p q < 1 :=
    Filter.eventually_all.mpr (fun q =>
      (sourceCosine_continuousAt l hl.1 q).eventually
        (Ioo_mem_nhds (hl.2 q).1 (hl.2 q).2))
  exact hlength.and hcosine

theorem path_eventually_genuine (l : ℝ → Fin 6 → ℝ) (t : ℝ)
    (hl : ContinuousAt l t) (hg : genuine (l t)) :
    ∀ᶠ s in 𝓝 t, genuine (l s) := hl.eventually (genuine_open.mem_nhds hg)

theorem path_common_interval (l : ℝ → Fin 6 → ℝ) (t : ℝ)
    (hl : ContinuousAt l t) (hg : genuine (l t)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Icc (t-ε) (t+ε), genuine (l s) := by
  obtain ⟨ε,hε,hsmall⟩ := (Metric.nhds_basis_closedBall (x := t)).mem_iff.mp
    (path_eventually_genuine l t hl hg)
  refine ⟨ε,hε,?_⟩
  intro s hs
  apply hsmall
  simpa only [Real.closedBall_eq_Icc] using hs

theorem genuine_realization_exists (l : Fin 6 → ℝ) (hg : genuine l) :
    ∃ (M : Matrix (Fin 4) (Fin 4) ℝ)
      (f : D5.S3.Geometry.Hyperideal.LengthGramBody.cutBody l →
        D5.S3.Geometry.HyperbolicUpperHalfSpace.HyperbolicThreeSpace),
      (∀ i j, D5.S3.Geometry.Hyperideal.LengthGramBody.lorentz (M i) (M j) =
        D5.S3.Geometry.Hyperideal.LengthGramBody.lengthGram l i j) ∧
      Continuous f ∧ Function.Injective f ∧ IsCompact (range f) ∧
      (∀ w, ∃ y : Fin 4 → ℝ,
        y = (D5.S3.Geometry.Hyperideal.LengthGramBody.radial l w.val) ᵥ* M ∧
        D5.S3.Geometry.Hyperideal.LengthGramBody.lorentz y y = -1 ∧ 0 < y 3 ∧
        (f w).coordinates.val = WithLp.toLp 2
          (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2))) := by
  have hc : -1 < cosine (Real.cosh (l 0)) (Real.cosh (l 1)) (Real.cosh (l 2))
      (Real.cosh (l 3)) (Real.cosh (l 4)) (Real.cosh (l 5)) ∧
      cosine (Real.cosh (l 0)) (Real.cosh (l 1)) (Real.cosh (l 2))
        (Real.cosh (l 3)) (Real.cosh (l 4)) (Real.cosh (l 5)) < 1 := by
    convert hg.2 0 using 1 <;> rfl
  obtain ⟨M,hm,_,_,f,hf,hfi,hcompact,_,hsource⟩ :=
    (D5.S3.Geometry.Hyperideal.LengthGramBody.shared_radial_body l hg.1).2.2.2.2.2.2.2.2.2 hc
  exact ⟨M,f,hm,hf,hfi,hcompact,hsource⟩

end CFMPGenuineLengthNeighborhood435Transient
end

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix BigOperators Topology
open Set Filter
open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
open D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface
namespace CFMPOriginalUnitSideCosine435Transient

theorem original_gram_cofactors (r a b o c d : ℝ) :
    (gram r a b o c d).adjugate 2 2 = -D2 r b c ∧
    (gram r a b o c d).adjugate 3 3 = -D1 r a d ∧
    (gram r a b o c d).adjugate 2 3 = N r a b o c d := by
  constructor
  · norm_num [Matrix.adjugate_fin_succ_eq_det_submatrix,gram,D2,
      Matrix.det_fin_three,Matrix.det_fin_two,Matrix.det_fin_one,Matrix.det_fin_zero,
      Matrix.submatrix_apply,Fin.sum_univ_succ,Matrix.of_apply,
      Matrix.cons_val_zero',Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.cons_val_succ',Matrix.head_cons,Matrix.tail_cons,Matrix.cons_val_succ,
      Matrix.vecHead,Matrix.vecTail,Fin.succAbove,Fin.reduceEq,Fin.reduceFinMk,
      Fin.castSucc,Fin.castAdd,Fin.succ,Fin.val_zero,Fin.val_succ,
      Nat.succ_eq_add_one,Fin.castLE,Fin.cast]
    ring
  · constructor
    · norm_num [Matrix.adjugate_fin_succ_eq_det_submatrix,gram,D1,
        Matrix.det_fin_three,Matrix.det_fin_two,Matrix.det_fin_one,Matrix.det_fin_zero,
        Matrix.submatrix_apply,Fin.sum_univ_succ,Matrix.of_apply,
        Matrix.cons_val_zero',Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
        Matrix.cons_val_succ',Matrix.head_cons,Matrix.tail_cons,Matrix.cons_val_succ,
        Matrix.vecHead,Matrix.vecTail,Fin.succAbove,Fin.reduceEq,Fin.reduceFinMk,
        Fin.castSucc,Fin.castAdd,Fin.succ,Fin.val_zero,Fin.val_succ,
        Nat.succ_eq_add_one,Fin.castLE,Fin.cast]
      ring
    · norm_num [Matrix.adjugate_fin_succ_eq_det_submatrix,gram,N,
        Matrix.det_fin_three,Matrix.det_fin_two,Matrix.det_fin_one,Matrix.det_fin_zero,
        Matrix.submatrix_apply,Fin.sum_univ_succ,Matrix.of_apply,
        Matrix.cons_val_zero',Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
        Matrix.cons_val_succ',Matrix.head_cons,Matrix.tail_cons,Matrix.cons_val_succ,
        Matrix.vecHead,Matrix.vecTail,Fin.succAbove,Fin.reduceEq,Fin.reduceFinMk,
        Fin.castSucc,Fin.castAdd,Fin.succ,Fin.val_zero,Fin.val_succ,
        Nat.succ_eq_add_one,Fin.castLE,Fin.cast]
      ring

theorem inverse_gram_cosine (r a b o c d : ℝ)
    (h1 : 0 < D1 r a d) (h2 : 0 < D2 r b c)
    (hdet : (gram r a b o c d).det < 0) :
    -((gram r a b o c d)⁻¹ 2 3 /
      (Real.sqrt ((gram r a b o c d)⁻¹ 2 2)*
        Real.sqrt ((gram r a b o c d)⁻¹ 3 3))) = cosine r a b o c d := by
  let G := gram r a b o c d
  let delta := -G.det
  have hd : 0 < delta := neg_pos.mpr hdet
  have hi (i j : Fin 4) : G⁻¹ i j = G.adjugate i j/G.det := by
    rw [Matrix.inv_def]
    simp only [Ring.inverse_eq_inv',Matrix.smul_apply,smul_eq_mul]
    ring
  obtain ⟨h22,h33,h23⟩ := original_gram_cofactors r a b o c d
  have hi22 : G⁻¹ 2 2 = D2 r b c/delta := by rw [hi,h22];simp [delta, neg_div, div_neg]
  have hi33 : G⁻¹ 3 3 = D1 r a d/delta := by rw [hi,h33];simp [delta, neg_div, div_neg]
  have hi23 : G⁻¹ 2 3 = -N r a b o c d/delta := by rw [hi,h23];simp [delta]
  have hr1 : rad r a d = D1 r a d := by dsimp [rad,D1];ring
  have hr2 : rad r b c = D2 r b c := by dsimp [rad,D2];ring
  have hcos : cosine r a b o c d =
      N r a b o c d/(Real.sqrt (D1 r a d)*Real.sqrt (D2 r b c)) := by
    simp only [cosine,hr1,hr2,div_div]
    rfl
  change -(G⁻¹ 2 3/(Real.sqrt (G⁻¹ 2 2)*Real.sqrt (G⁻¹ 3 3))) = _
  rw [hi22,hi33,hi23,Real.sqrt_div h2.le,Real.sqrt_div h1.le,hcos]
  have hs1 : Real.sqrt (D1 r a d) ≠ 0 := (Real.sqrt_pos.mpr h1).ne'
  have hs2 : Real.sqrt (D2 r b c) ≠ 0 := (Real.sqrt_pos.mpr h2).ne'
  have hsd : Real.sqrt delta ≠ 0 := (Real.sqrt_pos.mpr hd).ne'
  have hsq : (Real.sqrt delta)^2 = delta := Real.sq_sqrt hd.le
  field_simp [hd.ne',hs1,hs2,hsd]
  <;> linear_combination (N r a b o c d)*hsq

end CFMPOriginalUnitSideCosine435Transient
end

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix BigOperators Topology
open Set Filter
open D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface
open D5.S3.Geometry.Hyperideal.S4OppositePairAction (edgeIndex)
namespace CFMPOriginalAllSideCosines435Transient

def relabel (x : Fin 6 → ℝ) (σ : Equiv.Perm (Fin 4)) : Fin 6 → ℝ :=
  ![x (edgeIndex (σ 0) (σ 1)), x (edgeIndex (σ 0) (σ 2)),
    x (edgeIndex (σ 0) (σ 3)), x (edgeIndex (σ 2) (σ 3)),
    x (edgeIndex (σ 1) (σ 3)), x (edgeIndex (σ 1) (σ 2))]

theorem edgeIndex_symm (i j : Fin 4) : edgeIndex i j = edgeIndex j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem gram_relabel (x : Fin 6 → ℝ) (σ : Equiv.Perm (Fin 4)) :
    (gram (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)).submatrix σ σ =
      gram (relabel x σ 0) (relabel x σ 1) (relabel x σ 2)
        (relabel x σ 3) (relabel x σ 4) (relabel x σ 5) := by
  have entry (i j : Fin 4) : gram (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) i j =
      if i = j then 1 else -x (edgeIndex i j) := by
    fin_cases i <;> fin_cases j <;> norm_num [gram,edgeIndex]
  ext i j
  rw [Matrix.submatrix_apply,entry]
  simp only [σ.injective.eq_iff]
  fin_cases i <;> fin_cases j <;>
    simp [gram,relabel,edgeIndex_symm] <;>
      exact congrArg x (edgeIndex_symm _ _)

end CFMPOriginalAllSideCosines435Transient
end

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix BigOperators Topology
open Set Filter
open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes (cosine)
open D5.S3.Geometry.Hyperideal.TwoLengthAngleSum (rawCos)
open CFMPOriginalAllSideCosines435Transient
open CFMPGenuineLengthNeighborhood435Transient
namespace CFMPOriginalSixPairedAngles435Transient

def vertexPerm (k : Fin 6) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective
    (![![0,1,2,3],![0,2,3,1],![0,3,2,1],![2,3,0,1],![1,3,2,0],![1,2,3,0]] k)
    (by fin_cases k <;> decide)

theorem original_relabel_cosine (x : Fin 6 → ℝ) (k : Fin 6) :
    cosine (relabel x (vertexPerm k) 0) (relabel x (vertexPerm k) 1)
      (relabel x (vertexPerm k) 2) (relabel x (vertexPerm k) 3)
      (relabel x (vertexPerm k) 4) (relabel x (vertexPerm k) 5) = rawCos x k := by
  fin_cases k <;> rfl

def sourceAngle (l : Fin 6 → ℝ) (k : Fin 6) : ℝ := Real.arccos (sourceCosine l k)

end CFMPOriginalSixPairedAngles435Transient
end

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix BigOperators Topology
open Set Filter
open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
open D5.S3.Geometry.Hyperideal.FourCycleCurvature (frame)
open D5.S3.Geometry.Hyperideal.TwoLengthAngleSum (rawCos)
open D5.S3.Geometry.Hyperideal.LengthGramBody (lengthGram)
open CFMPGenuineLengthNeighborhood435Transient (genuine sourceCosine)
open CFMPOriginalSixPairedAngles435Transient (vertexPerm)
open CFMPOriginalAllSideCosines435Transient (relabel gram_relabel)
namespace CFMPGenuineDomain108Transient

abbrev Coordinates := Fin 6 → ℝ
/-- Every original angle frame is the edge action of its actual vertex permutation. -/
private theorem actual_frame_relabel (x : Coordinates) (q : Fin 6) :
    relabel x (vertexPerm q) = fun i => x (frame q i) := by
  fin_cases q <;> funext i <;> fin_cases i <;> rfl

/-- The corresponding Gram matrix is a simultaneous row and column permutation. -/
private theorem actual_frame_gram (x : Coordinates) (q : Fin 6) :
    (D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface.gram (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)).submatrix
        (vertexPerm q) (vertexPerm q) =
      D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface.gram (x (frame q 0)) (x (frame q 1)) (x (frame q 2))
        (x (frame q 3)) (x (frame q 4)) (x (frame q 5)) := by
  simpa only [actual_frame_relabel] using gram_relabel x (vertexPerm q)

private theorem cosine_bounds_iff_det_neg (r a b o c d : ℝ)
    (hr : 1 < r) (ha : 1 < a) (hb : 1 < b) (ho : 1 < o)
    (hc : 1 < c) (hd : 1 < d) :
    (-1 < cosine r a b o c d ∧ cosine r a b o c d < 1) ↔
      (D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface.gram r a b o c d).det < 0 := by
  have hi := D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface.original_cosine_interface r a b o c d hr ha hb ho hc hd
  have hrad1 : rad r a d = D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface.D1 r a d := by unfold rad D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface.D1; ring
  have hrad2 : rad r b c = D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface.D2 r b c := by unfold rad D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface.D2; ring
  let S := Real.sqrt (D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface.D1 r a d) * Real.sqrt (D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface.D2 r b c)
  let n := D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface.N r a b o c d
  have hS : 0 < S := mul_pos (Real.sqrt_pos.mpr hi.1.1) (Real.sqrt_pos.mpr hi.1.2)
  have hS2 : S^2 = D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface.D1 r a d * D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface.D2 r b c := by
    dsimp [S]
    rw [mul_pow, Real.sq_sqrt hi.1.1.le, Real.sq_sqrt hi.1.2.le]
  have hcos : cosine r a b o c d = n / S := by
    dsimp only [n, S]
    simp only [cosine, hrad1, hrad2, div_div, numerator,
      D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface.N]
  have hbounds : (-1 < cosine r a b o c d ∧ cosine r a b o c d < 1) ↔
      -S < n ∧ n < S := by
    simp only [hcos, lt_div_iff₀ hS, div_lt_iff₀ hS, neg_one_mul, one_mul]
  have hsquare : (-S < n ∧ n < S) ↔ n^2 < S^2 := by
    rw [← abs_lt]
    simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg n) hS.le).symm
  rw [hbounds, hsquare]
  constructor
  · intro h
    apply hi.2.2.mpr
    change 0 < D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface.D1 r a d * D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface.D2 r b c - n^2
    nlinarith only [h, hS2]
  · intro h
    have hg := hi.2.2.mp h
    change 0 < D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface.D1 r a d * D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface.D2 r b c - n^2 at hg
    nlinarith only [hg, hS2]

/-- This holds separately for each of the six literal source frames. -/
private theorem rawCos_bounds_iff_det_neg (x : Coordinates)
    (hx : ∀ i, 1 < x i) (q : Fin 6) :
    (-1 < rawCos x q ∧ rawCos x q < 1) ↔
      (D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface.gram (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)).det < 0 := by
  have h := cosine_bounds_iff_det_neg
    (x (frame q 0)) (x (frame q 1)) (x (frame q 2))
    (x (frame q 3)) (x (frame q 4)) (x (frame q 5))
    (hx _) (hx _) (hx _) (hx _) (hx _) (hx _)
  rw [← actual_frame_gram x q, Matrix.det_submatrix_equiv_self] at h
  exact h

/-- The quantifier ranges over all original six cosines, with no selected-edge restriction. -/
private theorem all_six_bounds_iff_det_neg (x : Coordinates)
    (hx : ∀ i, 1 < x i) :
    (∀ q, -1 < rawCos x q ∧ rawCos x q < 1) ↔
      (D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface.gram (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)).det < 0 := by
  constructor
  · intro h
    exact (rawCos_bounds_iff_det_neg x hx 0).mp (h 0)
  · intro h q
    exact (rawCos_bounds_iff_det_neg x hx q).mpr h

/-- The original genuine length domain has exactly the negative Gram determinant condition. -/
theorem genuine_iff_lengthGram_det_neg (l : Coordinates) :
    genuine l ↔ (∀ i, 0 < l i) ∧ (lengthGram l).det < 0 := by
  constructor
  · rintro ⟨hl,hc⟩
    refine ⟨hl,?_⟩
    have hx (i : Fin 6) : 1 < Real.cosh (l i) := Real.one_lt_cosh.mpr (hl i).ne'
    exact (all_six_bounds_iff_det_neg (fun i => Real.cosh (l i)) hx).mp hc
  · rintro ⟨hl,hd⟩
    refine ⟨hl,?_⟩
    have hx (i : Fin 6) : 1 < Real.cosh (l i) := Real.one_lt_cosh.mpr (hl i).ne'
    exact (all_six_bounds_iff_det_neg (fun i => Real.cosh (l i)) hx).mpr hd

end CFMPGenuineDomain108Transient
end

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Topology Matrix.Norms.Operator
open Filter
open D5.S3.Geometry.Hyperideal.LengthGramBody (lengthGram)
open D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface
open D5.S3.Geometry.Hyperideal.S4OppositePairAction (edgeIndex)
open CFMPGenuineLengthNeighborhood435Transient (genuine sourceCosine genuine_open)
open CFMPOriginalSixPairedAngles435Transient (sourceAngle vertexPerm original_relabel_cosine)
open CFMPOriginalAllSideCosines435Transient (relabel gram_relabel)
open CFMPOriginalUnitSideCosine435Transient (original_gram_cofactors inverse_gram_cosine)
open CFMPNormalizedInverseTangent107 (normalizedInverse normalScale)

namespace CFMPSourceAngleKernel111

abbrev Lengths := Fin 6 → ℝ
abbrev Mat := Matrix (Fin 4) (Fin 4) ℝ

def entryCLM (i j : Fin 4) : Mat →L[ℝ] ℝ :=
  (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap

private def coshCoordinates (l : Lengths) : Lengths := fun k => Real.cosh (l k)

def y (l : Lengths) (σ : Equiv.Perm (Fin 4)) : Lengths :=
  relabel (coshCoordinates l) σ

def Q (l : Lengths) (σ : Equiv.Perm (Fin 4)) : Mat :=
  gram (y l σ 0) (y l σ 1) (y l σ 2) (y l σ 3) (y l σ 4) (y l σ 5)

theorem relabeled_gram (l : Lengths) (σ : Equiv.Perm (Fin 4)) :
    (lengthGram l).submatrix σ σ = Q l σ := by
  exact gram_relabel (coshCoordinates l) σ

theorem relabeled_inverse (l : Lengths) (σ : Equiv.Perm (Fin 4)) :
    (Q l σ)⁻¹ = (lengthGram l)⁻¹.submatrix σ σ := by
  rw [← relabeled_gram, Matrix.inv_submatrix_equiv]

theorem relabeled_domain (l : Lengths) (hl : genuine l)
    (σ : Equiv.Perm (Fin 4)) :
    0 < D1 (y l σ 0) (y l σ 1) (y l σ 5) ∧
      0 < D2 (y l σ 0) (y l σ 2) (y l σ 4) ∧ (Q l σ).det < 0 := by
  have hy (k : Fin 6) : 1 < y l σ k := by
    fin_cases k <;> exact Real.one_lt_cosh.mpr (hl.1 _).ne'
  have hp := (original_cosine_interface
    (y l σ 0) (y l σ 1) (y l σ 2) (y l σ 3) (y l σ 4) (y l σ 5)
    (hy 0) (hy 1) (hy 2) (hy 3) (hy 4) (hy 5)).1
  refine ⟨hp.1, hp.2, ?_⟩
  rw [← relabeled_gram, Matrix.det_submatrix_equiv_self]
  exact ((CFMPGenuineDomain108Transient.genuine_iff_lengthGram_det_neg l).mp hl).2

private theorem permuted_inverse_diagonal_positive (l : Lengths) (hl : genuine l)
    (σ : Equiv.Perm (Fin 4)) :
    0 < (lengthGram l)⁻¹ (σ 2) (σ 2) ∧
      0 < (lengthGram l)⁻¹ (σ 3) (σ 3) := by
  obtain ⟨h1, h2, hd⟩ := relabeled_domain l hl σ
  have hc := original_gram_cofactors
    (y l σ 0) (y l σ 1) (y l σ 2) (y l σ 3) (y l σ 4) (y l σ 5)
  have h22 : 0 < (Q l σ)⁻¹ 2 2 := by
    change 0 < (gram (y l σ 0) (y l σ 1) (y l σ 2) (y l σ 3) (y l σ 4) (y l σ 5))⁻¹ 2 2
    rw [Matrix.inv_def]
    simp only [Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
    rw [hc.1]
    exact mul_pos_of_neg_of_neg (inv_neg''.mpr hd) (neg_neg_of_pos h2)
  have h33 : 0 < (Q l σ)⁻¹ 3 3 := by
    change 0 < (gram (y l σ 0) (y l σ 1) (y l σ 2) (y l σ 3) (y l σ 4) (y l σ 5))⁻¹ 3 3
    rw [Matrix.inv_def]
    simp only [Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
    rw [hc.2.1]
    exact mul_pos_of_neg_of_neg (inv_neg''.mpr hd) (neg_neg_of_pos h1)
  rw [relabeled_inverse] at h22 h33
  exact ⟨h22, h33⟩

theorem inverse_diagonal_positive (l : Lengths) (hl : genuine l)
    (i : Fin 4) : 0 < (lengthGram l)⁻¹ i i := by
  have h0 := permuted_inverse_diagonal_positive l hl (vertexPerm 0)
  have h3 := permuted_inverse_diagonal_positive l hl (vertexPerm 3)
  fin_cases i
  · exact h3.1
  · exact h3.2
  · exact h0.1
  · exact h0.2

theorem genuine_gram_isUnit (l : Lengths) (hl : genuine l) :
    IsUnit (lengthGram l) := by
  apply (Matrix.isUnit_iff_isUnit_det (lengthGram l)).mpr
  apply isUnit_iff_ne_zero.mpr
  exact ((CFMPGenuineDomain108Transient.genuine_iff_lengthGram_det_neg l).mp hl).2.ne

theorem normalized_entry (G : Mat) (i j : Fin 4) :
    normalizedInverse G i j = G⁻¹ i j /
      (Real.sqrt (G⁻¹ i i) * Real.sqrt (G⁻¹ j j)) := by
  simp [normalizedInverse, normalScale, Matrix.mul_diagonal, Matrix.diagonal_mul,
    div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

theorem normalized_source_cosine (l : Lengths) (hl : genuine l) (q : Fin 6) :
    normalizedInverse (lengthGram l) (vertexPerm q 2) (vertexPerm q 3) =
      -sourceCosine l q := by
  obtain ⟨h1, h2, hd⟩ := relabeled_domain l hl (vertexPerm q)
  have hc := inverse_gram_cosine
    (y l (vertexPerm q) 0) (y l (vertexPerm q) 1)
    (y l (vertexPerm q) 2) (y l (vertexPerm q) 3)
    (y l (vertexPerm q) 4) (y l (vertexPerm q) 5) h1 h2 hd
  change -((Q l (vertexPerm q))⁻¹ 2 3 /
    (Real.sqrt ((Q l (vertexPerm q))⁻¹ 2 2) *
      Real.sqrt ((Q l (vertexPerm q))⁻¹ 3 3))) = _ at hc
  rw [relabeled_inverse] at hc
  have hs : -((lengthGram l)⁻¹ (vertexPerm q 2) (vertexPerm q 3) /
      (Real.sqrt ((lengthGram l)⁻¹ (vertexPerm q 2) (vertexPerm q 2)) *
        Real.sqrt ((lengthGram l)⁻¹ (vertexPerm q 3) (vertexPerm q 3)))) =
      sourceCosine l q := by
    simp only [Matrix.submatrix_apply, y, original_relabel_cosine] at hc
    change -( (lengthGram l)⁻¹ (vertexPerm q 2) (vertexPerm q 3) /
      (Real.sqrt ((lengthGram l)⁻¹ (vertexPerm q 2) (vertexPerm q 2)) *
        Real.sqrt ((lengthGram l)⁻¹ (vertexPerm q 3) (vertexPerm q 3)))) = _ at hc
    convert! hc using 1 <;> rfl
  rw [normalized_entry]
  simpa only [neg_neg] using congrArg Neg.neg hs

end CFMPSourceAngleKernel111
end
