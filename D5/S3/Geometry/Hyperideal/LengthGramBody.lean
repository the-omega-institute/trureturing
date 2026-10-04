/- GID: D5/S3/Geometry/Hyperideal/LengthGramBody
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/LengthGramBody
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.StdSimplex]
   utility: none
   digest: The common six-length cut simplex avoids the null cone and
   admits a compact injective radial normalization. -/

import D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
import D5.S3.Geometry.HyperbolicTopology
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

noncomputable section
open scoped BigOperators Matrix
open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
open D5.S3.Geometry.HyperbolicUpperHalfSpace D5.S3.Geometry.HyperbolicTopology
open Set
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace D5.S3.Geometry.Hyperideal.LengthGramBody

/-- Length order: 01, 02, 03, 23, 13, 12. -/
def lengthGram (l : Fin 6 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, -Real.cosh (l 0), -Real.cosh (l 1), -Real.cosh (l 2);
    -Real.cosh (l 0), 1, -Real.cosh (l 5), -Real.cosh (l 4);
    -Real.cosh (l 1), -Real.cosh (l 5), 1, -Real.cosh (l 3);
    -Real.cosh (l 2), -Real.cosh (l 4), -Real.cosh (l 3), 1]

def cutBody (l : Fin 6 → ℝ) : Set (Fin 4 → ℝ) :=
  stdSimplex ℝ (Fin 4) ∩ {v | ∀ i, ∑ j, lengthGram l i j * v j ≤ 0}

def gramQuadratic (l : Fin 6 → ℝ) (v : Fin 4 → ℝ) : ℝ :=
  ∑ i, v i * ∑ j, lengthGram l i j * v j

def radial (l : Fin 6 → ℝ) (v : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun i => v i / Real.sqrt (-gramQuadratic l v)

/-- The standard space-positive, time-negative Lorentz form. -/
def lorentz (y z : Fin 4 → ℝ) : ℝ :=
  ∑ k, (![(1 : ℝ),1,1,-1] k) * y k * z k

/-- All points of the common cut body admit the same continuous, injective
radial normalization. Its image is compact, nonempty, and on the unit
negative quadric of the actual length Gram matrix. -/
theorem shared_radial_body (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k) :
    IsCompact (cutBody l) ∧
    (fun _ : Fin 4 => (1 : ℝ) / 4) ∈ cutBody l ∧
    (∀ i, ∑ j, lengthGram l i j * (1 / 4 : ℝ) < 0) ∧
    (∀ v ∈ cutBody l, gramQuadratic l v < 0) ∧
    ContinuousOn (radial l) (cutBody l) ∧
    InjOn (radial l) (cutBody l) ∧
    IsCompact (radial l '' cutBody l) ∧
    (radial l '' cutBody l).Nonempty ∧
    (∀ v ∈ cutBody l, gramQuadratic l (radial l v) = -1) ∧
    ((-1 < cosine (Real.cosh (l 0)) (Real.cosh (l 1)) (Real.cosh (l 2))
        (Real.cosh (l 3)) (Real.cosh (l 4)) (Real.cosh (l 5)) ∧ cosine (Real.cosh (l 0)) (Real.cosh (l 1)) (Real.cosh (l 2))
        (Real.cosh (l 3)) (Real.cosh (l 4)) (Real.cosh (l 5)) < 1) →
      ∃ m : Matrix (Fin 4) (Fin 4) ℝ,
        (∀ i j, lorentz (m i) (m j) = lengthGram l i j) ∧
        0 < m.det ∧ (lengthGram l).det < 0 ∧
        ∃ f : cutBody l → HyperbolicThreeSpace,
          Continuous f ∧ Function.Injective f ∧ IsCompact (range f) ∧
          (range f).Nonempty ∧
          (∀ v, ∃ y : Fin 4 → ℝ, y = (radial l v.val) ᵥ* m ∧
            lorentz y y = -1 ∧ 0 < y 3 ∧
            (f v).coordinates.val = WithLp.toLp 2
              (Complex.mk (y 0 / (y 3 - y 2)) (y 1 / (y 3 - y 2)),
               1 / (y 3 - y 2)))) := by
  classical
  have hcosh (k : Fin 6) : 1 < Real.cosh (l k) :=
    Real.one_lt_cosh.mpr (ne_of_gt (hl k))
  have hdiag (i : Fin 4) : lengthGram l i i = 1 := by
    fin_cases i <;> simp [lengthGram]
  have hoff (i j : Fin 4) (hij : i ≠ j) : lengthGram l i j < -1 := by
    fin_cases i <;> fin_cases j <;> first
      | exact (hij rfl).elim
      | exact neg_lt_neg (hcosh 0)
      | exact neg_lt_neg (hcosh 1)
      | exact neg_lt_neg (hcosh 2)
      | exact neg_lt_neg (hcosh 3)
      | exact neg_lt_neg (hcosh 4)
      | exact neg_lt_neg (hcosh 5)
  have hclosed : IsClosed {v : Fin 4 → ℝ | ∀ i, ∑ j, lengthGram l i j * v j ≤ 0} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro i
    apply isClosed_le _ continuous_const
    fun_prop
  have hcompact : IsCompact (cutBody l) :=
    (isCompact_stdSimplex ℝ (Fin 4)).inter_right hclosed
  have hbcut (i : Fin 4) : ∑ j, lengthGram l i j * (1 / 4 : ℝ) < 0 := by
    fin_cases i <;> simp [lengthGram, Fin.sum_univ_succ] <;>
      linarith [hcosh 0, hcosh 1, hcosh 2, hcosh 3, hcosh 4, hcosh 5]
  have hb : (fun _ : Fin 4 => (1 : ℝ) / 4) ∈ cutBody l := by
    refine ⟨⟨fun _ => by norm_num, ?_⟩, fun i => (hbcut i).le⟩
    norm_num [Fin.sum_univ_succ]
  have hnegative : ∀ v ∈ cutBody l, gramQuadratic l v < 0 := by
    intro v hv
    obtain ⟨⟨hnonneg, hsum⟩, hcut⟩ := hv
    let row : Fin 4 → ℝ := fun i => ∑ j, lengthGram l i j * v j
    have hsplit (i : Fin 4) : row i = v i +
        ∑ j ∈ Finset.univ.erase i, lengthGram l i j * v j := by
      dsimp [row]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      rw [hdiag, one_mul, add_comm]
    have hsplitSum (i : Fin 4) : (∑ j ∈ Finset.univ.erase i, v j) + v i = 1 := by
      rw [Finset.sum_erase_add _ _ (Finset.mem_univ i), hsum]
    have hhalf (i : Fin 4) (hi : 0 < v i) (hri : row i = 0) : 1 / 2 < v i := by
      have hex : ∃ j ∈ Finset.univ.erase i, 0 < v j := by
        by_contra h
        push Not at h
        have hz : ∑ j ∈ Finset.univ.erase i, lengthGram l i j * v j = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          have hvj : v j = 0 := le_antisymm (h j hj) (hnonneg j)
          simp [hvj]
        have := hsplit i
        rw [hz, hri] at this
        linarith
      have hstrict : (∑ j ∈ Finset.univ.erase i, lengthGram l i j * v j) <
          ∑ j ∈ Finset.univ.erase i, -(v j) := by
        apply Finset.sum_lt_sum
        · intro j hj
          have hji : i ≠ j := (Finset.ne_of_mem_erase hj).symm
          have := mul_le_mul_of_nonneg_right (hoff i j hji).le (hnonneg j)
          simpa using this
        · obtain ⟨j, hj, hvj⟩ := hex
          refine ⟨j, hj, ?_⟩
          have := mul_lt_mul_of_pos_right (hoff i j (Finset.ne_of_mem_erase hj).symm) hvj
          simpa using this
      rw [Finset.sum_neg_distrib] at hstrict
      have := hsplit i
      have := hsplitSum i
      linarith
    have hterms (i : Fin 4) : v i * row i ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (hnonneg i) (hcut i)
    have hqle : gramQuadratic l v ≤ 0 := Finset.sum_nonpos fun i _ => hterms i
    apply lt_of_le_of_ne hqle
    intro hqzero
    have hz : ∀ i, v i * row i = 0 := by
      have h := (Finset.sum_eq_zero_iff_of_nonpos (fun i _ => hterms i)).mp hqzero
      exact fun i => h i (Finset.mem_univ i)
    obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => hnonneg i)).mp
      (show 0 < ∑ i, v i by rw [hsum]; norm_num)
    have hri : row i = 0 := (mul_eq_zero.mp (hz i)).resolve_left (ne_of_gt hi)
    have hihalf := hhalf i hi hri
    have hotherzero : ∀ j ∈ Finset.univ.erase i, v j = 0 := by
      intro j hj
      by_contra hjzero
      have hjpos := lt_of_le_of_ne (hnonneg j) (Ne.symm hjzero)
      have hrj : row j = 0 := (mul_eq_zero.mp (hz j)).resolve_left hjzero
      have hjhalf := hhalf j hjpos hrj
      have hle : v j ≤ ∑ k ∈ Finset.univ.erase i, v k :=
        Finset.single_le_sum (fun k _ => hnonneg k) hj
      have := hsplitSum i
      linarith
    have hothersum : ∑ j ∈ Finset.univ.erase i, lengthGram l i j * v j = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp [hotherzero j hj]
    have := hsplit i
    rw [hothersum, hri] at this
    linarith
  have hqcontinuous : Continuous (gramQuadratic l) := by
    unfold gramQuadratic
    fun_prop
  have hcontinuous : ContinuousOn (radial l) (cutBody l) := by
    apply continuousOn_pi.mpr
    intro i
    exact (continuous_apply i).continuousOn.div
      hqcontinuous.neg.sqrt.continuousOn
      (fun v hv => ne_of_gt (Real.sqrt_pos.mpr (neg_pos.mpr (hnegative v hv))))
  have hsumradial (v : Fin 4 → ℝ) (hv : v ∈ cutBody l) :
      ∑ i, radial l v i = 1 / Real.sqrt (-gramQuadratic l v) := by
    simp only [radial, ← Finset.sum_div, hv.1.2]
  have hinjective : InjOn (radial l) (cutBody l) := by
    intro v hv w hw heq
    have hrootv := ne_of_gt (Real.sqrt_pos.mpr (neg_pos.mpr (hnegative v hv)))
    have hrootw := ne_of_gt (Real.sqrt_pos.mpr (neg_pos.mpr (hnegative w hw)))
    have hinv : 1 / Real.sqrt (-gramQuadratic l v) =
        1 / Real.sqrt (-gramQuadratic l w) := by
      rw [← hsumradial v hv, ← hsumradial w hw, heq]
    have hroot : Real.sqrt (-gramQuadratic l v) = Real.sqrt (-gramQuadratic l w) := by
      exact inv_injective (by simpa only [one_div] using hinv)
    funext i
    have := congrFun heq i
    simpa only [radial, hroot, div_left_inj' hrootw] using this
  have hnormalized (v : Fin 4 → ℝ) (hv : v ∈ cutBody l) :
      gramQuadratic l (radial l v) = -1 := by
    have hq := hnegative v hv
    have hs := Real.sq_sqrt (le_of_lt (neg_pos.mpr hq))
    have hn := ne_of_gt (Real.sqrt_pos.mpr (neg_pos.mpr hq))
    have hscale : gramQuadratic l (radial l v) =
        gramQuadratic l v / Real.sqrt (-gramQuadratic l v) ^ 2 := by
      let s := Real.sqrt (-gramQuadratic l v)
      have hrows (i : Fin 4) : (∑ j, lengthGram l i j * (v j / s)) =
          (∑ j, lengthGram l i j * v j) / s := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j _
        ring
      change (∑ i, (v i / s) * ∑ j, lengthGram l i j * (v j / s)) =
        (∑ i, v i * ∑ j, lengthGram l i j * v j) / s ^ 2
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      rw [hrows i]
      ring
    rw [hscale, hs]
    field_simp [ne_of_lt hq]
  refine ⟨hcompact, hb, hbcut, hnegative, hcontinuous, hinjective,
    hcompact.image_of_continuousOn hcontinuous,
    ⟨radial l (fun _ => 1 / 4), ⟨_, hb, rfl⟩⟩, hnormalized, ?_⟩
  intro hp
  let a := Real.cosh (l 0)
  let b := Real.cosh (l 1)
  let c := Real.cosh (l 2)
  let d := Real.cosh (l 3)
  let e := Real.cosh (l 4)
  let f := Real.cosh (l 5)
  have ha : 1 < a := hcosh 0
  have hb' : 1 < b := hcosh 1
  have hc : 1 < c := hcosh 2
  have hd' : 1 < d := hcosh 3
  have he : 1 < e := hcosh 4
  have hf' : 1 < f := hcosh 5
  have hframe : ∃ m : Matrix (Fin 4) (Fin 4) ℝ,
      (∀ i j, m i 0 * m j 0 + m i 1 * m j 1 + m i 2 * m j 2 - m i 3 * m j 3 =
        lengthGram l i j) ∧ 0 < m.det ∧ (∀ i, 0 ≤ m i 3) := by
    let A := rad a b f
    let B := rad a c e
    let P := numerator a b c d e f
    have hA : 0 < A := by
      have hh : 0 < 2*a*b*f := by positivity
      dsimp [A, rad]
      nlinarith [sq_nonneg (a-1),sq_nonneg (b-1),sq_nonneg (f-1)]
    have hB : 0 < B := by
      have hh : 0 < 2*a*c*e := by positivity
      dsimp [B, rad]
      nlinarith [sq_nonneg (a-1),sq_nonneg (c-1),sq_nonneg (e-1)]
    have hS : 0 < a^2-1 := by nlinarith
    let s := Real.sqrt (a^2-1)
    let u := Real.sqrt A
    let v := Real.sqrt B
    have hs : 0 < s := Real.sqrt_pos.mpr hS
    have hu : 0 < u := Real.sqrt_pos.mpr hA
    have hv : 0 < v := Real.sqrt_pos.mpr hB
    have hs2 : s^2=a^2-1 := Real.sq_sqrt hS.le
    have hu2 : u^2=A := Real.sq_sqrt hA.le
    have hv2 : v^2=B := Real.sq_sqrt hB.le
    have hratio : -1 < P/(u*v) ∧ P/(u*v) < 1 := by
      simpa only [cosine, div_div] using hp
    have hlo : -(u*v) < P := by
      have := (lt_div_iff₀ (mul_pos hu hv)).mp hratio.1
      linarith
    have hhi : P < u*v := by
      simpa using (div_lt_iff₀ (mul_pos hu hv)).mp hratio.2
    have huv2 : (u*v)^2 = A*B := by rw [mul_pow,hu2,hv2]
    have hDelta : 0 < A*B-P^2 := by
      have hprod := mul_pos (sub_pos.mpr hhi) (show 0 < P+u*v by linarith)
      nlinarith
    let w := Real.sqrt ((A*B-P^2)/((a^2-1)*A))
    have hw : 0 < w := Real.sqrt_pos.mpr (div_pos hDelta (mul_pos hS hA))
    have hw2 : w^2=(A*B-P^2)/((a^2-1)*A) :=
      Real.sq_sqrt (div_pos hDelta (mul_pos hS hA)).le
    let m : Matrix (Fin 4) (Fin 4) ℝ :=
      !![1,0,0,0; -a,0,0,s; -b,u/s,0,(a*b+f)/s;
        -c,P/(s*u),w,(a*c+e)/s]
    refine ⟨m, ?_, ?_, ?_⟩
    · change ∀ i j, m i 0 * m j 0 + m i 1 * m j 1 + m i 2 * m j 2 - m i 3 * m j 3 =
          (!![1,-a,-b,-c; -a,1,-f,-e; -b,-f,1,-d; -c,-e,-d,1] : Matrix (Fin 4) (Fin 4) ℝ) i j
      intro i j
      fin_cases i <;> fin_cases j <;> simp only [m, Matrix.of_apply,
        Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.head_cons, Matrix.tail_cons]
      all_goals try ring
      all_goals try (nlinarith only [hs2])
      all_goals try (field_simp [hs.ne',hu.ne'] <;> ring)
      all_goals
        try ring_nf
        simp only [← inv_pow,hs2,hu2,hw2]
        field_simp [hS.ne',hA.ne']
        dsimp [A,B,P,rad,numerator]
        <;> ring
    · have hdet : m.det = u*w := by
        simp [m, Matrix.of_apply, Matrix.det_succ_row_zero, Matrix.det_fin_three,
          Matrix.det_fin_two, Matrix.det_fin_one, Matrix.det_fin_zero,
          Matrix.submatrix_apply, Fin.sum_univ_succ, hs.ne']
        <;> field_simp [hs.ne']
        <;> ring
      rw [hdet]
      exact mul_pos hu hw
    · intro i
      fin_cases i <;> simp [m] <;> positivity
  obtain ⟨m,hg0,hdet,ht⟩ := hframe
  have hg (i j : Fin 4) : lorentz (m i) (m j) = lengthGram l i j := by
    simpa [lorentz, Fin.sum_univ_succ, sub_eq_add_neg, add_assoc] using hg0 i j
  let J : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![(1 : ℝ),1,1,-1]
  have hJ : J.det = -1 := by
    simp [J, Matrix.det_diagonal, Fin.prod_univ_succ]
  have hcong : m * J * m.transpose = lengthGram l := by
    ext i j
    simpa [J, Matrix.mul_apply, Fin.sum_univ_succ, sub_eq_add_neg, add_assoc] using hg0 i j
  have hgdet : (lengthGram l).det < 0 := by
    rw [← hcong, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hJ]
    nlinarith [sq_pos_of_pos hdet]
  refine ⟨m,hg,hdet,hgdet,?_⟩
  have hpull (v : Fin 4 → ℝ) : lorentz (v ᵥ* m) (v ᵥ* m) = gramQuadratic l v := by
    calc
      _ = ∑ k, ∑ i, ∑ j, v i * v j *
          ((![(1 : ℝ),1,1,-1] k) * m i k * m j k) := by
        simp only [lorentz, Matrix.vecMul, dotProduct, Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ∑ i, ∑ j, ∑ k, v i * v j *
          ((![(1 : ℝ),1,1,-1] k) * m i k * m j k) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = ∑ i, ∑ j, v i * v j * lengthGram l i j := by
        simp_rw [← Finset.mul_sum]
        change (∑ i, ∑ j, v i * v j * lorentz (m i) (m j)) = _
        simp only [hg]
      _ = _ := by
        unfold gramQuadratic
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  let y : cutBody l → Fin 4 → ℝ := fun v => (radial l v.val) ᵥ* m
  have hyunit (v : cutBody l) : lorentz (y v) (y v) = -1 := by
    exact (hpull _).trans (hnormalized v.val v.property)
  have hyrad (v : cutBody l) (i : Fin 4) : 0 ≤ radial l v.val i :=
    div_nonneg (v.property.1.1 i) (Real.sqrt_nonneg _)
  have hyt (v : cutBody l) : 0 < y v 3 := by
    have hn : 0 ≤ y v 3 := by
      change 0 ≤ ∑ i, radial l v.val i * m i 3
      exact Finset.sum_nonneg fun i _ => mul_nonneg (hyrad v i) (ht i)
    have hq := hyunit v
    simp [lorentz, Fin.sum_univ_succ] at hq
    nlinarith [sq_nonneg (y v 0),sq_nonneg (y v 1),sq_nonneg (y v 2)]
  have hd (v : cutBody l) : 0 < y v 3 - y v 2 := by
    have hq := hyunit v
    simp [lorentz, Fin.sum_univ_succ] at hq
    have ht' := hyt v
    by_contra h
    have hh : y v 3 ≤ y v 2 := by linarith
    have hh' := mul_self_le_mul_self (ht'.le) hh
    nlinarith [sq_nonneg (y v 0),sq_nonneg (y v 1)]
  let coords : cutBody l → UpperHalfSpace ℂ := fun v =>
    ⟨WithLp.toLp 2
      (Complex.mk (y v 0 / (y v 3 - y v 2)) (y v 1 / (y v 3 - y v 2)),
       1 / (y v 3 - y v 2)), one_div_pos.mpr (hd v)⟩
  let f : cutBody l → HyperbolicThreeSpace := fun v => ⟨coords v⟩
  have hycont : Continuous y := by
    have hr : Continuous (fun v : cutBody l => radial l v.val) :=
      hcontinuous.domRestrict
    apply continuous_pi
    intro k
    change Continuous (fun v : cutBody l => ∑ i, radial l v.val i * m i k)
    exact continuous_finsetSum _ fun i _ => (continuous_apply i |>.comp hr).mul continuous_const
  have hyk (k : Fin 4) : Continuous (fun v => y v k) := (continuous_apply k).comp hycont
  have hden : Continuous (fun v => y v 3 - y v 2) := (hyk 3).sub (hyk 2)
  have hcoords : Continuous coords := by
    apply Continuous.subtype_mk
    apply (WithLp.prod_continuous_toLp 2 ℂ ℝ).comp
    apply Continuous.prodMk
    · have ha := Complex.continuous_ofReal.comp ((hyk 0).div hden (fun v => (hd v).ne'))
      have hb := Complex.continuous_ofReal.comp ((hyk 1).div hden (fun v => (hd v).ne'))
      convert ha.add (hb.mul (continuous_const (y := Complex.I))) using 1
      funext v
      change Complex.mk (y v 0 / (y v 3 - y v 2)) (y v 1 / (y v 3 - y v 2)) =
        Complex.ofReal (y v 0 / (y v 3 - y v 2)) +
        Complex.ofReal (y v 1 / (y v 3 - y v 2)) * Complex.I
      apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im] <;> ring
    · exact continuous_const.div hden (fun v => (hd v).ne')
  have hf : Continuous f := coordinatesHomeomorph.symm.continuous.comp hcoords
  have hfinj : Function.Injective f := by
    intro v w heq
    have hc : coords v = coords w := congrArg HyperbolicSpace.coordinates heq
    have hp := congrArg (fun z : UpperHalfSpace ℂ => WithLp.ofLp z.val) hc
    have hdEq : y v 3 - y v 2 = y w 3 - y w 2 := by
      apply inv_injective
      have hh := congrArg Prod.snd hp
      simpa only [coords, WithLp.ofLp_toLp, one_div] using hh
    have hx : y v 0 = y w 0 := by
      have hh := congrArg (fun z : ℂ × ℝ => z.1.re) hp
      simpa only [coords, WithLp.ofLp_toLp, hdEq,
        div_left_inj' (hd w).ne'] using hh
    have hz : y v 1 = y w 1 := by
      have hh := congrArg (fun z : ℂ × ℝ => z.1.im) hp
      simpa only [coords, WithLp.ofLp_toLp, hdEq,
        div_left_inj' (hd w).ne'] using hh
    have hvq := hyunit v
    have hwq := hyunit w
    simp [lorentz, Fin.sum_univ_succ] at hvq hwq
    have hpEq : (y v 3 + y v 2) * (y v 3 - y v 2) =
        (y w 3 + y w 2) * (y v 3 - y v 2) := by
      calc
        _ = 1 + (y v 0)^2 + (y v 1)^2 := by nlinarith [hvq]
        _ = 1 + (y w 0)^2 + (y w 1)^2 := by rw [hx,hz]
        _ = (y w 3 + y w 2) * (y w 3 - y w 2) := by nlinarith [hwq]
        _ = _ := by rw [hdEq]
    have hsEq := mul_right_cancel₀ (hd v).ne' hpEq
    have htEq : y v 3 = y w 3 := by linarith
    have hyEq : y v 2 = y w 2 := by linarith
    have hY : y v = y w := by
      funext k
      fin_cases k
      · exact hx
      · exact hz
      · exact hyEq
      · exact htEq
    have hm : IsUnit m := m.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hdet.ne')
    have hr := Matrix.vecMul_injective_of_isUnit hm hY
    apply Subtype.ext
    exact hinjective v.property w.property hr
  letI : CompactSpace (cutBody l) := isCompact_iff_compactSpace.mp hcompact
  refine ⟨f,hf,hfinj,?_,?_,?_⟩
  · exact isCompact_range hf
  · exact ⟨f ⟨_,hb⟩, mem_range_self _⟩
  · intro v
    exact ⟨y v,rfl,hyunit v,hyt v,rfl⟩


#print axioms shared_radial_body

end D5.S3.Geometry.Hyperideal.LengthGramBody
