import D5.S3.Geometry.Hyperideal.CFMPOriginalCellTransport435Transient
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Abs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Matrix BigOperators Topology ContDiff Matrix.Norms.Elementwise
open Filter Set
open CFMPFrameMotion435Transient CFMPFrameContinuity435Transient
open CFMPActualCellMotion435Transient CFMPOriginalCellsIndependent435Transient
open CFMPActualNativeCellMotion435Transient
open CFMPOriginalFrameDensity435Transient CFMPOriginalNativeCoordinates435Transient
open CFMPAnchoredSmoothFrame435Transient
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramPolytope
open D5.S3.Geometry.Hyperideal.LengthGramSideTrace
open D5.S3.Geometry.HyperbolicUpperHalfSpace

namespace CFMPOriginalCellKernel435Transient

theorem endpoint_smooth (i j : Fin 4) (hij : i ≠ j) :
    ContDiff ℝ ∞ (fun p : Fin 6 → ℝ => endpoint p i j) := by
  have hcoords (k : Fin 6) : ContDiff ℝ ∞ (fun p : Fin 6 → ℝ => p k) := by
    fun_prop
  have hG : ContDiff ℝ ∞ (fun p => lengthGram p i j) := by
    fin_cases i <;> fin_cases j
    all_goals first
      | exact contDiff_const
      | exact (Real.contDiff_cosh.comp (hcoords 0)).neg
      | exact (Real.contDiff_cosh.comp (hcoords 1)).neg
      | exact (Real.contDiff_cosh.comp (hcoords 2)).neg
      | exact (Real.contDiff_cosh.comp (hcoords 3)).neg
      | exact (Real.contDiff_cosh.comp (hcoords 4)).neg
      | exact (Real.contDiff_cosh.comp (hcoords 5)).neg
  have hz (p : Fin 6 → ℝ) : 1-lengthGram p i j ≠ 0 := by
    fin_cases i <;> fin_cases j <;>
      first | exact (hij rfl).elim | simp [lengthGram]; positivity
  have ha := hG.neg.div ((contDiff_const : ContDiff ℝ ∞ (fun _ : Fin 6 → ℝ => (1:ℝ))).sub hG) hz
  have hb := (contDiff_const : ContDiff ℝ ∞ (fun _ : Fin 6 → ℝ => (1:ℝ))).div
    (contDiff_const.sub hG) hz
  apply contDiff_pi.mpr
  intro k
  simp only [endpoint,Pi.add_apply,Pi.single_apply]
  split_ifs <;> fun_prop

theorem vertices_smooth (n : Fin 20) (j : Fin 4) :
    ContDiff ℝ ∞ (fun p : Fin 6 → ℝ => vertices p n j) := by
  fin_cases n <;> fin_cases j <;> simp only [vertices] <;>
    first | exact contDiff_const | exact endpoint_smooth _ _ (by decide)

theorem edgeMatrix_smooth (n : Fin 20) :
    ContDiff ℝ ∞ (fun p : Fin 6 → ℝ => edgeMatrix p n) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact (contDiff_pi.mp (vertices_smooth n j.succ) i.castSucc).sub
    (contDiff_pi.mp (vertices_smooth n 0) i.castSucc)

theorem cellPoint_joint_c1 (l : ℝ → Fin 6 → ℝ) (t : ℝ)
    (hl : ContDiffAt ℝ 1 l t) (n : Fin 20) (u : Fin 3 → ℝ) :
    ContDiffAt ℝ 1 (fun z : ℝ × (Fin 3 → ℝ) => cellPoint (l z.1) n z.2) (t,u) := by
  have hl' : ContDiffAt ℝ 1 (fun z : ℝ × (Fin 3 → ℝ) => l z.1) (t,u) :=
    hl.comp (t,u) contDiffAt_fst
  have hv (j : Fin 4) (i : Fin 3) :
      ContDiffAt ℝ 1 (fun z : ℝ × (Fin 3 → ℝ) => vertices (l z.1) n j i.castSucc) (t,u) :=
    ((contDiff_pi.mp (vertices_smooth n j) i.castSucc).contDiffAt.of_le (by simp)).comp (t,u) hl'
  have hu (i : Fin 3) : ContDiffAt ℝ 1 (fun z : ℝ × (Fin 3 → ℝ) => z.2 i) (t,u) := by
    fun_prop
  apply contDiffAt_pi.mpr
  intro i
  change ContDiffAt ℝ 1 (fun z : ℝ × (Fin 3 → ℝ) => vertices (l z.1) n 0 i.castSucc +
    ∑ j : Fin 3, (vertices (l z.1) n j.succ i.castSucc - vertices (l z.1) n 0 i.castSucc)*z.2 j) (t,u)
  apply (hv 0 i).add
  exact ContDiffAt.sum (fun j _ => ((hv j.succ i).sub (hv 0 i)).mul (hu j))

theorem determinant_c1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : Type*} [Fintype k] [DecidableEq k]
    (P : E → Matrix k k ℝ) (z : E) (hP : ContDiffAt ℝ 1 P z) :
    ContDiffAt ℝ 1 (fun y => (P y).det) z := by
  simp only [Matrix.det_apply']
  apply ContDiffAt.sum
  intro σ _
  apply contDiffAt_const.mul
  apply contDiffAt_prod
  intro i _
  exact contDiffAt_pi.mp (contDiffAt_pi.mp hP (σ i)) i

theorem density_c1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : E → M4) (x : E → (Fin 3 → ℝ)) (z : E)
    (hP : ContDiffAt ℝ 1 P z) (hx : ContDiffAt ℝ 1 x z)
    (hd : (P z).det ≠ 0) (hq : q (P z) (x z) ≠ 0) :
    ContDiffAt ℝ 1 (fun y => density (P y) (x y)) z := by
  have ha := (determinant_c1 P z hP).abs hd
  have hp (i j : Fin 4) := contDiffAt_pi.mp (contDiffAt_pi.mp hP i) j
  have hl (i : Fin 4) : ContDiffAt ℝ 1 (fun y => lift (x y) i) z := by
    have hc (j : Fin 3) := contDiffAt_pi.mp hx j
    fin_cases i <;> simp [lift] <;> fun_prop
  have hu (j : Fin 4) : ContDiffAt ℝ 1 (fun y => ambient (P y) (x y) j) z := by
    simpa -implicitDefEqProofs only [ambient,Matrix.vecMul,dotProduct,
      Fin.sum_univ_four,Pi.mul_def,Pi.add_def] using
      ContDiffAt.sum (s := (Finset.univ : Finset (Fin 4))) (fun i _ => (hl i).mul (hp i j))
  have hq' : ContDiffAt ℝ 1 (fun y => q (P y) (x y)) z := by
    simp only [q,lorentz,Fin.sum_univ_four]
    fun_prop
  unfold density
  exact ha.div (hq'.pow 2) (pow_ne_zero 2 hq)

def kernel (l : ℝ → Fin 6 → ℝ) (n : Fin 20) (z : ℝ × (Fin 3 → ℝ)) : ℝ :=
  |(edgeMatrix (l z.1) n).det| * originalDensity (l z.1) (cellPoint (l z.1) n z.2)

theorem original_kernel_c1
    (l0 : Fin 6 → ℝ) (hl0 : ∀ i, 0 < l0 i)
    (M0 : M4) (hm0 : M0.det ≠ 0)
    (hg0 : M0 * J * M0.transpose = lengthGram l0)
    (f : cutBody l0 → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : Fin 4 → ℝ, y = (radial l0 w.val) ᵥ* M0 ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)), 1/(y 3-y 2)))
    (l : ℝ → (Fin 6 → ℝ)) (t : ℝ)
    (hl : ContDiffAt ℝ 1 l t) (hbase : l t = l0)
    (n : Fin 20) (u : Fin 3 → ℝ) (hu : referenceSimplex u) :
    ContDiffAt ℝ 1 (kernel l n) (t,u) := by
  let P : ℝ × (Fin 3 → ℝ) → M4 := fun z => frame M0 (l z.1)
  have hgood : good (H M0 l0) := by
    rw [normalized_base M0 hm0 l0 hg0]
    exact base.2
  have hl' : ContDiffAt ℝ 1 (fun z : ℝ × (Fin 3 → ℝ) => l z.1) (t,u) :=
    hl.comp (t,u) contDiffAt_fst
  have hp0 : ContDiffAt ℝ 1 (frame M0) (l t) := by
    simpa only [hbase] using (smooth_frame M0 l0 hgood).of_le (show 1 ≤ ∞ by simp)
  have hP : ContDiffAt ℝ 1 P (t,u) := by
    exact ContDiffAt.comp (f := fun z : ℝ × (Fin 3 → ℝ) => l z.1)
      (g := frame M0) (t,u) hp0 hl'
  have hPt : P (t,u) = M0 := by simp only [P,hbase,anchored M0 hm0 l0 hg0]
  have hdetP : (P (t,u)).det ≠ 0 := by simpa only [hPt] using hm0
  have hdetB : (edgeMatrix (l t) n).det ≠ 0 := by
    simpa only [hbase] using edgeMatrix_det_ne_zero l0 hl0 n
  have hx := lift_cellPoint_mem_body l0 hl0 n u hu
  have hq : q (P (t,u)) (cellPoint (l t) n u) ≠ 0 := by
    rw [hPt,hbase]
    exact (original_native_coordinates l0 hl0 M0 f hf ⟨lift (cellPoint l0 n u),hx⟩).1.ne'
  have hB : ContDiffAt ℝ 1 (fun p : Fin 6 → ℝ => edgeMatrix p n) (l t) :=
    (edgeMatrix_smooth n).contDiffAt.of_le (show 1 ≤ ∞ by simp)
  have hBc : ContDiffAt ℝ 1
      (fun z : ℝ × (Fin 3 → ℝ) => edgeMatrix (l z.1) n) (t,u) := by
    exact ContDiffAt.comp (f := fun z : ℝ × (Fin 3 → ℝ) => l z.1)
      (g := fun p : Fin 6 → ℝ => edgeMatrix p n) (t,u) hB hl'
  have hJ := (determinant_c1 (fun z : ℝ × (Fin 3 → ℝ) => edgeMatrix (l z.1) n)
    (t,u) hBc).abs hdetB
  have hρ := density_c1 P (fun z => cellPoint (l z.1) n z.2) (t,u)
    hP (cellPoint_joint_c1 l t hl n u) hdetP hq
  have hcont : ContinuousAt (fun z : ℝ × (Fin 3 → ℝ) => H M0 (l z.1)) (t,u) :=
    (smooth_H M0).continuous.continuousAt.comp hl'.continuousAt
  have hgoodt : good (H M0 (l t)) := by simpa only [hbase] using hgood
  have heq : kernel l n =ᶠ[𝓝 (t,u)]
      (fun z => |(edgeMatrix (l z.1) n).det| * density (P z) (cellPoint (l z.1) n z.2)) := by
    filter_upwards [hcont.eventually (good_open.mem_nhds hgoodt)] with z hz
    have hg := CFMPAnchoredFrameContinuity435Transient.matrix_gram_rows
      (P z) (l z.1) (frame_gram M0 hm0 (l z.1) hz)
    rw [density_eq_original (P z) (l z.1) hg]
    rfl
  exact (hJ.mul hρ).congr_of_eventuallyEq heq

end CFMPOriginalCellKernel435Transient
