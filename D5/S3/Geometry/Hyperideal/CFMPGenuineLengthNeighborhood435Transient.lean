import D5.S3.Geometry.Hyperideal.CFMPActualNativeMass435Transient
import D5.S3.Geometry.Hyperideal.TwoLengthAngleSum

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
