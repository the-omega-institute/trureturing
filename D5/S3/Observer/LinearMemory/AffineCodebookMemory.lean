/- GID: D5/S3/Observer/LinearMemory/AffineCodebookMemory
   generality: G
   mirror-B: D5/B/S3/Observer/LinearMemory/AffineCodebookMemory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Driven linear memory has an exact finite solution; a contractive hidden block gives bounded hidden errors, a visible drift, and the unique sharp Euclidean autonomous readout. -/

import D5.S3.Observer.BlockStructure.FourBlockDecomposition
import D5.S3.Observer.HiddenFlow.VisibleHiddenProjectionCriteria
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Monotone
import Mathlib.Tactic

/-! Actual affine codebook memory, uniform contractive drift, and its sharp Euclidean readout. -/

noncomputable section
open scoped BigOperators
open Filter Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 2048
-- Preserve the resource profile of the successful whole v4 check.
set_option maxHeartbeats 800000

namespace D5.S3.Observer.LinearMemory.AffineCodebookMemory
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)
def mean {I : Type} [Fintype I] {d : ℕ} (c : I → E d) : E d :=
  (Fintype.card I : ℝ)⁻¹ • ∑ i, c i
def U {I : Type} [Fintype I] {d : ℕ} (c : I → E d) : Submodule ℝ (E d) :=
  Submodule.span ℝ (Set.range (fun i => c i - mean c))
abbrev W {I : Type} [Fintype I] {d : ℕ} (c : I → E d) := (U c)ᗮ
def P {I : Type} [Fintype I] {d : ℕ} (c : I → E d) : E d →L[ℝ] E d :=
  (U c).starProjection
def Q {I : Type} [Fintype I] {d : ℕ} (c : I → E d) : E d →L[ℝ] E d := 1 - P c
def B {I : Type} [Fintype I] {d : ℕ} (c : I → E d) (A : E d →L[ℝ] E d) :
    W c →L[ℝ] U c := ((U c).orthogonalProjectionOnto.comp A).comp (W c).subtypeL
def D {I : Type} [Fintype I] {d : ℕ} (c : I → E d) (A : E d →L[ℝ] E d) :
    W c →L[ℝ] W c := ((W c).orthogonalProjectionOnto.comp A).comp (W c).subtypeL
def u {I : Type} [Fintype I] {d : ℕ} (c : I → E d) (i : I) (h : ℕ → E d) (t : ℕ) : U c :=
  (U c).orthogonalProjectionOnto (h t - c i)
def v {I : Type} [Fintype I] {d : ℕ} (c : I → E d) (i : I) (h : ℕ → E d) (t : ℕ) : W c :=
  (W c).orthogonalProjectionOnto (h t - c i)
def r {I : Type} [Fintype I] {d : ℕ} (c : I → E d) (ξ : ℕ → E d) (t : ℕ) : U c :=
  (U c).orthogonalProjectionOnto (ξ t)
def s {I : Type} [Fintype I] {d : ℕ} (c : I → E d) (ξ : ℕ → E d) (t : ℕ) : W c :=
  (W c).orthogonalProjectionOnto (ξ t)

section Codebook
variable {I : Type} [Fintype I] [Nonempty I] {d : ℕ}
variable (c : I → E d) (A : E d →L[ℝ] E d) (b : E d)
variable (hnonconstant : ∃ i j, c i ≠ c j) (hfixed : ∀ i, A (c i) + b = c i)

include hnonconstant hfixed in
lemma fixed_on_actual_span : U c ≠ ⊥ ∧ ∀ x : U c, A (x : E d) = (x : E d) := by
  classical
  have hcard : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hp (i : I) : A (c i) = c i - b := (eq_sub_iff_add_eq).mpr (hfixed i)
  have hm : A (mean c) = mean c - b := by
    simp only [mean, map_smul, map_sum, hp, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_sub]
    rw [smul_smul, inv_mul_cancel₀ hcard, one_smul]
  have hspan : U c ≤ LinearMap.ker (A.toLinearMap - LinearMap.id) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change A (c i - mean c) - (c i - mean c) = 0
    rw [map_sub, hp, hm]
    abel
  refine ⟨?_, fun x => ?_⟩
  · intro hz
    obtain ⟨i,j,hij⟩ := hnonconstant
    have hi : c i - mean c ∈ U c := Submodule.subset_span (Set.mem_range_self i)
    have hj : c j - mean c ∈ U c := Submodule.subset_span (Set.mem_range_self j)
    rw [hz, Submodule.mem_bot, sub_eq_zero] at hi hj
    exact hij (hi.trans hj.symm)
  · have hx := hspan x.property
    change A (x : E d) - (x : E d) = 0 at hx
    exact sub_eq_zero.mp hx

lemma actual_projection_and_blocks :
    Q c = (W c).starProjection ∧ LinearMap.ker (P c).toLinearMap = W c ∧
    B c A = D5.S3.Observer.BlockStructure.FourBlockDecomposition.hiddenVisibleInfluence (U c) A ∧
    D c A = D5.S3.Observer.BlockStructure.FourBlockDecomposition.residualInternalBlock (U c) A ∧
    ∀ x : E d, x = P c x + Q c x := by
  have hq : Q c = (W c).starProjection := by
    apply ContinuousLinearMap.ext
    intro x
    have hs := (U c).starProjection_add_starProjection_orthogonal x
    change x - (U c).starProjection x = (W c).starProjection x
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hs.symm)
  refine ⟨hq, ?_, ?_, ?_, ?_⟩
  · apply Submodule.ext
    intro x
    change ((U c).orthogonalProjectionOnto x : E d) = 0 ↔ x ∈ W c
    constructor
    · intro hx
      have hz : (U c).orthogonalProjectionOnto x = 0 := Subtype.ext hx
      exact Submodule.orthogonalProjectionOnto_eq_zero_iff.mp hz
    · intro hx
      have hz : (U c).orthogonalProjectionOnto x = 0 :=
        Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr hx
      exact congrArg Subtype.val hz
  · apply ContinuousLinearMap.ext
    intro x
    simp [B, D5.S3.Observer.BlockStructure.FourBlockDecomposition.hiddenVisibleInfluence]
  · apply ContinuousLinearMap.ext
    intro x
    simp [D, D5.S3.Observer.BlockStructure.FourBlockDecomposition.residualInternalBlock]
  · intro x
    rw [hq]
    exact ((U c).starProjection_add_starProjection_orthogonal x).symm

variable (i : I) (h ξ : ℕ → E d)
variable (hstep : ∀ t, h (t + 1) = A (h t) + b + ξ t)

include hnonconstant hfixed hstep in
lemma actual_error_and_recursions :
    (∀ t, h (t+1)-c i = A (h t-c i)+ξ t) ∧
    (∀ t, u c i h (t+1)=u c i h t+B c A (v c i h t)+r c ξ t) ∧
    (∀ t, v c i h (t+1)=D c A (v c i h t)+s c ξ t) := by
  have hn := (fixed_on_actual_span c A b hnonconstant hfixed).2
  have hs := (actual_projection_and_blocks c A).2.2.2.2
  have he : ∀ t, h (t+1)-c i = A (h t-c i)+ξ t := by
    intro t
    have hp : A (c i) = c i - b := (eq_sub_iff_add_eq).mpr (hfixed i)
    rw [hstep t, map_sub, hp]
    abel
  have ha (x : E d) : A x = P c x + A (Q c x) := by
    conv_lhs => rw [hs x]
    rw [map_add]
    have hp := hn ((U c).orthogonalProjectionOnto x)
    change A (P c x) = P c x at hp
    rw [hp]
  have hp (x : U c) : (U c).orthogonalProjectionOnto (x : E d) = x := by simp
  have hz (x : U c) : (W c).orthogonalProjectionOnto (x : E d) = 0 := by
    apply Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
    intro y hy
    exact inner_eq_zero_symm.mp (hy x x.property)
  refine ⟨he, ?_, ?_⟩
  · intro t
    change (U c).orthogonalProjectionOnto (h (t+1)-c i)=_
    rw [he t,map_add,ha (h t-c i),map_add]
    rw [(actual_projection_and_blocks c A).1]
    change (U c).orthogonalProjectionOnto ((u c i h t : E d)) +
      B c A (v c i h t) + r c ξ t = _
    rw [hp]
  · intro t
    change (W c).orthogonalProjectionOnto (h (t+1)-c i)=_
    rw [he t,map_add,ha (h t-c i),map_add]
    rw [(actual_projection_and_blocks c A).1]
    change (W c).orthogonalProjectionOnto ((u c i h t : E d)) +
      D c A (v c i h t) + s c ξ t = _
    rw [hz,zero_add]

/-- the exact nonautonomous finite-time hidden solution. -/
lemma driven_finite_solution {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : V →ₗ[ℝ] V) (x f : ℕ → V) (hx : ∀ t, x (t+1)=L (x t)+f t) :
    ∀ n, x n=(L^n) (x 0)+∑ j ∈ Finset.range n, (L^(n-1-j)) (f j) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hx, ih, map_add, map_sum, Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, Module.End.one_apply]
    rw [pow_succ', Module.End.mul_apply]
    simp only [add_assoc]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j<n := Finset.mem_range.mp hj
    have he : n-j=(n-1-j)+1 := by omega
    rw [he,pow_succ',Module.End.mul_apply]


def H : W c →L[ℝ] W c := Ring.inverse (1-D c A)
def K : W c →L[ℝ] U c := (B c A).comp (H c A)
variable (q : ℝ) (hD : ‖D c A‖≤q) (hq : q<1)
set_option synthInstance.maxHeartbeats 200000 in
include hD hq in
lemma actual_inverse_data :
    (1-D c A)*H c A=1 ∧ H c A*(1-D c A)=1 ∧
    H c A=∑' j:ℕ,D c A^j ∧
    ∀ n,H c A=(∑ j ∈ Finset.range n,D c A^j)+D c A^n*H c A := by
  letI : CompleteSpace (W c) := FiniteDimensional.complete ℝ (W c)
  letI : CompleteSpace (W c →L[ℝ] W c) := FiniteDimensional.complete ℝ (W c →L[ℝ] W c)
  have hc := lt_of_le_of_lt hD hq
  have hu := (Units.oneSub (D c A) hc).isUnit
  refine ⟨Ring.mul_inverse_cancel _ hu, Ring.inverse_mul_cancel _ hu, ?_, ?_⟩
  · exact NormedRing.inverse_one_sub _ hc
  · exact fun n => NormedRing.inverse_one_sub_nth_order' n hc

include hD in
lemma actual_power_bound (hq0 : 0 ≤ q) (n : ℕ) : ‖D c A ^ n‖ ≤ q ^ n := by
  have hb : ∀ n (x : W c), ‖(D c A ^ n) x‖ ≤ q ^ n * ‖x‖ := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ',ContinuousLinearMap.mul_def,ContinuousLinearMap.comp_apply,pow_succ']
      simpa only [mul_assoc] using ((D c A).le_opNorm _).trans
        ((mul_le_mul_of_nonneg_right hD (norm_nonneg _)).trans
          (mul_le_mul_of_nonneg_left (ih x) hq0))
  exact ContinuousLinearMap.opNorm_le_bound _ (pow_nonneg hq0 n) (hb n)

include hD hq in
lemma finite_power_bound (n : ℕ) : ‖∑ t ∈ Finset.range n,D c A^t‖≤(1-q)⁻¹ := by
  have hq0 : 0≤q := (norm_nonneg _).trans hD
  have hden : 0<1-q := sub_pos.mpr hq
  calc
    _ ≤ ∑ t ∈ Finset.range n, ‖D c A^t‖ := norm_sum_le _ _
    _ ≤ ∑ t ∈ Finset.range n,q^t := Finset.sum_le_sum (fun t _ =>
      actual_power_bound c A q hD hq0 t)
    _ ≤ (1-q)⁻¹ := by
      have hgeom := geom_sum_mul q n
      have hp : 0≤q^n := pow_nonneg hq0 n
      rw [← one_div (1-q)]
      apply (le_div_iff₀ hden).mpr
      nlinarith

include hnonconstant hfixed hstep hD hq in
lemma actual_constant_hidden_drift (w : W c) (hr : ∀ t,r c ξ t=0) (hs : ∀ t,s c ξ t=w) :
    (∀ t,v c i h t=H c A w+(D c A^t) (v c i h 0-H c A w)) ∧
    (∀ n,u c i h n-u c i h 0=(n:ℝ)•K c A w+
      B c A ((∑ t ∈ Finset.range n,D c A^t) (v c i h 0-H c A w))) ∧
    (∀ n,‖u c i h n-u c i h 0-(n:ℝ)•K c A w‖≤
      ‖B c A‖/(1-q)*‖v c i h 0-H c A w‖) ∧
    Tendsto (fun n:ℕ=>(n:ℝ)⁻¹•(u c i h n-u c i h 0)) atTop (𝓝 (K c A w)) ∧
    (∃ C:ℝ,∀ n,‖v c i h n‖≤C) ∧ ((∀ w:W c,K c A w=0) ↔ B c A=0) := by
  have hc := lt_of_le_of_lt hD hq
  have hq0 : 0≤q := (norm_nonneg _).trans hD
  have hi := actual_inverse_data c A q hD hq
  have he := actual_error_and_recursions c A b hnonconstant hfixed i h ξ hstep
  have hHw : D c A (H c A w)+w=H c A w := by
    have hh := DFunLike.congr_fun hi.1 w
    change H c A w - D c A (H c A w) = w at hh
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp hh).symm
  have hv : ∀ t,v c i h t=H c A w+(D c A^t) (v c i h 0-H c A w) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [he.2.2 t,hs t,ih,map_add,pow_succ',ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
      calc
        _ = (D c A (H c A w)+w) + D c A ((D c A^t) (v c i h 0-H c A w)) := by abel
        _ = _ := by rw [hHw]
  have hu : ∀ n,u c i h n-u c i h 0=(n:ℝ)•K c A w+
      B c A ((∑ t ∈ Finset.range n,D c A^t) (v c i h 0-H c A w)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [he.2.1 n,hr n,hv n,Finset.sum_range_succ,
        ContinuousLinearMap.add_apply,map_add,map_add]
      rw [Nat.cast_add,Nat.cast_one,add_smul,one_smul]
      dsimp only [K,ContinuousLinearMap.comp_apply] at ih ⊢
      have ih' := congrArg (fun z : U c => z + u c i h 0) ih
      have hiu : u c i h n = (n:ℝ)•B c A (H c A w) +
          B c A ((∑ t ∈ Finset.range n,D c A^t) (v c i h 0-H c A w)) + u c i h 0 := by
        simpa only [sub_add_cancel] using ih'
      rw [hiu]
      abel
  let C : ℝ := ‖B c A‖/(1-q)*‖v c i h 0-H c A w‖
  have hC0 : 0≤C := by dsimp [C]; positivity
  have hbound : ∀ n,‖u c i h n-u c i h 0-(n:ℝ)•K c A w‖≤C := by
    intro n
    rw [hu n,add_sub_cancel_left]
    calc
      _ ≤ ‖B c A‖*‖(∑ t ∈ Finset.range n,D c A^t) (v c i h 0-H c A w)‖ :=
        (B c A).le_opNorm _
      _ ≤ ‖B c A‖*((1-q)⁻¹*‖v c i h 0-H c A w‖) := by
        gcongr
        exact ((∑ t ∈ Finset.range n,D c A^t).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (finite_power_bound c A q hD hq n) (norm_nonneg _))
      _ = C := by dsimp [C]; ring
  have hlim0 : Tendsto (fun n:ℕ=>(n:ℝ)⁻¹•
      (u c i h n-u c i h 0-(n:ℝ)•K c A w)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) (by simpa using ((tendsto_inv_atTop_nhds_zero_nat (𝕜:=ℝ)).mul_const C))
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
    exact mul_le_mul_of_nonneg_left (hbound n) (inv_nonneg.mpr (Nat.cast_nonneg n))
  have hlim : Tendsto (fun n:ℕ=>(n:ℝ)⁻¹•(u c i h n-u c i h 0)) atTop (𝓝 (K c A w)) := by
    have hh : Tendsto (fun n : ℕ => (n:ℝ)⁻¹ •
        (u c i h n-u c i h 0-(n:ℝ)•K c A w)+K c A w) atTop (𝓝 (K c A w)) := by
      simpa using hlim0.add_const (K c A w)
    apply Tendsto.congr' _ hh
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
    simp only [smul_sub,smul_smul,inv_mul_cancel₀ hn0,one_smul,sub_add_cancel]
  refine ⟨hv,hu,hbound,hlim,?_,?_⟩
  · refine ⟨‖H c A w‖+‖v c i h 0-H c A w‖,fun n=>?_⟩
    rw [hv n]
    calc
      _ ≤ ‖H c A w‖+‖(D c A^n) (v c i h 0-H c A w)‖ := norm_add_le _ _
      _ ≤ _ := by
        gcongr
        have hp : ‖D c A^n‖≤1 := (actual_power_bound c A q hD hq0 n).trans (pow_le_one₀ hq0 hq.le)
        exact ((D c A^n).le_opNorm _).trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (norm_nonneg (v c i h 0-H c A w)))
  · constructor
    · intro hK
      apply ContinuousLinearMap.ext
      intro y
      change B c A y = 0
      have hh := hK ((1-D c A) y)
      have hiw := DFunLike.congr_fun hi.2.1 y
      change B c A (H c A ((1-D c A) y)) = 0 at hh
      change H c A ((1-D c A) y) = y at hiw
      rw [hiw] at hh
      exact hh
    · intro hz w
      simp [K,hz]


def PiStar : E d →L[ℝ] U c :=
  (U c).orthogonalProjectionOnto+(K c A).comp (W c).orthogonalProjectionOnto

/-- the sharp Euclidean norm, proved through the actual adjoint column. -/
lemma orthogonal_row_norm (L : W c →L[ℝ] U c) (hU : U c≠⊥) :
    ‖(U c).orthogonalProjectionOnto+L.comp (W c).orthogonalProjectionOnto‖=
      Real.sqrt (1+‖L‖^2) := by
  let R := (U c).orthogonalProjectionOnto+L.comp (W c).orthogonalProjectionOnto
  have ha : R.adjoint=(U c).subtypeL+(W c).subtypeL.comp L.adjoint := by
    simp [R,ContinuousLinearMap.adjoint_comp,Submodule.adjoint_orthogonalProjectionOnto]
  have hp (x:U c) : ‖R.adjoint x‖^2=‖x‖^2+‖L.adjoint x‖^2 := by
    rw [ha]
    have ho : inner ℝ (x:E d) (L.adjoint x:E d)=0 := (L.adjoint x).property x x.property
    have hh := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x:E d) (L.adjoint x:E d) ho
    simpa [pow_two] using hh
  have hupper : ‖R.adjoint‖≤Real.sqrt (1+‖L‖^2) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro x
    have hb := L.adjoint.le_opNorm x
    have hs : (Real.sqrt (1+‖L‖^2))^2=1+‖L‖^2 := Real.sq_sqrt (by positivity)
    have hnorm : ‖L.adjoint‖=‖L‖ := ContinuousLinearMap.adjoint.norm_map L
    rw [hnorm] at hb
    have hb2 := mul_self_le_mul_self (norm_nonneg (L.adjoint x)) hb
    have hsx := congrArg (fun z : ℝ => z * ‖x‖^2) hs
    nlinarith [hp x, norm_nonneg (R.adjoint x), mul_nonneg (Real.sqrt_nonneg (1+‖L‖^2)) (norm_nonneg x)]
  have hone : 1≤‖R.adjoint‖ := by
    have hex : ∃ x : U c, x ≠ 0 := by
      by_contra hn
      push_neg at hn
      apply hU
      apply Submodule.ext
      intro x
      change x ∈ U c ↔ x = 0
      constructor
      · intro hx
        exact congrArg Subtype.val (hn ⟨x,hx⟩)
      · intro hx
        rw [hx]
        exact (U c).zero_mem
    obtain ⟨y,hy⟩ := hex
    have hn : 0<‖y‖ := norm_pos_iff.mpr hy
    have hb := R.adjoint.le_opNorm y
    have hxle : ‖y‖ ≤ ‖R.adjoint y‖ := by
      nlinarith [hp y,sq_nonneg ‖L.adjoint y‖,norm_nonneg (R.adjoint y)]
    nlinarith
  have hL : ‖L.adjoint‖≤Real.sqrt (‖R.adjoint‖^2-1) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro x
    have hb := R.adjoint.le_opNorm x
    have hs := Real.sq_sqrt (show 0≤‖R.adjoint‖^2-1 by nlinarith)
    have hb2 := mul_self_le_mul_self (norm_nonneg (R.adjoint x)) hb
    have hsx := congrArg (fun z : ℝ => z * ‖x‖^2) hs
    nlinarith [hp x,norm_nonneg (L.adjoint x),
      mul_nonneg (Real.sqrt_nonneg (‖R.adjoint‖^2-1)) (norm_nonneg x)]
  have hnorm : ‖L.adjoint‖=‖L‖ := ContinuousLinearMap.adjoint.norm_map L
  rw [hnorm] at hL
  have hs := Real.sq_sqrt (show 0≤‖R.adjoint‖^2-1 by nlinarith)
  have hlow : Real.sqrt (1+‖L‖^2)≤‖R.adjoint‖ := by
    have ht := Real.sq_sqrt (show 0≤1+‖L‖^2 by positivity)
    have hb2 := mul_self_le_mul_self (norm_nonneg L) hL
    nlinarith [norm_nonneg L,Real.sqrt_nonneg (1+‖L‖^2),norm_nonneg R.adjoint]
  simpa only [ContinuousLinearMap.adjoint.norm_map] using le_antisymm hupper hlow

include hnonconstant hfixed hstep hD hq in
lemma actual_autonomous_readout :
    (∀ (x:U c) (y:W c),‖(x:E d)+(y:E d)‖^2=‖x‖^2+‖y‖^2) ∧
    (∀ x:U c,PiStar c A (x:E d)=x) ∧ (PiStar c A).comp A=PiStar c A ∧
    (∀ L:E d→ₗ[ℝ]U c,(∀ x:U c,L (x:E d)=x) →
      L.comp A.toLinearMap=L → L=(PiStar c A).toLinearMap) ∧
    (∀ (x:U c) (y:W c),PiStar c A ((x:E d)+(y:E d))=x+K c A y) ∧
    (∀ x:E d,PiStar c A x=0 ↔ ∃ y:W c,x=-(K c A y:E d)+(y:E d)) ∧
    ‖PiStar c A‖=Real.sqrt (1+‖K c A‖^2) ∧
    (∀ y:W c,A (-(K c A y:E d)+(y:E d))=-(K c A (D c A y):E d)+(D c A y:E d)) ∧
    (∀ y:W c,Tendsto (fun n:ℕ=>(A^n) (-(K c A y:E d)+(y:E d))) atTop (𝓝 0)) ∧
    (∀ j k:I,(PiStar c A (c j-c k):E d)=c j-c k) ∧
    (∀ t,u c i h (t+1)+K c A (v c i h (t+1))=
      u c i h t+K c A (v c i h t)+r c ξ t+K c A (s c ξ t)) := by
  have hn := fixed_on_actual_span c A b hnonconstant hfixed
  have hi := actual_inverse_data c A q hD hq
  have he := actual_error_and_recursions c A b hnonconstant hfixed i h ξ hstep
  have hsplit := (actual_projection_and_blocks c A).2.2.2.2
  have hK (y:W c) : B c A y+K c A (D c A y)=K c A y := by
    have hh := DFunLike.congr_fun hi.2.1 y
    change H c A (y-D c A y) = y at hh
    rw [map_sub] at hh
    have hb := congrArg (B c A) hh
    rw [map_sub] at hb
    change K c A y-K c A (D c A y) = B c A y at hb
    exact (sub_eq_iff_eq_add.mp hb).symm
  have hpu (x : U c) : (W c).orthogonalProjectionOnto (x : E d) = 0 := by
    apply Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
    intro y hy
    exact inner_eq_zero_symm.mp (hy x x.property)
  have hpw (y : W c) : (U c).orthogonalProjectionOnto (y : E d) = 0 :=
    Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr y.property
  have hsplit' (x : E d) : x =
      ((U c).orthogonalProjectionOnto x : E d) + ((W c).orthogonalProjectionOnto x : E d) := by
    calc
      x = P c x + Q c x := hsplit x
      _ = _ := by rw [(actual_projection_and_blocks c A).1]; rfl
  have hrow (x:U c) (y:W c) : PiStar c A ((x:E d)+(y:E d))=x+K c A y := by
    simp only [PiStar,add_apply,ContinuousLinearMap.comp_apply,map_add,
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,hpu,hpw,map_zero,add_zero,zero_add]
  have hblock (y:W c) : A (y:E d)=(B c A y:E d)+(D c A y:E d) := by
    have ht := D5.S3.Observer.BlockStructure.FourBlockDecomposition.typed_block_formulas
      (U c) A (0 : U c) y
    rw [← (actual_projection_and_blocks c A).2.2.1,
      ← (actual_projection_and_blocks c A).2.2.2.1] at ht
    have hb : (B c A y : E d) = (U c).starProjection (A (y:E d)) := by
      simpa only [Submodule.starProjection_eq_self_iff.mpr y.property] using ht.2.1
    have hd : (D c A y : E d) = (W c).starProjection (A (y:E d)) := by
      simpa only [Submodule.starProjection_eq_self_iff.mpr y.property] using ht.2.2.2
    calc
      A (y:E d) = P c (A y) + Q c (A y) := hsplit (A y)
      _ = (U c).starProjection (A y) + (W c).starProjection (A y) := by
        rw [(actual_projection_and_blocks c A).1]; rfl
      _ = _ := by rw [hb,hd]
  have hgraph (y:W c) : A (-(K c A y:E d)+(y:E d))=
      -(K c A (D c A y):E d)+(D c A y:E d) := by
    rw [map_add,map_neg,hn.2,hblock]
    have hb := congrArg (fun x:U c=>(x:E d)) (hK y)
    push_cast at hb
    rw [show (K c A y : E d) = (B c A y : E d) + (K c A (D c A y) : E d) from hb.symm]
    abel
  refine ⟨?_,?_,?_,?_,hrow,?_,?_,hgraph,?_,?_,?_⟩
  · intro x y
    simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (x:E d) (y:E d) (y.property x x.property)
  · intro x
    simpa using hrow x 0
  · apply ContinuousLinearMap.ext
    intro x
    change PiStar c A (A x) = PiStar c A x
    conv_lhs => rw [hsplit' x,map_add,hn.2,hblock]
    rw [map_add,hrow]
    have hu := hrow ((U c).orthogonalProjectionOnto x) 0
    simp only [Submodule.coe_zero,add_zero,zero_add,map_zero] at hu
    rw [hu]
    conv_rhs => rw [hsplit' x,hrow]
    rw [hK]
  · intro L hL hLA
    have hy (y:W c) : L (y:E d)=K c A y := by
      let z := H c A y
      have hz := LinearMap.congr_fun hLA (z:E d)
      change L (A (z:E d)) = L (z:E d) at hz
      rw [hblock,map_add,hL] at hz
      have hh := DFunLike.congr_fun hi.1 y
      have hd : z-D c A z=y := by
        change H c A y - D c A (H c A y) = y
        exact hh
      calc
        L (y:E d) = L (z:E d) - L (D c A z:E d) := by rw [← hd]; simp
        _ = B c A z := by rw [← hz]; abel
        _ = K c A y := rfl
    apply LinearMap.ext
    intro x
    change L x = PiStar c A x
    rw [hsplit' x,map_add,hL,hy,hrow]
  · intro x
    constructor
    · intro hx
      refine ⟨(W c).orthogonalProjectionOnto x,?_⟩
      conv at hx => lhs; rw [hsplit' x,hrow]
      have hh : (U c).orthogonalProjectionOnto x= -K c A ((W c).orthogonalProjectionOnto x) :=
        eq_neg_of_add_eq_zero_left hx
      calc
        x = ((U c).orthogonalProjectionOnto x : E d) + ((W c).orthogonalProjectionOnto x : E d) := hsplit' x
        _ = _ := by rw [hh]; rfl
    · rintro ⟨y,rfl⟩
      simpa using hrow (-K c A y) y
  · exact orthogonal_row_norm c (K c A) hn.1
  · intro y
    have hp : ∀ n,(A^n) (-(K c A y:E d)+(y:E d))=
        -(K c A ((D c A^n) y):E d)+((D c A^n) y:E d) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ',ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,ih,hgraph,
                         pow_succ',ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
    simp_rw [hp]
    have hd : Tendsto (fun n : ℕ => (D c A ^ n) y) atTop (𝓝 0) := by
      have hh := tendsto_pow_atTop_nhds_zero_of_norm_lt_one (lt_of_le_of_lt hD hq)
      have ht := ((ContinuousLinearMap.apply ℝ (W c) y).continuous.tendsto
        (0 : W c →L[ℝ] W c)).comp hh
      change Tendsto (fun n : ℕ => (D c A ^ n) y) atTop (𝓝 0) at ht
      exact ht
    have hk : Tendsto (fun n : ℕ => K c A ((D c A ^ n) y)) atTop (𝓝 0) := by
      simpa only [Function.comp_def,Submodule.subtypeL_apply,map_zero] using ((K c A).continuous.tendsto 0).comp hd
    have hku : Tendsto (fun n : ℕ => (K c A ((D c A ^ n) y) : E d)) atTop (𝓝 0) := by
      simpa only [Function.comp_def,Submodule.subtypeL_apply,map_zero] using ((U c).subtypeL.continuous.tendsto 0).comp hk
    have hwy : Tendsto (fun n : ℕ => ((D c A ^ n) y : E d)) atTop (𝓝 0) := by
      simpa only [Function.comp_def,Submodule.subtypeL_apply,map_zero] using ((W c).subtypeL.continuous.tendsto 0).comp hd
    simpa only [neg_zero,zero_add] using hku.neg.add hwy
  · intro j k
    have hj : c j-mean c∈U c := Submodule.subset_span (Set.mem_range_self j)
    have hk : c k-mean c∈U c := Submodule.subset_span (Set.mem_range_self k)
    have hmem : c j-c k∈U c := by
      convert (U c).sub_mem hj hk using 1 <;> abel
    have hh := hrow (⟨c j-c k,hmem⟩:U c) 0
    simpa using congrArg (fun x:U c=>(x:E d)) hh
  · intro t
    rw [he.2.1 t,he.2.2 t,map_add]
    have hh := hK (v c i h t)
    calc
      _ = u c i h t + (B c A (v c i h t) + K c A (D c A (v c i h t))) + r c ξ t + K c A (s c ξ t) := by abel
      _ = _ := by rw [hh]
end Codebook


end D5.S3.Observer.LinearMemory.AffineCodebookMemory
