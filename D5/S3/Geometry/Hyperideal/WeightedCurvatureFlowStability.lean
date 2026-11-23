/- GID: D5/S3/Geometry/Hyperideal/WeightedCurvatureFlowStability
   generality: I
   mirror-B: D5/B/S3/Geometry/Hyperideal/WeightedCurvatureFlowStability
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Hellinger stability for a multiplicative monotone flow without local Lipschitz assumptions. -/

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace D5.S3.Geometry.Hyperideal.WeightedCurvatureFlowStability
set_option autoImplicit false
open scoped BigOperators

variable {I : Type*} [Fintype I]

/-- Energy norm squared written as a sum, independently of the Hessian representation. -/
def SqNorm (v : I → ℝ) : ℝ := ∑ i, v i ^ 2

/-- Square-root chart that turns length-weighted descent into a Euclidean
vector field. One-sided stability does not require Lipschitz continuity of F. -/
noncomputable def pullback (F : (I → ℝ) → (I → ℝ)) (z : I → ℝ) : I → ℝ :=
  fun i => z i / 2 * F (fun j => z j ^ 2 / 4) i

private theorem pullback_pair_identity (F : (I → ℝ) → (I → ℝ)) (z w : I → ℝ) :
    let x := fun i => z i ^ 2 / 4
    let y := fun i => w i ^ 2 / 4
    (∑ i, (z i-w i)*(pullback F z i-pullback F w i)) =
      (∑ i, (x i-y i)*(F x i-F y i)) +
        (∑ i, (z i-w i)^2*(F x i+F y i))/4 := by
  dsimp only
  rw [div_eq_mul_inv,Finset.sum_mul,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold pullback
  ring

/-- Global one-sided Lipschitz constant C/2 for the negative pulled-back
field, under monotonicity in physical lengths and a curvature lower bound. -/
private theorem pullback_one_sided (F : (I → ℝ) → (I → ℝ)) (z w : I → ℝ) (C : ℝ)
    (hmon : let x := fun i => z i ^ 2 / 4; let y := fun i => w i ^ 2 / 4;
      0 ≤ ∑ i, (x i-y i)*(F x i-F y i))
    (hC : ∀ i, -C ≤ F (fun j => z j ^ 2 / 4) i ∧ -C ≤ F (fun j => w j ^ 2 / 4) i) :
    -(C/2)*SqNorm (z-w) ≤ ∑ i, (z i-w i)*(pullback F z i-pullback F w i) := by
  rw [pullback_pair_identity]
  dsimp only at hmon ⊢
  have hlo : (-2*C)*SqNorm (z-w) ≤
      ∑ i, (z i-w i)^2*(F (fun j => z j^2/4) i+F (fun j => w j^2/4) i) := by
    unfold SqNorm
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [mul_comm (-2*C)]
    exact mul_le_mul_of_nonneg_left (by linarith [(hC i).1,(hC i).2]) (sq_nonneg _)
  nlinarith only [hlo,hmon]

/-- Distance stability for any two trajectories of the square-root
chart equation. No continuity or local Lipschitz premise on F is needed
for comparison of existing trajectories. -/
private theorem chart_trajectory_stability
    (F : (I → ℝ) → (I → ℝ)) (z w : ℝ → I → ℝ) {a b C : ℝ} (hab : a≤b)
    (hz : ∀ t ∈ Set.Icc a b, ∀ i,
      HasDerivAt (fun s => z s i) (-pullback F (z t) i) t)
    (hw : ∀ t ∈ Set.Icc a b, ∀ i,
      HasDerivAt (fun s => w s i) (-pullback F (w t) i) t)
    (hm : ∀ t ∈ Set.Icc a b,
      let x := fun i => z t i ^ 2 / 4; let y := fun i => w t i ^ 2 / 4
      0 ≤ ∑ i, (x i-y i)*(F x i-F y i))
    (hC : ∀ t ∈ Set.Icc a b, ∀ i,
      -C ≤ F (fun j => z t j ^ 2/4) i ∧ -C ≤ F (fun j => w t j ^ 2/4) i) :
    SqNorm (z b-w b) ≤ Real.exp (C*(b-a)) * SqNorm (z a-w a) := by
  let E : ℝ → ℝ := fun t => SqNorm (z t-w t)
  let R : ℝ → ℝ := fun t => ∑ i, (z t i-w t i)*(pullback F (z t) i-pullback F (w t) i)
  have hd (t : ℝ) (ht : t∈Set.Icc a b) : HasDerivAt E (-2*R t) t := by
    have item (i : I) :
        HasDerivAt (fun s => (z s i-w s i)^2)
          (2*(z t i-w t i)*((-pullback F (z t) i)-(-pullback F (w t) i))) t := by
      convert ((hz t ht i).sub (hw t ht i)).pow 2 using 1
      simp only [Pi.sub_apply]
      ring
    have hd0 := HasDerivAt.fun_sum (fun (i : I) (_ : i∈Finset.univ) => item i)
    have heq : (∑ i, 2*(z t i-w t i)*((-pullback F (z t) i)-(-pullback F (w t) i))) = -2*R t := by
      unfold R
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [← heq]
    exact hd0
  let V : ℝ → ℝ := fun t => Real.exp (-C*(t-a)) * E t
  have hV (t : ℝ) (ht : t∈Set.Icc a b) :
      HasDerivAt V (Real.exp (-C*(t-a))*(-C*E t-2*R t)) t := by
    have hex : HasDerivAt (fun s : ℝ => Real.exp (-C*(s-a)))
        (Real.exp (-C*(t-a))*(-C)) t := by
      simpa using (((hasDerivAt_id t).sub_const a).const_mul (-C)).exp
    convert hex.mul (hd t ht) using 1
    ring
  have haV : AntitoneOn V (Set.Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
    · intro t ht
      exact (hV t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hV t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have hi := interior_subset ht
      rw [(hV t hi).deriv]
      have hc := pullback_one_sided F (z t) (w t) C (hm t hi) (hC t hi)
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by
        change -(C/2)*E t ≤ R t at hc
        linarith)
  have hv := haV (show a∈Set.Icc a b from ⟨le_rfl,hab⟩)
    (show b∈Set.Icc a b from ⟨hab,le_rfl⟩) hab
  change Real.exp (-C*(b-a))*E b ≤ Real.exp (-C*(a-a))*E a at hv
  rw [sub_self,mul_zero,Real.exp_zero,one_mul,show -C*(b-a)=-(C*(b-a)) by ring,Real.exp_neg] at hv
  have hv' : E b / Real.exp (C*(b-a)) ≤ E a := by
    rw [div_eq_inv_mul]
    exact hv
  simpa [E,mul_comm] using (div_le_iff₀ (Real.exp_pos (C*(b-a)))).mp hv'

omit [Fintype I] in
/-- The positive length-weighted ODE is the chart ODE after z=2√ℓ. -/
private theorem length_to_chart (F : (I → ℝ) → (I → ℝ)) (x : ℝ → I → ℝ)
    (t : ℝ) (hpos : ∀ i, 0<x t i)
    (hx : ∀ i, HasDerivAt (fun s => x s i) (-(x t i)*F (x t) i) t) (i : I) :
    HasDerivAt (fun s => 2*Real.sqrt (x s i))
      (-pullback F (fun j => 2*Real.sqrt (x t j)) i) t := by
  have hchart : (fun j => (2*Real.sqrt (x t j))^2/4) = x t := by
    funext j
    calc
      _ = (Real.sqrt (x t j))^2 := by ring
      _ = x t j := Real.sq_sqrt (hpos j).le
  have hp : Real.sqrt (x t i)≠0 := (Real.sqrt_pos.2 (hpos i)).ne'
  have hder := ((hx i).sqrt (hpos i).ne').const_mul (2:ℝ)
  convert hder using 1
  unfold pullback
  rw [hchart,← Real.sq_sqrt (hpos i).le]
  simp only [Real.sqrt_sq (Real.sqrt_nonneg _)]
  field_simp


/-- Squared Euclidean distance in the chart z=2√ℓ, on the first n lengths. -/
noncomputable def chartDistanceSq (n : ℕ) (x y : ℕ → ℝ) : ℝ :=
  SqNorm (fun i : Fin n => 2*Real.sqrt (x i.val) - 2*Real.sqrt (y i.val))

/-- The chart separates positive lengths and controls all positive trajectories
of multiplicative descent, with no local Lipschitz hypothesis on the field. -/
def StabilityLaw (n : ℕ) (observe : (ℕ → ℝ) → (ℕ → ℝ) → ℝ) : Prop :=
  (∀ x y : ℕ → ℝ, (∀ i<n, 0<x i ∧ 0<y i) →
    (observe x y = 0 ↔ ∀ i<n, x i=y i)) ∧
  (∀ (F : (ℕ → ℝ) → (ℕ → ℝ)) (x y : ℝ → ℕ → ℝ)
    (a b C : ℝ), a≤b →
    -- Only the chosen finite length coordinates can influence those coordinates.
    (∀ u v : ℕ → ℝ, (∀ i<n, u i=v i) → ∀ i<n, F u i=F v i) →
    (∀ t∈Set.Icc a b, ∀ i<n, 0<x t i ∧ 0<y t i) →
    (∀ t∈Set.Icc a b, ∀ i<n, HasDerivAt (fun s => x s i) (-(x t i)*F (x t) i) t) →
    (∀ t∈Set.Icc a b, ∀ i<n, HasDerivAt (fun s => y s i) (-(y t i)*F (y t) i) t) →
    (∀ t∈Set.Icc a b, 0≤∑ i : Fin n,(x t i.val-y t i.val)*(F (x t) i.val-F (y t) i.val)) →
    (∀ t∈Set.Icc a b, ∀ i<n, -C≤F (x t) i ∧ -C≤F (y t) i) →
    observe (x b) (y b) ≤ Real.exp (C*(b-a)) * observe (x a) (y a))

private theorem chart_definite (n : ℕ) (x y : ℕ → ℝ)
    (h : ∀ i<n, 0<x i ∧ 0<y i) :
    chartDistanceSq n x y = 0 ↔ ∀ i<n, x i=y i := by
  constructor
  · intro h0 i hi
    let j : Fin n := ⟨i,hi⟩
    have ht : (2*Real.sqrt (x i)-2*Real.sqrt (y i))^2 ≤ chartDistanceSq n x y :=
      Finset.single_le_sum (fun (k : Fin n) _ => sq_nonneg
        (2*Real.sqrt (x k.val)-2*Real.sqrt (y k.val))) (Finset.mem_univ j)
    rw [h0] at ht
    have hs : Real.sqrt (x i) = Real.sqrt (y i) := by nlinarith
    rw [← Real.sq_sqrt (h i hi).1.le, ← Real.sq_sqrt (h i hi).2.le, hs]
  · intro h0
    unfold chartDistanceSq SqNorm
    apply Finset.sum_eq_zero
    intro i _
    simp [h0 i.val i.isLt]

private def restrictField (n : ℕ) (F : (ℕ → ℝ) → (ℕ → ℝ)) (v : Fin n → ℝ) (i : Fin n) : ℝ :=
  F (fun j => if h : j<n then v ⟨j,h⟩ else 0) i.val

/-- Weighted flow uniqueness follows from a true pairwise distance bound.
One-sided boundedness of the original residual is enough for stability. -/
theorem weighted_stability :
    ∀ n : ℕ, let observed := chartDistanceSq n; StabilityLaw n observed := by
  intro n
  refine ⟨chart_definite n, ?_⟩
  intro F x y a b C hab hF hp hx hy hm hC
  let z (t : ℝ) (i : Fin n) := 2*Real.sqrt (x t i.val)
  let w (t : ℝ) (i : Fin n) := 2*Real.sqrt (y t i.val)
  let G := restrictField n F
  have hG (u : ℕ → ℝ) (i : Fin n) : G (fun j => u j.val) i=F u i.val := by
    unfold G restrictField
    apply hF
    · intro j hj
      simp [hj]
    · exact i.isLt
  have lift {t : ℝ} (ht : t∈Set.Icc a b) (i : Fin n) :
      z t i ^ 2 /4 = x t i.val ∧ w t i ^ 2/4 = y t i.val := by
    constructor
    · change (2*Real.sqrt (x t i.val))^2/4=_
      rw [show ∀ s : ℝ, (2*s)^2/4=s^2 by intro s; ring,Real.sq_sqrt (hp t ht i i.isLt).1.le]
    · change (2*Real.sqrt (y t i.val))^2/4=_
      rw [show ∀ s : ℝ, (2*s)^2/4=s^2 by intro s; ring,Real.sq_sqrt (hp t ht i i.isLt).2.le]
  have fx (t : ℝ) (ht : t∈Set.Icc a b) (i : Fin n) :
      G (fun j => z t j^2/4) i = F (x t) i.val := by
    rw [show (fun j => z t j^2/4) = (fun j => x t j.val) from funext (fun j => (lift ht j).1),hG]
  have fy (t : ℝ) (ht : t∈Set.Icc a b) (i : Fin n) :
      G (fun j => w t j^2/4) i = F (y t) i.val := by
    rw [show (fun j => w t j^2/4) = (fun j => y t j.val) from funext (fun j => (lift ht j).2),hG]
  exact chart_trajectory_stability G z w hab
    (fun t ht => length_to_chart G (fun s i => x s i.val) t
      (fun i => (hp t ht i i.isLt).1) (fun i => by rw [hG]; exact hx t ht i i.isLt))
    (fun t ht => length_to_chart G (fun s i => y s i.val) t
      (fun i => (hp t ht i i.isLt).2) (fun i => by rw [hG]; exact hy t ht i i.isLt))
    (fun t ht => by
      dsimp only
      simp_rw [fx t ht, fy t ht, fun i => (lift ht i).1, fun i => (lift ht i).2]
      exact hm t ht)
    (fun t ht i => by rw [fx t ht,fy t ht]; exact hC t ht i.val i.isLt)

#print axioms weighted_stability
end D5.S3.Geometry.Hyperideal.WeightedCurvatureFlowStability
