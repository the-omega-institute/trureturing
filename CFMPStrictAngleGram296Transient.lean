import D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic
import Lean.Util.CollectAxioms

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
open Real
open D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface (gram)

namespace CFMPStrictAngleGram296Transient

/-- The strict hyperbolic triangle-angle inequality gives the positive
cosine-law numerator, including a possible obtuse angle. -/
theorem triangle_cosine_margin (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hs : a+b+c < Real.pi) :
    0 < Real.sin a*Real.sin b ∧
      Real.sin a*Real.sin b < Real.cos c+Real.cos a*Real.cos b := by
  have hsa := Real.sin_pos_of_pos_of_lt_pi ha (by linarith)
  have hsb := Real.sin_pos_of_pos_of_lt_pi hb (by linarith)
  have hm := Real.cos_lt_cos_of_nonneg_of_le_pi
    (show 0 ≤ a+b by linarith)
    (show Real.pi-c ≤ Real.pi by linarith)
    (show a+b < Real.pi-c by linarith)
  rw [Real.cos_pi_sub,Real.cos_add] at hm
  exact ⟨mul_pos hsa hsb,by linarith⟩

theorem triangle_gram_negative (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hs : a+b+c < Real.pi) :
    1-Real.cos a^2-Real.cos b^2-Real.cos c^2-
      2*Real.cos a*Real.cos b*Real.cos c < 0 := by
  obtain ⟨hp,hm⟩ := triangle_cosine_margin a b c ha hb hc hs
  have hnum : 0 < Real.cos c+Real.cos a*Real.cos b := hp.trans hm
  have hsq : (Real.sin a*Real.sin b)^2 <
      (Real.cos c+Real.cos a*Real.cos b)^2 := by
    nlinarith [mul_pos (sub_pos.mpr hm) (add_pos hnum hp)]
  have hsa : Real.sin a^2 = 1-Real.cos a^2 := by
    nlinarith [Real.sin_sq_add_cos_sq a]
  have hsb : Real.sin b^2 = 1-Real.cos b^2 := by
    nlinarith [Real.sin_sq_add_cos_sq b]
  have hid : 1-Real.cos a^2-Real.cos b^2-Real.cos c^2-
      2*Real.cos a*Real.cos b*Real.cos c =
      (Real.sin a*Real.sin b)^2-(Real.cos c+Real.cos a*Real.cos b)^2 := by
    rw [mul_pow,hsa,hsb]
    ring
  rw [hid]
  exact sub_neg.mpr hsq

/-- These are entries of the original six-parameter Gram matrix. The final
identity is its nonprincipal complementary-minor identity. -/
theorem gram_cofactor_identities (p q r s t u : ℝ) :
    let G := gram p q r u t s
    let C := G.adjugate
    C 0 0 = 1-s^2-t^2-u^2-2*s*t*u ∧
    C 0 1 = (q+r*u)*(s+t*u)+(p+r*t)*(1-u^2) ∧
    C 0 2 = (p+r*t)*(s+u*t)+(q+r*u)*(1-t^2) ∧
    C 1 2 = (p+t*r)*(q+u*r)+(s+t*u)*(1-r^2) ∧
    C 0 0*C 1 2-C 0 1*C 0 2 = G.det*(s+t*u) := by
  dsimp only
  refine ⟨?_,?_,?_,?_,?_⟩ <;>
    norm_num [Matrix.adjugate_fin_succ_eq_det_submatrix,gram,
      Matrix.det_succ_row_zero,Matrix.det_fin_three,Matrix.det_fin_two,
      Matrix.det_fin_one,Matrix.det_fin_zero,Matrix.submatrix_apply,
      Fin.sum_univ_succ,Matrix.of_apply,Matrix.cons_val_zero',
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.cons_val_succ',Matrix.head_cons,Matrix.tail_cons,
      Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Fin.succAbove,
      Fin.reduceEq,Fin.reduceFinMk,Fin.castSucc,Fin.castAdd,Fin.succ,
      Fin.val_zero,Fin.val_succ,Nat.succ_eq_add_one,Nat.reduceAdd,
      Fin.castLE,Fin.cast] <;> ring

/-- All four strict triangle-angle inequalities force the original angle
Gram determinant to be negative. No nonobtuse-angle assumption is used. -/
theorem strict_angle_gram_det_neg (a b c d e f : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (h012 : a+b+d < Real.pi) (h013 : a+c+e < Real.pi)
    (h023 : b+c+f < Real.pi) (h123 : d+e+f < Real.pi) :
    (gram (Real.cos a) (Real.cos b) (Real.cos c)
      (Real.cos f) (Real.cos e) (Real.cos d)).det < 0 := by
  let G := gram (Real.cos a) (Real.cos b) (Real.cos c)
    (Real.cos f) (Real.cos e) (Real.cos d)
  let C := G.adjugate
  obtain ⟨h00,h01,h02,h12,hjac⟩ := gram_cofactor_identities
    (Real.cos a) (Real.cos b) (Real.cos c)
    (Real.cos d) (Real.cos e) (Real.cos f)
  have hq : 0 < Real.cos b+Real.cos c*Real.cos f :=
    (triangle_cosine_margin c f b hc hf hb (by linarith)).1.trans
      (triangle_cosine_margin c f b hc hf hb (by linarith)).2
  have hs : 0 < Real.cos d+Real.cos e*Real.cos f :=
    (triangle_cosine_margin e f d he hf hd (by linarith)).1.trans
      (triangle_cosine_margin e f d he hf hd (by linarith)).2
  have hp : 0 < Real.cos a+Real.cos c*Real.cos e :=
    (triangle_cosine_margin c e a hc he ha (by linarith)).1.trans
      (triangle_cosine_margin c e a hc he ha (by linarith)).2
  have hsq (x : ℝ) (hx : 0 < x) (hxp : x < Real.pi) :
      0 < 1-Real.cos x^2 := by
    have hh := Real.sin_pos_of_pos_of_lt_pi hx hxp
    nlinarith [Real.sin_sq_add_cos_sq x,sq_pos_of_pos hh]
  have hC00 : C 0 0 < 0 := by
    rw [show C 0 0 = _ from h00]
    exact triangle_gram_negative d e f hd he hf h123
  have hC01 : 0 < C 0 1 := by
    rw [show C 0 1 = _ from h01]
    exact add_pos (mul_pos hq hs) (mul_pos hp (hsq f hf (by linarith)))
  have hC02 : 0 < C 0 2 := by
    rw [show C 0 2 = _ from h02]
    have hs' : 0 < Real.cos d+Real.cos f*Real.cos e := by simpa [mul_comm] using hs
    exact add_pos (mul_pos hp hs') (mul_pos hq (hsq e he (by linarith)))
  have hC12 : 0 < C 1 2 := by
    rw [show C 1 2 = _ from h12]
    have hp' : 0 < Real.cos a+Real.cos e*Real.cos c := by simpa [mul_comm] using hp
    have hq' : 0 < Real.cos b+Real.cos f*Real.cos c := by simpa [mul_comm] using hq
    exact add_pos (mul_pos hp' hq') (mul_pos hs (hsq c hc (by linarith)))
  have hneg : G.det*(Real.cos d+Real.cos e*Real.cos f) < 0 := by
    rw [← hjac]
    exact sub_neg.mpr ((mul_neg_of_neg_of_pos hC00 hC12).trans (mul_pos hC01 hC02))
  by_contra hnot
  have hnonneg : 0 ≤ G.det := le_of_not_gt hnot
  have hprod := mul_nonneg hnonneg hs.le
  linarith

end CFMPStrictAngleGram296Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  let name := ``CFMPStrictAngleGram296Transient.strict_angle_gram_det_neg
  unless (env.checked.get.find? name).isSome do
    Lean.throwError "CFMP296 strict-angle Gram determinant theorem absent"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP296 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP296 CHECKED {name} axioms={axioms}"
