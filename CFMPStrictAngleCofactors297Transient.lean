import CFMPStrictAngleGram296Transient
import D5.S3.Geometry.Hyperideal.ActualCornerTransport
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Real.Sqrt

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
open Real
open D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface (gram)
open D5.S3.Geometry.Hyperideal.ActualCornerTransport (endpoints)
open CFMPStrictAngleGram296Transient

namespace CFMPStrictAngleCofactors297Transient

/-- The positive residual factor makes the mixed cofactor exceed the
geometric mean of the absolute diagonal cofactors. -/
private theorem factor_gap (v A B S T P : ℝ)
    (hv : 0 < v) (hA : 0 < A) (hB : 0 < B)
    (hS : 0 < S) (hT : 0 < T) (hP : 0 < P)
    (hX : v*A-S^2 < 0) (hY : v*B-T^2 < 0) :
    0 < S*T+P*v ∧
      (v*A-S^2)*(v*B-T^2) < (S*T+P*v)^2 := by
  have hXm : -(v*A-S^2) < S^2 := by linarith [mul_pos hv hA]
  have hYm : -(v*B-T^2) < T^2 := by linarith [mul_pos hv hB]
  have hprod : (v*A-S^2)*(v*B-T^2) < S^2*T^2 := by
    calc
      _ = (-(v*A-S^2))*(-(v*B-T^2)) := by ring
      _ < S^2*(-(v*B-T^2)) := mul_lt_mul_of_pos_right hXm (neg_pos.mpr hY)
      _ < S^2*T^2 := mul_lt_mul_of_pos_left hYm (sq_pos_of_pos hS)
  have hST : 0 < S*T := mul_pos hS hT
  have hPv : 0 < P*v := mul_pos hP hv
  have hoff : 0 < S*T+P*v := add_pos hST hPv
  have hsq := (sq_lt_sq₀ hST.le hoff.le).mpr (show S*T < S*T+P*v by linarith)
  constructor
  · exact hoff
  · exact hprod.trans (by simpa only [mul_pow] using hsq)

/-- The six entries not already supplied by the determinant prerequisite. -/
private theorem remaining_cofactors (p q r s t u : ℝ) :
    let C := (gram p q r u t s).adjugate
    C 1 1 = 1-q^2-r^2-u^2-2*q*r*u ∧
    C 2 2 = 1-p^2-r^2-t^2-2*p*r*t ∧
    C 3 3 = 1-p^2-q^2-s^2-2*p*q*s ∧
    C 0 3 = (p+q*s)*(t+u*s)+(r+q*u)*(1-s^2) ∧
    C 1 3 = (p+s*q)*(r+u*q)+(t+s*u)*(1-q^2) ∧
    C 2 3 = (q+s*p)*(r+t*p)+(u+s*t)*(1-p^2) := by
  dsimp only
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;>
    norm_num [Matrix.adjugate_fin_succ_eq_det_submatrix,gram,
      Matrix.det_fin_three,Matrix.det_fin_two,Matrix.det_fin_one,
      Matrix.det_fin_zero,Matrix.submatrix_apply,Fin.sum_univ_succ,
      Matrix.of_apply,Matrix.cons_val_zero',Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_succ',
      Matrix.head_cons,Matrix.tail_cons,Matrix.cons_val_succ,
      Matrix.vecHead,Matrix.vecTail,Fin.succAbove,Fin.reduceEq,
      Fin.reduceFinMk,Fin.castSucc,Fin.castAdd,Fin.succ,Fin.val_zero,
      Fin.val_succ,Nat.succ_eq_add_one,Nat.reduceAdd,Fin.castLE,Fin.cast] <;> ring

/-- All diagonal cofactors are negative, every offdiagonal cofactor is
positive, and every original pair has a strict hyperbolic length ratio. -/
theorem strict_angle_cofactor_gaps (a b c d e f : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (h012 : a+b+d < Real.pi) (h013 : a+c+e < Real.pi)
    (h023 : b+c+f < Real.pi) (h123 : d+e+f < Real.pi) :
    let G := gram (Real.cos a) (Real.cos b) (Real.cos c)
      (Real.cos f) (Real.cos e) (Real.cos d)
    let C := G.adjugate
    (∀ i : Fin 4, C i i < 0) ∧
      ∀ i j : Fin 4, i ≠ j → 0 < C i j ∧ C i i*C j j < (C i j)^2 := by
  let p := Real.cos a; let q := Real.cos b; let r := Real.cos c
  let s := Real.cos d; let t := Real.cos e; let u := Real.cos f
  let G := gram p q r u t s
  let C := G.adjugate
  obtain ⟨h00,h01,h02,h12,hjac⟩ := gram_cofactor_identities p q r s t u
  obtain ⟨h11,h22,h33,h03,h13,h23⟩ := remaining_cofactors p q r s t u
  have hm (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
      (hxyz : x+y+z < Real.pi) : 0 < Real.cos x+Real.cos y*Real.cos z :=
    (triangle_cosine_margin y z x hy hz hx (by linarith)).1.trans
      (triangle_cosine_margin y z x hy hz hx (by linarith)).2
  have hunit (x : ℝ) (hx : 0 < x) (hxπ : x < Real.pi) : 0 < 1-Real.cos x^2 := by
    have hs := Real.sin_pos_of_pos_of_lt_pi hx hxπ
    nlinarith [Real.sin_sq_add_cos_sq x,sq_pos_of_pos hs]
  have hvp : 0 < 1-p^2 := hunit a ha (by linarith)
  have hvq : 0 < 1-q^2 := hunit b hb (by linarith)
  have hvr : 0 < 1-r^2 := hunit c hc (by linarith)
  have hvs : 0 < 1-s^2 := hunit d hd (by linarith)
  have hvt : 0 < 1-t^2 := hunit e he (by linarith)
  have hvu : 0 < 1-u^2 := hunit f hf (by linarith)
  have hmpqs : 0 < p+q*s := hm a b d ha hb hd (by linarith)
  have hmprt : 0 < p+r*t := hm a c e ha hc he (by linarith)
  have hmqru : 0 < q+r*u := hm b c f hb hc hf (by linarith)
  have hmrqu : 0 < r+q*u := hm c b f hc hb hf (by linarith)
  have hmtsu : 0 < t+s*u := hm e d f he hd hf (by linarith)
  have hmstu : 0 < s+t*u := hm d e f hd he hf (by linarith)
  have hmqps : 0 < q+p*s := hm b a d hb ha hd (by linarith)
  have hmrpt : 0 < r+p*t := hm c a e hc ha he (by linarith)
  have hmust : 0 < u+s*t := hm f d e hf hd he (by linarith)
  have hD0 : C 0 0 < 0 := by
    rw [show C 0 0 = _ from h00]
    exact triangle_gram_negative d e f hd he hf h123
  have hD1 : C 1 1 < 0 := by
    rw [show C 1 1 = _ from h11]
    exact triangle_gram_negative b c f hb hc hf h023
  have hD2 : C 2 2 < 0 := by
    rw [show C 2 2 = _ from h22]
    exact triangle_gram_negative a c e ha hc he h013
  have hD3 : C 3 3 < 0 := by
    rw [show C 3 3 = _ from h33]
    exact triangle_gram_negative a b d ha hb hd h012
  have hpair01 : 0 < C 0 1 ∧ C 0 0*C 1 1 < (C 0 1)^2 := by
    have hX : C 0 0 = (1-u^2)*(1-t^2)-(s+t*u)^2 := by
      rw [show C 0 0 = _ from h00]
      ring
    have hY : C 1 1 = (1-u^2)*(1-r^2)-(q+r*u)^2 := by
      rw [show C 1 1 = _ from h11]
      ring
    have hZ : C 0 1 = (s+t*u)*(q+r*u)+(p+r*t)*(1-u^2) := by
      rw [show C 0 1 = _ from h01]
      ring
    have hS : 0 < s+t*u := by simpa only [mul_comm] using hmstu
    have hT : 0 < q+r*u := by simpa only [mul_comm] using hmqru
    have hgap := factor_gap (1-u^2) (1-t^2) (1-r^2)
      (s+t*u) (q+r*u) (p+r*t) hvu hvt hvr hS hT hmprt
      (by rw [← hX];exact hD0) (by rw [← hY];exact hD1)
    rwa [← hX,← hY,← hZ] at hgap
  have hpair02 : 0 < C 0 2 ∧ C 0 0*C 2 2 < (C 0 2)^2 := by
    have hX : C 0 0 = (1-t^2)*(1-u^2)-(s+u*t)^2 := by
      rw [show C 0 0 = _ from h00]
      ring
    have hY : C 2 2 = (1-t^2)*(1-r^2)-(p+r*t)^2 := by
      rw [show C 2 2 = _ from h22]
      ring
    have hZ : C 0 2 = (s+u*t)*(p+r*t)+(q+r*u)*(1-t^2) := by
      rw [show C 0 2 = _ from h02]
      ring
    have hS : 0 < s+u*t := by simpa only [mul_comm] using hmstu
    have hT : 0 < p+r*t := by simpa only [mul_comm] using hmprt
    have hgap := factor_gap (1-t^2) (1-u^2) (1-r^2)
      (s+u*t) (p+r*t) (q+r*u) hvt hvu hvr hS hT hmqru
      (by rw [← hX];exact hD0) (by rw [← hY];exact hD2)
    rwa [← hX,← hY,← hZ] at hgap
  have hpair03 : 0 < C 0 3 ∧ C 0 0*C 3 3 < (C 0 3)^2 := by
    have hX : C 0 0 = (1-s^2)*(1-u^2)-(t+u*s)^2 := by
      rw [show C 0 0 = _ from h00]
      ring
    have hY : C 3 3 = (1-s^2)*(1-q^2)-(p+q*s)^2 := by
      rw [show C 3 3 = _ from h33]
      ring
    have hZ : C 0 3 = (t+u*s)*(p+q*s)+(r+q*u)*(1-s^2) := by
      rw [show C 0 3 = _ from h03]
      ring
    have hS : 0 < t+u*s := by simpa only [mul_comm] using hmtsu
    have hT : 0 < p+q*s := by simpa only [mul_comm] using hmpqs
    have hgap := factor_gap (1-s^2) (1-u^2) (1-q^2)
      (t+u*s) (p+q*s) (r+q*u) hvs hvu hvq hS hT hmrqu
      (by rw [← hX];exact hD0) (by rw [← hY];exact hD3)
    rwa [← hX,← hY,← hZ] at hgap
  have hpair12 : 0 < C 1 2 ∧ C 1 1*C 2 2 < (C 1 2)^2 := by
    have hX : C 1 1 = (1-r^2)*(1-u^2)-(q+u*r)^2 := by
      rw [show C 1 1 = _ from h11]
      ring
    have hY : C 2 2 = (1-r^2)*(1-t^2)-(p+t*r)^2 := by
      rw [show C 2 2 = _ from h22]
      ring
    have hZ : C 1 2 = (q+u*r)*(p+t*r)+(s+t*u)*(1-r^2) := by
      rw [show C 1 2 = _ from h12]
      ring
    have hS : 0 < q+u*r := by simpa only [mul_comm] using hmqru
    have hT : 0 < p+t*r := by simpa only [mul_comm] using hmprt
    have hgap := factor_gap (1-r^2) (1-u^2) (1-t^2)
      (q+u*r) (p+t*r) (s+t*u) hvr hvu hvt hS hT hmstu
      (by rw [← hX];exact hD1) (by rw [← hY];exact hD2)
    rwa [← hX,← hY,← hZ] at hgap
  have hpair13 : 0 < C 1 3 ∧ C 1 1*C 3 3 < (C 1 3)^2 := by
    have hX : C 1 1 = (1-q^2)*(1-u^2)-(r+u*q)^2 := by
      rw [show C 1 1 = _ from h11]
      ring
    have hY : C 3 3 = (1-q^2)*(1-s^2)-(p+s*q)^2 := by
      rw [show C 3 3 = _ from h33]
      ring
    have hZ : C 1 3 = (r+u*q)*(p+s*q)+(t+s*u)*(1-q^2) := by
      rw [show C 1 3 = _ from h13]
      ring
    have hS : 0 < r+u*q := by simpa only [mul_comm] using hmrqu
    have hT : 0 < p+s*q := by simpa only [mul_comm] using hmpqs
    have hgap := factor_gap (1-q^2) (1-u^2) (1-s^2)
      (r+u*q) (p+s*q) (t+s*u) hvq hvu hvs hS hT hmtsu
      (by rw [← hX];exact hD1) (by rw [← hY];exact hD3)
    rwa [← hX,← hY,← hZ] at hgap
  have hpair23 : 0 < C 2 3 ∧ C 2 2*C 3 3 < (C 2 3)^2 := by
    have hX : C 2 2 = (1-p^2)*(1-t^2)-(r+t*p)^2 := by
      rw [show C 2 2 = _ from h22]
      ring
    have hY : C 3 3 = (1-p^2)*(1-s^2)-(q+s*p)^2 := by
      rw [show C 3 3 = _ from h33]
      ring
    have hZ : C 2 3 = (r+t*p)*(q+s*p)+(u+s*t)*(1-p^2) := by
      rw [show C 2 3 = _ from h23]
      ring
    have hS : 0 < r+t*p := by simpa only [mul_comm] using hmrpt
    have hT : 0 < q+s*p := by simpa only [mul_comm] using hmqps
    have hgap := factor_gap (1-p^2) (1-t^2) (1-s^2)
      (r+t*p) (q+s*p) (u+s*t) hvp hvt hvs hS hT hmust
      (by rw [← hX];exact hD2) (by rw [← hY];exact hD3)
    rwa [← hX,← hY,← hZ] at hgap
  have hG : G.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  have hC : C.IsSymm := hG.adjugate
  have reverse_pair (i j : Fin 4)
      (h : 0 < C i j ∧ C i i*C j j < (C i j)^2) :
      0 < C j i ∧ C j j*C i i < (C j i)^2 := by
    rw [hC.apply i j, mul_comm (C j j) (C i i)]
    exact h
  constructor
  · intro i
    fin_cases i
    · exact hD0
    · exact hD1
    · exact hD2
    · exact hD3
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hpair01
    · exact hpair02
    · exact hpair03
    · exact reverse_pair 0 1 hpair01
    · exact (hij rfl).elim
    · exact hpair12
    · exact hpair13
    · exact reverse_pair 0 2 hpair02
    · exact reverse_pair 1 2 hpair12
    · exact (hij rfl).elim
    · exact hpair23
    · exact reverse_pair 0 3 hpair03
    · exact reverse_pair 1 3 hpair13
    · exact reverse_pair 2 3 hpair23
    · exact (hij rfl).elim

/-- The cofactor ratio is strictly above one; zero and imaginary lengths
are excluded before applying arcosh. -/
theorem cofactor_ratio_gt_one (G : Matrix (Fin 4) (Fin 4) ℝ)
    (hd : ∀ i, G.adjugate i i < 0)
    (hg : ∀ i j, i ≠ j → 0 < G.adjugate i j ∧
      G.adjugate i i*G.adjugate j j < (G.adjugate i j)^2)
    (i j : Fin 4) (hij : i ≠ j) :
    1 < G.adjugate i j / Real.sqrt (G.adjugate i i*G.adjugate j j) := by
  obtain ⟨hp,hgap⟩ := hg i j hij
  have hprod : 0 < G.adjugate i i*G.adjugate j j := mul_pos_of_neg_of_neg (hd i) (hd j)
  have hr : 0 < Real.sqrt (G.adjugate i i*G.adjugate j j) := Real.sqrt_pos.mpr hprod
  have hrsq := Real.sq_sqrt hprod.le
  have hroot : Real.sqrt (G.adjugate i i*G.adjugate j j) < G.adjugate i j := by
    nlinarith
  exact (lt_div_iff₀ hr).mpr (by simpa only [one_mul] using hroot)

def cofactorLength (G : Matrix (Fin 4) (Fin 4) ℝ) (q : Fin 6) : ℝ :=
  Real.arcosh (G.adjugate (endpoints q).1 (endpoints q).2 /
    Real.sqrt (G.adjugate (endpoints q).1 (endpoints q).1*
      G.adjugate (endpoints q).2 (endpoints q).2))

/-- The six original edge positions each obtain a positive length and the
exact prescribed cosh ratio; no arbitrary replacement edge set is used. -/
theorem cofactor_lengths_positive (G : Matrix (Fin 4) (Fin 4) ℝ)
    (hd : ∀ i, G.adjugate i i < 0)
    (hg : ∀ i j, i ≠ j → 0 < G.adjugate i j ∧
      G.adjugate i i*G.adjugate j j < (G.adjugate i j)^2) :
    ∀ q : Fin 6, 0 < cofactorLength G q ∧
      Real.cosh (cofactorLength G q) =
        G.adjugate (endpoints q).1 (endpoints q).2 /
          Real.sqrt (G.adjugate (endpoints q).1 (endpoints q).1*
            G.adjugate (endpoints q).2 (endpoints q).2) := by
  intro q
  have hij : (endpoints q).1 ≠ (endpoints q).2 := by fin_cases q <;> decide
  have hratio := cofactor_ratio_gt_one G hd hg _ _ hij
  exact ⟨Real.arcosh_pos hratio,Real.cosh_arcosh hratio.le⟩

end CFMPStrictAngleCofactors297Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPStrictAngleCofactors297Transient.strict_angle_cofactor_gaps,
      ``CFMPStrictAngleCofactors297Transient.cofactor_lengths_positive] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP297 strict-angle cofactor theorem absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP297 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP297 CHECKED {name} axioms={axioms}"
