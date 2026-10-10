/- GID: D5/S3/Quantum/Recovery/SharedPhaseBudgetGap
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/SharedPhaseBudgetGap
   mirror-E: none(waiver:shared-phase-budget-gap)
   anchors: []
   utility: none
   digest: A common-phase compactness argument gives a strict finite shared-budget gap for the four-phase recovery matrix. -/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Complex.Order
import Mathlib.Tactic

noncomputable section
open Complex Matrix Finset
open scoped ComplexConjugate
set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
namespace D5.S3.Quantum.Recovery.SharedPhaseBudgetGap

def s : ℝ := Real.sqrt 2
def nu : ℝ := 3 - 2 * s
private lemma s_pos : 0 < s := Real.sqrt_pos.2 (by norm_num)
private lemma s_sq : s ^ 2 = 2 := Real.sq_sqrt (by norm_num)
private lemma s_gt_one : 1 < s := by nlinarith [s_sq, s_pos]
private lemma nu_pos : 0 < nu := by
  have h : (s-1)^2 > 0 := sq_pos_of_pos (by linarith [s_gt_one])
  dsimp [nu]; nlinarith [s_sq]
private lemma nu_mul : nu * (s+1)^2 = 1 := by dsimp [nu]; nlinarith [s_sq]

def torus : Set (Fin 4 → ℂ) := {z | ∀ i, ‖z i‖ = 1}
def A (z : Fin 4 → ℂ) : ℂ := (z 0 + z 1) / (s : ℂ)
def D (z : Fin 4 → ℂ) : ℂ := (z 0 + I * z 1) / (s : ℂ)
def y (z : Fin 4 → ℂ) : Fin 2 → ℂ := ![z 2 - A z, z 3 - D z]
def energy (z : Fin 4 → ℂ) : ℝ := ‖y z 0‖^2 + ‖y z 1‖^2
def cross (z : Fin 4 → ℂ) : ℝ := (y z 0 * conj (y z 1)).re

def B : Matrix (Fin 2) (Fin 4) ℂ :=
  !![-(s : ℂ)⁻¹, -(s : ℂ)⁻¹, 1, 0; -(s : ℂ)⁻¹, -I * (s : ℂ)⁻¹, 0, 1]
def M : Matrix (Fin 2) (Fin 2) ℂ := B * Bᴴ

private lemma B_apply (z : Fin 4 → ℂ) : B.mulVec z = y z := by
  ext i; fin_cases i <;> simp [B, y, A, D, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, div_eq_mul_inv] <;> ring

private lemma M_value : M = !![(2:ℂ), (1-I)/2; (1+I)/2, 2] := by
  have hsc : (s : ℂ)^2 = 2 := by exact_mod_cast s_sq
  have hsn : (s : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt s_pos
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [M,B,Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_succ, map_neg, map_inv₀, Complex.conj_ofReal] <;>
    field_simp <;> ring_nf <;> simp_all <;> ring

private lemma scalar_bound (u v e f : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hus : u ≤ s) (hvs : v ≤ s)
    (hc : (u^2-1)^2 + (v^2-1)^2 = 1)
    (he : (u-1)^2 ≤ e) (hf : (v-1)^2 ≤ f) : nu ≤ e+f := by
  have h0 : 0 ≤ (s+1)^2 := sq_nonneg _
  have h1 : (u+1)^2 ≤ (s+1)^2 := by nlinarith
  have h2 : (v+1)^2 ≤ (s+1)^2 := by nlinarith
  have h3 := mul_le_mul_of_nonneg_right h1 (sq_nonneg (u-1))
  have h4 := mul_le_mul_of_nonneg_right h2 (sq_nonneg (v-1))
  have h5 := mul_le_mul_of_nonneg_left he h0
  have h6 := mul_le_mul_of_nonneg_left hf h0
  have h7 : 1 ≤ (s+1)^2*(e+f) := by nlinarith [hc]
  have h8 : 0 < (s+1)^2 := sq_pos_of_pos (by linarith [s_pos])
  nlinarith [nu_mul]

private lemma scalar_equality (u v e f : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hus : u ≤ s) (hvs : v ≤ s)
    (hc : (u^2-1)^2 + (v^2-1)^2 = 1)
    (he : (u-1)^2 ≤ e) (hf : (v-1)^2 ≤ f) (h : e+f=nu) :
    (u=s ∧ v=1 ∧ f=0) ∨ (u=1 ∧ v=s ∧ e=0) := by
  have h0 : 0 < (s+1)^2 := sq_pos_of_pos (by linarith [s_pos])
  have h1 : 0 ≤ ((s+1)^2-(u+1)^2)*(u-1)^2 := mul_nonneg (by nlinarith) (sq_nonneg _)
  have h2 : 0 ≤ ((s+1)^2-(v+1)^2)*(v-1)^2 := mul_nonneg (by nlinarith) (sq_nonneg _)
  have h3 : 0 ≤ (s+1)^2*(e-(u-1)^2) := mul_nonneg h0.le (by linarith)
  have h4 : 0 ≤ (s+1)^2*(f-(v-1)^2) := mul_nonneg h0.le (by linarith)
  have hid : ((s+1)^2-(u+1)^2)*(u-1)^2 +
      ((s+1)^2-(v+1)^2)*(v-1)^2 +
      (s+1)^2*(e-(u-1)^2) + (s+1)^2*(f-(v-1)^2) = 0 := by
    calc
      _ = (s+1)^2*(e+f) - ((u^2-1)^2+(v^2-1)^2) := by ring
      _ = 0 := by rw [h,hc]; nlinarith only [nu_mul]
  have hu0 : ((s+1)^2-(u+1)^2)*(u-1)^2=0 := by linarith only [hid,h1,h2,h3,h4]
  have hv0 : ((s+1)^2-(v+1)^2)*(v-1)^2=0 := by linarith only [hid,h1,h2,h3,h4]
  have he0 : e=(u-1)^2 := by
    have hh : (s+1)^2*(e-(u-1)^2)=0 := by linarith only [hid,h1,h2,h3,h4]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (ne_of_gt h0))
  have hf0 : f=(v-1)^2 := by
    have hh : (s+1)^2*(f-(v-1)^2)=0 := by linarith only [hid,h1,h2,h3,h4]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (ne_of_gt h0))
  have uopts : u=s ∨ u=1 := by
    rcases mul_eq_zero.mp hu0 with ha | ha
    · left; nlinarith only [ha,hu,s_pos]
    · right; exact sub_eq_zero.mp (sq_eq_zero_iff.mp ha)
  have vopts : v=s ∨ v=1 := by
    rcases mul_eq_zero.mp hv0 with ha | ha
    · left; nlinarith only [ha,hv,s_pos]
    · right; exact sub_eq_zero.mp (sq_eq_zero_iff.mp ha)
  rcases uopts with rfl | rfl <;> rcases vopts with rfl | rfl
  · exfalso; nlinarith [s_sq]
  · left; exact ⟨rfl,rfl,by nlinarith⟩
  · right; exact ⟨rfl,rfl,by nlinarith⟩
  · norm_num at hc

open Complex Matrix Finset
open scoped ComplexConjugate
set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

private lemma reverse_square (a z : ℂ) (hz : ‖z‖=1) : (‖a‖-1)^2 ≤ ‖z-a‖^2 := by
  have hh := abs_norm_sub_norm_le a z
  rw [hz, norm_sub_rev] at hh
  have hh' := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 hh
  simpa using hh'

private lemma A_sq (z : Fin 4 → ℂ) (hz : z ∈ torus) : ‖A z‖^2=1+(z 0*conj (z 1)).re := by
  have hn (i : Fin 4) : normSq (z i)=1 := by rw [normSq_eq_norm_sq,hz i]; norm_num
  have hs : s*s=2 := by nlinarith only [s_sq]
  rw [← normSq_eq_norm_sq]
  simp only [A,normSq_div,normSq_add,hn,normSq_ofReal,hs]
  ring
private lemma D_sq (z : Fin 4 → ℂ) (hz : z ∈ torus) : ‖D z‖^2=1+(z 0*conj (z 1)).im := by
  have hn (i : Fin 4) : normSq (z i)=1 := by rw [normSq_eq_norm_sq,hz i]; norm_num
  have hs : s*s=2 := by nlinarith only [s_sq]
  rw [← normSq_eq_norm_sq]
  simp only [D,normSq_div,normSq_add,hn,normSq_ofReal,hs,normSq_mul,normSq_I]
  simp [Complex.mul_re,Complex.mul_im]; ring

private lemma phase_data (z : Fin 4 → ℂ) (hz : z ∈ torus) :
    0 ≤ ‖A z‖ ∧ 0 ≤ ‖D z‖ ∧ ‖A z‖ ≤ s ∧ ‖D z‖ ≤ s ∧
    ((‖A z‖^2-1)^2+(‖D z‖^2-1)^2=1) ∧
    (‖A z‖-1)^2 ≤ ‖y z 0‖^2 ∧ (‖D z‖-1)^2 ≤ ‖y z 1‖^2 := by
  have hn (i : Fin 4) : normSq (z i)=1 := by rw [normSq_eq_norm_sq, hz i]; norm_num
  have hs : s*s=2 := by nlinarith only [s_sq]
  have ha := A_sq z hz
  have hd := D_sq z hz
  have hw : normSq (z 0*conj (z 1))=1 := by simp [normSq_mul, normSq_conj, hn]
  have hwr : (z 0*conj (z 1)).re^2+(z 0*conj (z 1)).im^2=1 := by
    simpa only [normSq_apply,pow_two] using hw
  have hcircle : (‖A z‖^2-1)^2+(‖D z‖^2-1)^2=1 := by rw [ha,hd]; nlinarith only [hwr]
  have hr : (z 0*conj (z 1)).re ≤ 1 := by nlinarith only [hwr,sq_nonneg (z 0*conj (z 1)).im]
  have hi : (z 0*conj (z 1)).im ≤ 1 := by nlinarith only [hwr,sq_nonneg (z 0*conj (z 1)).re]
  refine ⟨norm_nonneg _,norm_nonneg _,?_,?_,hcircle,?_,?_⟩
  · nlinarith only [ha,hr,s_sq,s_pos,norm_nonneg (A z)]
  · nlinarith only [hd,hi,s_sq,s_pos,norm_nonneg (D z)]
  · exact reverse_square (A z) (z 2) (hz 2)
  · exact reverse_square (D z) (z 3) (hz 3)

private lemma energy_lower (z : Fin 4 → ℂ) (hz : z ∈ torus) : nu ≤ energy z := by
  rcases phase_data z hz with ⟨hu,hv,hus,hvs,hc,he,hf⟩
  exact scalar_bound _ _ _ _ hu hv hus hvs hc he hf

private lemma torus_compact : IsCompact torus := by
  have hh := isCompact_univ_pi (fun _ : Fin 4 => isCompact_sphere (0:ℂ) 1)
  convert hh using 1
  ext z
  simp [torus,Set.mem_pi,Metric.mem_sphere]

private lemma energy_continuous : Continuous energy := by
  unfold energy y A D
  fun_prop
private lemma cross_continuous : Continuous cross := by
  unfold cross y A D
  fun_prop

open Complex Matrix Finset
open scoped ComplexConjugate
set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

private lemma unit_scaled (a b : ℂ) (ha : ‖a‖=1) (hb : ‖b‖=1)
    (h : normSq (b-(s:ℂ)*a)=nu) : b=a := by
  have ha' : normSq a=1 := by rw [normSq_eq_norm_sq,ha]; norm_num
  have hb' : normSq b=1 := by rw [normSq_eq_norm_sq,hb]; norm_num
  have hs : s*s=2 := by nlinarith only [s_sq]
  have hcross : (b*conj ((s:ℂ)*a)).re=s*(b*conj a).re := by
    simp [Complex.mul_re,Complex.mul_im]; ring
  rw [normSq_sub,normSq_mul,normSq_ofReal,hs,ha',hb',hcross] at h
  have hr : (b*conj a).re=1 := by
    dsimp [nu] at h
    nlinarith only [h,s_pos]
  apply sub_eq_zero.mp
  apply normSq_eq_zero.mp
  rw [normSq_sub,hb',ha',hr]
  norm_num

def q0 (c : ℂ) : Fin 4 → ℂ := ![c,c,c,(c+I*c)/(s:ℂ)]
def q1 (c : ℂ) : Fin 4 → ℂ := ![c,-I*c,(c-I*c)/(s:ℂ),c]

private lemma equality_forward (z : Fin 4 → ℂ) (hz : z ∈ torus) (h : energy z=nu) :
    z=q0 (z 0) ∨ z=q1 (z 0) := by
  rcases phase_data z hz with ⟨hu,hv,hus,hvs,hc,he,hf⟩
  have hn (i : Fin 4) : normSq (z i)=1 := by rw [normSq_eq_norm_sq,hz i]; norm_num
  have hsc : (s:ℂ)^2=2 := by exact_mod_cast s_sq
  have hsn : (s:ℂ)≠0 := by exact_mod_cast ne_of_gt s_pos
  rcases scalar_equality _ _ _ _ hu hv hus hvs hc he hf h with hh | hh
  · have hr : (z 0*conj (z 1)).re=1 := by
      have ha := A_sq z hz
      rw [hh.1] at ha
      nlinarith only [ha,s_sq]
    have h01 : z 0=z 1 := by
      apply sub_eq_zero.mp; apply normSq_eq_zero.mp
      rw [normSq_sub,hn,hn,hr]; norm_num
    have hd0 : y z 1=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hh.2.2)
    have h3 : z 3=D z := sub_eq_zero.mp hd0
    have hA : A z=(s:ℂ)*z 0 := by
      unfold A; rw [←h01]
      field_simp; linear_combination -z 0*hsc
    have heq : normSq (z 2-(s:ℂ)*z 0)=nu := by
      have h' := h
      simp only [energy,hd0,norm_zero,zero_pow,add_zero] at h'
      simpa [y,hA,normSq_eq_norm_sq] using h'
    have h2 := unit_scaled (z 0) (z 2) (hz 0) (hz 2) heq
    left
    ext i; fin_cases i <;> simp [q0,h01.symm,h2,h3,D]
  · have hi : (z 0*conj (z 1)).im=1 := by
      have hd := D_sq z hz
      rw [hh.2.1] at hd
      nlinarith only [hd,s_sq]
    have h10 : z 1=-I*z 0 := by
      have heq : normSq (z 1+I*z 0)=0 := by
        rw [normSq_add,normSq_mul,normSq_I,hn,hn]
        simp [Complex.mul_re,Complex.mul_im] at hi ⊢
        nlinarith only [hi]
      have heq' := normSq_eq_zero.mp heq
      linear_combination heq'
    have ha0 : y z 0=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hh.2.2)
    have h2 : z 2=A z := sub_eq_zero.mp ha0
    have hD : D z=(s:ℂ)*z 0 := by
      unfold D; rw [h10]
      field_simp; ring_nf; rw [hsc,Complex.I_sq]; ring
    have heq : normSq (z 3-(s:ℂ)*z 0)=nu := by
      have h' := h
      simp only [energy,ha0,norm_zero,zero_pow,zero_add] at h'
      simpa [y,hD,normSq_eq_norm_sq] using h'
    have h3 := unit_scaled (z 0) (z 3) (hz 0) (hz 3) heq
    right
    ext i; fin_cases i <;> simp [q1,h10,h2,h3,A,neg_mul,sub_eq_add_neg]

private lemma q_images (c : ℂ) :
    y (q0 c)=![(1-(s:ℂ))*c,0] ∧ y (q1 c)=![0,(1-(s:ℂ))*c] := by
  have hsc : (s:ℂ)^2=2 := by exact_mod_cast s_sq
  have hsn : (s:ℂ)≠0 := by exact_mod_cast ne_of_gt s_pos
  constructor <;> ext i <;> fin_cases i <;>
    simp [y,q0,q1,A,D] <;> field_simp <;> ring_nf <;>
    (try simp [Complex.I_mul_I]) <;> linear_combination c*hsc

private lemma equality_classification (z : Fin 4 → ℂ) (hz : z ∈ torus) :
    energy z=nu ↔ z=q0 (z 0) ∨ z=q1 (z 0) := by
  refine ⟨equality_forward z hz,?_⟩
  intro h
  have hq (c : ℂ) (hc : ‖c‖=1) : energy (q0 c)=nu ∧ energy (q1 c)=nu := by
    rcases q_images c with ⟨h0,h1⟩
    simp only [energy,h0,h1,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,norm_zero,zero_pow,add_zero,zero_add]
    have hn : ‖(1-(s:ℂ))*c‖^2=nu := by
      rw [←normSq_eq_norm_sq,normSq_mul]
      have hcast : (1:ℂ)-(s:ℂ)=((1-s:ℝ):ℂ) := by push_cast; rfl
      rw [hcast]
      rw [normSq_ofReal,normSq_eq_norm_sq c,hc]
      dsimp [nu]; nlinarith only [s_sq]
    constructor <;> simpa using hn
  rcases h with h | h
  · rw [h]; exact (hq (z 0) (hz 0)).1
  · rw [h]; exact (hq (z 0) (hz 0)).2

open Complex Matrix Finset
open scoped ComplexConjugate ComplexOrder
set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

private lemma equality_cross_zero (z : Fin 4 → ℂ) (hz : z ∈ torus) (heq : energy z=nu) : cross z=0 := by
  rcases (equality_classification z hz).mp heq with h | h
  · have hy := (q_images (z 0)).1
    unfold cross
    rw [h, hy]
    simp
  · have hy := (q_images (z 0)).2
    unfold cross
    rw [h, hy]
    simp

private lemma compact_tilt : ∃ a : ℝ, 0<a ∧ a≤1 ∧
    ∀ z ∈ torus, nu-a*(nu/16) ≤ energy z-a*cross z := by
  let c : ℝ := nu/16
  have hc : 0<c := div_pos nu_pos (by norm_num)
  have ht : IsCompact (torus ∩ {z | c ≤ cross z}) :=
    torus_compact.inter_right (isClosed_le continuous_const cross_continuous)
  have hstrict : ∀ z ∈ torus ∩ {z | c ≤ cross z}, 0 < energy z-nu := by
    intro z hz
    have he := energy_lower z hz.1
    have hn : energy z≠nu := by
      intro heq
      have hg := equality_cross_zero z hz.1 heq
      have := hz.2
      dsimp at this; rw [hg] at this
      linarith
    exact sub_pos.mpr (lt_of_le_of_ne he (Ne.symm hn))
  obtain ⟨d,hd,hdb⟩ := ht.exists_forall_le' (energy_continuous.sub continuous_const).continuousOn hstrict
  obtain ⟨b,hb⟩ := (torus_compact.image cross_continuous).bddAbove
  let L : ℝ := |b|+|c|+1
  have hL : 0<L := by dsimp [L]; positivity
  have hg : ∀ z ∈ torus, cross z-c ≤ L := by
    intro z hz
    have hh := hb (Set.mem_image_of_mem cross hz)
    dsimp [L]
    linarith [le_abs_self b, neg_le_abs c]
  let a : ℝ := min 1 (d/L)
  have ha : 0<a := lt_min (by norm_num) (div_pos hd hL)
  have ha1 : a≤1 := min_le_left _ _
  have had : a*L≤d := (le_div_iff₀ hL).mp (min_le_right _ _)
  refine ⟨a,ha,ha1,?_⟩
  intro z hz
  by_cases hzc : c≤cross z
  · have he := hdb z ⟨hz,hzc⟩
    change d ≤ energy z-nu at he
    have hmul := mul_le_mul_of_nonneg_left (hg z hz) ha.le
    change nu-a*c ≤ energy z-a*cross z
    nlinarith only [he,hmul,had]
  · have he := energy_lower z hz
    have hmul := mul_nonneg ha.le (sub_nonneg.mpr (le_of_not_ge hzc))
    change nu-a*c ≤ energy z-a*cross z
    nlinarith only [he,hmul]

def linearBudget (a : ℝ) (P : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  (P 0 0).re+(P 1 1).re-a*(P 0 1).re

private lemma linearBudget_nonneg (a : ℝ) (ha : 0≤a) (ha1 : a≤1)
    (P : Matrix (Fin 2) (Fin 2) ℂ) (hP : P.PosSemidef) : 0≤linearBudget a P := by
  have h0 := (Complex.nonneg_iff.mp (hP.diag_nonneg (i:=0))).1
  have h1 := (Complex.nonneg_iff.mp (hP.diag_nonneg (i:=1))).1
  have hv := (Complex.nonneg_iff.mp (hP.dotProduct_mulVec_nonneg ![1,-1])).1
  have hsym : (P 1 0).re=(P 0 1).re := by
    have hh := congrArg Complex.re (hP.isHermitian.apply 0 1)
    simpa only [Complex.star_def,Complex.conj_re] using hh
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, star, Complex.mul_re, Complex.mul_im] at hv
  rw [hsym] at hv
  have h2 := mul_nonneg (show 0≤1-a/2 by linarith) (add_nonneg h0 h1)
  have h3 := mul_nonneg (show 0≤a/2 by positivity) hv
  unfold linearBudget
  nlinarith only [h2,h3]

def gram {m : ℕ} (p : Fin m → ℝ) (z : Fin m → Fin 4 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i k => ∑ j, (p j : ℂ)*y (z j) i*conj (y (z j) k)

private lemma budget_sum {m : ℕ} (p : Fin m → ℝ) (z : Fin m → Fin 4 → ℂ)
    (a : ℝ) (ha : 0≤a) (ha1 : a≤1) (hP : (M-gram p z).PosSemidef) :
    (∑ j, p j*(energy (z j)-a*cross (z j))) ≤ 4-a/2 := by
  have hh := linearBudget_nonneg a ha ha1 (M-gram p z) hP
  rw [M_value] at hh
  simp only [linearBudget, Matrix.sub_apply, gram, Complex.sub_re, Complex.re_sum,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
    Complex.conj_im, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const, Complex.div_re, Complex.div_im,
    Complex.normSq_ofNat, Complex.one_re, Complex.one_im, Complex.I_re,Complex.I_im] at hh
  norm_num at hh
  simp only [mul_assoc,←mul_add,←pow_two] at hh
  have heq : (∑ j, p j*(energy (z j)-a*cross (z j))) =
      (∑ j, p j*((y (z j) 0).re^2+(y (z j) 0).im^2)) +
      (∑ j, p j*((y (z j) 1).re^2+(y (z j) 1).im^2)) -
      a*(∑ j, p j*((y (z j) 0).re*(y (z j) 1).re+(y (z j) 0).im*(y (z j) 1).im)) := by
    have hterm (j : Fin m) : p j*(energy (z j)-a*cross (z j)) =
        p j*((y (z j) 0).re^2+(y (z j) 0).im^2) +
        p j*((y (z j) 1).re^2+(y (z j) 1).im^2) -
        a*(p j*((y (z j) 0).re*(y (z j) 1).re+(y (z j) 0).im*(y (z j) 1).im)) := by
      simp only [energy,cross,←normSq_eq_norm_sq,normSq_apply,Complex.mul_re,Complex.conj_re,Complex.conj_im]
      ring
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum]
  rw [heq]
  nlinarith only [hh]

/-- The branch count is arbitrary, including the empty family. -/
private theorem first_hop : ∃ gamma : ℝ, 0<gamma ∧
    ∀ (m : ℕ) (p : Fin m → ℝ) (z : Fin m → Fin 4 → ℂ),
      (∀ j, 0≤p j) → (∀ j, z j ∈ torus) →
      (M-gram p z).PosSemidef → (∑ j, p j) ≤ 4/nu-gamma := by
  obtain ⟨a,ha,ha1,hab⟩ := compact_tilt
  let q : ℝ := nu-a*(nu/16)
  have hq : 0<q := by dsimp [q]; nlinarith only [nu_pos,ha1,mul_nonneg (sub_nonneg.mpr ha1) nu_pos.le]
  let k : ℝ := (4-a/2)/q
  have hk : k<4/nu := by
    apply (div_lt_div_iff₀ hq nu_pos).2
    dsimp [q]
    have hp := mul_pos ha nu_pos
    nlinarith only [hp]
  refine ⟨4/nu-k,sub_pos.mpr hk,?_⟩
  intro m p z hp hz hP
  have hsum : q*(∑ j, p j) ≤ ∑ j, p j*(energy (z j)-a*cross (z j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have hh := mul_le_mul_of_nonneg_left (hab (z j) (hz j)) (hp j)
    dsimp [q]; nlinarith only [hh]
  have hub := budget_sum p z a ha.le ha1 hP
  have hfinal : (∑ j, p j) ≤ k := (le_div_iff₀ hq).2 (by nlinarith only [hsum,hub])
  linarith

open Complex Matrix Finset
open scoped ComplexConjugate ComplexOrder
set_option linter.style.whitespace false
set_option linter.style.longLine false

private lemma gram_original {m : ℕ} (p : Fin m → ℝ) (z : Fin m → Fin 4 → ℂ) :
    gram p z=∑ j, p j • Matrix.vecMulVec (B.mulVec (z j)) (star (B.mulVec (z j))) := by
  ext i k
  simp only [gram,Matrix.sum_apply,Matrix.smul_apply,Matrix.vecMulVec,B_apply,
    Pi.star_apply,Complex.star_def,Complex.real_smul,Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro j _; ring

theorem first_hop_original : ∃ gamma : ℝ, 0<gamma ∧
    ∀ (m : ℕ) (_ : 1≤m) (p : Fin m → ℝ) (z : Fin m → Fin 4 → ℂ),
      (∀ j, 0≤p j) → (∀ j k, ‖z j k‖=1) →
      (M-∑ j, p j • Matrix.vecMulVec (B.mulVec (z j)) (star (B.mulVec (z j)))).PosSemidef →
      (∑ j, p j) ≤ 4/(3-2*Real.sqrt 2)-gamma := by
  obtain ⟨g,hg,h⟩ := first_hop
  refine ⟨g,hg,?_⟩
  intro m _ p z hp hz hP
  rw [←gram_original p z] at hP
  exact h m p z hp hz hP

/-- The ket-row coordinates of the four original records. -/
def R0 : Matrix (Fin 4) (Fin 2) ℂ :=
  !![1, 0; 0, 1; (s : ℂ)⁻¹, (s : ℂ)⁻¹; (s : ℂ)⁻¹, I * (s : ℂ)⁻¹]

def C0 : Matrix (Fin 4) (Fin 4) ℂ := R0 * R0ᴴ

def noisyCorrelation (epsilon : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (1-epsilon) • C0 + epsilon • (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-- Zero weights include the empty decomposition while keeping a positive branch count. -/
def phaseMasses (C : Matrix (Fin 4) (Fin 4) ℂ) : Set ℝ :=
  {t | ∃ (m : ℕ), 1 ≤ m ∧ ∃ (p : Fin m → ℝ) (z : Fin m → Fin 4 → ℂ),
    (∀ j, 0 ≤ p j) ∧ (∀ j k, ‖z j k‖ = 1) ∧
    (C - ∑ j, p j • Matrix.vecMulVec (z j) (star (z j))).PosSemidef ∧
    t = ∑ j, p j}

def eta (C : Matrix (Fin 4) (Fin 4) ℂ) : ℝ := sSup (phaseMasses C)

private lemma B_R0 : B * R0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B, R0, Matrix.mul_apply, Fin.sum_univ_succ]

private lemma compressed_noisy (epsilon : ℝ) :
    B * noisyCorrelation epsilon * Bᴴ = epsilon • M := by
  simp only [noisyCorrelation, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, C0, ← Matrix.mul_assoc, B_R0,
    Matrix.zero_mul, smul_zero, zero_add, M]

private lemma compressed_family {m : ℕ} (p : Fin m → ℝ) (z : Fin m → Fin 4 → ℂ) :
    B * (∑ j, p j • Matrix.vecMulVec (z j) (star (z j))) * Bᴴ = gram p z := by
  rw [gram_original]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec]

private lemma compressed_feasible {m : ℕ} (epsilon : ℝ) (p : Fin m → ℝ)
    (z : Fin m → Fin 4 → ℂ)
    (hP : (noisyCorrelation epsilon -
      ∑ j, p j • Matrix.vecMulVec (z j) (star (z j))).PosSemidef) :
    (epsilon • M - gram p z).PosSemidef := by
  have h := hP.mul_mul_conjTranspose_same B
  simpa only [Matrix.mul_sub, Matrix.sub_mul, compressed_noisy, compressed_family] using h

private lemma gram_scale {m : ℕ} (p : Fin m → ℝ) (z : Fin m → Fin 4 → ℂ) (r : ℝ) :
    gram (fun j => r * p j) z = r • gram p z := by
  simp only [gram_original, mul_smul, Finset.smul_sum]

private lemma zero_budget_mass {m : ℕ} (p : Fin m → ℝ) (z : Fin m → Fin 4 → ℂ)
    (hp : ∀ j, 0 ≤ p j) (hz : ∀ j, z j ∈ torus)
    (hP : (-gram p z).PosSemidef) : (∑ j, p j) ≤ 0 := by
  have hd (i : Fin 2) := (Complex.nonneg_iff.mp (hP.diag_nonneg (i := i))).1
  have hdiag (i : Fin 2) : (gram p z i i).re = ∑ j, p j * ‖y (z j) i‖^2 := by
    simp only [gram, Complex.re_sum, ← normSq_eq_norm_sq, normSq_apply,
      Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have htrace : (∑ j, p j * energy (z j)) ≤ 0 := by
    have h0 := hd 0
    have h1 := hd 1
    simp only [Matrix.neg_apply, Complex.neg_re, hdiag] at h0 h1
    simp only [energy, mul_add, Finset.sum_add_distrib]
    linarith only [h0, h1]
  have hlower : nu * (∑ j, p j) ≤ ∑ j, p j * energy (z j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (energy_lower (z j) (hz j)) (hp j)
  nlinarith only [nu_pos, hlower, htrace]

private lemma scaled_mass_bound (gamma : ℝ)
    (hgap : ∀ (m : ℕ) (_ : 1 ≤ m) (p : Fin m → ℝ) (z : Fin m → Fin 4 → ℂ),
      (∀ j, 0 ≤ p j) → (∀ j k, ‖z j k‖ = 1) →
      (M - ∑ j, p j • Matrix.vecMulVec (B.mulVec (z j))
        (star (B.mulVec (z j)))).PosSemidef → (∑ j, p j) ≤ 4/nu-gamma)
    (epsilon : ℝ) (he : 0 ≤ epsilon) (t : ℝ) (ht : t ∈ phaseMasses (noisyCorrelation epsilon)) :
    t ≤ (4/nu-gamma)*epsilon := by
  rcases ht with ⟨m,hm,p,z,hp,hz,hP,rfl⟩
  have hc := compressed_feasible epsilon p z hP
  rcases he.eq_or_lt with he | he
  · subst epsilon
    simp only [zero_smul, zero_sub] at hc
    simpa using zero_budget_mass p z hp hz hc
  · have hn : (M - gram (fun j => epsilon⁻¹*p j) z).PosSemidef := by
      have hh := hc.smul (inv_nonneg.mpr he.le)
      simpa only [smul_sub, smul_smul, inv_mul_cancel₀ he.ne', one_smul,
        ← gram_scale] using hh
    rw [gram_original] at hn
    have hb := hgap m hm (fun j => epsilon⁻¹*p j) z
      (fun j => mul_nonneg (inv_nonneg.mpr he.le) (hp j)) hz hn
    rw [← Finset.mul_sum] at hb
    calc
      (∑ j, p j) = (epsilon⁻¹ * ∑ j, p j) * epsilon := by field_simp
      _ ≤ (4/nu-gamma)*epsilon := mul_le_mul_of_nonneg_right hb he.le

/-- A common strict improvement of the phase-cone coefficient, including the zero-noise endpoint.
The supremum is over all positive finite branch counts and nonnegative weights. -/
theorem eta_strict_improvement : ∃ gamma : ℝ, 0 < gamma ∧
    ∀ epsilon : ℝ, 0 ≤ epsilon → epsilon ≤ 1 →
      0 ∈ phaseMasses (noisyCorrelation epsilon) ∧
      BddAbove (phaseMasses (noisyCorrelation epsilon)) ∧
      IsLUB (phaseMasses (noisyCorrelation epsilon)) (eta (noisyCorrelation epsilon)) ∧
      0 ≤ eta (noisyCorrelation epsilon) ∧
      eta (noisyCorrelation epsilon) ≤ (4/(3-2*Real.sqrt 2)-gamma)*epsilon := by
  obtain ⟨gamma,hgamma,hgap⟩ := first_hop_original
  refine ⟨gamma,hgamma,?_⟩
  intro epsilon he he1
  have hC : (noisyCorrelation epsilon).PosSemidef :=
    ((Matrix.posSemidef_self_mul_conjTranspose R0).smul (sub_nonneg.mpr he1)).add
      (Matrix.PosSemidef.one.smul he)
  have hzero : 0 ∈ phaseMasses (noisyCorrelation epsilon) := by
    refine ⟨1,le_rfl,(fun _ => 0),(fun _ _ => 1),?_,?_,?_,?_⟩
    · simp
    · simp
    · simpa using hC
    · simp
  have hbound : ∀ t ∈ phaseMasses (noisyCorrelation epsilon),
      t ≤ (4/nu-gamma)*epsilon := scaled_mass_bound gamma hgap epsilon he
  have hbounded : BddAbove (phaseMasses (noisyCorrelation epsilon)) := ⟨_,hbound⟩
  exact ⟨hzero,hbounded,isLUB_csSup ⟨0,hzero⟩ hbounded,
    le_csSup hbounded hzero,csSup_le ⟨0,hzero⟩ hbound⟩

end D5.S3.Quantum.Recovery.SharedPhaseBudgetGap
