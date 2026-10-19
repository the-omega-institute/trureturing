/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/StructuralCone
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/StructuralCone
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Arbitrary ordered defects and constructive bulk subtraction for the full three-row cone. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.HalfspaceConeTransfer
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ScalarEnvelopes
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Mul
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
open scoped BigOperators Matrix
open Finset Matrix
open UniformSpectralBound.SharedSpectral
noncomputable section

-- Upstream interval principles, adapted inside the actual analytic proof.
private theorem quadratic_convex (a b c : ℝ) (ha : 0 ≤ a) :
    ConvexOn ℝ Set.univ (fun x : ℝ => a*x^2+b*x+c) := by
  have hs : ConvexOn ℝ Set.univ (fun x : ℝ => x^2) :=
    (show Even (2 : ℕ) from ⟨1, rfl⟩).convexOn_pow
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy p q hp hq hpq
  have hpow := hs.2 hx hy hp hq hpq
  have hqeq : q = 1-p := by linarith
  subst q
  simp only [smul_eq_mul] at hpow ⊢
  nlinarith only [mul_nonneg ha (sub_nonneg.mpr hpow)]

theorem quadratic_interval_le_fun (f : ℝ → ℝ) (a b c l r x M : ℝ)
    (hf : ∀ y, f y = a*y^2+b*y+c) (ha : 0 ≤ a)
    (hl : l ≤ x) (hr : x ≤ r) (hleft : f l ≤ M) (hright : f r ≤ M) :
    f x ≤ M := by
  have hcv : ConvexOn ℝ Set.univ f := by
    rw [show f = (fun y => a*y^2+b*y+c) from funext hf]
    exact quadratic_convex a b c ha
  exact (hcv.le_max_of_mem_Icc (Set.mem_univ _) (Set.mem_univ _) ⟨hl, hr⟩).trans
    (max_le hleft hright)

theorem quadratic_interval_nonneg (f : ℝ → ℝ) (a b c l r x : ℝ)
    (hf : ∀ y, f y = a*y^2+b*y+c) (ha : a ≤ 0)
    (hl : l ≤ x) (hr : x ≤ r) (hleft : 0 ≤ f l) (hright : 0 ≤ f r) :
    0 ≤ f x := by
  have hcc : ConcaveOn ℝ Set.univ f := by
    have hn := (quadratic_convex (-a) (-b) (-c) (by linarith)).neg
    refine ⟨convex_univ, ?_⟩
    intro y hy z hz p q hp hq hpq
    have hineq := hn.2 hy hz hp hq hpq
    simp only [smul_eq_mul, Pi.neg_apply] at hineq
    simp only [hf, smul_eq_mul]
    nlinarith only [hineq]

  exact (le_min hleft hright).trans
    (hcc.min_le_of_mem_Icc (Set.mem_univ _) (Set.mem_univ _) ⟨hl, hr⟩)

theorem ordered_block_energy {ι κ : Type*} [Fintype ι] [Fintype κ]
    (upper : ι → ℝ) (lower : κ → ℝ) (m : ℝ)
    (hm : 0 ≤ m) (hu : ∀ i, m ≤ upper i)
    (hl0 : ∀ i, 0 ≤ lower i) (hl1 : ∀ i, lower i ≤ m)
    (hk : 1 ≤ (Fintype.card ι : ℝ))
    (hcard : (Fintype.card κ : ℝ) ≤
      (Fintype.card ι : ℝ)*((Fintype.card ι : ℝ)-1)) :
    (∑ i, (upper i)^2)+(∑ i, (lower i)^2) ≤ (∑ i, upper i)^2 := by
  classical
  let k : ℝ := Fintype.card ι
  let Z : ℝ := ∑ i, (upper i-m)
  have hZ : 0 ≤ Z := Finset.sum_nonneg (fun i _ => sub_nonneg.mpr (hu i))
  have hZsq : (∑ i, (upper i-m)^2) ≤ Z^2 := by
    simpa only [Z] using
      (Finset.sum_sq_le_sq_sum_of_nonneg
        (s := Finset.univ) (f := fun i => upper i-m)
        (fun i _ => sub_nonneg.mpr (hu i)))
  have hsum : (∑ i, upper i) = k*m+Z := by
    dsimp [Z, k]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    ring
  have hpoint (i : ι) : (upper i)^2 = m^2+2*m*(upper i-m)+(upper i-m)^2 := by
    ring
  have hsq : (∑ i, (upper i)^2) =
      k*m^2+2*m*Z+(∑ i, (upper i-m)^2) := by
    calc
      _ = ∑ i, (m^2+2*m*(upper i-m)+(upper i-m)^2) :=
        Finset.sum_congr rfl (fun i _ => hpoint i)
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
        <;> rfl
  have hlower : (∑ i, (lower i)^2) ≤ (Fintype.card κ : ℝ)*m^2 := by
    calc
      _ ≤ ∑ _i : κ, m^2 := by
        apply Finset.sum_le_sum
        intro i _
        nlinarith [mul_nonneg (sub_nonneg.mpr (hl1 i)) (add_nonneg hm (hl0 i))]
      _ = _ := by simp
  have hcount : (Fintype.card κ : ℝ)*m^2 ≤ k*(k-1)*m^2 :=
    mul_le_mul_of_nonneg_right hcard (sq_nonneg m)
  have hexcess : 0 ≤ 2*(k-1)*m*Z := by
    apply mul_nonneg
    · apply mul_nonneg
      · exact mul_nonneg (by norm_num) (by simpa [k] using sub_nonneg.mpr hk)
      · exact hm
    · exact hZ
  calc
    _ ≤ k*m^2+2*m*Z+Z^2+k*(k-1)*m^2 := by
      rw [hsq]
      linarith [hlower.trans hcount]
    _ = (k*m+Z)^2-2*(k-1)*m*Z := by ring
    _ ≤ (k*m+Z)^2 := sub_le_self _ hexcess
    _ = _ := by rw [hsum]

private theorem affine_defect_transport (theta N j w c E : ℝ)
    (ht : 0 ≤ theta) (hw : 0 ≤ w) (hj : 6 ≤ j)
    (ha0 : 0 ≤ 2*theta*(N+3+2*w)-(2+w))
    (ha1 : 2*theta*(N+3+2*w)-(2+w) ≤ 1/4)
    (hF0 : 0 ≤ theta*(N+3+2*w)^2-(N+11+3*w+w^2))
    (hE0 : E ≤ 5-4*w-w^2)
    (hE1 : E ≤ 5-4*w-w^2+(c-(3-4*w))/4) :
    (2+w)*(N+w*j+c)-(1+w)*N+E ≤ theta*(N+w*j+c)^2 := by
  let L := N+3+2*w
  let e := w*(j-6)
  let a := 2*theta*L-(2+w)
  have he : 0 ≤ e := mul_nonneg hw (by linarith)
  have ha : 0 ≤ a := ha0
  have ha' : 0 ≤ 1/4-a := sub_nonneg.mpr ha1
  have hF : 0 ≤ theta*L^2-(2+w)*L+(1+w)*N-(5-4*w-w^2) := by
    dsimp [L]
    nlinarith only [hF0]
  by_cases hc : 3-4*w ≤ c
  · let d := c-(3-4*w)
    have hd : 0 ≤ d := sub_nonneg.mpr hc
    have hpos : 0 ≤ theta*(e+d)^2+a*(e+d) :=
      add_nonneg (mul_nonneg ht (sq_nonneg _))
        (mul_nonneg ha (add_nonneg he hd))
    have hid : theta*(N+w*j+c)^2-
        ((2+w)*(N+w*j+c)-(1+w)*N+(5-4*w-w^2)) =
        (theta*L^2-(2+w)*L+(1+w)*N-(5-4*w-w^2))+
        theta*(e+d)^2+a*(e+d) := by dsimp [L,e,d,a]; ring
    linarith
  · let d := (3-4*w)-c
    have hd : 0 ≤ d := by dsimp [d]; linarith
    have hpos : 0 ≤ theta*(e-d)^2+a*e+(1/4-a)*d :=
      add_nonneg (add_nonneg (mul_nonneg ht (sq_nonneg _)) (mul_nonneg ha he))
        (mul_nonneg ha' hd)
    have hid : theta*(N+w*j+c)^2-
        ((2+w)*(N+w*j+c)-(1+w)*N+(5-4*w-w^2-d/4)) =
        (theta*L^2-(2+w)*L+(1+w)*N-(5-4*w-w^2))+
        theta*(e-d)^2+a*e+(1/4-a)*d := by dsimp [L,e,d,a]; ring
    have hE : E ≤ 5-4*w-w^2-d/4 := by dsimp [d]; linarith [hE1]
    linarith

def H (h : Fin 5 → ℝ) : ℝ := ∑ i, h i
def D (d : Fin 9 → ℝ) : ℝ := ∑ i, d i
def H2 (h : Fin 5 → ℝ) : ℝ := ∑ i, (h i)^2
def D2 (d : Fin 9 → ℝ) : ℝ := ∑ i, (d i)^2
def H3 (h : Fin 5 → ℝ) : ℝ := h 0+h 1+h 2
def D6 (d : Fin 9 → ℝ) : ℝ := d 3+d 4+d 5+d 6+d 7+d 8
def D3 (d : Fin 9 → ℝ) : ℝ := d 6+d 7+d 8
def E (w : ℝ) (h : Fin 5 → ℝ) (d : Fin 9 → ℝ) : ℝ :=
  w*(H h+D d)+H2 h+D2 d
private def P (w : ℝ) : ℝ := 5-4*w-w^2
private def energyUpper (w z b r : ℝ) : ℝ := w*(4-6*w)+z^2+b^2+r^2
private def transferUpper (w z b r : ℝ) : ℝ :=
  4*w*(4-6*w)+4*z^2-z+4*b^2-b+4*r^2+3*r

-- This record holds only actual order and row budgets, never a good-cone premise.
structure DefectData (u v : ℝ) (h : Fin 5 → ℝ) (d : Fin 9 → ℝ) : Prop where
  hn : ∀ i, 0 ≤ h i
  ho : Antitone h
  dn : ∀ i, 0 ≤ d i
  do_ : Monotone d
  du : ∀ i, d i ≤ u
  row0 : H3 h+D6 d ≤ 3*u-3*v
  row1 : H h+D d ≤ 4*u-6*v
  row2 : h 0+D3 d ≤ 2*u-v

theorem defect_totals_nonneg {u v : ℝ} {h : Fin 5 → ℝ} {d : Fin 9 → ℝ}
    (hd : DefectData u v h d) : 0 ≤ H h ∧ 0 ≤ D d :=
  ⟨sum_nonneg (fun i _ => hd.hn i), sum_nonneg (fun i _ => hd.dn i)⟩

theorem defect_subtotals {u v : ℝ} {h : Fin 5 → ℝ} {d : Fin 9 → ℝ}
    (hd : DefectData u v h d) :
    h 0+h 1+h 2 ≤ H h ∧ D3 d ≤ D6 d ∧
      H3 h+D6 d ≤ H h+D d ∧ h 0+D3 d ≤ H h+D d ∧ d 8 ≤ H h+D d := by
  have hh := hd.hn
  have dd := hd.dn
  simp only [H, D, H3, D3, D6, Fin.sum_univ_succ, Fin.reduceFinMk, Fin.reduceSucc, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  constructor
  · linarith [hh 3, hh 4]
  constructor
  · linarith [dd 3, dd 4, dd 5]
  constructor
  · linarith [hh 3, hh 4, dd 0, dd 1, dd 2]
  constructor
  · linarith [hh 1, hh 2, hh 3, hh 4, dd 0, dd 1, dd 2, dd 3, dd 4, dd 5]
  · linarith [hh 0, hh 1, hh 2, hh 3, hh 4,
      dd 0, dd 1, dd 2, dd 3, dd 4, dd 5, dd 6, dd 7]

private theorem ordered_defect_energy {u v : ℝ} {h : Fin 5 → ℝ} {d : Fin 9 → ℝ}
    (hd : DefectData u v h d) :
    H2 h ≤ (h 0)^2+(h 1+h 2)^2 ∧ D2 d ≤ (D3 d)^2 ∧ D d ≤ 3*D3 d := by
  have heh := ordered_block_energy
    (fun i : Fin 2 => (![h 1,h 2] : Fin 2 → ℝ) i)
    (fun i : Fin 2 => (![h 3,h 4] : Fin 2 → ℝ) i) (h 2)
    (hd.hn 2)
    (by intro i; fin_cases i; exact hd.ho (by decide); exact le_rfl)
    (by intro i; fin_cases i; exact hd.hn 3; exact hd.hn 4)
    (by intro i; fin_cases i; exact hd.ho (by decide); exact hd.ho (by decide))
    (by norm_num) (by norm_num)
  have hed := ordered_block_energy
    (fun i : Fin 3 => (![d 6,d 7,d 8] : Fin 3 → ℝ) i)
    (fun i : Fin 6 => (![d 0,d 1,d 2,d 3,d 4,d 5] : Fin 6 → ℝ) i) (d 6)
    (hd.dn 6)
    (by intro i; fin_cases i <;> exact hd.do_ (by decide))
    (by intro i; fin_cases i <;> exact hd.dn _)
    (by intro i; fin_cases i <;> exact hd.do_ (by decide))
    (by norm_num) (by norm_num)
  simp only [Fin.sum_univ_succ, Fin.reduceFinMk, Fin.reduceSucc, Finset.univ_eq_empty, Finset.sum_empty, add_zero, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Fin.reduceFinMk, Fin.reduceSucc, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one, add_zero] at heh hed
  constructor
  · dsimp [H2]
    simp only [Fin.sum_univ_succ, Fin.reduceFinMk, Fin.reduceSucc, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    nlinarith only [heh]
  constructor
  · dsimp [D2, D3]
    simp only [Fin.sum_univ_succ, Fin.reduceFinMk, Fin.reduceSucc, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    nlinarith only [hed]
  · dsimp [D, D3]
    simp only [Fin.sum_univ_succ, Fin.reduceFinMk, Fin.reduceSucc, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    linarith [hd.do_ (show (0 : Fin 9) ≤ 6 by decide),
      hd.do_ (show (1 : Fin 9) ≤ 7 by decide),
      hd.do_ (show (2 : Fin 9) ≤ 8 by decide),
      hd.do_ (show (3 : Fin 9) ≤ 6 by decide),
      hd.do_ (show (4 : Fin 9) ≤ 7 by decide),
      hd.do_ (show (5 : Fin 9) ≤ 8 by decide)]

theorem small_head_energy {w : ℝ} {h : Fin 5 → ℝ} {d : Fin 9 → ℝ}
    (hd : DefectData 1 w h d) (hw : 0 ≤ w) (hz : h 0 ≤ 1) :
    E w h d ≤ 4-2*w-6*w^2 := by
  have hh2 : H2 h ≤ H h := by
    apply sum_le_sum
    intro i _
    have hi : h i ≤ 1 := (hd.ho (Fin.zero_le i)).trans hz
    nlinarith [hd.hn i]
  have dd2 : D2 d ≤ D d := by
    apply sum_le_sum
    intro i _
    nlinarith [hd.dn i, hd.du i]
  have hb := mul_le_mul_of_nonneg_left hd.row1 (show 0 ≤ 1+w by linarith)
  dsimp [E]
  nlinarith only [hh2, dd2, hb]

-- First of the two bounds needed at a large head; b is monotone here.
private theorem large_head_energy_parameters (w z b r : ℝ)
    (hw : 0 ≤ w) (hw1 : w ≤ 1/2) (hz : 1 ≤ z) (hz1 : z ≤ 2-w)
    (hb : 0 ≤ b) (hr : 0 ≤ r) (hr1 : r ≤ 2-w-z)
    (hb1 : b ≤ 3-3*w-z-r) : energyUpper w z b r ≤ P w := by
  have hp := mul_nonneg hw (show 0 ≤ 1-w by linarith)
  have hz0 : energyUpper w z (3-3*w-z) 0 ≤ P w := by
    apply quadratic_interval_le_fun (fun y => energyUpper w y (3-3*w-y) 0)
      2 (-2*(3-3*w)) (w*(4-6*w)+(3-3*w)^2) 1 (2-w) z (P w)
    · intro y; dsimp [energyUpper]; ring
    · norm_num
    · exact hz
    · exact hz1
    · dsimp [energyUpper, P]; nlinarith
    · dsimp [energyUpper, P]; nlinarith
  have hzA : energyUpper w z (1-2*w) (2-w-z) ≤ P w := by
    apply quadratic_interval_le_fun (fun y => energyUpper w y (1-2*w) (2-w-y))
      2 (-2*(2-w)) (w*(4-6*w)+(1-2*w)^2+(2-w)^2) 1 (2-w) z (P w)
    · intro y; dsimp [energyUpper]; ring
    · norm_num
    · exact hz
    · exact hz1
    · dsimp [energyUpper, P]; nlinarith
    · dsimp [energyUpper, P]; nlinarith
  have hR : energyUpper w z (3-3*w-z-r) r ≤ P w := by
    apply quadratic_interval_le_fun (fun y => energyUpper w z (3-3*w-z-y) y)
      2 (-2*(3-3*w-z)) (w*(4-6*w)+z^2+(3-3*w-z)^2)
      0 (2-w-z) r (P w)
    · intro y; dsimp [energyUpper]; ring
    · norm_num
    · exact hr
    · exact hr1
    · simpa using hz0
    · convert hzA using 1 <;> dsimp [energyUpper] <;> ring
  have hB : energyUpper w z b r ≤ energyUpper w z (3-3*w-z-r) r := by
    dsimp [energyUpper]
    nlinarith [mul_nonneg (sub_nonneg.mpr hb1)
      (show 0 ≤ 3-3*w-z-r+b by linarith)]
  exact hB.trans hR

-- The second bound must retain the -c term. Neither estimate is a premise.
private theorem large_head_transfer_parameters (w z b r : ℝ)
    (hw : 0 ≤ w) (hw1 : w ≤ 1/2) (hz : 1 ≤ z) (hz1 : z ≤ 2-w)
    (hb : 0 ≤ b) (hr : 0 ≤ r) (hr1 : r ≤ 2-w-z)
    (hb1 : b ≤ 3-3*w-z-r) :
    transferUpper w z b r ≤ 17-12*w-4*w^2 := by
  have h00 : transferUpper w z 0 0 ≤ 17-12*w-4*w^2 := by
    apply quadratic_interval_le_fun (fun y => transferUpper w y 0 0)
      4 (-1) (4*w*(4-6*w)) 1 (2-w) z (17-12*w-4*w^2)
    · intro y; dsimp [transferUpper]; ring
    · norm_num
    · exact hz
    · exact hz1
    · dsimp [transferUpper]; nlinarith [sq_nonneg w]
    · dsimp [transferUpper]; nlinarith [sq_nonneg (w-13/32)]
  have h01 : transferUpper w z 0 (2-w-z) ≤ 17-12*w-4*w^2 := by
    apply quadratic_interval_le_fun (fun y => transferUpper w y 0 (2-w-y))
      8 (-8*(2-w)-4) (4*w*(4-6*w)+4*(2-w)^2+3*(2-w))
      1 (2-w) z (17-12*w-4*w^2)
    · intro y; dsimp [transferUpper]; ring
    · norm_num
    · exact hz
    · exact hz1
    · dsimp [transferUpper]; nlinarith [sq_nonneg (w-17/32)]
    · dsimp [transferUpper]; nlinarith [sq_nonneg (w-13/32)]
  have h10 : transferUpper w z (3-3*w-z) 0 ≤ 17-12*w-4*w^2 := by
    apply quadratic_interval_le_fun (fun y => transferUpper w y (3-3*w-y) 0)
      8 (-8*(3-3*w)) (4*w*(4-6*w)+4*(3-3*w)^2-(3-3*w))
      1 (2-w) z (17-12*w-4*w^2)
    · intro y; dsimp [transferUpper]; ring
    · norm_num
    · exact hz
    · exact hz1
    · dsimp [transferUpper]
      nlinarith [mul_nonneg hw (show 0 ≤ 17-16*w by linarith)]
    · dsimp [transferUpper]; nlinarith
  have h11 : transferUpper w z (1-2*w) (2-w-z) ≤ 17-12*w-4*w^2 := by
    apply quadratic_interval_le_fun (fun y => transferUpper w y (1-2*w) (2-w-y))
      8 (-8*(2-w)-4)
      (4*w*(4-6*w)+4*(1-2*w)^2-(1-2*w)+4*(2-w)^2+3*(2-w))
      1 (2-w) z (17-12*w-4*w^2)
    · intro y; dsimp [transferUpper]; ring
    · norm_num
    · exact hz
    · exact hz1
    · dsimp [transferUpper]; nlinarith
    · dsimp [transferUpper]; nlinarith
  have h0 : transferUpper w z 0 r ≤ 17-12*w-4*w^2 := by
    apply quadratic_interval_le_fun (fun y => transferUpper w z 0 y)
      4 3 (4*w*(4-6*w)+4*z^2-z) 0 (2-w-z) r (17-12*w-4*w^2)
    · intro y; dsimp [transferUpper]; ring
    · norm_num
    · exact hr
    · exact hr1
    · exact h00
    · exact h01
  have h1 : transferUpper w z (3-3*w-z-r) r ≤ 17-12*w-4*w^2 := by
    apply quadratic_interval_le_fun (fun y => transferUpper w z (3-3*w-z-y) y)
      8 (4-8*(3-3*w-z))
      (4*w*(4-6*w)+4*z^2-z+4*(3-3*w-z)^2-(3-3*w-z))
      0 (2-w-z) r (17-12*w-4*w^2)
    · intro y; dsimp [transferUpper]; ring
    · norm_num
    · exact hr
    · exact hr1
    · simpa only [sub_zero] using h10
    · convert h11 using 1 <;> dsimp [transferUpper] <;> ring
  apply quadratic_interval_le_fun (fun y => transferUpper w z y r)
    4 (-1) (4*w*(4-6*w)+4*z^2-z+4*r^2+3*r)
    0 (3-3*w-z-r) b (17-12*w-4*w^2)
  · intro y; dsimp [transferUpper]; ring
  · norm_num
  · exact hb
  · exact hb1
  · exact h0
  · exact h1

private theorem large_head_estimates {w : ℝ} {h : Fin 5 → ℝ} {d : Fin 9 → ℝ}
    (hd : DefectData 1 w h d) (hw : 0 ≤ w) (hw1 : w ≤ 1/2) (hz : 1 ≤ h 0) :
    E w h d ≤ P w ∧ 4*E w h d-(H h-D d) ≤ 17-12*w-4*w^2 := by
  obtain ⟨hH, hD⟩ := defect_totals_nonneg hd
  obtain ⟨hHs, hDs, _, _, _⟩ := defect_subtotals hd
  obtain ⟨hh2, hd2, hDr⟩ := ordered_defect_energy hd
  have hr : 0 ≤ D3 d := add_nonneg (add_nonneg (hd.dn 6) (hd.dn 7)) (hd.dn 8)
  have hb : 0 ≤ h 1+h 2 := add_nonneg (hd.hn 1) (hd.hn 2)
  have hz1 : h 0 ≤ 2-w := by linarith [hd.row2]
  have hr1 : D3 d ≤ 2-w-h 0 := by linarith [hd.row2]
  have hb1 : h 1+h 2 ≤ 3-3*w-h 0-D3 d := by
    have hrow := hd.row0
    dsimp [H3] at hrow
    linarith
  have hmul := mul_le_mul_of_nonneg_left hd.row1 hw
  have hE : E w h d ≤ energyUpper w (h 0) (h 1+h 2) (D3 d) := by
    dsimp [E, energyUpper]
    linarith
  have hT : 4*E w h d-(H h-D d) ≤
      transferUpper w (h 0) (h 1+h 2) (D3 d) := by
    dsimp [E, transferUpper]
    linarith
  constructor
  · exact hE.trans (large_head_energy_parameters w (h 0) (h 1+h 2) (D3 d)
      hw hw1 hz hz1 hb hr hr1 hb1)
  · exact hT.trans (large_head_transfer_parameters w (h 0) (h 1+h 2) (D3 d)
      hw hw1 hz hz1 hb hr hr1 hb1)

theorem total_energy_estimate {u w : ℝ} {h : Fin 5 → ℝ} {d : Fin 9 → ℝ}
    (hd : DefectData u w h d) (hw : 0 ≤ w) :
    E w h d ≤ (4*u-6*w)*(4*u-5*w) := by
  obtain ⟨hH, hD⟩ := defect_totals_nonneg hd
  have hh2 : H2 h ≤ (H h)^2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (s := univ) (f := h) (fun i _ => hd.hn i)
  have hd2 : D2 d ≤ (D d)^2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (s := univ) (f := d) (fun i _ => hd.dn i)
  have hcross := mul_nonneg hH hD
  have hb := hd.row1
  have hgap := mul_nonneg (show 0 ≤ (4*u-6*w)-(H h+D d) by linarith)
    (show 0 ≤ (4*u-6*w)+(H h+D d)+w by linarith)
  dsimp [E]
  nlinarith

-- Uniform scalar comparisons. Existing envelopes are used at their actual types.
private structure ScalarBounds (N : ℝ) : Prop where
  pos : 0 < commonEnvelope N
  upper : commonEnvelope N ≤ 16/(15*N)
  small : commonEnvelope N < 1/24
  lower : 16/(15*N+49) ≤ commonEnvelope N
  boundary : (N+11)/(N+3)^2 ≤ commonEnvelope N
  atZero : 1/(N-4) ≤ commonEnvelope N
  atHalf : 25/(24*(N-1)) ≤ commonEnvelope N
  atTwoFifths : 36/(35*N-80) ≤ commonEnvelope N
  atTwoFifteenths : 256/(255*N-1001) ≤ commonEnvelope N
  atTwoFifthsP : 36/(35*N-81) ≤ commonEnvelope N

private theorem scalar_bounds (N : ℝ) (hN : 67 ≤ N) : ScalarBounds N := by
  have hB : 0 < 15*N-4 := by linarith
  have hNs : 0 < 15*N := by linarith
  have hL : 0 < 15*N+49 := by linarith
  have ht : 0 < commonEnvelope N := by
    unfold commonEnvelope
    exact div_pos (by linarith) (sq_pos_of_pos hB)
  have hu : commonEnvelope N ≤ 16/(15*N) := by
    unfold commonEnvelope
    apply (div_le_div_iff₀ (sq_pos_of_pos hB) hNs).2
    nlinarith
  have hsmall : commonEnvelope N < 1/24 := by
    apply lt_of_le_of_lt hu
    apply (div_lt_iff₀ hNs).2
    linarith
  have hlo : 16/(15*N+49) ≤ commonEnvelope N := by
    unfold commonEnvelope
    apply (div_le_div_iff₀ hL (sq_pos_of_pos hB)).2
    nlinarith
  have hbd := boundary_envelope_le_common N hN
  have he1 := middle_envelope₁_le_common N (by linarith)
  have he2 := middle_envelope₂_le_common N hN
  have hz : 1/(N-4) ≤ commonEnvelope N := by
    apply le_trans _ hbd
    unfold boundaryEnvelope
    apply (div_le_div_iff₀ (by linarith : 0 < N-4)
      (sq_pos_of_pos (by linarith : 0 < N+3))).2
    nlinarith
  have h256 : 256/(255*N-1001) ≤ commonEnvelope N := by
    unfold commonEnvelope
    apply (div_le_div_iff₀ (by linarith : 0 < 255*N-1001) (sq_pos_of_pos hB)).2
    apply sub_nonneg.mp
    have hq : 0 ≤ N-67 := sub_nonneg.mpr hN
    calc
      _ = 3600*(N-67)^2+240240*(N-67)+59712 := by ring
      _ ≥ 0 := by positivity
  have h36 : 36/(35*N-81) ≤ commonEnvelope N := by
    unfold commonEnvelope
    apply (div_le_div_iff₀ (by linarith : 0 < 35*N-81) (sq_pos_of_pos hB)).2
    apply sub_nonneg.mp
    have hq : 0 ≤ N-67 := sub_nonneg.mpr hN
    calc
      _ = 300*(N-67)^2+20600*(N-67)+43292 := by ring
      _ ≥ 0 := by positivity
  exact ⟨ht, hu, hsmall, hlo, hbd, hz, he1, he2, h256, h36⟩

private def disc (theta N : ℝ) (U : ℝ → ℝ) (w : ℝ) : ℝ :=
  4*theta*((1+w)*N-U w)-(2+w)^2

-- Completing squares is consumed immediately by all three interval branches.
theorem square_completion (theta h K S : ℝ) (ht : 0 < theta)
    (hdisc : h^2 ≤ 4*theta*K) : h*S-K ≤ theta*S^2 := by
  have hid : 4*theta*(theta*S^2-(h*S-K)) =
      (2*theta*S-h)^2+4*theta*K-h^2 := by ring
  have hp : 0 ≤ 4*theta*(theta*S^2-(h*S-K)) := by
    rw [hid]
    nlinarith only [sq_nonneg (2*theta*S-h), hdisc]
  have hs := nonneg_of_mul_nonneg_right hp (by positivity : 0 < 4*theta)
  linarith

private theorem discriminant_intervals (N : ℝ) (hN : 67 ≤ N) :
    (∀ w : ℝ, 0 ≤ w → w ≤ 1/2 →
      0 ≤ disc (commonEnvelope N) N (fun y => 4-2*y-6*y^2) w) ∧
    (∀ w : ℝ, 2/15 ≤ w → w ≤ 2/5 →
      0 ≤ disc (commonEnvelope N) N P w) ∧
    (∀ w : ℝ, 2/5 ≤ w → w ≤ 1/2 →
      0 ≤ disc (commonEnvelope N) N (fun y => (4-6*y)*(4-5*y)) w) := by
  let theta := commonEnvelope N
  have hb := scalar_bounds N hN
  have h0 : 1 ≤ theta*(N-4) :=
    (div_le_iff₀ (by linarith : 0 < N-4)).mp hb.atZero
  have hH : 25 ≤ theta*(24*(N-1)) :=
    (div_le_iff₀ (by linarith : 0 < 24*(N-1))).mp hb.atHalf
  have hF : 36 ≤ theta*(35*N-80) :=
    (div_le_iff₀ (by linarith : 0 < 35*N-80)).mp hb.atTwoFifths
  have hFP : 36 ≤ theta*(35*N-81) :=
    (div_le_iff₀ (by linarith : 0 < 35*N-81)).mp hb.atTwoFifthsP
  have hT : 256 ≤ theta*(255*N-1001) :=
    (div_le_iff₀ (by linarith : 0 < 255*N-1001)).mp hb.atTwoFifteenths
  have ht : 0 < theta := hb.pos
  have ht1 : theta < 1/24 := hb.small
  constructor
  · intro w hw hw1
    apply quadratic_interval_nonneg
      (disc theta N (fun y => 4-2*y-6*y^2))
      (24*theta-1) (4*theta*(N+2)-4) (4*theta*(N-4)-4) 0 (1/2) w
    · intro y; dsimp [disc]; ring
    · linarith
    · exact hw
    · exact hw1
    · dsimp [disc]; nlinarith only [h0]
    · dsimp [disc]; nlinarith only [hH]
  constructor
  · intro w hw hw1
    apply quadratic_interval_nonneg (disc theta N P)
      (4*theta-1) (4*theta*(N+4)-4) (4*theta*(N-5)-4) (2/15) (2/5) w
    · intro y; dsimp [disc, P]; ring
    · linarith
    · exact hw
    · exact hw1
    · dsimp [disc, P]; nlinarith only [hT]
    · dsimp [disc, P]; nlinarith only [hFP]
  · intro w hw hw1
    apply quadratic_interval_nonneg (disc theta N (fun y => (4-6*y)*(4-5*y)))
      (-120*theta-1) (4*theta*(N+44)-4) (4*theta*(N-16)-4) (2/5) (1/2) w
    · intro y; dsimp [disc]; ring
    · linarith
    · exact hw
    · exact hw1
    · dsimp [disc]; nlinarith only [hF]
    · dsimp [disc]; nlinarith only [hH]

-- Pays every hypothesis of the small-w mass/defect transport.
private theorem small_jump_scalars (N w : ℝ) (hN : 67 ≤ N)
    (hw : 0 ≤ w) (hw1 : w ≤ 2/15) :
    0 ≤ 2*commonEnvelope N*(N+3+2*w)-(2+w) ∧
    2*commonEnvelope N*(N+3+2*w)-(2+w) ≤ 1/4 ∧
    0 ≤ commonEnvelope N*(N+3+2*w)^2-(N+11+3*w+w^2) := by
  let theta := commonEnvelope N
  have hb := scalar_bounds N hN
  have ht : 0 < theta := hb.pos
  have ht1 : theta < 1/24 := hb.small
  have hlow : 16 ≤ theta*(15*N+49) :=
    (div_le_iff₀ (by linarith : 0 < 15*N+49)).mp hb.lower
  have hupp : theta*(15*N) ≤ 16 :=
    (le_div_iff₀ (by linarith : 0 < 15*N)).mp hb.upper
  have hdec := mul_nonneg (show 0 ≤ 1-4*theta by linarith)
    (show 0 ≤ 2/15-w by linarith)
  have hdec0 := mul_nonneg (show 0 ≤ 1-4*theta by linarith) hw
  have htheta : theta ≤ 16/1005 := by
    nlinarith [mul_nonneg ht.le (show 0 ≤ N-67 by linarith)]
  have ha0 : 0 ≤ 2*theta*(N+3+2*w)-(2+w) := by nlinarith only [hlow, hdec]
  have ha1 : 2*theta*(N+3+2*w)-(2+w) ≤ 1/4 := by
    nlinarith only [hupp, htheta, hdec0]
  have hf0 : 0 ≤ theta*(N+3)^2-(N+11) := by
    have hh := (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < N+3))).mp hb.boundary
    linarith
  have hdisc : 0 ≤ disc theta N P (2/15) :=
    (discriminant_intervals N hN).2.1 (2/15) (by norm_num) (by norm_num)
  have hf1 : 0 ≤ theta*(N+3+2*(2/15))^2-(N+11+3*(2/15)+(2/15)^2) := by
    have hid : 4*theta*(theta*(N+3+2*(2/15))^2-(N+11+3*(2/15)+(2/15)^2)) =
        (2*theta*(N+3+2*(2/15))-(2+2/15))^2+disc theta N P (2/15) := by
      dsimp [disc, P]
      ring
    have hp : 0 ≤ 4*theta*(theta*(N+3+2*(2/15))^2-
        (N+11+3*(2/15)+(2/15)^2)) := by
      rw [hid]
      exact add_nonneg (sq_nonneg _) hdisc
    exact nonneg_of_mul_nonneg_right hp (by positivity : 0 < 4*theta)
  have hF : 0 ≤ theta*(N+3+2*w)^2-(N+11+3*w+w^2) := by
    apply quadratic_interval_nonneg
      (fun y => theta*(N+3+2*y)^2-(N+11+3*y+y^2))
      (4*theta-1) (4*theta*(N+3)-3) (theta*(N+3)^2-(N+11)) 0 (2/15) w
    · intro y; ring
    · linarith
    · exact hw
    · exact hw1
    · simpa using hf0
    · exact hf1
  exact ⟨ha0, ha1, hF⟩

private theorem normalized_defect_bound (N j w : ℝ) (hN : 67 ≤ N) (hj : 6 ≤ j)
    (hw : 0 ≤ w) (hw1 : w ≤ 1/2) (h : Fin 5 → ℝ) (d : Fin 9 → ℝ)
    (hd : DefectData 1 w h d) :
    (2+w)*(N+w*j+H h-D d)-(1+w)*N+E w h d ≤
      commonEnvelope N*(N+w*j+H h-D d)^2 := by
  have ht := (scalar_bounds N hN).pos
  obtain ⟨hI0, hIP, hIT⟩ := discriminant_intervals N hN
  by_cases hz : h 0 ≤ 1
  · have he := small_head_energy hd hw hz
    have hi := hI0 w hw hw1
    have hs := square_completion (commonEnvelope N) (2+w)
      ((1+w)*N-(4-2*w-6*w^2)) (N+w*j+H h-D d) ht
      (by dsimp [disc] at hi; linarith)
    linarith
  · have hz1 : 1 ≤ h 0 := le_of_lt (lt_of_not_ge hz)
    obtain ⟨he, he4⟩ := large_head_estimates hd hw hw1 hz1
    by_cases hwsmall : w ≤ 2/15
    · obtain ⟨ha0, ha1, hF⟩ := small_jump_scalars N w hN hw hwsmall
      have he1 : E w h d ≤ 5-4*w-w^2+((H h-D d)-(3-4*w))/4 := by
        linarith only [he4]
      have hs := affine_defect_transport (commonEnvelope N) N j w (H h-D d) (E w h d)
        ht.le hw hj ha0 ha1 hF he he1
      convert hs using 1 <;> ring
    · have hwlow : 2/15 ≤ w := le_of_lt (lt_of_not_ge hwsmall)
      by_cases hwmed : w ≤ 2/5
      · have hi := hIP w hwlow hwmed
        have hs := square_completion (commonEnvelope N) (2+w)
          ((1+w)*N-P w) (N+w*j+H h-D d) ht
          (by dsimp [disc] at hi; linarith)
        linarith
      · have heT := total_energy_estimate hd hw
        have hi := hIT w (le_of_lt (lt_of_not_ge hwmed)) hw1
        have hs := square_completion (commonEnvelope N) (2+w)
          ((1+w)*N-(4-6*w)*(4-5*w)) (N+w*j+H h-D d) ht
          (by dsimp [disc] at hi; linarith)
        linarith

-- Actual coordinates; the nine tail entries represent d_1,...,d_9.
def low (x : Fin 16 → ℝ) : ℝ := x 6+x 7+x 8+x 9+x 10+x 11+x 12+x 13+x 14+x 15
def head (x : Fin 16 → ℝ) : Fin 5 → ℝ :=
  ![x 0+x 1+x 2+x 3+x 4,
    x 1+x 2+x 3+x 4,
    x 2+x 3+x 4,
    x 3+x 4,
    x 4]
def tail (x : Fin 16 → ℝ) : Fin 9 → ℝ :=
  ![x 6,
    x 6+x 7,
    x 6+x 7+x 8,
    x 6+x 7+x 8+x 9,
    x 6+x 7+x 8+x 9+x 10,
    x 6+x 7+x 8+x 9+x 10+x 11,
    x 6+x 7+x 8+x 9+x 10+x 11+x 12,
    x 6+x 7+x 8+x 9+x 10+x 11+x 12+x 13,
    x 6+x 7+x 8+x 9+x 10+x 11+x 12+x 13+x 14]

theorem actual_row_identities (x : Fin 16 → ℝ) :
    (A *ᵥ x) 0 = 3*low x-3*x 5-H3 (head x)-D6 (tail x) ∧
    (A *ᵥ x) 1 = 4*low x-6*x 5-H (head x)-D (tail x) ∧
    (A *ᵥ x) 2 = 2*low x-x 5-head x 0-D3 (tail x) := by
  simp only [A, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.reduceFinMk, Fin.reduceSucc, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    Matrix.cons_val, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Fin.reduceFinMk, Fin.reduceSucc, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
    low, head, tail, H, D, H3, D6, D3]
  constructor
  · ring
  constructor <;> ring

theorem actual_defects (x : Fin 16 → ℝ)
    (hx : ∀ q, 0 ≤ x q) (hAx : ∀ r, 0 ≤ (A *ᵥ x) r) :
    DefectData (low x) (x 5) (head x) (tail x) := by
  obtain ⟨hr0, hr1, hr2⟩ := actual_row_identities x
  have hn : ∀ i, 0 ≤ head x i := by
    intro i
    fin_cases i <;> simp only [head, Matrix.cons_val, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Fin.reduceFinMk, Fin.reduceSucc, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one] <;> linarith [hx 0, hx 1, hx 2, hx 3, hx 4]
  have ho : Antitone (head x) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num (config := { decide := true }) at hij <;>
      simp only [head, Matrix.cons_val, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Fin.reduceFinMk, Fin.reduceSucc, Matrix.cons_val_succ,
        Matrix.cons_val_fin_one] <;> linarith [hx 0, hx 1, hx 2, hx 3, hx 4]
  have dn : ∀ i, 0 ≤ tail x i := by
    intro i
    fin_cases i <;> simp only [tail, Matrix.cons_val, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Fin.reduceFinMk, Fin.reduceSucc, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one] <;>
      linarith [hx 6, hx 7, hx 8, hx 9, hx 10, hx 11, hx 12, hx 13, hx 14]
  have do_ : Monotone (tail x) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num (config := { decide := true }) at hij <;>
      simp only [tail, Matrix.cons_val, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Fin.reduceFinMk, Fin.reduceSucc, Matrix.cons_val_succ,
        Matrix.cons_val_fin_one] <;>
      linarith [hx 6, hx 7, hx 8, hx 9, hx 10, hx 11, hx 12, hx 13, hx 14]
  have du : ∀ i, tail x i ≤ low x := by
    intro i
    fin_cases i <;> simp only [tail, low, Matrix.cons_val, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Fin.reduceFinMk, Fin.reduceSucc, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one] <;>
      linarith [hx 6, hx 7, hx 8, hx 9, hx 10, hx 11, hx 12, hx 13, hx 14, hx 15]
  exact ⟨hn, ho, dn, do_, du,
    by linarith [hAx 0], by linarith [hAx 1], by linarith [hAx 2]⟩

theorem last_defect_identity (x : Fin 16 → ℝ) : tail x 8 = low x-x 15 := by
  simp only [tail, low, Matrix.cons_val_succ, Matrix.cons_val, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Fin.reduceFinMk, Fin.reduceSucc,
    Matrix.cons_val_fin_one]
  ring

theorem low_nonneg (x : Fin 16 → ℝ) (hx : ∀ q, 0 ≤ x q) : 0 ≤ low x := by
  dsimp [low]
  linarith [hx 6, hx 7, hx 8, hx 9, hx 10, hx 11, hx 12, hx 13, hx 14, hx 15]

theorem low_smul (a : ℝ) (x : Fin 16 → ℝ) : low (a • x) = a*low x := by
  simp only [low, Pi.smul_apply, smul_eq_mul]
  ring

private theorem boundary_positions_literal (N j : ℕ) (hN : 16 ≤ N) :
    positions N j = ![1,2,3,4,5,j,N-9,N-8,N-7,N-6,N-5,N-4,N-3,N-2,N-1,N] := by
  funext q
  fin_cases q <;> simp [positions] <;> omega

private theorem boundary_positions_strict (N j : ℕ) (hN : 16 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) : StrictMono (positions N j) := by
  intro q r hqr
  have hq := q.isLt
  have hr := r.isLt
  have hqr' : q.val < r.val := hqr
  dsimp [positions]
  split_ifs <;> omega

private theorem slot_bounds (N j : ℕ) (hN : 16 ≤ N) (hj : 6 ≤ j) (hj' : j ≤ N-10) :
    ∀ q, positions N j q ≤ N := by
  intro q
  have hq := q.isLt
  dsimp [positions]
  split_ifs <;> omega

-- Identities for every real x, including infeasible and negative vectors.
theorem boundary_mass (N j : ℕ) (hN : 16 ≤ N) (hj : 6 ≤ j) (hj' : j ≤ N-10)
    (x : Fin 16 → ℝ) :
    (∑ k : Fin N, synth (positions N j) x k) =
      low x*(N : ℝ)+x 5*(j : ℝ)+H (head x)-D (tail x) := by
  rw [mass_synth (positions N j) (slot_bounds N j hN hj hj')]
  rw [boundary_positions_literal N j (by omega)]
  norm_num [Matrix.cons_val, Fin.sum_univ_succ, Fin.reduceFinMk, Fin.reduceSucc, Finset.univ_eq_empty, Finset.sum_empty, add_zero, low, head, tail, H, D]
  try simp (disch := omega) only [Nat.cast_sub]
  norm_num
  ring

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem boundary_square (N j : ℕ) (hN : 16 ≤ N) (hj : 6 ≤ j) (hj' : j ≤ N-10)
    (x : Fin 16 → ℝ) :
    (∑ k : Fin N, (synth (positions N j) x k)^2) =
      (2*low x+x 5)*(low x*(N : ℝ)+x 5*(j : ℝ)+H (head x)-D (tail x))-
        low x*(low x+x 5)*(N : ℝ)+E (x 5) (head x) (tail x) := by
  rw [square_synth (positions N j) (slot_bounds N j hN hj hj')]
  have hmin (q r : Fin 16) :
      min (positions N j q) (positions N j r) = positions N j (min q r) := by
    rcases le_total q r with hqr | hrq
    · rw [min_eq_left hqr, min_eq_left ((boundary_positions_strict N j (by omega) hj hj').monotone hqr)]
    · rw [min_eq_right hrq, min_eq_right ((boundary_positions_strict N j (by omega) hj hj').monotone hrq)]
  simp_rw [hmin]
  rw [boundary_positions_literal N j (by omega)]
  norm_num [Matrix.cons_val, Fin.sum_univ_succ, Fin.reduceFinMk, Fin.reduceSucc, Finset.univ_eq_empty, Finset.sum_empty, add_zero, low, head, tail, H, D, H2, D2, E]
  try simp (disch := omega) only [Nat.cast_sub]
  norm_num
  ring

theorem actual_mass (N j : ℕ) (hN : 56 ≤ N) (hj : 6 ≤ j) (hj' : j ≤ N-10)
    (x : Fin 16 → ℝ) :
    (∑ k : Fin N, synth (positions N j) x k) =
      low x*(N : ℝ)+x 5*(j : ℝ)+H (head x)-D (tail x) := by
  exact boundary_mass N j (by omega) hj hj' x

theorem actual_square (N j : ℕ) (hN : 56 ≤ N) (hj : 6 ≤ j) (hj' : j ≤ N-10)
    (x : Fin 16 → ℝ) :
    (∑ k : Fin N, (synth (positions N j) x k)^2) =
      (2*low x+x 5)*(low x*(N : ℝ)+x 5*(j : ℝ)+H (head x)-D (tail x))-
        low x*(low x+x 5)*(N : ℝ)+E (x 5) (head x) (tail x) := by
  exact boundary_square N j (by omega) hj hj' x

theorem synth_nonneg (N j : ℕ) (x : Fin 16 → ℝ) (hx : ∀ q, 0 ≤ x q) :
    ∀ k : Fin N, 0 ≤ synth (positions N j) x k := by
  intro k
  change 0 ≤ (∑ q, x q • step N (positions N j q)) k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply sum_nonneg
  intro q _
  apply mul_nonneg (hx q)
  unfold step
  split_ifs <;> norm_num

theorem zero_low (x : Fin 16 → ℝ) (hx : ∀ q, 0 ≤ x q)
    (hAx : ∀ r, 0 ≤ (A *ᵥ x) r) (hu : low x = 0) : x = 0 := by
  obtain ⟨_, hr, _⟩ := actual_row_identities x
  have hrow := hAx 1
  rw [hr, hu] at hrow
  have he : H (head x)+D (tail x) =
      x 0+2*x 1+3*x 2+4*x 3+5*x 4+
      9*x 6+8*x 7+7*x 8+6*x 9+5*x 10+4*x 11+3*x 12+2*x 13+x 14 := by
    norm_num [Matrix.cons_val, H, D, head, tail, Fin.sum_univ_succ, Fin.reduceFinMk, Fin.reduceSucc, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    ring
  have hrowTotal : 0 ≤ -6*x 5-(H (head x)+D (tail x)) := by linarith
  rw [he] at hrowTotal
  dsimp [low] at hu
  ext q
  fin_cases q <;> simp only [Pi.zero_apply, Fin.reduceFinMk, Fin.reduceSucc, Nat.reduceAdd, Fin.isValue] <;>
    linarith [hx 0, hx 1, hx 2, hx 3, hx 4, hx 5, hx 6, hx 7,
      hx 8, hx 9, hx 10, hx 11, hx 12, hx 13, hx 14, hx 15]

private theorem normalized_cone_good (N j : ℕ) (hN : 67 ≤ N) (hj : 6 ≤ j) (hj' : j ≤ N-10)
    (x : Fin 16 → ℝ) (hx : ∀ q, 0 ≤ x q) (hAx : ∀ r, 0 ≤ (A *ᵥ x) r)
    (hu : low x = 1) (hv : x 5 ≤ 1/2) :
    spectralGood (Real.sqrt (target N)) (synth (d := N) (positions N j) x) := by
  have hd : DefectData 1 (x 5) (head x) (tail x) := by
    simpa only [hu] using actual_defects x hx hAx
  have hb := normalized_defect_bound (N : ℝ) (j : ℝ) (x 5)
    (by exact_mod_cast hN) (by exact_mod_cast hj) (hx 5) hv (head x) (tail x) hd
  have hmass := actual_mass N j (by omega) hj hj' x
  have hsq := actual_square N j (by omega) hj hj' x
  simp only [hu, one_mul, mul_one] at hmass hsq
  have hcommon : commonEnvelope (N : ℝ) ≤ target N := by
    simpa only [target, bulkValue, bulkIndex] using common_le_integer_bulk N (by omega)
  have hmono := mul_le_mul_of_nonneg_right hcommon
    (sq_nonneg ((N : ℝ)+x 5*(j : ℝ)+H (head x)-D (tail x)))
  apply spectralGood_of_square _ _ (Real.sqrt_nonneg _)
  · exact sum_nonneg (fun k _ => synth_nonneg N j x hx k)
  · rw [Real.sq_sqrt (target_nonneg N), hmass, hsq]
    linarith

-- Homogeneity is implemented on x itself, so row feasibility is preserved.
private theorem small_jump_good (N j : ℕ) (hN : 67 ≤ N) (hj : 6 ≤ j) (hj' : j ≤ N-10)
    (x : Fin 16 → ℝ) (hx : ∀ q, 0 ≤ x q) (hAx : ∀ r, 0 ≤ (A *ᵥ x) r)
    (hv : 2*x 5 ≤ low x) :
    spectralGood (Real.sqrt (target N)) (synth (d := N) (positions N j) x) := by
  have hu0 := low_nonneg x hx
  by_cases hu : low x = 0
  · rw [zero_low x hx hAx hu, map_zero]
    exact spectralGood_zero N _
  · let z : Fin 16 → ℝ := (low x)⁻¹ • x
    have hinv : 0 ≤ (low x)⁻¹ := inv_nonneg.mpr hu0
    have hz : ∀ q, 0 ≤ z q := by
      intro q
      exact mul_nonneg hinv (hx q)
    have hAz : ∀ r, 0 ≤ (A *ᵥ z) r := by
      intro r
      dsimp [z]
      rw [Matrix.mulVec_smul]
      exact mul_nonneg hinv (hAx r)
    have huz : low z = 1 := by
      dsimp [z]
      rw [low_smul, inv_mul_cancel₀ hu]
    have hvz : z 5 ≤ 1/2 := by
      have hm := mul_le_mul_of_nonneg_left hv hinv
      rw [inv_mul_cancel₀ hu] at hm
      change (low x)⁻¹*x 5 ≤ 1/2
      nlinarith only [hm]
    have hg := normalized_cone_good N j hN hj hj' z hz hAz huz hvz
    have hrec : (low x) • z = x := by
      ext q
      dsimp [z]
      simp only [Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hu, one_mul]
    rw [← hrec, map_smul]
    exact spectralGood_smul _ _ _ hu0 hg

def bulk : Fin 16 → ℝ := ![0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,3]

private theorem bulk_rows : A *ᵥ bulk = ![3,0,4] := by
  ext r
  fin_cases r <;> norm_num [A, bulk, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.reduceFinMk, Fin.reduceSucc, Finset.univ_eq_empty, Finset.sum_empty, add_zero]

set_option maxRecDepth 8192 in
theorem bulk_good (N j : ℕ) (hN : 56 ≤ N) (hj : 6 ≤ j) (hj' : j ≤ N-10) :
    spectralGood (Real.sqrt (target N)) (synth (d := N) (positions N j) bulk) := by
  have hm : (∑ k : Fin N, synth (positions N j) bulk k) = 3*(N : ℝ)+2*(j : ℝ) := by
    rw [actual_mass N j hN hj hj']
    simp only [bulk, low, head, tail, H, D, Fin.sum_univ_succ, Fin.reduceFinMk, Fin.reduceSucc, Nat.reduceAdd, Fin.isValue, Matrix.cons_val, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    norm_num
  have hq : (∑ k : Fin N, (synth (positions N j) bulk k)^2) = 9*(N : ℝ)+16*(j : ℝ) := by
    rw [actual_square N j hN hj hj']
    simp only [bulk, low, head, tail, H, D, H2, D2, E, Fin.sum_univ_succ, Fin.reduceFinMk, Fin.reduceSucc, Nat.reduceAdd, Fin.isValue, Matrix.cons_val, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    norm_num <;> ring
  have hden : 0 < 3*(N : ℝ)+2*(j : ℝ) := by
    have hn : (56 : ℝ) ≤ N := by exact_mod_cast hN
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have hmax : (9*(N : ℝ)+16*(j : ℝ))/(3*(N : ℝ)+2*(j : ℝ))^2 ≤ target N := by
    simpa only [bulkValue, bulkIndex, target] using bulk_integer_maximum N j hN
  have hqbound := (div_le_iff₀ (sq_pos_of_pos hden)).mp hmax
  apply spectralGood_of_square _ _ (Real.sqrt_nonneg _)
  · rw [hm]
    exact hden.le
  · rw [Real.sq_sqrt (target_nonneg N), hm, hq]
    exact hqbound

private def alpha (x : Fin 16 → ℝ) : ℝ :=
  min (min (x 5/2) (x 15/3)) (min ((A *ᵥ x) 0/3) ((A *ᵥ x) 2/4))

private theorem alpha_bounds (x : Fin 16 → ℝ)
    (hx : ∀ q, 0 ≤ x q) (hAx : ∀ r, 0 ≤ (A *ᵥ x) r) :
    0 ≤ alpha x ∧ alpha x ≤ x 5/2 ∧ alpha x ≤ x 15/3 ∧
      alpha x ≤ (A *ᵥ x) 0/3 ∧ alpha x ≤ (A *ᵥ x) 2/4 := by
  have h0 : 0 ≤ alpha x := by
    unfold alpha
    exact le_min
      (le_min (div_nonneg (hx 5) (by norm_num)) (div_nonneg (hx 15) (by norm_num)))
      (le_min (div_nonneg (hAx 0) (by norm_num)) (div_nonneg (hAx 2) (by norm_num)))
  have hl := min_le_left (min (x 5/2) (x 15/3))
    (min ((A *ᵥ x) 0/3) ((A *ᵥ x) 2/4))
  have hr := min_le_right (min (x 5/2) (x 15/3))
    (min ((A *ᵥ x) 0/3) ((A *ᵥ x) 2/4))
  exact ⟨h0, hl.trans (min_le_left _ _), hl.trans (min_le_right _ _),
    hr.trans (min_le_left _ _), hr.trans (min_le_right _ _)⟩

private theorem alpha_attained (x : Fin 16 → ℝ) :
    alpha x = x 5/2 ∨ alpha x = x 15/3 ∨
      alpha x = (A *ᵥ x) 0/3 ∨ alpha x = (A *ᵥ x) 2/4 := by
  have hc (a b : ℝ) : min a b = a ∨ min a b = b := by
    rcases le_total a b with hab | hba
    · exact Or.inl (min_eq_left hab)
    · exact Or.inr (min_eq_right hba)
  rcases hc (min (x 5/2) (x 15/3))
      (min ((A *ᵥ x) 0/3) ((A *ᵥ x) 2/4)) with hl | hr
  · rcases hc (x 5/2) (x 15/3) with h5 | h15
    · exact Or.inl (hl.trans h5)
    · exact Or.inr (Or.inl (hl.trans h15))
  · rcases hc ((A *ᵥ x) 0/3) ((A *ᵥ x) 2/4) with h0 | h2
    · exact Or.inr (Or.inr (Or.inl (hr.trans h0)))
    · exact Or.inr (Or.inr (Or.inr (hr.trans h2)))

theorem subtraction_rows (a : ℝ) (x : Fin 16 → ℝ) :
    (A *ᵥ (x-a • bulk)) 0 = (A *ᵥ x) 0-3*a ∧
    (A *ᵥ (x-a • bulk)) 1 = (A *ᵥ x) 1 ∧
    (A *ᵥ (x-a • bulk)) 2 = (A *ᵥ x) 2-4*a := by
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, bulk_rows,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ', Fin.reduceFinMk, Fin.reduceSucc, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  constructor
  · ring
  constructor <;> ring

private theorem residual_feasible (x : Fin 16 → ℝ)
    (hx : ∀ q, 0 ≤ x q) (hAx : ∀ r, 0 ≤ (A *ᵥ x) r) :
    (∀ q, 0 ≤ (x-alpha x • bulk) q) ∧
    (∀ r, 0 ≤ (A *ᵥ (x-alpha x • bulk)) r) ∧
    ((x-alpha x • bulk) 5 = 0 ∨ (x-alpha x • bulk) 15 = 0 ∨
      (A *ᵥ (x-alpha x • bulk)) 0 = 0 ∨ (A *ᵥ (x-alpha x • bulk)) 2 = 0) := by
  obtain ⟨ha, h5, h15, h0, h2⟩ := alpha_bounds x hx hAx
  obtain ⟨hr0, hr1, hr2⟩ := subtraction_rows (alpha x) x
  have hy : ∀ q, 0 ≤ (x-alpha x • bulk) q := by
    intro q
    fin_cases q <;>
      simp only [bulk, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        Fin.reduceFinMk, Fin.reduceSucc, Nat.reduceAdd, Fin.isValue, Matrix.cons_val] <;>
      norm_num <;>
      linarith [hx 0, hx 1, hx 2, hx 3, hx 4, hx 5, hx 6, hx 7,
        hx 8, hx 9, hx 10, hx 11, hx 12, hx 13, hx 14, hx 15]
  have hAy : ∀ r, 0 ≤ (A *ᵥ (x-alpha x • bulk)) r := by
    intro r
    fin_cases r
    · change 0 ≤ (A *ᵥ (x-alpha x • bulk)) 0
      rw [hr0]; linarith
    · change 0 ≤ (A *ᵥ (x-alpha x • bulk)) 1
      rw [hr1]; exact hAx 1
    · change 0 ≤ (A *ᵥ (x-alpha x • bulk)) 2
      rw [hr2]; linarith
  refine ⟨hy, hAy, ?_⟩
  rcases alpha_attained x with he | he | he | he
  · left
    simp only [bulk, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val]
    linarith
  · right; left
    simp only [bulk, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val]
    linarith
  · right; right; left
    rw [hr0]
    linarith
  · right; right; right
    rw [hr2]
    linarith

-- Each attained face implies the same paid region, before normalization.
private theorem four_faces_small (x : Fin 16 → ℝ)
    (hx : ∀ q, 0 ≤ x q) (hAx : ∀ r, 0 ≤ (A *ᵥ x) r)
    (hf : x 5 = 0 ∨ x 15 = 0 ∨ (A *ᵥ x) 0 = 0 ∨ (A *ᵥ x) 2 = 0) :
    2*x 5 ≤ low x := by
  have hd := actual_defects x hx hAx
  have hu := low_nonneg x hx
  have hb := hd.row1
  obtain ⟨_, _, hsub0, hsub2, hlast⟩ := defect_subtotals hd
  obtain ⟨hr0, _, hr2⟩ := actual_row_identities x
  rcases hf with h5 | h15 | h0 | h2
  · rw [h5]
    linarith
  · have he := last_defect_identity x
    rw [h15] at he
    linarith
  · rw [h0] at hr0
    linarith
  · rw [h2] at hr2
    linarith

/-- Unconditional sixteen-slot cone theorem, with the original exact integer
optimizer. Its live mechanism is ordered defects, continuous interval bounds,
homogeneous normalization, attained four-face reduction, and norm addition.
The owner consumes this through its existing private norm_from_fixed_cones. -/
theorem structural_fixed_good (N j : ℕ) (hN : 67 ≤ N) (hj : 6 ≤ j) (hj' : j ≤ N-10)
    (x : Fin 16 → ℝ) (hx : ∀ q, 0 ≤ x q) (hAx : ∀ r, 0 ≤ (A *ᵥ x) r) :
    spectralGood (Real.sqrt (target N)) (synth (d := N) (positions N j) x) := by
  obtain ⟨hy, hAy, hface⟩ := residual_feasible x hx hAx
  have hsmall := four_faces_small (x-alpha x • bulk) hy hAy hface
  have hres := small_jump_good N j hN hj hj' (x-alpha x • bulk) hy hAy hsmall
  have hbulk := bulk_good N j (by omega) hj hj'
  have ha : 0 ≤ alpha x := (alpha_bounds x hx hAx).1
  have hrec : x = (x-alpha x • bulk)+alpha x • bulk := by
    exact (sub_add_cancel x (alpha x • bulk)).symm
  rw [hrec, map_add, map_smul]
  exact spectralGood_add _ _ _ hres (spectralGood_smul _ _ _ ha hbulk)

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
