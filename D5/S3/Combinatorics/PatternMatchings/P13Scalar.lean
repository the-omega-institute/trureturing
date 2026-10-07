/- GID: D5/S3/Combinatorics/PatternMatchings/P13Scalar
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PatternMatchings/P13Scalar
   mirror-E: none(waiver:formal-scalar-series-uniform-annihilation)
   anchors: []
   utility: none
   digest: Finite-coefficient q-series satisfy the exact Phi difference, uniformly annihilate the bulk W family, and define a lawful scalar G. -/

import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.MvPowerSeries.LinearTopology
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace D5.S3.Combinatorics.PatternMatchings.P13Scalar
open scoped BigOperators
abbrev PS := PowerSeries ℚ
local notation "QX" => (PowerSeries.X : PS)

/-- The finite q-Pochhammer denominator, including the empty product. -/
def Den (r : ℕ) : PS := ∏ i ∈ Finset.range r, (1 - QX ^ (i + 1))
@[simp] theorem Den_zero : Den 0 = 1 := by simp [Den]
theorem Den_succ (r : ℕ) : Den (r+1) = Den r * (1-QX^(r+1)) := by
  simp [Den, Finset.prod_range_succ]
@[simp] theorem constantCoeff_Den (r : ℕ) : PowerSeries.constantCoeff (Den r) = 1 := by
  simp [Den]
/-- Inversion is justified by the proved constant coefficient one. -/
def DenInv (r : ℕ) : PS := PowerSeries.invOfUnit (Den r) 1
@[simp] theorem Den_mul_DenInv (r : ℕ) : Den r * DenInv r = 1 := by
  exact PowerSeries.mul_invOfUnit _ _ (by simp)
@[simp] theorem DenInv_mul_Den (r : ℕ) : DenInv r * Den r = 1 := by
  rw [mul_comm]; exact Den_mul_DenInv r

@[simp] theorem DenInv_zero : DenInv 0 = 1 := by
  have h := Den_mul_DenInv 0
  simpa using h
theorem DenInv_succ (r : ℕ) : (1-QX^(r+1))*DenInv (r+1) = DenInv r := by
  calc
    _ = DenInv r * (Den r * (1-QX^(r+1)) * DenInv (r+1)) := by
      rw [← mul_assoc, ← mul_assoc, DenInv_mul_Den]; simp
    _ = _ := by rw [← Den_succ, Den_mul_DenInv, mul_one]

/-- An independent v-series whose coefficients are the explicit denominator inverses. -/
def E : PowerSeries PS := PowerSeries.mk DenInv
local notation "V" => (PowerSeries.X : PowerSeries PS)
theorem E_rescale : PowerSeries.rescale QX E = (1-V)*E := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [E, PowerSeries.coeff_rescale, PowerSeries.coeff_zero_eq_constantCoeff]
  | succ n =>
    simp only [PowerSeries.coeff_rescale, E, PowerSeries.coeff_mk, sub_mul,
      one_mul, map_sub, PowerSeries.coeff_succ_X_mul]
    change QX^(n+1)*DenInv (n+1) = DenInv (n+1)-DenInv n
    linear_combination -DenInv_succ n

/-- The explicit finite convolution, rather than a recurrence definition. -/
def S (k : ℕ) : PS := ∑ r ∈ Finset.range (k+1), DenInv r * DenInv (k-r)
theorem coeff_E_sq (k : ℕ) : PowerSeries.coeff k (E*E) = S k := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [E, S]
@[simp] theorem S_zero : S 0 = 1 := by simp [S]
theorem S_one : (1-QX)*S 1 = 2 := by
  have h : (1-QX)*DenInv 1 = 1 := by simpa using DenInv_succ 0
  have hs : S 1 = 2*DenInv 1 := by simp [S, Finset.sum_range_succ]; ring
  rw [hs]
  linear_combination 2*h

theorem S_recurrence (k : ℕ) :
    (1-QX^(k+2))*S (k+2) = 2*S (k+1)-S k := by
  have hs : PowerSeries.rescale QX (E*E) = (1-2*V+V^2)*(E*E) := by
    rw [map_mul, E_rescale]; ring
  have hs' : PowerSeries.rescale QX (E*E) =
      E*E - (V*(E*E)+V*(E*E)) + V^2*(E*E) := by rw [hs]; ring
  have h := congrArg (PowerSeries.coeff (k+2)) hs'
  simp only [PowerSeries.coeff_rescale, map_add, map_sub,
    PowerSeries.coeff_X_pow_mul', coeff_E_sq] at h
  simp [show 2 ≤ k+2 by omega, show k+2-2=k by omega, coeff_E_sq] at h
  linear_combination -h


/-- Signed q-series coefficients from the finite convolution. -/
def c (k : ℕ) : PS := (-1)^k * QX^(k.choose 2) * S k
@[simp] theorem c_zero : c 0 = 1 := by simp [c]
theorem c_one : (1-QX)*c 1 = -2 := by
  have h := S_one
  simp only [c, pow_one, Nat.choose_eq_zero_of_lt (by omega : 1 < 2), pow_zero, mul_one]
  linear_combination -h

theorem choose_step (k : ℕ) : (k+1).choose 2 = k.choose 2 + k := by
  simpa [Nat.choose_one_right, add_comm] using Nat.choose_succ_succ' k 1

theorem c_recurrence (k : ℕ) :
    (1-QX^(k+2))*c (k+2) = -2*QX^(k+1)*c (k+1)-QX^(2*k+1)*c k := by
  have h := S_recurrence k
  simp only [c, show k+2 = (k+1)+1 by omega, choose_step,
    pow_add, pow_succ]
  rw [show 2*k = k+k by omega, pow_add]
  simp only [pow_succ] at h
  linear_combination (-1 : PS)^k * QX^(k.choose 2) * QX^k * QX^k * QX * h


/-- The x-series with explicit coefficient c_k. -/
def PhiSeries : PowerSeries PS := PowerSeries.mk c

theorem PhiSeries_difference :
    PhiSeries = (1-2*V)*PowerSeries.rescale QX PhiSeries -
      PowerSeries.C QX * V^2 * PowerSeries.rescale (QX^2) PhiSeries := by
  have hform : (1-2*V)*PowerSeries.rescale QX PhiSeries -
      PowerSeries.C QX * V^2 * PowerSeries.rescale (QX^2) PhiSeries =
      PowerSeries.rescale QX PhiSeries -
        (V*PowerSeries.rescale QX PhiSeries + V*PowerSeries.rescale QX PhiSeries) -
        PowerSeries.C QX * (V^2 * PowerSeries.rescale (QX^2) PhiSeries) := by ring
  rw [hform]
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    simp only [map_sub, map_add, PowerSeries.coeff_rescale, PhiSeries,
      PowerSeries.coeff_mk, PowerSeries.coeff_zero_X_mul,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', pow_zero]
    norm_num
  | succ n =>
    cases n with
    | zero =>
      simp only [map_sub, map_add, PowerSeries.coeff_rescale, PhiSeries,
        PowerSeries.coeff_mk, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_X_pow_mul']
      norm_num
      linear_combination c_one
    | succ k =>
      simp only [map_sub, map_add, PowerSeries.coeff_rescale, PhiSeries,
        PowerSeries.coeff_mk, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_X_pow_mul']
      simp [show 2 ≤ k+1+1 by omega, show k+1+1-2 = k by omega]
      have h := c_recurrence k
      rw [show 2*k+1 = 1+2*k by omega, pow_add QX 1 (2*k), pow_mul QX 2 k] at h
      simp only [pow_one] at h
      linear_combination h


/-- The unit used to clear the substitution denominators. -/
def delta : PS := (1-QX)^2
@[simp] theorem constantCoeff_delta : PowerSeries.constantCoeff delta = 1 := by simp [delta]
def deltaInv : PS := PowerSeries.invOfUnit delta 1
@[simp] theorem delta_mul_deltaInv : delta*deltaInv = 1 :=
  PowerSeries.mul_invOfUnit _ _ (by simp)
@[simp] theorem deltaInv_mul_delta : deltaInv*delta = 1 := by
  rw [mul_comm]; exact delta_mul_deltaInv

@[simp] theorem constantCoeff_deltaInv : PowerSeries.constantCoeff deltaInv = 1 := by
  simp [deltaInv]

def point (j : ℕ) : PS := QX^(j+1)*deltaInv
def term (j k : ℕ) : PS := c k * point j ^ k
def termOrder (j k : ℕ) : ℕ := k.choose 2 + (j+1)*k

theorem term_factor (j k : ℕ) : term j k =
    QX^(termOrder j k) * ((-1)^k * S k * deltaInv^k) := by
  simp only [term, c, point, mul_pow, ← pow_mul, termOrder, pow_add]
  ring

theorem index_le_termOrder (j k : ℕ) : k ≤ termOrder j k := by
  unfold termOrder
  nlinarith

theorem coeff_term_eq_zero (j k n : ℕ) (h : n < termOrder j k) :
    PowerSeries.coeff n (term j k) = 0 := by
  rw [term_factor, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

/-- Each coefficient is an explicitly finite sum, without an infinite-sum definition. -/
def Phi (j : ℕ) : PS := PowerSeries.mk fun n =>
  ∑ k ∈ Finset.range (n+1), PowerSeries.coeff n (term j k)

theorem coeff_Phi (j n : ℕ) : PowerSeries.coeff n (Phi j) =
    ∑ k ∈ Finset.range (n+1), PowerSeries.coeff n (term j k) := by simp [Phi]

@[simp] theorem term_zero (j : ℕ) : term j 0 = 1 := by simp [term]
@[simp] theorem constantCoeff_Phi (j : ℕ) : PowerSeries.constantCoeff (Phi j) = 1 := by
  simp [Phi, Finset.sum_range_succ, PowerSeries.coeff_zero_eq_constantCoeff]

-- Only the proof of the finite coefficient identity uses the discrete product topology.
local instance : UniformSpace ℚ := ⊥
local instance : TopologicalSpace ℚ := (inferInstance : UniformSpace ℚ).toTopologicalSpace
open scoped PowerSeries.WithPiTopology

theorem hasSum_term (j : ℕ) : HasSum (term j) (Phi j) := by
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro n
  rw [coeff_Phi]
  apply hasSum_sum_of_ne_finset_zero
  intro k hk
  apply coeff_term_eq_zero
  have := index_le_termOrder j k
  simp only [Finset.mem_range] at hk
  omega

theorem point_hasEval (j : ℕ) : PowerSeries.HasEval (point j) := by
  apply PowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_zero
  simp [point]

def evaluate (a : PS) (ha : PowerSeries.HasEval a) : PowerSeries PS →+* PS :=
  PowerSeries.eval₂Hom (φ := RingHom.id PS) continuous_id ha

@[simp] theorem evaluate_C (a : PS) (ha : PowerSeries.HasEval a) (b : PS) :
    evaluate a ha (PowerSeries.C b) = b := by
  simp [evaluate, PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_C]
@[simp] theorem evaluate_V (a : PS) (ha : PowerSeries.HasEval a) :
    evaluate a ha V = a := by
  simp [evaluate, PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_X]

theorem Phi_eq_evaluate (j : ℕ) : Phi j = evaluate (point j) (point_hasEval j) PhiSeries := by
  simp only [evaluate, PowerSeries.coe_eval₂Hom]
  apply PowerSeries.ext
  intro n
  have he := (PowerSeries.hasSum_eval₂ (φ := RingHom.id PS) continuous_id
    (point_hasEval j) PhiSeries).map (PowerSeries.coeff n)
    (PowerSeries.WithPiTopology.uniformContinuous_coeff (R := ℚ) n).continuous
  have hf : HasSum (fun k => PowerSeries.coeff n (term j k))
      (PowerSeries.coeff n (Phi j)) := by
    simpa only [Function.comp_def] using (hasSum_term j).map (PowerSeries.coeff n)
      (PowerSeries.WithPiTopology.uniformContinuous_coeff (R := ℚ) n).continuous
  apply hf.unique
  simpa [Function.comp_def, PhiSeries, term] using he

theorem evaluate_rescale (a b : PS) (ha : PowerSeries.HasEval a)
    (hba : PowerSeries.HasEval (b*a)) (f : PowerSeries PS) :
    evaluate a ha (PowerSeries.rescale b f) = evaluate (b*a) hba f := by
  simp only [evaluate, PowerSeries.coe_eval₂Hom]
  have h₁ := PowerSeries.hasSum_eval₂ (φ := RingHom.id PS) continuous_id ha
    (PowerSeries.rescale b f)
  have h₂ := PowerSeries.hasSum_eval₂ (φ := RingHom.id PS) continuous_id hba f
  apply h₁.unique
  convert h₂ using 1
  funext k
  simp only [RingHom.id_apply, PowerSeries.coeff_rescale, mul_pow]
  ring


theorem point_succ (j : ℕ) : point (j+1) = QX*point j := by
  simp only [point, pow_succ]; ring
theorem point_add_two (j : ℕ) : point (j+2) = QX^2*point j := by
  simp only [point, pow_succ]; ring

theorem evaluate_rescale_X (j : ℕ) :
    evaluate (point j) (point_hasEval j) (PowerSeries.rescale QX PhiSeries) = Phi (j+1) := by
  have ha : PowerSeries.HasEval (QX*point j) := by
    rw [← point_succ]; exact point_hasEval (j+1)
  rw [evaluate_rescale _ _ _ ha]
  simp only [evaluate, PowerSeries.coe_eval₂Hom]
  rw [← point_succ]
  simpa only [evaluate, PowerSeries.coe_eval₂Hom] using (Phi_eq_evaluate (j+1)).symm

theorem evaluate_rescale_X_sq (j : ℕ) :
    evaluate (point j) (point_hasEval j) (PowerSeries.rescale (QX^2) PhiSeries) = Phi (j+2) := by
  have ha : PowerSeries.HasEval (QX^2*point j) := by
    rw [← point_add_two]; exact point_hasEval (j+2)
  rw [evaluate_rescale _ _ _ ha]
  simp only [evaluate, PowerSeries.coe_eval₂Hom]
  rw [← point_add_two]
  simpa only [evaluate, PowerSeries.coe_eval₂Hom] using (Phi_eq_evaluate (j+2)).symm

theorem Phi_difference_uncleared (j : ℕ) :
    Phi j = (1-2*point j)*Phi (j+1) - QX*point j^2*Phi (j+2) := by
  have h := congrArg (evaluate (point j) (point_hasEval j)) PhiSeries_difference
  simpa only [map_sub, map_mul, map_one, map_ofNat, map_pow, evaluate_V, evaluate_C,
    evaluate_rescale_X, evaluate_rescale_X_sq, ← Phi_eq_evaluate] using h

/-- The exact cleared q-difference, valid in particular for every j ≥ 1. -/
theorem Phi_difference (j : ℕ) :
    delta^2*Phi j = delta*(delta-2*QX^(j+1))*Phi (j+1) -
      QX^(2*j+3)*Phi (j+2) := by
  have hi : delta^2*deltaInv^2 = 1 := by rw [← mul_pow, delta_mul_deltaInv, one_pow]
  rw [Phi_difference_uncleared, point]
  calc
    _ = delta*(delta-2*QX^(j+1)*(delta*deltaInv))*Phi (j+1) -
      QX^(2*j+3)*(delta^2*deltaInv^2)*Phi (j+2) := by
      rw [show 2*j+3 = 1+(j+1)*2 by omega,
        pow_add QX 1 ((j+1)*2), pow_mul QX (j+1) 2, pow_one]
      ring
    _ = _ := by rw [delta_mul_deltaInv, hi]; ring


/-- The section 6 bulk recurrence on an arbitrary ordinary series family. -/
def Bulk (h : ℕ → PS) : Prop := ∀ j : ℕ, 2 ≤ j →
  QX^(j+2)*h (j+1) + (delta-2*QX^(j+1))*h j + QX^j*h (j-1) = 0

def W (h : ℕ → PS) (j : ℕ) : PS :=
  delta*Phi j*h j + QX^j*Phi (j+1)*h (j-1)

/-- This shift is derived from the explicit Phi difference and the bulk equation. -/
theorem W_cleared_shift (h : ℕ → PS) (hb : Bulk h) (j : ℕ) (hj : 2 ≤ j) :
    delta*W h j = -QX^(j+2)*W h (j+1) := by
  have hp := Phi_difference j
  have he : QX^(j+2)*QX^(j+1) = QX^(2*j+3) := by
    rw [← pow_add]; congr 1; omega
  rw [← he] at hp
  have hr := hb j hj
  simp only [W, show j+1-1 = j by omega]
  linear_combination (delta*Phi (j+1))*hr + h j*hp

theorem W_shift (h : ℕ → PS) (hb : Bulk h) (j : ℕ) (hj : 2 ≤ j) :
    W h j = -QX^(j+2)*(deltaInv*W h (j+1)) := by
  calc
    W h j = deltaInv*(delta*W h j) := by
      rw [← mul_assoc, deltaInv_mul_delta, one_mul]
    _ = _ := by rw [W_cleared_shift h hb j hj]; ring

/-- Uniform annihilation at every finite degree, with no premise on a tail. -/
theorem W_uniform_dvd (h : ℕ → PS) (hb : Bulk h) (n j : ℕ) (hj : 2 ≤ j) :
    QX^n ∣ W h j := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
    obtain ⟨u, hu⟩ := ih (j+1) (by omega)
    refine ⟨-QX^(j+1)*deltaInv*u, ?_⟩
    rw [W_shift h hb j hj, hu]
    simp only [pow_succ]
    ring

/-- Actual minimal-solution lemma for any family satisfying the bulk recurrence. -/
theorem minimal_solution (h : ℕ → PS) (hb : Bulk h) (j : ℕ) (hj : 2 ≤ j) :
    delta*Phi j*h j + QX^j*Phi (j+1)*h (j-1) = 0 := by
  change W h j = 0
  apply PowerSeries.ext
  intro n
  have hd := (PowerSeries.X_pow_dvd_iff.mp (W_uniform_dvd h hb (n+1) j hj)) n (by omega)
  simpa using hd

/-- The two explicit series used by the scalar expression. -/
def P : PS := Phi 1
def R : PS := Phi 2
def D : PS := delta*(1-2*QX-QX^2)*P - QX^3*(1+QX)*R
@[simp] theorem constantCoeff_P : PowerSeries.constantCoeff P = 1 := by simp [P]
@[simp] theorem constantCoeff_R : PowerSeries.constantCoeff R = 1 := by simp [R]
@[simp] theorem constantCoeff_D : PowerSeries.constantCoeff D = 1 := by simp [D]


def DInv : PS := PowerSeries.invOfUnit D 1
@[simp] theorem D_mul_DInv : D*DInv = 1 := PowerSeries.mul_invOfUnit _ _ (by simp)
@[simp] theorem DInv_mul_D : DInv*D = 1 := by rw [mul_comm]; exact D_mul_DInv

def G : PS := 1 + QX*(1-QX)^3*P*DInv

theorem G_cleared : (G-1)*D = QX*(1-QX)^3*P := by
  simp only [G, add_sub_cancel_left, mul_assoc, DInv_mul_D, mul_one]

end D5.S3.Combinatorics.PatternMatchings.P13Scalar
