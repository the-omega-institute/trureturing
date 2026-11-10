/- GID: D5/S3/Zeros/LeeYang/FiolDoubleHubSamples
   generality: I
   mirror-B: D5/B/S3/Zeros/LeeYang/FiolDoubleHubSamples
   mirror-E: none(waiver:analytic-family-proof)
   anchors: []
   utility: none
   digest: All-parameter physical double-hub samples identities. -/
import D5.S3.Zeros.LeeYang.FiolDoubleHubRootGeometry
import D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Order.Fin.InsertNth

open scoped BigOperators
open Polynomial Finset
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Zeros.LeeYang
open FiolDoubleHubEndpoint
namespace FiolDoubleHub
private noncomputable def aAngle (d j : ℕ) : ℝ :=
  if Odd d then 2*Real.pi*(j:ℝ)/(d:ℝ) else (2*(j:ℝ)-1)*Real.pi/(d:ℝ)
private noncomputable def bAngle (d j : ℕ) : ℝ :=
  if Odd d then 2*Real.pi*(j:ℝ)/((d:ℝ)+1) else (2*(j:ℝ)-1)*Real.pi/((d:ℝ)+1)

private theorem angle_interlace (d j : ℕ) (hd : 2 ≤ d) (hj : 1 ≤ j) (hjd : 2*j ≤ d) :
    0 < bAngle d j ∧ bAngle d j < aAngle d j ∧
      aAngle d j < bAngle d (j+1) ∧ aAngle d j < Real.pi := by
  have hdp : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hjp : (1:ℝ) ≤ j := by exact_mod_cast hj
  have hjdr : 2*(j:ℝ) ≤ d := by exact_mod_cast hjd
  have hp := Real.pi_pos
  unfold aAngle bAngle
  by_cases ho : Odd d
  · simp only [ho,ite_true,Nat.cast_add,Nat.cast_one]
    have hstrict : 2*j < d := by rw [Nat.odd_iff] at ho; omega
    have hjstrict : 2*(j:ℝ) < d := by exact_mod_cast hstrict
    refine ⟨by positivity,?_,?_,?_⟩
    · apply (div_lt_div_iff₀ (by positivity : (0:ℝ)<(d:ℝ)+1) hdp).mpr
      nlinarith [mul_pos (by linarith : (0:ℝ)<j) hp]
    · apply (div_lt_div_iff₀ hdp (by positivity : (0:ℝ)<(d:ℝ)+1)).mpr
      nlinarith [mul_pos (by linarith : (0:ℝ)<2*(d:ℝ)-2*j) hp]
    · apply (div_lt_iff₀ hdp).mpr
      nlinarith [mul_pos (sub_pos.mpr hjstrict) hp]
  · simp only [ho,ite_false,Nat.cast_add,Nat.cast_one]
    have hnum : 0 < (2*(j:ℝ)-1)*Real.pi := mul_pos (by linarith) hp
    refine ⟨div_pos hnum (by positivity),?_,?_,?_⟩
    · apply (div_lt_div_iff₀ (by positivity : (0:ℝ)<(d:ℝ)+1) hdp).mpr
      nlinarith
    · apply (div_lt_div_iff₀ hdp (by positivity : (0:ℝ)<(d:ℝ)+1)).mpr
      nlinarith [mul_pos (by linarith : (0:ℝ)<2*(d:ℝ)-(2*j-1)) hp]
    · apply (div_lt_iff₀ hdp).mpr
      nlinarith [mul_pos (by linarith : (0:ℝ)<(d:ℝ)-(2*j-1)) hp]

noncomputable def baseSample (d k : ℕ) : ℝ :=
  if k=0 then 0 else if k%2=1 then bAngle d ((k+1)/2) else aAngle d (k/2)

private theorem N_even (d : ℕ) : Even (N d) := by
  by_cases ho : Odd d
  · simp only [N,ho,ite_true]
    rw [Nat.even_iff,Nat.odd_iff] at *
    omega
  · simp only [N,ho,ite_false]
    rw [Nat.even_iff,Nat.odd_iff] at *
    omega

theorem baseSample_succ (d k : ℕ) (hd : 2 ≤ d) (hk : k+1 < N d) :
    baseSample d k < baseSample d (k+1) := by
  have hNd : N d = if Odd d then d+1 else d+2 := rfl
  have hdpar : Odd d ↔ d%2=1 := Nat.odd_iff
  by_cases hz : k=0
  · subst k
    simp only [baseSample,ite_true,Nat.zero_add,Nat.reduceEqDiff,Nat.reduceMod,Nat.reduceDiv,ite_false]
    exact (angle_interlace d 1 hd (by omega) (by omega)).1
  · by_cases ho : k%2=1
    · have he : (k+1)%2 ≠ 1 := by omega
      have hkp : k+1 ≠ 0 := by omega
      have hidx : 1 ≤ (k+1)/2 := by omega
      have hidxd : 2*((k+1)/2) ≤ d := by
        by_cases hod : Odd d <;> simp only [N,hod,ite_true,ite_false] at hk
        · omega
        · rw [Nat.odd_iff] at hod; omega
      simpa only [baseSample,hz,hkp,ho,he,ite_false,ite_true] using
        (angle_interlace d ((k+1)/2) hd hidx hidxd).2.1
    · have he : (k+1)%2=1 := by omega
      have hkp : k+1 ≠ 0 := by omega
      have hidx : 1 ≤ k/2 := by omega
      have hidxd : 2*(k/2) ≤ d := by
        by_cases hod : Odd d <;> simp only [N,hod,ite_true,ite_false] at hk <;> omega
      have hindex : (k+1+1)/2 = k/2+1 := by omega
      simpa only [baseSample,hz,hkp,ho,he,hindex,ite_false,ite_true] using
        (angle_interlace d (k/2) hd hidx hidxd).2.2.1

end FiolDoubleHub

namespace FiolDoubleHub
private theorem phase_zero_angle_pos (d : ℕ) (hd : 2 ≤ d) : 0 < (phaseValue d 0).re := by
  have h := FiolDoubleHub.Q_one_pos d hd
  simpa [phaseValue] using h

private theorem bAngle_sign (d j : ℕ) (hd : 2 ≤ d) (hj : 1 ≤ j)
    (hjd : if Odd d then 2*j ≤ d+1 else 2*j ≤ d+2) :
    if 2*(if Odd d then 2*j else 2*j-1) ≤ d+1 then
      (phaseValue d (bAngle d j)).re < 0
    else 0 < (phaseValue d (bAngle d j)).re := by
  by_cases hlarge : 5 ≤ d
  · by_cases ho : Odd d
    · simp only [ho,ite_true] at hjd ⊢
      have h := odd_b_sign_large d j hlarge ho hj hjd
      simpa only [bAngle,ho,ite_true,show 2*(2*j)=4*j by omega] using h
    · simp only [ho,ite_false] at hjd ⊢
      simpa only [bAngle,ho,ite_false] using even_b_sign_large d j hlarge ho hj hjd
  · have hd4 : d ≤ 4 := by omega
    have hsmall := small_b_grid_values
    have hs5 : (2:ℝ) < Real.sqrt 5 := by
      have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤5)
      have hp := Real.sqrt_nonneg (5:ℝ)
      nlinarith
    have h21 : (phaseValue 2 (Real.pi*(1/3))).re = -21 := by
      rw [show Real.pi*(1/3)=Real.pi/3 by ring,hsmall.1]; norm_num
    have h22 : (phaseValue 2 Real.pi).re = 216 := by rw [hsmall.2.1]; norm_num
    have h31 : (phaseValue 3 (Real.pi*(1/2))).re = -82 := by
      rw [show Real.pi*(1/2)=Real.pi/2 by ring,hsmall.2.2.1]; norm_num
    have h32 : (phaseValue 3 Real.pi).re = 234 := by rw [hsmall.2.2.2.1]; norm_num
    have h41 : (phaseValue 4 (Real.pi*(1/5))).re = 42-69*Real.sqrt 5 := by
      rw [show Real.pi*(1/5)=Real.pi/5 by ring,hsmall.2.2.2.2.1,Complex.ofReal_re]
    have h42 : (phaseValue 4 (Real.pi*(3/5))).re = 42+69*Real.sqrt 5 := by
      rw [show Real.pi*(3/5)=3*Real.pi/5 by ring,hsmall.2.2.2.2.2.1,Complex.ofReal_re]
    have h43 : (phaseValue 4 Real.pi).re = 2952 := by rw [hsmall.2.2.2.2.2.2]; norm_num
    have hj3 : j ≤ 3 := by split_ifs at hjd <;> omega
    interval_cases d <;> norm_num [Nat.odd_iff] at hjd ⊢
    all_goals interval_cases j
    all_goals norm_num [bAngle,Nat.odd_iff] at *
    all_goals simp only [show Real.pi*(1/3)=Real.pi/3 by ring,
      show Real.pi*(1/2)=Real.pi/2 by ring,
      show 2*Real.pi/4=Real.pi/2 by ring,
      show 2*Real.pi*2/4=Real.pi by ring,
      show Real.pi*(1/5)=Real.pi/5 by ring,
      show Real.pi*(3/5)=3*Real.pi/5 by ring] at *
    all_goals linarith

private theorem aAngle_phase_sign (d j : ℕ) (hd : 2 ≤ d) (hj : 1 ≤ j) (hjd : 2*j ≤ d) :
    (aAngle d j < Real.pi/2 → 0 < (phaseValue d (aAngle d j)).re) ∧
    (aAngle d j = Real.pi/2 → (phaseValue d (aAngle d j)).re = 0) ∧
    (Real.pi/2 < aAngle d j → (phaseValue d (aAngle d j)).re < 0) := by
  have hangle := angle_interlace d j hd hj hjd
  have hap : 0 < aAngle d j := hangle.1.trans hangle.2.1
  have hapi : aAngle d j < Real.pi := hangle.2.2.2
  have hdp : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hA : 0 < 2*(d:ℝ)^4 := by positivity
  have ht : 0 < 2-2*Real.cos (aAngle d j) := by
    have hc := Real.strictAntiOn_cos
      (show (0:ℝ) ∈ Set.Icc 0 Real.pi from ⟨le_rfl,Real.pi_pos.le⟩)
      (show aAngle d j ∈ Set.Icc 0 Real.pi from ⟨hap.le,hapi.le⟩) hap
    rw [Real.cos_zero] at hc
    linarith
  have hval : (phaseValue d (aAngle d j)).re =
      2*(d:ℝ)^4*(2*Real.cos (aAngle d j))*(if Odd d then 1 else 2-2*Real.cos (aAngle d j)) := by
    by_cases ho : Odd d
    · have hh := odd_a_phase d j hd ho hj (by rw [Nat.odd_iff] at ho; omega)
      dsimp only at hh
      simp only [aAngle,ho,ite_true] at *
      rw [hh,Complex.ofReal_re,mul_one]
    · have hh := even_a_phase d j hd ho hj hjd
      dsimp only at hh
      simp only [aAngle,ho,ite_false] at *
      rw [hh,Complex.ofReal_re]
  have hfactor : 0 < (if Odd d then 1 else 2-2*Real.cos (aAngle d j)) := by split_ifs <;> positivity
  simp only [hval]
  refine ⟨?_,?_,?_⟩
  · intro h
    have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],h⟩
    exact mul_pos (mul_pos hA (mul_pos (by norm_num) hc)) hfactor
  · intro h
    rw [h,Real.cos_pi_div_two]
    ring
  · intro h
    have hc := Real.cos_neg_of_pi_div_two_lt_of_lt h (by linarith [Real.pi_pos])
    exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hA (mul_neg_of_pos_of_neg (by norm_num) hc)) hfactor

end FiolDoubleHub

namespace FiolDoubleHub
private theorem aAngle_compare (d j : ℕ) (hd : 2 ≤ d) (hj : 1 ≤ j) :
    ((if Odd d then 4*j else 4*j-2) < d → aAngle d j < Real.pi/2) ∧
    (d < (if Odd d then 4*j else 4*j-2) → Real.pi/2 < aAngle d j) ∧
    ((if Odd d then 4*j else 4*j-2) = d → aAngle d j = Real.pi/2) := by
  let k := if Odd d then 4*j else 4*j-2
  have hdp : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have he : aAngle d j = (k:ℝ)*Real.pi/(2*(d:ℝ)) := by
    by_cases ho : Odd d
    · simp only [aAngle,k,ho,ite_true]
      push_cast
      field_simp <;> ring
    · simp only [aAngle,k,ho,ite_false]
      rw [Nat.cast_sub (by omega : 2 ≤ 4*j)]
      push_cast
      field_simp <;> ring
  refine ⟨?_,?_,?_⟩
  · intro h
    have hkr : (k:ℝ) < d := by exact_mod_cast h
    rw [he]
    apply (div_lt_iff₀ (by positivity : (0:ℝ) < 2*(d:ℝ))).mpr
    nlinarith [mul_lt_mul_of_pos_right hkr Real.pi_pos]
  · intro h
    have hkr : (d:ℝ) < k := by exact_mod_cast h
    rw [he]
    apply (lt_div_iff₀ (by positivity : (0:ℝ) < 2*(d:ℝ))).mpr
    nlinarith [mul_lt_mul_of_pos_right hkr Real.pi_pos]
  · intro h
    have hkr : (k:ℝ) = (d:ℝ) := by exact_mod_cast h
    rw [he,hkr]
    field_simp <;> ring

theorem baseSample_signed (d k : ℕ) (hd : 2 ≤ d) (hk : k < N d)
    (hnotzero : ¬(d%4=2 ∧ k=N d/2)) :
    if k < N d/2 then 0 < (-1:ℝ)^k*(phaseValue d (baseSample d k)).re
    else (-1:ℝ)^k*(phaseValue d (baseSample d k)).re < 0 := by
  by_cases hz : k=0
  · subst k
    have hbefore : 0 < N d/2 := by unfold N; split_ifs <;> omega
    simpa only [hbefore,ite_true,pow_zero,one_mul,baseSample,ite_true] using phase_zero_angle_pos d hd
  · by_cases hodd : k%2=1
    · let j := (k+1)/2
      have hj : 1 ≤ j := by dsimp [j]; omega
      have hlegal : if Odd d then 2*j ≤ d+1 else 2*j ≤ d+2 := by
        by_cases ho : Odd d <;> simp only [ho,ite_true,ite_false] <;>
          simp only [N,ho,ite_true,ite_false] at hk <;> dsimp [j] <;> omega
      have hb := bAngle_sign d j hd hj hlegal
      have hcond : 2*(if Odd d then 2*j else 2*j-1) ≤ d+1 ↔ k < N d/2 := by
        by_cases ho : Odd d <;> simp only [N,ho,ite_true,ite_false] <;>
          rw [Nat.odd_iff] at ho <;> dsimp [j] <;> omega
      have hpow : (-1:ℝ)^k = -1 := (Nat.odd_iff.mpr hodd).neg_one_pow
      simp only [baseSample,hz,hodd,ite_false,ite_true,hpow]
      by_cases hbefore : k < N d/2
      · rw [if_pos hbefore]
        rw [if_pos (hcond.mpr hbefore)] at hb
        nlinarith [hb]
      · rw [if_neg hbefore]
        have hnot : ¬ 2*(if Odd d then 2*j else 2*j-1) ≤ d+1 := fun h => hbefore (hcond.mp h)
        rw [if_neg hnot] at hb
        nlinarith [hb]
    · let j := k/2
      have hj : 1 ≤ j := by dsimp [j]; omega
      have hjd : 2*j ≤ d := by
        by_cases ho : Odd d <;> simp only [N,ho,ite_true,ite_false] at hk <;>
          rw [Nat.odd_iff] at ho <;> dsimp [j] <;> omega
      have ha := aAngle_phase_sign d j hd hj hjd
      have hcomp := aAngle_compare d j hd hj
      have hpow : (-1:ℝ)^k = 1 := (show Even k from Nat.even_iff.mpr (by omega)).neg_one_pow
      simp only [baseSample,hz,hodd,ite_false,hpow,one_mul]
      by_cases hbefore : k < N d/2
      · rw [if_pos hbefore]
        apply ha.1
        apply hcomp.1
        by_cases ho : Odd d <;> simp only [N,ho,ite_true,ite_false] at hbefore ⊢
        · dsimp [j]; rw [Nat.odd_iff] at ho; omega
        · dsimp [j]; rw [Nat.odd_iff] at ho; omega
      · rw [if_neg hbefore]
        apply ha.2.2
        apply hcomp.2.1
        by_cases ho : Odd d <;> simp only [N,ho,ite_true,ite_false] at hbefore hnotzero ⊢
        · dsimp [j]; rw [Nat.odd_iff] at ho; omega
        · dsimp [j]; rw [Nat.odd_iff] at ho; omega

end FiolDoubleHub

namespace FiolDoubleHub
noncomputable def insertSample (b : ℕ → ℝ) (mid : ℕ) (c : ℝ) (k : ℕ) : ℝ :=
  if k < mid then b k else if k = mid then c else b (k-1)

theorem insertSample_succ (b : ℕ → ℝ) (n mid : ℕ) (c : ℝ)
    (hm : 0 < mid ∧ mid < n) (hb : ∀ k, k+1 < n → b k < b (k+1))
    (hc : b (mid-1) < c ∧ c < b mid) (k : ℕ) (hk : k < n) :
    insertSample b mid c k < insertSample b mid c (k+1) := by
  by_cases h1 : k+1 < mid
  · simpa only [insertSample,h1,show k<mid by omega,ite_true] using hb k (by omega)
  · by_cases h2 : k+1=mid
    · have h3 : k=mid-1 := by omega
      simp only [insertSample,show k<mid by omega,h2,lt_self_iff_false,ite_true,ite_false]
      simpa only [h3] using hc.1
    · by_cases h3 : k=mid
      · subst k
        simpa only [insertSample,lt_self_iff_false,ite_false,ite_true,
          show ¬mid+1<mid by omega,show mid+1≠mid by omega,Nat.add_sub_cancel] using hc.2
      · have h4 : ¬k<mid := by omega
        have hidx : k-1+1=k := by omega
        simpa only [insertSample,h1,h4,h2,h3,ite_false,Nat.add_sub_cancel,hidx] using hb (k-1) (by omega)

noncomputable def replaceSample (b : ℕ → ℝ) (mid : ℕ) (l r : ℝ) (k : ℕ) : ℝ :=
  if k < mid then b k else if k=mid then l else if k=mid+1 then r else b (k-1)

theorem replaceSample_succ (b : ℕ → ℝ) (n mid : ℕ) (l r : ℝ)
    (hm : 0 < mid ∧ mid+1 < n) (hb : ∀ k, k+1 < n → b k < b (k+1))
    (hc : b (mid-1)<l ∧ l<r ∧ r<b (mid+1)) (k : ℕ) (hk : k < n) :
    replaceSample b mid l r k < replaceSample b mid l r (k+1) := by
  by_cases h1 : k+1 < mid
  · simpa only [replaceSample,h1,show k<mid by omega,ite_true] using hb k (by omega)
  · by_cases h2 : k+1=mid
    · have h3 : k=mid-1 := by omega
      simp only [replaceSample,show k<mid by omega,h2,lt_self_iff_false,ite_true,ite_false]
      simpa only [h3] using hc.1
    · by_cases h3 : k=mid
      · subst k
        simpa only [replaceSample,lt_self_iff_false,ite_false,ite_true,
          show ¬mid+1<mid by omega,show mid+1≠mid by omega] using hc.2.1
      · by_cases h4 : k=mid+1
        · subst k
          simpa only [replaceSample,show ¬mid+1<mid by omega,show ¬mid+1+1<mid by omega,
            show mid+1≠mid by omega,show mid+1+1≠mid by omega,
            show mid+1+1≠mid+1 by omega,ite_false,ite_true,Nat.add_sub_cancel] using hc.2.2
        · have h5 : ¬k<mid := by omega
          have h6 : k+1≠mid+1 := by omega
          have hidx : k-1+1=k := by omega
          simpa only [replaceSample,h1,h5,h2,h3,h4,h6,ite_false,Nat.add_sub_cancel,hidx] using hb (k-1) (by omega)

theorem signed_succ_product (f : ℝ → ℝ) (s : ℕ → ℝ) (k : ℕ)
    (ha : 0 < (-1:ℝ)^k*f (s k)) (hb : 0 < (-1:ℝ)^(k+1)*f (s (k+1))) :
    f (s k)*f (s (k+1)) < 0 := by
  have hsq : ((-1:ℝ)^k)^2=1 := by rw [←pow_mul,Nat.mul_comm]; exact (even_two_mul k).neg_one_pow
  have h := mul_pos ha hb
  have hp : (-1:ℝ)^k*(-1:ℝ)^(k+1) = -1 := by
    rw [pow_succ]
    nlinarith [hsq]
  rw [mul_mul_mul_comm,hp] at h
  nlinarith

theorem insertSample_signed (f : ℝ → ℝ) (b : ℕ → ℝ) (n mid : ℕ) (c : ℝ)
    (hm : 0 < mid ∧ mid < n)
    (hb : ∀ k, k<n → if k<mid then 0<(-1:ℝ)^k*f (b k) else (-1:ℝ)^k*f (b k)<0)
    (hc : 0<(-1:ℝ)^mid*f c) (k : ℕ) (hk : k≤n) :
    0<(-1:ℝ)^k*f (insertSample b mid c k) := by
  by_cases h1 : k<mid
  · have h := hb k (by omega)
    simpa only [insertSample,h1,ite_true] using h
  · by_cases h2 : k=mid
    · subst k
      simpa only [insertSample,lt_self_iff_false,ite_false,ite_true] using hc
    · have hidx : k-1+1=k := by omega
      have h := hb (k-1) (by omega)
      rw [if_neg (show ¬k-1<mid by omega)] at h
      simp only [insertSample,h1,h2,ite_false]
      have hp : (-1:ℝ)^k = -(-1:ℝ)^(k-1) := by
        conv_lhs => rw [←hidx,pow_succ]
        ring
      rw [hp]
      nlinarith

theorem replaceSample_signed (f : ℝ → ℝ) (b : ℕ → ℝ) (n mid : ℕ) (l r : ℝ)
    (hm : 0<mid ∧ mid+1<n) (he : Even mid)
    (hb : ∀ k, k<n → k≠mid → if k<mid then 0<(-1:ℝ)^k*f (b k) else (-1:ℝ)^k*f (b k)<0)
    (hl : 0<f l) (hr : f r<0) (k : ℕ) (hk : k≤n) :
    0<(-1:ℝ)^k*f (replaceSample b mid l r k) := by
  by_cases h1 : k<mid
  · have h := hb k (by omega) (by omega)
    simpa only [replaceSample,h1,ite_true] using h
  · by_cases h2 : k=mid
    · subst k
      simpa only [replaceSample,lt_self_iff_false,ite_false,ite_true,he.neg_one_pow,one_mul] using hl
    · by_cases h3 : k=mid+1
      · subst k
        simp only [replaceSample,show ¬mid+1<mid by omega,show mid+1≠mid by omega,
          ite_false,ite_true,pow_succ,he.neg_one_pow,one_mul]
        linarith
      · have hidx : k-1+1=k := by omega
        have h := hb (k-1) (by omega) (by omega)
        rw [if_neg (show ¬k-1<mid by omega)] at h
        simp only [replaceSample,h1,h2,h3,ite_false]
        have hp : (-1:ℝ)^k = -(-1:ℝ)^(k-1) := by
          conv_lhs => rw [←hidx,pow_succ]
          ring
        rw [hp]
        nlinarith

theorem baseSample_last (d : ℕ) (hd : 2≤d) : baseSample d (N d-1)=Real.pi := by
  have hn : 2≤N d := by unfold N; split_ifs <;> omega
  have he := N_even d
  rw [Nat.even_iff] at he
  have ho : (N d-1)%2=1 := by omega
  have hz : N d-1≠0 := by omega
  simp only [baseSample,hz,ho,ite_false,ite_true,Nat.sub_add_cancel (by omega : 1≤N d)]
  by_cases hodd : Odd d
  · have hj : N d/2=(d+1)/2 := by simp only [N,hodd,ite_true]
    have hcast : ((N d/2:ℕ):ℝ)*2=(d:ℝ)+1 := by
      have hh : N d/2*2=d+1 := by simp only [N,hodd,ite_true] at he ⊢; omega
      exact_mod_cast hh
    simp only [bAngle,hodd,ite_true]
    apply (div_eq_iff (by positivity : (d:ℝ)+1≠0)).mpr
    nlinarith [congrArg (fun x : ℝ => x*Real.pi) hcast]
  · have hcast : 2*((N d/2:ℕ):ℝ)-1=(d:ℝ)+1 := by
      have hh : 2*(N d/2)=d+2 := by simp only [N,hodd,ite_false] at he ⊢; omega
      have h := (show (2:ℝ)*((N d/2:ℕ):ℝ)=(d:ℝ)+2 by exact_mod_cast hh)
      linarith
    simp only [bAngle,hodd,ite_false,hcast]
    field_simp [show (d:ℝ)+1≠0 by positivity] <;> ring

end FiolDoubleHub

namespace FiolDoubleHub
private theorem baseSample_even (d j : ℕ) (hj : 0<j) : baseSample d (2*j)=aAngle d j := by
  simp only [baseSample,show 2*j≠0 by omega,show (2*j)%2≠1 by omega,ite_false,
    show 2*j/2=j by omega]
private theorem baseSample_odd (d j : ℕ) : baseSample d (2*j+1)=bAngle d (j+1) := by
  simp only [baseSample,show 2*j+1≠0 by omega,show (2*j+1)%2=1 by omega,ite_false,ite_true,
    show (2*j+1+1)/2=j+1 by omega]

private theorem bAngle_compare (d j : ℕ) (hd : 2 ≤ d) (hj : 1 ≤ j) :
    ((if Odd d then 4*j else 4*j-2) < d+1 → bAngle d j < Real.pi/2) ∧
    (d+1 < (if Odd d then 4*j else 4*j-2) → Real.pi/2 < bAngle d j) ∧
    ((if Odd d then 4*j else 4*j-2) = d+1 → bAngle d j = Real.pi/2) := by
  let k := if Odd d then 4*j else 4*j-2
  have hdp : (0:ℝ) < (d:ℝ)+1 := by positivity
  have he : bAngle d j = (k:ℝ)*Real.pi/(2*((d:ℝ)+1)) := by
    by_cases ho : Odd d
    · simp only [bAngle,k,ho,ite_true]
      push_cast
      field_simp <;> ring
    · simp only [bAngle,k,ho,ite_false]
      rw [Nat.cast_sub (by omega : 2 ≤ 4*j)]
      push_cast
      field_simp <;> ring
  refine ⟨?_,?_,?_⟩
  · intro h
    have hkr : (k:ℝ) < (d:ℝ)+1 := by exact_mod_cast h
    rw [he]
    apply (div_lt_iff₀ (by positivity : (0:ℝ) < 2*((d:ℝ)+1))).mpr
    nlinarith [mul_lt_mul_of_pos_right hkr Real.pi_pos]
  · intro h
    have hkr : (d:ℝ)+1 < k := by exact_mod_cast h
    rw [he]
    apply (lt_div_iff₀ (by positivity : (0:ℝ) < 2*((d:ℝ)+1))).mpr
    nlinarith [mul_lt_mul_of_pos_right hkr Real.pi_pos]
  · intro h
    have hkr : (k:ℝ) = (d:ℝ)+1 := by exact_mod_cast h
    rw [he,hkr]
    field_simp <;> ring

theorem central_insert_data (d : ℕ) (hd : 2≤d) (hi : d%4≠2) :
    ∃ c : ℝ, baseSample d (N d/2-1)<c ∧ c<baseSample d (N d/2) ∧
      0<(-1:ℝ)^(N d/2)*(phaseValue d c).re := by
  have hr : d%4<4 := Nat.mod_lt d (by norm_num)
  interval_cases hmod : d%4
  · obtain ⟨r,rfl⟩ : ∃ r, d=4*r := ⟨d/4,by omega⟩
    have hrp : 0<r := by omega
    have ho : ¬Odd (4*r) := by rw [Nat.odd_iff]; omega
    have hm : N (4*r)/2=2*r+1 := by simp only [N,ho,ite_false]; omega
    have hl : N (4*r)/2-1=2*r := by omega
    have hsign := phaseValue_half_pi_negative (4*r) hd (by omega)
    refine ⟨Real.pi/2,?_,?_,?_⟩
    · rw [hl,baseSample_even _ _ hrp]
      apply (aAngle_compare _ _ hd (by omega)).1
      simp only [ho,ite_false]; omega
    · rw [hm,baseSample_odd]
      apply (bAngle_compare _ _ hd (by omega)).2.1
      simp only [ho,ite_false]; omega
    · have he : Odd (N (4*r)/2) := by rw [hm,Nat.odd_iff]; omega
      rw [he.neg_one_pow]
      linarith
  · obtain ⟨r,rfl⟩ : ∃ r, d=4*r+1 := ⟨d/4,by omega⟩
    have hrp : 0<r := by omega
    have ho : Odd (4*r+1) := by rw [Nat.odd_iff]; omega
    have hm : N (4*r+1)/2=2*r+1 := by simp only [N,ho,ite_true]; omega
    have hl : N (4*r+1)/2-1=2*r := by omega
    have hsign := phaseValue_half_pi_negative (4*r+1) hd (by omega)
    refine ⟨Real.pi/2,?_,?_,?_⟩
    · rw [hl,baseSample_even _ _ hrp]
      apply (aAngle_compare _ _ hd (by omega)).1
      simp only [ho,ite_true]; omega
    · rw [hm,baseSample_odd]
      apply (bAngle_compare _ _ hd (by omega)).2.1
      simp only [ho,ite_true]; omega
    · have he : Odd (N (4*r+1)/2) := by rw [hm,Nat.odd_iff]; omega
      rw [he.neg_one_pow]
      linarith
  · exact False.elim (hi rfl)
  · obtain ⟨r,rfl⟩ : ∃ r, d=4*r+3 := ⟨d/4,by omega⟩
    have ho : Odd (4*r+3) := by rw [Nat.odd_iff]; omega
    have hm : N (4*r+3)/2=2*(r+1) := by simp only [N,ho,ite_true]; omega
    have hl : N (4*r+3)/2-1=2*r+1 := by omega
    obtain ⟨c,hc1,hc2,hc3⟩ := central_gap_residue_three r
    refine ⟨c,?_,?_,?_⟩
    · rw [hl,baseSample_odd]
      have he := (bAngle_compare (4*r+3) (r+1) hd (by omega)).2.2
      rw [he (by simp only [ho,ite_true]; omega)]
      exact hc1
    · rw [hm,baseSample_even _ _ (by omega)]
      simpa only [aAngle,ho,ite_true,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat] using hc2
    · have he : Even (N (4*r+3)/2) := by rw [hm]; exact even_two_mul _
      simpa only [he.neg_one_pow,one_mul] using hc3

theorem central_replace_data (d : ℕ) (hd : 2≤d) (hi : d%4=2) :
    Even (N d/2) ∧ ∃ l r : ℝ,
      baseSample d (N d/2-1)<l ∧ l<r ∧ r<baseSample d (N d/2+1) ∧
      0<(phaseValue d l).re ∧ (phaseValue d r).re<0 := by
  obtain ⟨q,rfl⟩ : ∃ q,d=4*q+2 := ⟨d/4,by omega⟩
  have ho : ¬Odd (4*q+2) := by rw [Nat.odd_iff]; omega
  have hm : N (4*q+2)/2=2*(q+1) := by simp only [N,ho,ite_false]; omega
  have hl : N (4*q+2)/2-1=2*q+1 := by omega
  have he : N (4*q+2)/2+1=2*(q+1)+1 := by omega
  refine ⟨by rw [hm]; exact even_two_mul _,?_⟩
  have ha : baseSample (4*q+2) (N (4*q+2)/2-1)<Real.pi/2 := by
    rw [hl,baseSample_odd]
    apply (bAngle_compare _ _ hd (by omega)).1
    simp only [ho,ite_false]; omega
  have hb : Real.pi/2<baseSample (4*q+2) (N (4*q+2)/2+1) := by
    rw [he,baseSample_odd]
    apply (bAngle_compare _ _ hd (by omega)).2.1
    simp only [ho,ite_false]; omega
  obtain ⟨l,r,hal,hlc,hcr,hrb,hfl,hfr⟩ := actual_central_two_sides q _ _ ha hb
  exact ⟨l,r,hal,hlc.trans hcr,hrb,hfl,hfr⟩

end FiolDoubleHub

end D5.S3.Zeros.LeeYang
