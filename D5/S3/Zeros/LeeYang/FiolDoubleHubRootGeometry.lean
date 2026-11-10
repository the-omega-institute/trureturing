/- GID: D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry
   generality: I
   mirror-B: D5/B/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry
   mirror-E: none(waiver:analytic-family-proof)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Zeros/LeeYang/FiolDoubleHubSamples.baseSample_signed; premises=D5/S3/Zeros/LeeYang/FiolDoubleHubRootGeometry.small_b_grid_values
   digest: All-parameter physical double-hub rootgeometry identities. -/
import D5.S3.Zeros.LeeYang.FiolDoubleHubPhase
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
-- A sign change is converted to an interior zero, never to an assumed root predicate.
private theorem phase_interior_zero (d : ℕ) (hd : 2 ≤ d) (a b : ℝ)
    (hab : a < b) (hsign : (phaseValue d a).re*(phaseValue d b).re < 0) :
    ∃ c ∈ Set.Ioo a b, phaseValue d c = 0 := by
  have hc : Continuous (fun x => (phaseValue d x).re) :=
    Complex.continuous_re.comp (phaseValue_continuous d)
  have hz : ∃ c ∈ Set.Ioo a b, (phaseValue d c).re = 0 := by
    rcases (mul_neg_iff.mp hsign) with h | h
    · exact intermediate_value_Ioo' hab.le hc.continuousOn ⟨h.2,h.1⟩
    · exact intermediate_value_Ioo hab.le hc.continuousOn ⟨h.1,h.2⟩
  obtain ⟨c,hc,hz⟩ := hz
  refine ⟨c,hc,?_⟩
  apply Complex.ext
  · simpa using hz
  · simpa using phaseValue_real d hd c

theorem exp_upper_injective :
    Set.InjOn (fun x : ℝ => Complex.exp ((x:ℂ)*Complex.I)) (Set.Icc 0 Real.pi) := by
  intro x hx y hy he
  apply Real.injOn_cos hx hy
  have h := congrArg Complex.re he
  simpa only [Complex.exp_ofReal_mul_I_re] using h

theorem roots_from_alternating_samples (d n : ℕ) (hd : 2 ≤ d)
    (s : Fin (n+1) → ℝ) (hmono : StrictMono s)
    (hbound : ∀ j, 0 ≤ s j ∧ s j ≤ Real.pi)
    (hsign : ∀ j : Fin n,
      (phaseValue d (s j.castSucc)).re*(phaseValue d (s j.succ)).re < 0) :
    ∃ theta : Fin n → ℝ,
      (∀ j, s j.castSucc < theta j ∧ theta j < s j.succ) ∧
      StrictMono theta ∧
      (∀ j, 0 < theta j ∧ theta j < Real.pi ∧
        ((Q d).map Complex.ofRealHom).IsRoot (Complex.exp ((theta j:ℂ)*Complex.I))) := by
  have hex : ∀ j : Fin n, ∃ c ∈ Set.Ioo (s j.castSucc) (s j.succ), phaseValue d c = 0 := by
    intro j
    exact phase_interior_zero d hd _ _ (hmono (by simp)) (hsign j)
  choose theta htheta hzero using hex
  refine ⟨theta,htheta,?_,?_⟩
  · intro j k hjk
    have hle : j.succ ≤ k.castSucc := by simpa using (show j.val+1 ≤ k.val by omega)
    have hm : s j.succ ≤ s k.castSucc := hmono.monotone hle
    exact (htheta j).2.trans_le (hm.trans (htheta k).1.le)
  · intro j
    exact ⟨(hbound j.castSucc).1.trans_lt (htheta j).1,
      (htheta j).2.trans_le (hbound j.succ).2,
      (phaseValue_zero_iff d (theta j)).mp (hzero j)⟩


theorem roots_exhausted_by_upper_family (p : Polynomial ℝ) (n : ℕ)
    (hp : p ≠ 0) (hdeg : p.natDegree ≤ 2*n) (r : Fin n → ℂ)
    (hrinj : Function.Injective r) (hrupper : ∀ j, 0 < (r j).im)
    (hrroot : ∀ j, (p.map Complex.ofRealHom).IsRoot (r j)) :
    (p.map Complex.ofRealHom).roots =
      Finset.univ.val.map r + Finset.univ.val.map (fun j => star (r j)) ∧
    (p.map Complex.ofRealHom).roots.Nodup := by
  classical
  let roots := Finset.univ.val.map r + Finset.univ.val.map (fun j => star (r j))
  have hmap : p.map Complex.ofRealHom ≠ 0 :=
    (Polynomial.map_eq_zero_iff Complex.ofReal_injective).not.mpr hp
  have hconj : ∀ j, (p.map Complex.ofRealHom).IsRoot (star (r j)) := by
    intro j
    have h := hrroot j
    simp only [Polynomial.IsRoot,Polynomial.eval_map] at h ⊢
    have hc := Polynomial.aeval_conj p (r j)
    change p.eval₂ Complex.ofRealHom (star (r j)) =
      star (p.eval₂ Complex.ofRealHom (r j)) at hc
    rw [hc,h,star_zero]
  have hn : roots.Nodup := by
    apply Multiset.nodup_add.mpr
    refine ⟨Finset.univ.nodup.map hrinj,
      Finset.univ.nodup.map (star_injective.comp hrinj),?_⟩
    apply Multiset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨j,_,hj⟩ := Multiset.mem_map.mp hz
    obtain ⟨k,_,hk⟩ := Multiset.mem_map.mp hz'
    have h := congrArg Complex.im (hj.trans hk.symm)
    change (r j).im = -(r k).im at h
    linarith [hrupper j,hrupper k]
  have hle : roots ≤ (p.map Complex.ofRealHom).roots := by
    apply (Multiset.le_iff_subset hn).mpr
    intro z hz
    apply (Polynomial.mem_roots hmap).mpr
    rcases Multiset.mem_add.mp hz with hz | hz
    · obtain ⟨j,_,rfl⟩ := Multiset.mem_map.mp hz
      exact hrroot j
    · obtain ⟨j,_,rfl⟩ := Multiset.mem_map.mp hz
      exact hconj j
  have hcard : roots.card = 2*n := by simp [roots]; omega
  have he : roots = (p.map Complex.ofRealHom).roots := by
    apply Multiset.eq_of_le_of_card_le hle
    rw [hcard]
    exact (Polynomial.card_roots_map_le_natDegree p).trans hdeg
  exact ⟨he.symm,he ▸ hn⟩

end FiolDoubleHub

namespace FiolDoubleHub
private theorem ep_half_pi : ep (Real.pi/2) = Complex.I := by
  simp [ep,Complex.exp_ofReal_mul_I]

private theorem ep_neg_half_pi : ep (-Real.pi/2) = -Complex.I := by
  simp [ep,Complex.exp_ofReal_mul_I]

private theorem phaseValue_half_pi (d : ℕ) :
    phaseValue d (Real.pi/2) =
      if d%4 = 0 then ((-(4*(8*(d:ℝ)*(2*d-1))+8*(16*((d:ℝ)-1))+72):ℝ):ℂ)
      else if d%4 = 1 then ((-(2*(8*(d:ℝ)*(2*d-1))+2*(16*((d:ℝ)-1))+18):ℝ):ℂ)
      else if d%4 = 2 then 0 else ((-2*(16*((d:ℝ)-1))-18:ℝ):ℂ) := by
  have he : phaseValue d (Real.pi/2) =
      (-Complex.I)^N d * (Q d).eval₂ Complex.ofRealHom Complex.I := by
    unfold phaseValue
    have hp : Complex.exp (-((N d:ℕ):ℂ)*((Real.pi/2:ℝ):ℂ)*Complex.I) =
        (-Complex.I)^N d := by
      have hh : ep ((-Real.pi/2)*(N d:ℝ)) = (-Complex.I)^N d := by
        rw [← ep_pow,ep_neg_half_pi]
      convert hh using 1 <;> unfold ep <;> congr 1 <;> push_cast <;> ring
    rw [hp]
    change _ * (Q d).eval₂ Complex.ofRealHom (ep (Real.pi/2)) = _
    rw [ep_half_pi]
  have hp : (-Complex.I)^N d = (-Complex.I)^(N d%4) := by
    conv_lhs => rw [← Nat.mod_add_div (N d) 4]
    rw [pow_add,pow_mul]
    norm_num
  have ho : Odd d ↔ d%4=1 ∨ d%4=3 := by rw [Nat.odd_iff]; omega
  have hn : N d%4 = if d%4=0 ∨ d%4=1 then 2 else 0 := by
    unfold N
    split_ifs <;> rw [Nat.odd_iff] at * <;> omega
  rw [he,hp,hn,Q_eval_I]
  have hm : d%4 < 4 := Nat.mod_lt d (by norm_num)
  interval_cases hd : d%4 <;> norm_num [hd,pow_succ,Complex.I_sq] <;> push_cast <;> ring

theorem phaseValue_half_pi_negative (d : ℕ) (hd : 2 ≤ d) (hi : d%4 ≠ 2) :
    (phaseValue d (Real.pi/2)).re < 0 := by
  rw [phaseValue_half_pi]
  have hx : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hE : 0 < 8*(d:ℝ)*(2*d-1) := by
    have h1 : 0 < (d:ℝ) := by linarith
    have h2 : 0 < 2*(d:ℝ)-1 := by linarith
    positivity
  have hG : 0 < 16*((d:ℝ)-1) := by linarith
  split_ifs <;> simp only [Complex.ofReal_re] <;> first | contradiction | linarith

end FiolDoubleHub

namespace FiolDoubleHub
theorem small_b_grid_values :
    phaseValue 2 (Real.pi/3) = -21 ∧ phaseValue 2 Real.pi = 216 ∧
    phaseValue 3 (Real.pi/2) = -82 ∧ phaseValue 3 Real.pi = 234 ∧
    phaseValue 4 (Real.pi/5) = ((42-69*Real.sqrt 5:ℝ):ℂ) ∧
    phaseValue 4 (3*Real.pi/5) = ((42+69*Real.sqrt 5:ℝ):ℂ) ∧
    phaseValue 4 Real.pi = 2952 := by
  have h21 := even_b_phase 2 1 (by norm_num) (by norm_num [Nat.odd_iff]) (by omega) (by omega)
  have h22 := even_b_phase 2 2 (by norm_num) (by norm_num [Nat.odd_iff]) (by omega) (by omega)
  have h31 := odd_b_phase 3 1 (by norm_num) (by norm_num [Nat.odd_iff]) (by omega) (by omega)
  have h32 := odd_b_phase 3 2 (by norm_num) (by norm_num [Nat.odd_iff]) (by omega) (by omega)
  have h41 := even_b_phase 4 1 (by norm_num) (by norm_num [Nat.odd_iff]) (by omega) (by omega)
  have h42 := even_b_phase 4 2 (by norm_num) (by norm_num [Nat.odd_iff]) (by omega) (by omega)
  have h43 := even_b_phase 4 3 (by norm_num) (by norm_num [Nat.odd_iff]) (by omega) (by omega)
  dsimp only at h21 h22 h31 h32 h41 h42 h43
  norm_num only [Nat.cast_ofNat] at h21 h22 h31 h32 h41 h42 h43
  rw [show 1*Real.pi/3=Real.pi/3 by ring,Real.cos_pi_div_three] at h21
  rw [show 3*Real.pi/3=Real.pi by ring,Real.cos_pi] at h22
  rw [show 2*Real.pi*1/4=Real.pi/2 by ring,Real.cos_pi_div_two] at h31
  rw [show 2*Real.pi*2/4=Real.pi by ring,Real.cos_pi] at h32
  rw [show 1*Real.pi/5=Real.pi/5 by ring,Real.cos_pi_div_five] at h41
  rw [show 3*Real.pi/5=3*Real.pi/5 by ring] at h42
  rw [show 5*Real.pi/5=Real.pi by ring,Real.cos_pi] at h43
  have hs : (Real.sqrt 5)^2 = 5 := Real.sq_sqrt (by norm_num)
  have hc : 2*Real.cos (3*Real.pi/5) = (1-Real.sqrt 5)/2 := by
    rw [show 3*Real.pi/5=Real.pi-2*(Real.pi/5) by ring,Real.cos_pi_sub,
      Real.cos_two_mul,Real.cos_pi_div_five]
    nlinarith
  rw [hc] at h42
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · norm_num [fValue] at h21; exact h21
  · norm_num [fValue] at h22; exact h22
  · norm_num [fValue] at h31; exact h31
  · norm_num [fValue] at h32; exact h32
  · rw [h41]
    congr 1
    unfold fValue
    linear_combination ((591-87*Real.sqrt 5)/8)*hs
  · rw [h42]
    congr 1
    unfold fValue
    linear_combination ((591+87*Real.sqrt 5)/8)*hs
  · norm_num [fValue] at h43; exact h43

end FiolDoubleHub

namespace FiolDoubleHub
-- Reuse the sealed uniform analytic bound on the actual integer-angle grid.
private theorem fValue_integer_grid_sign (d k : ℕ) (hd : 5 ≤ d)
    (hk : 1 ≤ k) (hkd : k ≤ d+1) :
    if 2*k ≤ d+1 then
      fValue (d:ℝ) (2*Real.cos ((k:ℝ)*Real.pi/((d:ℝ)+1))) < 0
    else 0 < fValue (d:ℝ) (2*Real.cos ((k:ℝ)*Real.pi/((d:ℝ)+1))) := by
  exact actual_grid_sign d k hd hk hkd

theorem odd_b_sign_large (d j : ℕ) (hd : 5 ≤ d) (ho : Odd d)
    (hj : 1 ≤ j) (hjd : 2*j ≤ d+1) :
    let b := 2*Real.pi*(j:ℝ)/((d:ℝ)+1)
    if 4*j ≤ d+1 then (phaseValue d b).re < 0 else 0 < (phaseValue d b).re := by
  dsimp only
  have hv := odd_b_phase d j (by omega) ho hj hjd
  dsimp only at hv
  rw [hv,Complex.ofReal_re]
  have hh := fValue_integer_grid_sign d (2*j) hd (by omega) hjd
  convert hh using 1 <;> first | omega | congr 2 <;> push_cast <;> ring

theorem even_b_sign_large (d j : ℕ) (hd : 5 ≤ d) (ho : ¬ Odd d)
    (hj : 1 ≤ j) (hjd : 2*j ≤ d+2) :
    let b := (2*(j:ℝ)-1)*Real.pi/((d:ℝ)+1)
    if 2*(2*j-1) ≤ d+1 then (phaseValue d b).re < 0 else 0 < (phaseValue d b).re := by
  dsimp only
  let b := (2*(j:ℝ)-1)*Real.pi/((d:ℝ)+1)
  have hv := even_b_phase d j (by omega) ho hj hjd
  change phaseValue d b = _ at hv
  rw [hv,Complex.ofReal_re]
  have hh := fValue_integer_grid_sign d (2*j-1) hd (by omega) (by omega)
  have hangle : ((2*j-1:ℕ):ℝ)*Real.pi/((d:ℝ)+1) = b := by
    dsimp [b]
    rw [Nat.cast_sub (by omega : 1 ≤ 2*j)]
    push_cast
    ring
  rw [hangle] at hh
  have hbp : 0 < b := by
    dsimp [b]
    apply div_pos
    · apply mul_pos _ Real.pi_pos
      have h : (1:ℝ) ≤ j := by exact_mod_cast hj
      linarith
    · positivity
  have hble : b ≤ Real.pi := by
    dsimp [b]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<(d:ℝ)+1)).mpr
    have h : 2*(j:ℝ) ≤ (d:ℝ)+2 := by exact_mod_cast hjd
    nlinarith [Real.pi_pos]
  have ht : 0 < 2-2*Real.cos b := by
    have hc := Real.strictAntiOn_cos (show (0:ℝ) ∈ Set.Icc 0 Real.pi by simp [Real.pi_pos.le])
      (show b ∈ Set.Icc 0 Real.pi from ⟨hbp.le,hble⟩) hbp
    rw [Real.cos_zero] at hc
    linarith
  split_ifs with hcond
  · rw [if_pos hcond] at hh
    exact mul_neg_of_pos_of_neg ht hh
  · rw [if_neg hcond] at hh
    exact mul_pos ht hh

end FiolDoubleHub

open Filter Topology
namespace FiolDoubleHub
theorem actual_central_derivative (r : ℕ) :
    HasDerivAt (fun theta : ℝ => (phaseValue (4*r+2) theta).re)
      (-8*(4*(r:ℝ)+2)^4-16*(4*(r:ℝ)+2)^2*(2*(4*(r:ℝ)+2)-1)) (Real.pi/2) := by
  have h := FiolDoubleHubCentral.central_derivative r
  have heq : (fun theta : ℝ => (phaseValue (4*r+2) theta).re) =ᶠ[nhds (Real.pi/2)]
      FiolDoubleHubCentral.F (4*(r:ℝ)+2) := by
    have hnh : Set.Ioo (0:ℝ) Real.pi ∈ nhds (Real.pi/2) :=
      isOpen_Ioo.mem_nhds ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩
    filter_upwards [hnh] with theta htheta
    have hs : Real.sin (theta/2) ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [htheta.1])
        (by linarith [htheta.2,Real.pi_pos]))
    have hphase := Q_phase_reduced (4*r+2) (by omega) theta hs
    dsimp only at hphase
    rw [hphase,Complex.ofReal_re]
    have ho : ¬ Odd (4*r+2) := by rw [Nat.odd_iff]; omega
    unfold realVal fValue
    simp only [ho,ite_false,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_zero,add_zero]
    change _ =
      (2*(4*(r:ℝ)+2)^4)*(2*Real.cos theta)*(2*Real.cos (((4*(r:ℝ)+2)+1)*theta/2))^2 +
      (2*Real.cos (theta/2))*
        ((((3/2:ℝ)*(4*(r:ℝ)+2)^2*((4*(r:ℝ)+2)^2-1))+
          4*(4*(r:ℝ)+2)*((4*(r:ℝ)+2)-1)*(2*(4*(r:ℝ)+2)-1)+
          8*(4*(r:ℝ)+2)*(2*(4*(r:ℝ)+2)-1))*(2*Real.cos theta)-
          8*(4*(r:ℝ)+2)*(2*(4*(r:ℝ)+2)-1))*
          (2*Real.cos ((4*(r:ℝ)+2)*theta/2))*(2*Real.cos (((4*(r:ℝ)+2)+1)*theta/2)) +
      ((4*(4*(r:ℝ)+2)^2+6*(4*(r:ℝ)+2)-1)*(2*Real.cos theta)^2-
        ((3*(4*(r:ℝ)+2)^4-19*(4*(r:ℝ)+2)^2+8*(4*(r:ℝ)+2)+8)/2)*(2*Real.cos theta)-
        (32*(4*(r:ℝ)+2)-14))*(2*Real.cos ((4*(r:ℝ)+2)*theta/2))^2
    norm_num only [Nat.cast_one] <;> ring
  convert h.2.congr_of_eventuallyEq heq using 1
  change -8*(4*(r:ℝ)+2)^4-16*(4*(r:ℝ)+2)^2*(2*(4*(r:ℝ)+2)-1) =
    -4*(2*(4*(r:ℝ)+2)^4)-2*(4*(r:ℝ)+2)*(8*(4*(r:ℝ)+2)*(2*(4*(r:ℝ)+2)-1))
  ring

private theorem negative_derivative_two_sides (f : ℝ → ℝ) (x v a b : ℝ)
    (hf : HasDerivAt f v x) (hv : v < 0) (hz : f x = 0) (ha : a < x) (hb : x < b) :
    ∃ l r : ℝ, a < l ∧ l < x ∧ x < r ∧ r < b ∧ 0 < f l ∧ f r < 0 := by
  have hs : ∀ᶠ y in nhdsWithin x ({x}ᶜ), slope f x y < 0 :=
    hf.tendsto_slope.eventually (eventually_lt_nhds hv)
  have hleft : ∀ᶠ y in nhdsWithin x (Set.Iio x), slope f x y < 0 :=
    hs.filter_mono (nhdsWithin_mono _ (by intro y hy; simpa using ne_of_lt hy))
  have hright : ∀ᶠ y in nhdsWithin x (Set.Ioi x), slope f x y < 0 :=
    hs.filter_mono (nhdsWithin_mono _ (by intro y hy; simpa using ne_of_gt hy))
  have hal : ∀ᶠ y in nhdsWithin x (Set.Iio x), a < y :=
    (eventually_gt_nhds ha).filter_mono nhdsWithin_le_nhds
  have hrb : ∀ᶠ y in nhdsWithin x (Set.Ioi x), y < b :=
    (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds
  obtain ⟨l,hsl,hal,hxl⟩ := (hleft.and (hal.and self_mem_nhdsWithin)).exists
  obtain ⟨r,hsr,hrb,hxr⟩ := (hright.and (hrb.and self_mem_nhdsWithin)).exists
  refine ⟨l,r,hal,hxl,hxr,hrb,?_,?_⟩
  · rw [slope_def_field,hz,sub_zero] at hsl
    rcases div_neg_iff.mp hsl with h | h <;> linarith
  · rw [slope_def_field,hz,sub_zero] at hsr
    rcases div_neg_iff.mp hsr with h | h <;> linarith

theorem actual_central_two_sides (r : ℕ) (a b : ℝ)
    (ha : a < Real.pi/2) (hb : Real.pi/2 < b) :
    ∃ l q : ℝ, a < l ∧ l < Real.pi/2 ∧ Real.pi/2 < q ∧ q < b ∧
      0 < (phaseValue (4*r+2) l).re ∧ (phaseValue (4*r+2) q).re < 0 := by
  apply negative_derivative_two_sides _ _ _ a b (actual_central_derivative r) _ _ ha hb
  · have hd : 0 < 4*(r:ℝ)+2 := by positivity
    have he : 0 < 2*(4*(r:ℝ)+2)-1 := by nlinarith [(Nat.cast_nonneg r : (0:ℝ) ≤ (r:ℝ))]
    have h1 : 0 < 8*(4*(r:ℝ)+2)^4 := by positivity
    have h2 : 0 < 16*(4*(r:ℝ)+2)^2*(2*(4*(r:ℝ)+2)-1) := by positivity
    linarith
  · rw [phaseValue_half_pi]
    norm_num [Nat.add_mod,Nat.mul_mod]

end FiolDoubleHub

namespace FiolDoubleHub
private noncomputable def gValue (d t : ℝ) : ℝ :=
  fValue d t + (2*d^4-(3/2:ℝ)*d^2*(d^2-1)-4*d*(d-1)*(2*d-1)-8*d*(2*d-1))*t*(t+2)+
    8*d*(2*d-1)*(t+2)

private theorem gValue_pos (d t : ℝ) (hd : 2 ≤ d) (ht : -2 ≤ t ∧ t ≤ 0) : 0 < gValue d t := by
  have hdpos : 0 < d := by linarith
  let a := (4*d^2+6*d-1) +
    (2*d^4-(3/2:ℝ)*d^2*(d^2-1)-4*d*(d-1)*(2*d-1)-8*d*(2*d-1))
  let b := (d^4+32*d^3-41*d^2+8*d+8)/2
  let c := 16*d*(2*d-3)+14
  have hb : 0 < b := by
    have hp := mul_pos (show 0 < d^2 by positivity)
      (show 0 < d^2+32*d-41 by nlinarith [sq_nonneg d])
    dsimp [b]; nlinarith
  have hc : 0 < c := by
    have hp := mul_pos (show 0 < d by linarith) (show 0 < 2*d-3 by linarith)
    dsimp [c]; nlinarith
  have hend : 0 < 4*a+2*b+c := by
    have hp := mul_nonneg (sq_nonneg d) (show 0 ≤ d^2-1 by nlinarith)
    dsimp [a,b,c]; nlinarith
  have heq : gValue d t = a*t^2-b*t+c := by dsimp [gValue,fValue,a,b,c]; ring
  rw [heq]
  by_cases ha : 0 ≤ a
  · have h1 := mul_nonneg ha (sq_nonneg t)
    have h2 := mul_nonneg hb.le (neg_nonneg.mpr ht.2)
    nlinarith
  · have hchord : a*t^2-b*t+c - ((-t/2)*(4*a+2*b+c)+(1+t/2)*c) = a*t*(t+2) := by ring
    have hcurv : 0 ≤ a*t*(t+2) :=
      mul_nonneg (mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge ha) ht.2) (by linarith)
    have hq' := mul_nonneg (show 0 ≤ 1+t/2 by linarith) hc.le
    by_cases hz : t = 0
    · simpa [hz] using hc
    · have hstrict := mul_pos (show 0 < -t/2 by grind) hend
      linarith

private theorem realVal_joint_nonzero (d : ℕ) (ho : Odd d) (theta : ℝ)
    (hs : Real.sin (theta/2) ≠ 0) :
    ¬ (realVal d 0 theta = 0 ∧ realVal d 1 theta = 0) := by
  intro h
  simp only [realVal,ho,ite_true,Nat.cast_add,Nat.cast_zero,Nat.cast_one,add_zero] at h
  have hu : Real.sin ((d:ℝ)*theta/2) = 0 := (div_eq_zero_iff.mp h.1).resolve_right hs
  have hv : Real.sin (((d:ℝ)+1)*theta/2) = 0 := (div_eq_zero_iff.mp h.2).resolve_right hs
  rw [show ((d:ℝ)+1)*theta/2=(d:ℝ)*theta/2+theta/2 by ring,Real.sin_add,hu,zero_mul,zero_add] at hv
  have hc : Real.cos ((d:ℝ)*theta/2) = 0 := (mul_eq_zero.mp hv).resolve_right hs
  have hh := Real.sin_sq_add_cos_sq ((d:ℝ)*theta/2)
  rw [hu,hc] at hh
  norm_num at hh

private theorem phase_gap_positive (d : ℕ) (hd : 2 ≤ d) (theta : ℝ)
    (htheta : Real.pi/2 < theta ∧ theta < Real.pi)
    (hu : realVal d 0 theta ≠ 0)
    (hv : realVal d 1 theta = -(2*Real.cos (theta/2))*realVal d 0 theta) :
    0 < (phaseValue d theta).re := by
  have hs : Real.sin (theta/2) ≠ 0 := ne_of_gt
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [htheta.1,Real.pi_pos])
      (by linarith [htheta.2,Real.pi_pos]))
  have hred := Q_phase_reduced d hd theta hs
  dsimp only at hred
  rw [hred,Complex.ofReal_re,hv]
  have hell : (2*Real.cos (theta/2))^2 = 2*Real.cos theta+2 := by
    nth_rw 2 [show theta=2*(theta/2) by ring]
    rw [Real.cos_two_mul]
    ring
  have he :
      2*(d:ℝ)^4*(2*Real.cos theta)*(-(2*Real.cos (theta/2))*realVal d 0 theta)^2 +
        (2*Real.cos (theta/2))*(((3/2:ℝ)*(d:ℝ)^2*((d:ℝ)^2-1)+
          4*(d:ℝ)*(d-1)*(2*d-1)+8*(d:ℝ)*(2*d-1))*(2*Real.cos theta)-8*(d:ℝ)*(2*d-1))*
          realVal d 0 theta*(-(2*Real.cos (theta/2))*realVal d 0 theta)+
        fValue (d:ℝ) (2*Real.cos theta)*realVal d 0 theta^2 =
        gValue (d:ℝ) (2*Real.cos theta)*realVal d 0 theta^2 := by
    unfold gValue
    linear_combination ((2*(d:ℝ)^4-(3/2:ℝ)*(d:ℝ)^2*((d:ℝ)^2-1)-
      4*(d:ℝ)*(d-1)*(2*d-1)-8*(d:ℝ)*(2*d-1))*(2*Real.cos theta)+8*(d:ℝ)*(2*d-1))*
        realVal d 0 theta^2*hell
  rw [he]
  apply mul_pos
  · apply gValue_pos (d:ℝ) _ (by exact_mod_cast hd)
    constructor
    · nlinarith [Real.neg_one_le_cos theta]
    · have h := Real.cos_nonpos_of_pi_div_two_le_of_le htheta.1.le
        (by linarith [htheta.2,Real.pi_pos])
      linarith
  · exact sq_pos_of_ne_zero hu

theorem central_gap_residue_three (r : ℕ) :
    ∃ c : ℝ, Real.pi/2 < c ∧ c < 2*Real.pi*((r:ℝ)+1)/(4*(r:ℝ)+3) ∧
      0 < (phaseValue (4*r+3) c).re := by
  let d := 4*r+3
  let a := 2*Real.pi*((r:ℝ)+1)/(4*(r:ℝ)+3)
  have hd : 2 ≤ d := by dsimp [d]; omega
  have ho : Odd d := by dsimp [d]; rw [Nat.odd_iff]; omega
  have hdp : (0:ℝ) < 4*(r:ℝ)+3 := by positivity
  have hba : Real.pi/2 < a := by
    dsimp [a]; apply (lt_div_iff₀ hdp).mpr; nlinarith [Real.pi_pos]
  have hap : a < Real.pi := by
    dsimp [a]; apply (div_lt_iff₀ hdp).mpr
    nlinarith [Real.pi_pos,mul_nonneg (show (0:ℝ) ≤ (r:ℝ) by positivity) Real.pi_pos.le]
  have hva := odd_a_values d (r+1) hd ho (by omega) (by dsimp [d]; omega)
  have hvb := odd_b_values d (r+1) hd ho (by omega) (by dsimp [d]; omega)
  have heqa : 2*Real.pi*((r+1:ℕ):ℝ)/(d:ℝ) = a := by dsimp [a,d]; push_cast; ring
  have heqb : 2*Real.pi*((r+1:ℕ):ℝ)/((d:ℝ)+1) = Real.pi/2 := by
    dsimp [d]; push_cast; field_simp <;> ring
  dsimp only at hva hvb
  rw [heqa] at hva
  rw [heqb] at hvb
  let z := fun theta : ℝ => (-1:ℝ)^r *
    (realVal d 1 theta+2*Real.cos (theta/2)*realVal d 0 theta)
  have hsig : ((-1:ℝ)^r)^2 = 1 := by rw [← pow_mul,Nat.mul_comm]; exact (even_two_mul r).neg_one_pow
  have hza : z a = -1 := by
    dsimp [z]; rw [hva.1,hva.2,pow_succ]
    nlinarith [hsig]
  have hzb : z (Real.pi/2) = Real.sqrt 2 := by
    dsimp [z]; rw [hvb.1,hvb.2,show Real.pi/2/2=Real.pi/4 by ring,Real.cos_pi_div_four]
    rw [show r+1+1=r+2 by omega,pow_add]
    norm_num
    nlinarith [congrArg (fun x : ℝ => Real.sqrt 2*x) hsig]
  have hsin : ∀ theta ∈ Set.Icc (Real.pi/2) a, Real.sin (theta/2) ≠ 0 := by
    intro theta htheta
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [htheta.1,Real.pi_pos])
      (by linarith [htheta.2,hap,Real.pi_pos]))
  have hcont (k : ℕ) : ContinuousOn (realVal d k) (Set.Icc (Real.pi/2) a) := by
    change ContinuousOn (fun theta => realVal d k theta) _
    simp only [realVal,ho,ite_true]
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · exact hsin
  have hzcont : ContinuousOn z (Set.Icc (Real.pi/2) a) := by
    dsimp [z]
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.add (hcont 1)
    exact (show ContinuousOn (fun x : ℝ => 2*Real.cos (x/2)) _ by fun_prop).mul (hcont 0)
  have hex := intermediate_value_Ioo' hba.le hzcont
  rw [hza,hzb] at hex
  obtain ⟨c,hc,hzc⟩ := hex ⟨by norm_num,Real.sqrt_pos.mpr (by norm_num)⟩
  have hsig0 : (-1:ℝ)^r ≠ 0 := pow_ne_zero _ (by norm_num)
  have hzc' : realVal d 1 c+2*Real.cos (c/2)*realVal d 0 c = 0 :=
    (mul_eq_zero.mp hzc).resolve_left hsig0
  have hs : Real.sin (c/2) ≠ 0 := hsin c ⟨hc.1.le,hc.2.le⟩
  have hu : realVal d 0 c ≠ 0 := by
    intro hu
    have hv : realVal d 1 c = 0 := by simpa only [hu,mul_zero,add_zero] using hzc'
    exact realVal_joint_nonzero d ho c hs ⟨hu,hv⟩
  refine ⟨c,hc.1,hc.2,?_⟩
  exact phase_gap_positive d hd c ⟨hc.1,hc.2.trans hap⟩ hu (by linarith [hzc'])

end FiolDoubleHub

end D5.S3.Zeros.LeeYang
