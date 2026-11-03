/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakAdjacentTail/Dyadic
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakAdjacentTail/Dyadic
   mirror-E: none(waiver:adjacent-tail-physical-source)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Unbounded dyadic residue and integer quotient identities. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.Algebra
import Mathlib.Data.Int.ModEq
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail
open private A B L K SU SV SW E F Common Residual StocksAndResidual HighResidual Windows ceilDiv residueRepresentative chooseM3 chooseV2 chooseM2
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.Algebra

private theorem quotient_parity (ell : ℕ) :
    (-1 : ℤ)^ell=if ell%2=0 then 1 else -1 := by
  have he : ell=2*(ell/2)+ell%2 := by omega
  conv_lhs => rw [he,pow_add,pow_mul]
  norm_num
  have hr : ell%2<2 := Nat.mod_lt ell (by decide)
  by_cases h : ell%2=0
  · simp [h]
  · have hh : ell%2=1 := by omega
    simp [hh]

/-- Euclidean exponent division and the exact signed dyadic residue, unbounded c. -/
private theorem dyadic_residue (a c shift : ℕ) (ha : 1 ≤ a) :
    let ell := (c+shift)/a
    let j := (c+shift)%a
    let x : ℤ := 2^a
    let u : ℤ := 2^j
    c+shift=a*ell+j ∧ j<a ∧ 1≤u ∧ 2*u≤x ∧
    (2:ℤ)^(c+shift)%(x+1)=(if ell%2=0 then u else x+1-u) := by
  dsimp only
  let ell := (c+shift)/a
  let j := (c+shift)%a
  let x : ℤ := 2^a
  let u : ℤ := 2^j
  have he : c+shift=a*ell+j := by
    simpa only [ell,j,Nat.add_comm] using (Nat.mod_add_div (c+shift) a).symm
  have hj : j<a := Nat.mod_lt _ (by omega)
  have hu : 1≤u := one_le_pow₀ (by norm_num)
  have hux : 2*u≤x := by
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show j+1≤a by omega)
    simpa only [pow_succ,mul_comm] using hp
  have hx : 0<x := by dsimp [x]; positivity
  have hbase : Int.ModEq (x+1) x (-1) := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-1,?_⟩
    ring
  have hp : Int.ModEq (x+1) ((2:ℤ)^(c+shift)) ((-1:ℤ)^ell*u) := by
    rw [he,pow_add,pow_mul]
    exact (hbase.pow ell).mul (Int.ModEq.refl u)
  rw [quotient_parity] at hp
  refine ⟨he,hj,hu,hux,?_⟩
  change (2:ℤ)^(c+shift)%(x+1)=(if ell%2=0 then u else x+1-u)
  by_cases hpar : ell%2=0
  · simp only [hpar,if_true,one_mul] at hp ⊢
    exact hp.eq.trans (Int.emod_eq_of_lt (show 0 ≤ u by omega) (show u < x+1 by omega))
  · simp only [hpar,if_false,neg_one_mul] at hp ⊢
    have hrep : Int.ModEq (x+1) (-u) (x+1-u) := by
      apply Int.modEq_iff_dvd.mpr
      refine ⟨1,?_⟩
      ring
    exact (hp.trans hrep).eq.trans (Int.emod_eq_of_lt (show 0 ≤ x+1-u by omega) (show x+1-u < x+1 by omega))

/-! The residue identity also supplies the integer quotient used by the mask
selectors.  This is the divisibility step that cannot be replaced by a
rational stock assumption. -/
private theorem dyadic_residue_integer_quotient (a c shift : ℕ) (ha : 1≤a) :
    let ell := (c+shift)/a
    let j := (c+shift)%a
    let x : ℤ := 2^a
    let u : ℤ := 2^j
    ∃ T : ℤ, (2:ℤ)^(c+shift)=
      (if ell%2=0 then u else x+1-u)+(x+1)*T := by
  dsimp only
  let ell := (c+shift)/a
  let j := (c+shift)%a
  let x : ℤ := 2^a
  let u : ℤ := 2^j
  obtain ⟨he,hj,hu,hux,hr⟩ := dyadic_residue a c shift ha
  let r : ℤ := if ell%2=0 then u else x+1-u
  let T : ℤ := (2:ℤ)^(c+shift)/(x+1)
  have hdecomp := Int.emod_add_mul_ediv ((2:ℤ)^(c+shift)) (x+1)
  have hrem : (2:ℤ)^(c+shift)%(x+1)=r := by simpa [r,x,u] using hr
  refine ⟨T,?_⟩
  dsimp [T] at hdecomp ⊢
  rw [hrem] at hdecomp
  nlinarith

private theorem dyadic_small_or_large (j : ℕ) :
    (2:ℤ)^j=1 ∨ (2:ℤ)^j=2 ∨ (2:ℤ)^j=4 ∨
    (2:ℤ)^j=8 ∨ 16≤(2:ℤ)^j := by
  by_cases hj : j<4
  · interval_cases j <;> norm_num
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (by simpa using pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show 4≤j by omega)))))

/-- Actual exponents in one class modulo 2a differ by a nonnegative multiple of x+1. -/
private theorem periodic_nonnegative_inverse (a c c0 : ℕ) (ha : 1≤a)
    (hc : c0≤c) (hr : c%(2*a)=c0%(2*a)) :
    ∃ T : ℤ, 0≤T ∧ (2:ℤ)^c=(2:ℤ)^c0+((2:ℤ)^a+1)*T := by
  let h : ℤ := (2:ℤ)^a+1
  have hh : 0<h := by dsimp [h]; positivity
  have hbase : Int.ModEq h ((2:ℤ)^a) (-1) := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-1,?_⟩
    dsimp [h]
    ring
  have hperiod : Int.ModEq h ((2:ℤ)^(2*a)) 1 := by
    have hp := hbase.pow 2
    simpa only [show 2*a=a*2 by omega,pow_mul,neg_one_sq] using hp
  have reduce (n : ℕ) : Int.ModEq h ((2:ℤ)^n) ((2:ℤ)^(n%(2*a))) := by
    have he : n=2*a*(n/(2*a))+n%(2*a) := by
      simpa [Nat.add_comm] using (Nat.mod_add_div n (2*a)).symm
    conv_lhs => rw [he,pow_add,pow_mul]
    simpa only [one_pow,one_mul] using
      (hperiod.pow (n/(2*a))).mul (Int.ModEq.refl ((2:ℤ)^(n%(2*a))))
  have hp : Int.ModEq h ((2:ℤ)^c0) ((2:ℤ)^c) := by
    exact (reduce c0).trans (by simpa only [hr] using (reduce c).symm)
  obtain ⟨T,hT⟩ := Int.modEq_iff_add_fac.mp hp
  have hpow : (2:ℤ)^c0≤(2:ℤ)^c := pow_le_pow_right₀ (by norm_num) hc
  have hT0 : 0≤T := by nlinarith
  exact ⟨T,hT0,hT⟩

/-- The lower orthants used at q=4 follow from exponent division, not sampling. -/
private theorem plus_two_orthant_bounds (a c : ℕ) (ha : 4≤a) (hac : a<c) :
    let ell := (c+2)/a
    let j := (c+2)%a
    let x : ℤ := 2^a
    let z : ℤ := 2^c
    let u : ℤ := 2^j
    (ell%2=0 → u*x^2≤4*z) ∧
    (ell%2=1 → u≤4 → x^2≤z) := by
  dsimp only
  let ell := (c+2)/a
  let j := (c+2)%a
  let x : ℤ := 2^a
  let z : ℤ := 2^c
  let u : ℤ := 2^j
  obtain ⟨he,hj,hu,hux,hr⟩ := dyadic_residue a c 2 (by omega)
  change j < a at hj
  change 1 ≤ u at hu
  change 2*u ≤ x at hux
  have he' : c+2=a*ell+j := he
  have hx : 16≤x := by simpa [x] using pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) ha
  have hz : 4*z=u*x^ell := by
    calc
      4*z=(2:ℤ)^(c+2) := by dsimp [z]; rw [pow_add]; norm_num; ring
      _=u*x^ell := by rw [he',pow_add,pow_mul]; dsimp [u,x]; ring
  constructor
  · intro hp
    change ell%2=0 at hp
    have he2 : 2≤ell := by
      have hell : 0<ell := Nat.div_pos (by omega) (by omega)
      omega
    have hpow : x^2≤x^ell := pow_le_pow_right₀ (by omega) he2
    nlinarith
  · intro hp hu4
    change ell%2=1 at hp
    change u ≤ 4 at hu4
    have hj2 : j≤2 := by
      by_contra hn
      have h8 : 8≤u := by
        dsimp [u]
        simpa using pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show 3≤j by omega)
      omega
    have he3 : 3≤ell := by
      have hell : 0<ell := Nat.div_pos (by omega) (by omega)
      by_contra hn
      have he1 : ell=1 := by omega
      rw [he1] at he'
      omega
    have hpow : x^3≤x^ell := pow_le_pow_right₀ (by omega) he3
    have hx3 : 4*x^2≤u*x^3 := by
      calc
        4*x^2 ≤ x*x^2 := mul_le_mul_of_nonneg_right (by omega) (sq_nonneg x)
        _ = x^3 := by ring
        _ ≤ u*x^3 := le_mul_of_one_le_left (by positivity) hu
    have hh := mul_le_mul_of_nonneg_left hpow (show 0 ≤ u by omega)
    nlinarith

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail
