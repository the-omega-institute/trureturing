/- GID: D5/S3/Arith/Primes/GoldenCubicOrientedPolynomialPartition
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenCubicOrientedPolynomialPartition
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Three monic orientation factors multiply to the finite-field polynomial. -/

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace D5.S3.Arith.Primes.GoldenCubicOrientedPolynomialPartition

abbrev QA (R : Type*) [CommRing R] := QuadraticAlgebra R (-3) 0

private theorem imag_cube {R : Type*} [CommRing R] (z : QA R) :
    (z^3).im = 3*z.im*(z.re-z.im)*(z.re+z.im) := by
  simp only [pow_succ, pow_zero,one_mul,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul]
  ring

private theorem one_plus {R : Type*} [CommRing R] (X : R) :
    (⟨X,1⟩ : QA R) = algebraMap R (QA R) X + QuadraticAlgebra.omega := by
  ext <;> simp [QuadraticAlgebra.omega]

private theorem frob_one_plus {R : Type*} [CommRing R] (p d : ℕ) [CharP R p]
    (hp : p.Prime) (X e : R)
    (hδ : (QuadraticAlgebra.omega : QA R)^(p^d) = ⟨0,e⟩) :
    ((⟨X,1⟩ : QA R)^(p^d)) = ⟨X^(p^d),e⟩ := by
  let _ : CharP (QA R) p := ⟨fun n => by
    rw [←map_natCast (algebraMap R (QA R)), ←map_zero (algebraMap R (QA R)),
      QuadraticAlgebra.algebraMap_injective.eq_iff]
    exact CharP.cast_eq_zero_iff R p n⟩
  let _ : ExpChar (QA R) p := .prime hp
  have hscalar : (algebraMap R (QA R) X)^(p^d)=algebraMap R (QA R) (X^(p^d)) :=
    (map_pow (algebraMap R (QA R)) X (p^d)).symm
  rw [one_plus,add_pow_expChar_pow,hδ,hscalar]
  change (⟨X^(p^d),0⟩ : QA R)+⟨0,e⟩=⟨X^(p^d),e⟩
  apply QuadraticAlgebra.ext
  · exact add_zero _
  · exact zero_add _

/-- The oriented partition identity in a ring (in particular, the polynomial
ring over a finite field). The sign premise records the actual action of the
base-field Frobenius on the formal square root of minus three. -/
private theorem oriented_partition {R : Type*} [CommRing R] (p d m : ℕ) [CharP R p]
    (hp : p.Prime) (X : R) (split : Bool)
    (hm : if split then 3*m+1 = p^d else 3*m=p^d+1)
    (hδ : (QuadraticAlgebra.omega : QA R)^(p^d) =
      ⟨0,if split then 1 else -1⟩) :
    let z := (⟨X,1⟩ : QA R)^m
    let U := z.re
    let V := z.im
    if split then (X^2+3)*(3*V*(U-V)*(U+V))=X-X^(p^d)
      else 3*V*(U-V)*(U+V)=X^(p^d)-X := by
  let Y : QA R := ⟨X,1⟩
  let z := Y^m
  have hf : Y^(p^d)=⟨X^(p^d),if split then 1 else -1⟩ :=
    frob_one_plus p d hp _ _ hδ
  have hcube := imag_cube z
  have hpower : z^3=Y^(3*m) := by dsimp [z]; rw [←pow_mul,Nat.mul_comm]
  cases split with
  | false =>
    simp only [Bool.false_eq_true,ite_false] at hm hf ⊢
    change 3*z.im*(z.re-z.im)*(z.re+z.im)=X^(p^d)-X
    rw [←hcube,hpower,hm,pow_succ,hf]
    change ((⟨X^(p^d),-1⟩ : QA R) * ⟨X,1⟩).im=_
    simp [sub_eq_add_neg]
  | true =>
    simp only [ite_true] at hm hf ⊢
    change (X^2+3)*(3*z.im*(z.re-z.im)*(z.re+z.im))=X-X^(p^d)
    let Y' : QA R := ⟨X,-1⟩
    have hnorm : Y'*Y=(⟨X^2+3,0⟩ : QA R) := by
      apply QuadraticAlgebra.ext
      · change X*X+(-3)*(-1)*1 = X^2+3
        ring
      · change X*1+(-1)*X+0*(-1)*1 = 0
        ring
    have hY : Y' * Y^(p^d)=(⟨X^2+3,0⟩ : QA R)*z^3 := by
      rw [hpower,←hm,pow_succ',←mul_assoc,hnorm]
    have h := congrArg QuadraticAlgebra.im hY
    rw [hf] at h
    rw [←hcube]
    change X*1+(-1)*X^(p^d)+0*(-1)*1 =
      (X^2+3)*(z^3).im + 0*(z^3).re + 0*0*(z^3).im at h
    simpa only [mul_one,neg_one_mul,zero_mul,add_zero,sub_eq_add_neg] using h.symm


/-- The sign on the formal square root is determined solely by p^d modulo
three. No field splitting or quadratic-residue theorem is used. -/
private theorem omega_frobenius_sign {R : Type*} [CommRing R] (p d : ℕ) [CharP R p]
    (hp : p.Prime) (h2 : IsUnit (2:R)) (split : Bool)
    (hq : (p^d)%3 = if split then 1 else 2) :
    (QuadraticAlgebra.omega : QA R)^(p^d) = ⟨0,if split then 1 else -1⟩ := by
  let T := QA R
  let _ : CharP T p := ⟨fun n => by
    rw [←map_natCast (algebraMap R T), ←map_zero (algebraMap R T),
      QuadraticAlgebra.algebraMap_injective.eq_iff]
    exact CharP.cast_eq_zero_iff R p n⟩
  let _ : ExpChar T p := .prime hp
  let w : T := QuadraticAlgebra.omega
  let u : Tˣ := Units.map (algebraMap R T) h2.unit
  have hu : (u:T)=2 := by
    change algebraMap R T (h2.unit:R)=2
    rw [h2.unit_spec,map_ofNat]
  let v : T := (u⁻¹:Tˣ)
  have hv : 2*v=1 := by rw [←hu]; exact u.mul_inv
  let θ := (w-1)*v
  have hθ : 2*θ+1=w := by
    calc
      _ = (w-1)*(2*v)+1 := by unfold θ; ring
      _ = _ := by rw [hv]; ring
  have hw2 : w^2=-3 := by
    rw [pow_two]
    apply QuadraticAlgebra.ext
    · change (0*0+(-3)*1*1 : R) = -3
      ring
    · rw [QuadraticAlgebra.im_neg,QuadraticAlgebra.im_ofNat,neg_zero]
      change (0*1+1*0+0*1*1 : R) = 0
      ring
  have hquad : (θ^2+θ+1)*(2:T)^2=0 := by
    calc
      _ = (2*θ+1)^2+3 := by ring
      _ = _ := by rw [hθ,hw2,neg_add_cancel]
  have hqθ : θ^2+θ+1=0 := by
    calc
      _ = ((θ^2+θ+1)*(2:T)^2)*v^2 := by
        rw [mul_assoc,←mul_pow,hv,one_pow,mul_one]
      _ = 0 := by rw [hquad,zero_mul]
  have hcθ : θ^3=1 := by
    apply sub_eq_zero.mp
    calc
      _ = (θ-1)*(θ^2+θ+1) := by ring
      _ = 0 := by rw [hqθ,mul_zero]
  have htF : θ^(p^d)=θ^(p^d%3) := by
    calc
      _ = θ^(3*(p^d/3)+p^d%3) := by rw [show 3*(p^d/3)+p^d%3=p^d by omega]
      _ = _ := by rw [pow_add,pow_mul,hcθ,one_pow,one_mul]
  let σ := iterateFrobenius T p d
  have hF : w^(p^d)=2*θ^(p^d)+1 := by
    change σ w = 2*σ θ+1
    rw [←hθ,map_add,map_mul,map_ofNat,map_one]
  cases split with
  | false =>
    simp only [Bool.false_eq_true,ite_false] at hq ⊢
    have hn : (-w : T) = ⟨0,-1⟩ := by
      apply QuadraticAlgebra.ext
      · exact neg_zero
      · rfl
    change w^(p^d) = (⟨0,-1⟩ : T)
    rw [←hn,hF,htF,hq,←hθ]
    calc
      _ = 2*(θ^2+θ+1)-(2*θ+1) := by ring
      _ = _ := by rw [hqθ]; ring
  | true =>
    simp only [ite_true] at hq ⊢
    change w^(p^d)=w
    rw [hF,htF,hq,pow_one,hθ]
/-- Exact finite-characteristic polynomial partition, with leading
normalization factor ±3 (= 1/m). No Frobenius-sign assumption. -/
private theorem oriented_partition_normalized {R : Type*} [CommRing R] (p d : ℕ) [CharP R p]
    (hp : p.Prime) (hp3 : 3<p) (hd : 0<d) (h2 : IsUnit (2:R)) (X : R) :
    let q := p^d
    let split := q%3=1
    let m := if split then (q-1)/3 else (q+1)/3
    let z := (⟨X,1⟩ : QA R)^m
    let U := z.re
    let V := z.im
    let c : R := if split then -3 else 3
    c*(m:R)=1 ∧
      (if split then (X^2+3)*(c*V)*(U-V)*(U+V) else (c*V)*(U-V)*(U+V)) =
        X^q-X := by
  let q := p^d
  let h3 : Nat.Prime 3 := by decide
  have hpNd : ¬ 3 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq h3 hp).mp h
    omega
  have hqNd : q%3 ≠ 0 := fun h => hpNd (h3.dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero h))
  have hqpos : 0<q := pow_pos hp.pos _
  have hqzero : (q:R) = 0 := by
    dsimp [q]
    rw [Nat.cast_pow,CharP.cast_eq_zero R p,zero_pow hd.ne']
  by_cases hs : q%3=1
  · let m := (q-1)/3
    have hm : 3*m+1=q := by dsimp [m]; omega
    have hs' : (p^d)%3 = if true then 1 else 2 := hs
    have hf := omega_frobenius_sign p d hp h2 true hs'
    have H := oriented_partition p d m hp X true (by exact hm) hf
    have hnorm : (-3:R)*(m:R)=1 := by
      have hcast := congrArg (fun n : ℕ => (n:R)) hm
      push_cast at hcast
      rw [hqzero] at hcast
      have hz : (3:R)*(m:R)= -1 := eq_neg_of_add_eq_zero_left hcast
      calc
        _ = -(3*(m:R)) := by ring
        _ = 1 := by rw [hz,neg_neg]
    dsimp only [q] at hs
    simp only [hs,ite_true]
    refine ⟨hnorm,?_⟩
    let z := (⟨X,1⟩ : QA R)^m
    change (X^2+3)*(-3*z.im)*(z.re-z.im)*(z.re+z.im)=X^(p^d)-X
    change (X^2+3)*(3*z.im*(z.re-z.im)*(z.re+z.im))=X-X^(p^d) at H
    calc
      _ = -((X^2+3)*(3*z.im*(z.re-z.im)*(z.re+z.im))) := by ring
      _ = _ := by rw [H]; ring
  · have hs2 : q%3=2 := by omega
    let m := (q+1)/3
    have hm : 3*m=q+1 := by dsimp [m]; omega
    have hs' : (p^d)%3 = if false then 1 else 2 := hs2
    have hf := omega_frobenius_sign p d hp h2 false hs'
    have H := oriented_partition p d m hp X false (by exact hm) hf
    have hnorm : (3:R)*(m:R)=1 := by
      have hcast := congrArg (fun n : ℕ => (n:R)) hm
      push_cast at hcast
      rwa [hqzero,zero_add] at hcast
    dsimp only [q] at hs
    simp only [hs,ite_false]
    exact ⟨hnorm,H⟩


section Degrees
open Polynomial
variable {R : Type*} [CommRing R]


private noncomputable def U (m : ℕ) : R[X] := (((⟨X,1⟩ : QA R[X])^m).re)
private noncomputable def V (m : ℕ) : R[X] := (((⟨X,1⟩ : QA R[X])^m).im)

private theorem U_succ (m : ℕ) : (U (m+1) : R[X]) = X*U m + C (-3)*V m := by
  unfold U V
  rw [pow_succ']
  change X*_+(-3)*1*_ = X*_+C (-3)*_
  rw [map_neg,map_ofNat,mul_one]

private theorem V_succ (m : ℕ) : (V (m+1) : R[X]) = X*V m + U m := by
  unfold U V
  rw [pow_succ']
  change X*_+1*_+0*1*_ = X*_+_
  simp only [one_mul,zero_mul,add_zero]

private theorem coeff_fiber (m : ℕ) :
    (U m : R[X]).coeff m = 1 ∧ (∀ k, m<k → (U m : R[X]).coeff k=0) ∧
    (V m : R[X]).coeff (m-1) = (m:R) ∧ (∀ k, m≤k → (V m : R[X]).coeff k=0) := by
  induction m with
  | zero =>
    simp [U,V,QuadraticAlgebra.re_one,QuadraticAlgebra.im_one,coeff_one]; omega
  | succ m ih =>
    obtain ⟨hum,hu, hvm,hv⟩ := ih
    rw [U_succ,V_succ]
    refine ⟨?_,?_,?_,?_⟩
    · rw [coeff_add,coeff_X_mul, coeff_C_mul,hum,hv _ (by omega),mul_zero,add_zero]
    · intro k hk
      obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
      rw [coeff_add, coeff_X_mul,coeff_C_mul,hu _ (by omega),hv _ (by omega),mul_zero,add_zero]
    · rw [Nat.add_sub_cancel,coeff_add,hum,Nat.cast_succ]
      congr 1
      cases m with
      | zero => simp
      | succ m => exact (coeff_X_mul (V (m+1) : R[X]) m).trans hvm
    · intro k hk
      obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
      rw [coeff_add, coeff_X_mul,hv _ (by omega),hu _ (by omega),add_zero]

/-- The factors of the exact quadratic-coordinate partition are monic at their
advertised degrees whenever the coefficient used to normalize V is inverse to m. -/
private theorem monic_fiber_degrees [Nontrivial R] (m : ℕ) (hm : 0<m) (c : R) (hc : c*(m:R)=1) :
    let z := (⟨X,1⟩ : QA R[X])^m
    let U := z.re
    let V := z.im
    (C c*V).Monic ∧ (C c*V).natDegree=m-1 ∧
    (U-V).Monic ∧ (U-V).natDegree=m ∧
    (U+V).Monic ∧ (U+V).natDegree=m := by
  obtain ⟨hum,hu,hvm,hv⟩ := (coeff_fiber (R:=R) m)
  change (C c*V m).Monic ∧ (C c*V m).natDegree=m-1 ∧
    (U m-V m).Monic ∧ (U m-V m).natDegree=m ∧
    (U m+V m).Monic ∧ (U m+V m).natDegree=m
  have he (P : R[X]) (n : ℕ) (hn : P.coeff n=1)
      (hs : ∀ k, n<k → P.coeff k=0) : P.Monic ∧ P.natDegree=n := by
    have hdeg := natDegree_le_iff_coeff_eq_zero.mpr hs
    exact ⟨monic_of_natDegree_le_of_coeff_eq_one n hdeg hn,
      natDegree_eq_of_le_of_coeff_ne_zero hdeg (by rw [hn]; exact one_ne_zero)⟩
  have h0 := he (C c*V m) (m-1) (by rw [coeff_C_mul,hvm,hc])
    (fun k hk => by rw [coeff_C_mul,hv _ (by omega),mul_zero])
  have h1 := he (U m-V m) m (by rw [coeff_sub,hum,hv _ le_rfl,sub_zero])
    (fun k hk => by rw [coeff_sub,hu _ hk,hv _ hk.le,sub_zero])
  have h2 := he (U m+V m) m (by rw [coeff_add,hum,hv _ le_rfl,add_zero])
    (fun k hk => by rw [coeff_add,hu _ hk,hv _ hk.le,add_zero])
  exact ⟨h0.1,h0.2,h1.1,h1.2,h2.1,h2.2⟩

end Degrees

open Polynomial

set_option maxHeartbeats 500000 in
/-- The three normalized oriented factors over a polynomial ring have exactly
degrees m−1, m, m, and multiply to the characteristic-q polynomial after
retaining the two forbidden split points when appropriate. -/
theorem monic_oriented_polynomial_partition {R : Type*} [CommRing R] [Nontrivial R]
    (p d : ℕ) [CharP R p] (hp : p.Prime) (hp3 : 3<p) (hd : 0<d) (h2 : IsUnit (2:R)) :
    let m := if p^d%3=1 then (p^d-1)/3 else (p^d+1)/3
    let q := p^d
    let split := q%3=1
    let z := (⟨(X:R[X]),1⟩ : QA R[X])^m
    let U := z.re
    let V := z.im
    let c : R := if split then -3 else 3
    0<m ∧ c*(m:R)=1 ∧
    (C c*V).Monic ∧ (C c*V).natDegree=m-1 ∧
    (U-V).Monic ∧ (U-V).natDegree=m ∧ (U+V).Monic ∧ (U+V).natDegree=m ∧
    (if split then (X^2+3)*(C c*V)*(U-V)*(U+V) else (C c*V)*(U-V)*(U+V)) =
        X^q-X := by
  let q := p^d
  let split := q%3=1
  let m := if split then (q-1)/3 else (q+1)/3
  let z := (⟨(X:R[X]),1⟩ : QA R[X])^m
  let c : R := if split then -3 else 3
  let _ : CharP R[X] p := ⟨fun n => by
    rw [←map_natCast (C : R →+* R[X]),←map_zero (C : R →+* R[X]), C_injective.eq_iff]
    exact CharP.cast_eq_zero_iff R p n⟩
  have h2p : IsUnit (2:R[X]) := by simpa only [map_ofNat] using h2.map (C : R →+* R[X])
  have hQge : 3<q := hp3.trans_le (Nat.le_self_pow hd.ne' p)
  have hm : 0<m := by
    unfold m
    split <;> omega
  have hpC : (if split then -3 else 3 : R[X]) = C c := by
    by_cases hs : split <;> simp [hs,c, map_ofNat]
  have h := oriented_partition_normalized p d hp hp3 hd h2p (X:R[X])
  have hcp : (C c : R[X])*(m:R[X])=1 := by
    rw [←hpC]
    exact h.1
  have hcm : c*(m:R)=1 := by
    apply Polynomial.C_injective (R := R)
    simpa only [map_mul,map_natCast,map_one] using hcp
  obtain ⟨hVm,hVd,hUm,hUd,hU'm,hU'd⟩ := monic_fiber_degrees (R:=R) m hm c hcm
  change 0<m ∧ c*(m:R)=1 ∧
    (C c*z.im).Monic ∧ (C c*z.im).natDegree=m-1 ∧
    (z.re-z.im).Monic ∧ (z.re-z.im).natDegree=m ∧
    (z.re+z.im).Monic ∧ (z.re+z.im).natDegree=m ∧
    (if split then (X^2+3)*(C c*z.im)*(z.re-z.im)*(z.re+z.im)
      else (C c*z.im)*(z.re-z.im)*(z.re+z.im)) = X^q-X
  refine ⟨hm,hcm,hVm,hVd,hUm,hUd,hU'm,hU'd,?_⟩
  rw [←hpC]
  exact h.2

#print axioms monic_oriented_polynomial_partition
end D5.S3.Arith.Primes.GoldenCubicOrientedPolynomialPartition
