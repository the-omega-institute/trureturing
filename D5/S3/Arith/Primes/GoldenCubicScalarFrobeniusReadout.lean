/- GID: D5/S3/Arith/Primes/GoldenCubicScalarFrobeniusReadout
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenCubicScalarFrobeniusReadout
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Signed comparisons in the prime field recover the oriented Cardano output without extension-field computation. -/

import D5.S3.Arith.Primes.GoldenCubicInertFrobeniusReadout
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

/-! # Signed base-field readout of the golden cubic

The second-kind Dickson divided-power recurrence is classical. For the native
cubic it recovers the two nonzero labels separately, not only the split label.
The inert branch explicitly uses the protected short Frobenius theorem.
-/

namespace D5.S3.Arith.Primes.GoldenCubicScalarFrobeniusReadout

section Ring
variable {R : Type*} [CommRing R]

/-- Divided-power recurrence with sum A and product C. -/
def divided (A C : R) : ℕ → R
  | 0 => 0
  | 1 => 1
  | n+2 => A * divided A C (n+1) - C * divided A C n

private theorem divided_pow_gap (u v : R) (n : ℕ) :
    u^n - v^n = (u-v)*divided (u+v) (u*v) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [divided]
  | one => simp [divided]
  | more n h0 h1 =>
    calc
      u^(n+2)-v^(n+2) =
          (u+v)*(u^(n+1)-v^(n+1))-u*v*(u^n-v^n) := by
        simp only [pow_succ]; ring
      _ = (u-v)*divided (u+v) (u*v) (n+2) := by
        rw [h0,h1,divided]; ring

private theorem map_divided {S : Type*} [CommRing S] (f : R →+* S) (A C : R) (n : ℕ) :
    f (divided A C n) = divided (f A) (f C) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [divided]
  | one => simp [divided]
  | more n h0 h1 => simp only [divided,map_sub,map_mul,h0,h1]

-- These parameter names use the same B and A in the native cubic.
def block (x : R) := x^2+3
def scalar (x : R) := 2*(x^2-3)
def numer (x : R) (n : ℕ) := 4*x*divided (scalar x) ((block x)^2) n

private theorem native_power_gap (x δ : R) (hd : δ^2 = -3) (n : ℕ) :
    ((x+δ)^2)^n-((x-δ)^2)^n = δ*numer x n := by
  have hs : (x+δ)^2+(x-δ)^2=scalar x := by
    calc
      _ = 2*(x^2+δ^2) := by ring
      _ = _ := by rw [hd, scalar, sub_eq_add_neg]
  have hp : ((x+δ)^2)*((x-δ)^2) = (block x)^2 := by
    calc
      _ = (x^2-δ^2)^2 := by ring
      _ = _ := by rw [hd,block,sub_neg_eq_add]
  have hdiff : (x+δ)^2-(x-δ)^2=δ*(4*x) := by ring
  rw [divided_pow_gap,hs,hp,hdiff,numer,mul_assoc]

private theorem map_numer {S : Type*} [CommRing S] (f : R →+* S) (x : R) (n : ℕ) :
    f (numer x n) = numer (f x) n := by
  simp [numer,scalar,block,map_divided,map_ofNat]

end Ring


section Field
variable {K : Type*} [Field K]

def torus (x δ : K) := (x+δ)/(x-δ)
def omegaOf (δ : K) := (δ-1)/2

private theorem factors (x δ : K) (hδ : δ^2 = -3) :
    (x+δ)*(x-δ) = block x := by
  calc
    _ = x^2-δ^2 := by ring
    _ = _ := by rw [hδ,block,sub_neg_eq_add]

private theorem factor_units (x δ : K) (hδ : δ^2 = -3) (hB : block x ≠ 0) :
    x+δ ≠ 0 ∧ x-δ ≠ 0 := by
  exact ⟨left_ne_zero_of_mul (factors x δ hδ ▸ hB),
    right_ne_zero_of_mul (factors x δ hδ ▸ hB)⟩

private theorem torus_power_gap (x δ : K) (hδ : δ^2 = -3) (hB : block x ≠ 0) (m : ℕ) :
    (block x)^m * ((torus x δ)^m-((torus x δ)^m)⁻¹) = δ*numer x m := by
  obtain ⟨hplus,hminus⟩ := factor_units x δ hδ hB
  have h1 : block x * torus x δ = (x+δ)^2 := by
    rw [← factors x δ hδ,torus]
    field_simp
  have h2 : block x * (torus x δ)⁻¹ = (x-δ)^2 := by
    rw [← factors x δ hδ,torus,inv_div]
    field_simp
  calc
    _ = (block x * torus x δ)^m - (block x * (torus x δ)⁻¹)^m := by
      rw [mul_sub,mul_pow,mul_pow,inv_pow]
    _ = _ := by rw [h1,h2,native_power_gap x δ hδ]

private theorem omega_coordinates (δ : K) (hδ : δ^2 = -3) (h2 : (2:K) ≠ 0) :
    (omegaOf δ)⁻¹=(-δ-1)/2 ∧ omegaOf δ + (omegaOf δ)⁻¹= -1 ∧
      omegaOf δ - (omegaOf δ)⁻¹=δ := by
  have hp : omegaOf δ*((-δ-1)/2)=1 := by
    unfold omegaOf
    field_simp
    have he : (δ-1)*(-δ-1) = 4 := by
      calc
        _ = 1-δ^2 := by ring
        _ = _ := by rw [hδ]; norm_num
    norm_num at he ⊢; exact he
  have hi : (omegaOf δ)⁻¹=(-δ-1)/2 := by
    exact (eq_inv_of_mul_eq_one_right hp).symm
  exact ⟨hi,by rw [hi]; unfold omegaOf; field_simp; ring,
    by rw [hi]; unfold omegaOf; field_simp; ring⟩

/-- Exact signed comparison law. It works both in a split base field and an
inert quadratic extension once the common exponent is a cube root of unity.
The recurrence never divides by the Lucas parameter x. -/
private theorem scalar_signed_comparisons (x δ : K) (m : ℕ)
    (hδ : δ^2 = -3) (hB : block x ≠ 0) (h2 : (2:K) ≠ 0) (h3 : (3:K) ≠ 0)
    (hCube : ((torus x δ)^m)^3=1) :
    (numer x m = 0 ↔ (torus x δ)^m = 1) ∧
    (numer x m = (block x)^m ↔ (torus x δ)^m = omegaOf δ) ∧
    (numer x m = -(block x)^m ↔ (torus x δ)^m = (omegaOf δ)⁻¹) := by
  let z := (torus x δ)^m
  let w := omegaOf δ
  let c := (block x)^m
  let N := numer x m
  obtain ⟨_,hs,hd⟩ := omega_coordinates δ hδ h2
  have hδ0 : δ ≠ 0 := by
    intro h
    rw [h,zero_pow (by decide : 2≠0),eq_comm,neg_eq_zero] at hδ
    exact h3 hδ
  have hW0 : w ≠ 0 := by
    intro h
    change w+w⁻¹ = -1 at hs
    simp [h] at hs
  have hp : w*w⁻¹=1 := mul_inv_cancel₀ hW0
  have hc : c ≠ 0 := pow_ne_zero m hB
  have hroots : z=1 ∨ z=w ∨ z=w⁻¹ := by
    change z^3=1 at hCube
    have hF : (z-1)*((z-w)*(z-w⁻¹)) = z^3-1 := by
      change w+w⁻¹ = -1 at hs
      calc
        _ = (z-1)*(z^2-(w+w⁻¹)*z+w*w⁻¹) := by ring
        _ = _ := by rw [hs,hp]; ring
    rw [hCube,sub_self] at hF
    rcases mul_eq_zero.mp hF with h|h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr ((mul_eq_zero.mp h).imp sub_eq_zero.mp sub_eq_zero.mp)
  have hg : c*(z-z⁻¹)=δ*N := torus_power_gap x δ hδ hB m
  have h01 : z=1 → N=0 := by
    intro h
    rw [h,inv_one,sub_self,mul_zero,eq_comm] at hg
    exact (mul_eq_zero.mp hg).resolve_left hδ0
  have h11 : z=w → N=c := by
    intro h
    change w-w⁻¹=δ at hd
    rw [h,hd,mul_comm c δ] at hg
    exact (mul_left_cancel₀ hδ0 hg).symm
  have h21 : z=w⁻¹ → N= -c := by
    intro h
    have he : w⁻¹-(w⁻¹)⁻¹ = -δ := by
      rw [inv_inv]; change w-w⁻¹=δ at hd; rw [← hd,neg_sub]
    rw [h,he, mul_neg, mul_comm c δ, ← mul_neg] at hg
    exact (mul_left_cancel₀ hδ0 hg).symm
  have hnot : c ≠ -c := by
    intro he
    have hf : (2:K)*c=0 := calc
      _ = c+c := by ring
      _ = -c+c := congrArg (fun u => u+c) he
      _ = 0 := neg_add_cancel c
    exact hc ((mul_eq_zero.mp hf).resolve_left h2)
  change (N=0 ↔ z=1) ∧ (N=c ↔ z=w) ∧ (N= -c ↔ z=w⁻¹)
  refine ⟨⟨?_,h01⟩,⟨?_,h11⟩,⟨?_,h21⟩⟩
  · intro h
    rcases hroots with hz|hz|hz
    · exact hz
    · exact (hc ((h11 hz).symm.trans h)).elim
    · exact (hc (neg_eq_zero.mp ((h21 hz).symm.trans h))).elim
  · intro h
    rcases hroots with hz|hz|hz
    · exact (hc (h.symm.trans (h01 hz))).elim
    · exact hz
    · exact (hnot (h.symm.trans (h21 hz))).elim
  · intro h
    rcases hroots with hz|hz|hz
    · exact (hc (neg_eq_zero.mp (h.symm.trans (h01 hz)))).elim
    · exact (hnot ((h11 hz).symm.trans h)).elim
    · exact hz

end Field

section Finite
variable {K : Type*} [Field K]

/-- The split and inert torus exponents differ by the sign of q mod 3. -/
def probePower (q : ℕ) := if q % 3 = 1 then (q-1)/3 else (q+1)/3

private theorem prime_mod_three (q : ℕ) (hp : q.Prime) (hgt : 3<q) :
    q%3=1 ∨ q%3=2 := by
  have hd : ¬ 3 ∣ q := by
    intro h
    have he := (Nat.prime_dvd_prime_iff_eq (show Nat.Prime 3 from by decide) hp).mp h
    omega
  have hz : q%3≠0 := fun h => hd (Nat.dvd_of_mod_eq_zero h)
  omega

private theorem small_ne (q n : ℕ) [CharP K q] (hn : 0<n) (hnq : n<q) :
    (n:K) ≠ 0 := by
  intro h
  exact (not_le_of_gt hnq) (Nat.le_of_dvd hn ((CharP.cast_eq_zero_iff K q n).mp h))

private theorem torus_cube (q : ℕ) [CharP K q] (hp : q.Prime) (hgt : 3<q) (x δ : K)
    (hδ : δ^2=-3) (hB : block x ≠ 0)
    (hx : x^q=x)
    (hF : δ^q = if q%3=1 then δ else -δ) :
    ((torus x δ)^(probePower q))^3 = 1 := by
  let _ : ExpChar K q := .prime hp
  let σ := frobenius K q
  have hxσ : σ x=x := hx
  have hδσ : σ δ=if q%3=1 then δ else -δ := hF
  have hprod : (x+δ)*(x-δ)=block x := by
    calc
      _ = x^2-δ^2 := by ring
      _ = _ := by rw [hδ,block,sub_neg_eq_add]
  have hx0 : x+δ≠0 ∧ x-δ≠0 := by
    have hh : (x+δ)*(x-δ)≠0 := hprod ▸ hB
    exact ⟨left_ne_zero_of_mul hh,right_ne_zero_of_mul hh⟩
  have ht0 : torus x δ≠0 := div_ne_zero hx0.1 hx0.2
  have hσt : (torus x δ)^q = if q%3=1 then torus x δ else (torus x δ)⁻¹ := by
    change σ (torus x δ)=_
    unfold torus
    rw [map_div₀,map_add,map_sub,hxσ,hδσ]
    split
    · rfl
    · rw [inv_div]; simp [sub_eq_add_neg]
  rcases prime_mod_three q hp hgt with hmod | hmod
  · have hqmul : (q-1)/3*3=q-1 := by omega
    rw [probePower,ite_eq_left hmod,←pow_mul,hqmul]
    apply mul_right_cancel₀ ht0
    rw [←pow_succ, show q-1+1=q by omega,one_mul,hσt,ite_eq_left hmod]
  · have hn : ¬ q%3=1 := by omega
    have hqmul : (q+1)/3*3=q+1 := by omega
    rw [probePower,ite_eq_right hn,←pow_mul,hqmul,pow_succ,hσt,ite_eq_right hn,inv_mul_cancel₀ ht0]

/-- Universal signed readout carried out entirely in the scalar base field.
The extension supplies only a semantic comparison with its three torus labels,
not a computational dependency of the evaluator. -/
private theorem base_field_signed_probe {F : Type*} [CommRing F] (f : F →+* K) (hf : Function.Injective f)
    (q : ℕ) [CharP K q] (hp : q.Prime) (hgt : 3<q) (x : F) (δ : K)
    (hδ : δ^2=-3) (hB : block x≠0)
    (hx : (f x)^q=f x)
    (hF : δ^q=if q%3=1 then δ else -δ) :
    let m := probePower q
    let z := (torus (f x) δ)^m
    (numer x m = 0 ↔ z=1) ∧
    (numer x m = (block x)^m ↔ z=omegaOf δ) ∧
    (numer x m = -(block x)^m ↔ z=(omegaOf δ)⁻¹) := by
  have hBK : block (f x)≠0 := by simpa [block,map_ofNat] using hf.ne hB
  have h2 : (2:K)≠0 := small_ne q 2 (by decide) (by omega)
  have h3 : (3:K)≠0 := small_ne q 3 (by decide) hgt
  let m := probePower q
  have hS := scalar_signed_comparisons (f x) δ m hδ hBK h2 h3
    (torus_cube q hp hgt (f x) δ hδ hBK hx hF)
  have hmapB : f (block x)=block (f x) := by simp [block,map_ofNat]
  have hN := map_numer f x m
  change (numer x m=0 ↔ _) ∧ (numer x m=(block x)^m ↔ _) ∧
    (numer x m=-(block x)^m ↔ _)
  refine ⟨?_,?_,?_⟩
  · rw [← hS.1,←hN,←map_zero f,hf.eq_iff]
  · rw [←hS.2.1,←hN,←hmapB,←map_pow,hf.eq_iff]
  · rw [←hS.2.2,←hN,←hmapB,←map_pow,←map_neg,hf.eq_iff]

end Finite

section Field
variable {K : Type*} [Field K]

/-- The actual radicand of the native cubic. -/
def cardanoBeta (x δ : K) := block x * (-x+δ)

/-- Math used by the protected short inert readout, plus the split power. -/
def shortPower (q : ℕ) (x δ : K) :=
  if q%3=1 then (cardanoBeta x δ)^(probePower q)
  else (cardanoBeta x δ)^(probePower q)/block x

private theorem cardano_power_eq_torus (q : ℕ) [CharP K q] (hp : q.Prime) (hgt : 3<q)
    (x δ : K) (hδ : δ^2=-3) (hB : block x≠0) (hx : x^q=x)
    (hF : δ^q=if q%3=1 then δ else -δ) :
    shortPower q x δ = (torus x δ)^(probePower q) := by
  let _ : ExpChar K q := .prime hp
  let σ := frobenius K q
  have hprod : (x+δ)*(x-δ)=block x := by
    calc
      _ = x^2-δ^2 := by ring
      _ = _ := by rw [hδ,block,sub_neg_eq_add]
  have hn := right_ne_zero_of_mul (show (x+δ)*(x-δ)≠0 by rw [hprod]; exact hB)
  let a := δ-x
  have hBeta : cardanoBeta x δ = a^3 * torus x δ := by
    unfold cardanoBeta a torus
    rw [← hprod]
    field_simp
    ring
  have ha0 : a≠0 := by
    unfold a
    rw [← neg_sub,neg_ne_zero]
    exact hn
  have hxσ : σ x=x := hx
  have hδσ : σ δ=if q%3=1 then δ else -δ := hF
  have haσ : a^q= (if q%3=1 then δ else -δ)-x := by
    change σ (δ-x)=_
    rw [map_sub,hxσ,hδσ]
  have hnot : ¬ q%3=0 := by
    intro hh
    have hd : 3∣q := Nat.dvd_of_mod_eq_zero hh
    have he := (Nat.prime_dvd_prime_iff_eq (show Nat.Prime 3 from by decide) hp).mp hd
    omega
  by_cases h1 : q%3=1
  · have hqm : 3*((q-1)/3)=q-1 := by omega
    have ha : a^(q-1)=1 := by
      apply mul_right_cancel₀ ha0
      rw [←pow_succ,show q-1+1=q by omega,one_mul,haσ,ite_eq_left h1]
    rw [shortPower,ite_eq_left h1,probePower,ite_eq_left h1,hBeta,mul_pow,←pow_mul,hqm,ha,one_mul]
  · have hqm : 3*((q+1)/3)=q+1 := by omega
    have ha : a^(q+1)=block x := by
      rw [pow_succ,haσ,ite_eq_right h1,← hprod]
      unfold a
      ring
    rw [shortPower,ite_eq_right h1,probePower,ite_eq_right h1,hBeta,mul_pow,←pow_mul,hqm,ha,
      mul_comm (block x),mul_div_cancel_right₀ _ hB]

/-- The signed scalar comparisons express exactly the actual Cardano
short-power output, with no root or inverse used on the computational side. -/
private theorem scalar_equals_cardano_readout {F : Type*} [CommRing F] (f : F →+* K)
    (hf : Function.Injective f) (q : ℕ) [CharP K q] (hp : q.Prime) (hgt : 3<q)
    (x : F) (δ : K) (hδ : δ^2=-3) (hB : block x≠0) (hx : (f x)^q=f x)
    (hF : δ^q=if q%3=1 then δ else -δ) :
    let m := probePower q
    let z := shortPower q (f x) δ
    (numer x m = 0 ↔ z=1) ∧
    (numer x m = (block x)^m ↔ z=omegaOf δ) ∧
    (numer x m = -(block x)^m ↔ z=(omegaOf δ)⁻¹) := by
  have hBK : block (f x)≠0 := by simpa [block,map_ofNat] using hf.ne hB
  simpa only [cardano_power_eq_torus q hp hgt _ _ hδ hBK hx hF] using
    (base_field_signed_probe f hf q hp hgt x δ hδ hB hx hF)

end Field

section Field
variable {K : Type*} [Field K]

/-- Rational orientation: the degree-two residue-field witness is inverted. -/
def rationalCardano (q : ℕ) (x δ : K) :=
  if q%3=1 then (cardanoBeta x δ)^((q-1)/3)
  else ((cardanoBeta x δ)^((q^2-1)/3))⁻¹

private theorem scalar_oriented_readout {F : Type*} [CommRing F] (f : F →+* K)
    (hf : Function.Injective f) (q : ℕ) [CharP K q] (hp : q.Prime) (hgt : 3<q)
    (x : F) (δ : K) (hδ : δ^2=-3) (hB : block x≠0) (hx : (f x)^q=f x)
    (hF : δ^q=if q%3=1 then δ else -δ) :
    let m := probePower q
    let z := rationalCardano q (f x) δ
    let w := if q%3=1 then omegaOf δ else (omegaOf δ)⁻¹
    (numer x m = 0 ↔ z=1) ∧
    (numer x m = (block x)^m ↔ z=w) ∧
    (numer x m = -(block x)^m ↔ z=w⁻¹) := by
  have H := scalar_equals_cardano_readout f hf q hp hgt x δ hδ hB hx hF
  by_cases hmod : q%3=1
  · simpa only [rationalCardano,shortPower,probePower,ite_eq_left hmod] using H
  · have hmod2 : q%3=2 := by
      have hz : q%3≠0 := by
        intro h
        have hd : 3∣q := Nat.dvd_of_mod_eq_zero h
        have he := (Nat.prime_dvd_prime_iff_eq (show Nat.Prime 3 from by decide) hp).mp hd
        omega
      omega
    have hBK : (f x)^2+3≠0 := by simpa [block,map_ofNat] using hf.ne hB
    have hF' : δ^q=-δ := by simpa only [ite_eq_right hmod] using hF
    have hp2 :=
      (D5.S3.Arith.Primes.GoldenCubicInertFrobeniusReadout.native_inert_readout q hp hgt
        hmod2 (f x) δ hδ hF' hx hBK).2.1
    simp only [shortPower,probePower,ite_eq_right hmod] at H
    change (cardanoBeta (f x) δ)^((q^2-1)/3) =
      (cardanoBeta (f x) δ)^((q+1)/3)/block (f x) at hp2
    simpa only [rationalCardano,probePower,ite_eq_right hmod,hp2,
      inv_eq_one,inv_inj] using H

end Field

section PrimeField
variable {K : Type*} [Field K]

/-- The sign of the square root under prime Frobenius is forced by its
quadratic relation and the residue of q modulo three. -/
private theorem delta_frob (q : ℕ) [CharP K q] (hp : q.Prime) (hgt : 3<q)
    (δ : K) (hδ : δ^2=-3) :
    δ^q = if q%3=1 then δ else -δ := by
  let _ : ExpChar K q := .prime hp
  let σ := frobenius K q
  let w := omegaOf δ
  have h2 : (2:K)≠0 := small_ne q 2 (by decide) (by omega)
  have hsum : w+w⁻¹ = -1 := (omega_coordinates δ hδ h2).2.1
  have hw0 : w≠0 := by
    intro he
    simp [he] at hsum
  have hquad : w^2+w+1=0 := by
    calc
      _ = w*(w+w⁻¹+1) := by rw [mul_add,mul_add,mul_inv_cancel₀ hw0]; ring
      _ = 0 := by rw [hsum,neg_add_cancel,mul_zero]
  have hw3 : w^3=1 := by
    apply sub_eq_zero.mp
    calc
      _ = (w-1)*(w^2+w+1) := by ring
      _ = 0 := by rw [hquad,mul_zero]
  have heδ : δ = 2*w+1 := by
    unfold w omegaOf
    field_simp
    ring
  have hpow : σ w = w^(q%3) := by
    change w^q=_
    conv_lhs => rw [show q=3*(q/3)+q%3 by omega]
    rw [pow_add,pow_mul,hw3,one_pow,one_mul]
  change σ δ = _
  rw [heδ,map_add,map_mul,map_ofNat,map_one,hpow]
  rcases prime_mod_three q hp hgt with h|h
  · simp only [h,pow_one,ite_true]
  · have hh : ¬q%3=1 := by omega
    rw [ite_eq_right hh,h]
    have he : w^2= -(w+1) := eq_neg_of_add_eq_zero_left (by simpa only [add_assoc] using hquad)
    rw [he]
    ring

/-- The three signed scalar comparisons over the actual prime field recover
the orientation of the same native Cardano witness at every good odd prime. -/
theorem prime_field_scalar_oriented_readout (q : ℕ) [CharP K q]
    (hp : q.Prime) (hgt : 3<q) (x : ZMod q) (δ : K) (hδ : δ^2=-3)
    (hB : block x≠0) :
    let m := probePower q
    let z := rationalCardano q (ZMod.castHom (dvd_rfl : q∣q) K x) δ
    let w := if q%3=1 then omegaOf δ else (omegaOf δ)⁻¹
    (numer x m = 0 ↔ z=1) ∧
    (numer x m = (block x)^m ↔ z=w) ∧
    (numer x m = -(block x)^m ↔ z=w⁻¹) := by
  let f := ZMod.castHom (dvd_rfl : q∣q) K
  have hf : Function.Injective f := by
    intro a b he
    obtain ⟨i,rfl⟩ := ZMod.intCast_surjective a
    obtain ⟨j,rfl⟩ := ZMod.intCast_surjective b
    simp only [map_intCast] at he
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub i j q).mpr
    apply (CharP.intCast_eq_zero_iff K q (j-i)).mp
    rw [Int.cast_sub,he,sub_self]
  have hx : (f x)^q=f x := by
    let _ : ExpChar K q := .prime hp
    obtain ⟨i,rfl⟩ := ZMod.intCast_surjective x
    change frobenius K q (f (i : ZMod q))=f (i : ZMod q)
    simp only [map_intCast]
  exact scalar_oriented_readout f hf q hp hgt x δ hδ hB hx (delta_frob q hp hgt δ hδ)

end PrimeField
#print axioms prime_field_scalar_oriented_readout
end D5.S3.Arith.Primes.GoldenCubicScalarFrobeniusReadout
