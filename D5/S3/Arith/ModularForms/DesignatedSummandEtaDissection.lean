/- GID: D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/DesignatedSummandEtaDissection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries]
   utility: none
   digest: Integral dissections control the progression supports of the reciprocal and square. -/

import D5.S3.Arith.ModularForms.DesignatedSummandThetaDissection
import D5.S3.Combinatorics.Partitions.DesignatedSummands
import D5.S3.Combinatorics.PowerSeries.DyadicDilation

/-! The reciprocal of the designated-summand series has no coefficients of degree 3 modulo 4. The square has an integral odd multiplier with coefficients divisible by 4 in odd degree. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

namespace D5.S3.Arith.ModularForms.DesignatedSummandEtaDissection

open PowerSeries Finset Filter
open scoped PowerSeries.WithPiTopology
open D5.S3.Combinatorics.PowerSeries.DilatedEulerProduct D5.S3.Combinatorics.Partitions.DesignatedSummands D5.S3.Arith.ModularForms.DesignatedSummandThetaDissection D5.S3.Combinatorics.PowerSeries.DyadicDilation

section ReciprocalDissection

local notation "u[" d "]" => (etaUnit d (by decide))

private theorem from_mul_unit {R : Type*} [CommRing R] {p : R} {a b : Rˣ}
    (h : p * ↑a = (b : R)) : p = (↑(b/a) : R) := by
  rw [← mul_one p, ← a.mul_inv, ← mul_assoc, h]
  rfl

private noncomputable def Hu {R : Type*} [CommRing R] : (PowerSeries R)ˣ :=
  u[1]*u[2]*u[3]/u[6]

noncomputable def H {R : Type*} [CommRing R] : PowerSeries R := ↑(Hu (R := R))

private noncomputable def H₀u {R : Type*} [CommRing R] : (PowerSeries R)ˣ :=
  u[1]^2 * u[4]^2 * u[6]^4 / (u[2]^2 * u[3]^2 * u[12]^2)

private noncomputable def Tu {R : Type*} [CommRing R] : (PowerSeries R)ˣ :=
  u[1]^4 * u[6]^2 / (u[2]^2 * u[3]^2)

noncomputable def H₀ {R : Type*} [CommRing R] : PowerSeries R := ↑(H₀u (R := R))
noncomputable def T {R : Type*} [CommRing R] : PowerSeries R := ↑(Tu (R := R))

private theorem coe_unit_map {R S : Type*} [Monoid R] [Monoid S] (f : R →* S) (u : Rˣ) :
    f ↑u = ↑(Units.map f u) := rfl

private theorem F_eq_unit {R : Type*} [CommRing R] : (F : PowerSeries R) = ↑((Hu (R := R))⁻¹) := by
  let d : (PowerSeries R)ˣ := u[1]*u[2]*u[3]
  have h : ((↑d : PowerSeries R) * invOne ↑d) = 1 := mul_invOne
    (by simp [d, etaUnit, euler_const])
  have hd : invOne (↑d : PowerSeries R) = ↑d⁻¹ := by
    calc
      _ = ↑d⁻¹ * ((↑d : PowerSeries R) * invOne ↑d) := by rw [← mul_assoc]; simp
      _ = _ := by rw [h, mul_one]
  change (euler 6 (by decide) : PowerSeries R) * invOne ↑d = _
  rw [hd]
  change ((↑(u[6] : (PowerSeries R)ˣ) : PowerSeries R) * ↑d⁻¹) =
    (↑((d/u[6])⁻¹ : (PowerSeries R)ˣ) : PowerSeries R)
  rw [← Units.val_mul]
  congr 1

theorem FH {R : Type*} [CommRing R] : (F : PowerSeries R) * H = 1 := by
  rw [F_eq_unit, H, ← Units.val_mul, inv_mul_cancel, Units.val_one]

private theorem H_dissection_rat :
    (H : PowerSeries ℚ) = expand 2 (by decide) H₀ - PowerSeries.X * expand 4 (by decide) T := by
  let c : (PowerSeries ℚ)ˣ := u[2]^2/(u[4]*u[12])
  have hU : U = (↑(u[4]*u[1]/u[2] : (PowerSeries ℚ)ˣ) : PowerSeries ℚ) :=
    from_mul_unit (R := PowerSeries ℚ) (p := U) (a := u[2]) (b := u[4]*u[1]) U_product
  have hp : phi = (↑(u[2]^5/(u[1]^2*u[4]^2) : (PowerSeries ℚ)ˣ) : PowerSeries ℚ) :=
    from_mul_unit (R := PowerSeries ℚ) (p := phi) (a := u[1]^2*u[4]^2) (b := u[2]^5) phi_product
  have hs : psi = (↑(u[2]^2/u[1] : (PowerSeries ℚ)ˣ) : PowerSeries ℚ) :=
    from_mul_unit (R := PowerSeries ℚ) (p := psi) (a := u[1]) (b := u[2]^2) psi_product
  have h := congrArg (fun p : PowerSeries ℚ => (↑c : PowerSeries ℚ) * p) U_dissection
  rw [hU,hp,hs] at h
  simp only [mul_sub] at h
  have hl : (↑c : PowerSeries ℚ) *
     ((↑(u[4]*u[1]/u[2] : (PowerSeries ℚ)ˣ) : PowerSeries ℚ) *
      expand 3 (by decide) (↑(u[4]*u[1]/u[2] : (PowerSeries ℚ)ˣ))) = H := by
    change (↑c : PowerSeries ℚ) * (↑(u[4]*u[1]/u[2] : (PowerSeries ℚ)ˣ) *
      (expand 3 (by decide) (R := ℚ)).toMonoidHom (↑(u[4]*u[1]/u[2] : (PowerSeries ℚ)ˣ))) = _
    simp only [coe_unit_map, ← Units.val_mul]
    congr 1
    simp only [map_div, map_mul, expand_eta, Nat.reduceMul, c, H, Hu]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_inv, ofMul_pow, ofMul_one]
    abel
  have h₀ : (↑c : PowerSeries ℚ) *
      (expand 4 (by decide) (↑(u[2]^2/u[1] : (PowerSeries ℚ)ˣ)) *
       expand 6 (by decide) (↑(u[2]^5/(u[1]^2*u[4]^2) : (PowerSeries ℚ)ˣ))) =
      expand 2 (by decide) H₀ := by
    change (↑c : PowerSeries ℚ) *
      ((expand 4 (by decide) (R := ℚ)).toMonoidHom ↑(u[2]^2/u[1] : (PowerSeries ℚ)ˣ) *
       (expand 6 (by decide) (R := ℚ)).toMonoidHom ↑(u[2]^5/(u[1]^2*u[4]^2) : (PowerSeries ℚ)ˣ)) =
      (expand 2 (by decide) (R := ℚ)).toMonoidHom ↑(H₀u (R := ℚ))
    simp only [coe_unit_map, ← Units.val_mul]
    congr 1
    simp only [H₀u, map_div, map_mul, map_pow, expand_eta, Nat.reduceMul, c]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_inv, ofMul_pow, ofMul_one]
    abel
  have hT : (↑c : PowerSeries ℚ) *
      (expand 2 (by decide) (↑(u[2]^5/(u[1]^2*u[4]^2) : (PowerSeries ℚ)ˣ)) *
       expand 12 (by decide) (↑(u[2]^2/u[1] : (PowerSeries ℚ)ˣ))) =
      expand 4 (by decide) T := by
    change (↑c : PowerSeries ℚ) *
      ((expand 2 (by decide) (R := ℚ)).toMonoidHom ↑(u[2]^5/(u[1]^2*u[4]^2) : (PowerSeries ℚ)ˣ) *
       (expand 12 (by decide) (R := ℚ)).toMonoidHom ↑(u[2]^2/u[1] : (PowerSeries ℚ)ˣ)) =
      (expand 4 (by decide) (R := ℚ)).toMonoidHom ↑(Tu (R := ℚ))
    simp only [coe_unit_map, ← Units.val_mul]
    congr 1
    simp only [Tu, map_div, map_mul, map_pow, expand_eta, Nat.reduceMul, c]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_inv, ofMul_pow, ofMul_one]
    abel
  rw [hl, h₀, mul_left_comm (↑c : PowerSeries ℚ), hT] at h
  exact h

theorem H_dissection :
    (H : PowerSeries ℤ) = expand 2 (by decide) H₀ - PowerSeries.X * expand 4 (by decide) T := by
  let g := Int.castRingHom ℚ
  apply PowerSeries.map_injective g (Int.cast_injective (α := ℚ))
  rw [map_sub, map_mul, PowerSeries.map_X, map_expand, map_expand]
  change (PowerSeries.map g).toMonoidHom (↑(Hu (R := ℤ))) =
    expand 2 (by decide) ((PowerSeries.map g).toMonoidHom (↑(H₀u (R := ℤ)))) -
      PowerSeries.X * expand 4 (by decide) ((PowerSeries.map g).toMonoidHom (↑(Tu (R := ℤ))))
  simp only [coe_unit_map, Hu, H₀u, Tu, map_div, map_mul, map_pow, map_eta]
  exact H_dissection_rat

theorem H_support (n : ℕ) : coeff (4*n+3) (H : PowerSeries ℤ) = 0 := by
  rw [H_dissection, map_sub, coeff_expand_of_not_dvd 2 _ _ (by omega)]
  rw [show (PowerSeries.X : PowerSeries ℤ) * expand 4 (by decide) T =
    PowerSeries.X ^ 1 * expand 4 (by decide) T by rw [pow_one], coeff_X_pow_mul', ite_eq_left (by omega)]
  rw [coeff_expand_of_not_dvd 4 _ _ (by omega), sub_zero]

end ReciprocalDissection

section SquareDissection

local notation "P" => PowerSeries ℤ
local notation "x" => (PowerSeries.X : P)
local notation "u[" d "]" => (etaUnit (R := ℤ) d (by decide))
local notation "s" => PowerSeries.rescale (-1 : ℤ)

private local instance : TopologicalSpace ℤ := ⊥
private local instance : DiscreteTopology ℤ := ⟨rfl⟩

private noncomputable def finEta (d N : ℕ) : P :=
  ∏ i ∈ range N, (1 - x ^ (d * (i+1)))

private noncomputable def finOdd (d N : ℕ) : P :=
  ∏ i ∈ range N, (1 - x ^ (d*(2*i+1)))

private theorem finEta_split (d N : ℕ) :
    finEta d (2*N) = finEta (2*d) N * finOdd d N := by
  simp only [finEta, finOdd]
  rw [prod_split_two, mul_comm]
  congr 1
  apply prod_congr rfl
  intro i _
  congr 2
  ring

private theorem sign_X_pow (n : ℕ) : s (x^n) = C ((-1 : ℤ)^n)*x^n := by
  rw [map_pow, rescale_X, mul_pow, map_pow]

private theorem sign_X_pow_even {n : ℕ} (hn : Even n) : s (x^n) = x^n := by
  rw [sign_X_pow, hn.neg_one_pow, map_one, one_mul]

private theorem sign_X_pow_odd {n : ℕ} (hn : Odd n) : s (x^n) = -(x^n) := by
  rw [sign_X_pow, hn.neg_one_pow, map_neg, map_one, neg_one_mul]

private theorem finEta_sign_even (d N : ℕ) : s (finEta (2*d) N) = finEta (2*d) N := by
  simp only [finEta, map_prod, map_sub, map_one]
  apply prod_congr rfl
  intro i _
  rw [sign_X_pow_even (by use d*(i+1); ring)]

private theorem finOdd_sign (d N : ℕ) (hd : Odd d) :
    finOdd d N * s (finOdd d N) = finOdd (2*d) N := by
  simp only [finOdd, map_prod, map_sub, map_one, ← prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  rw [sign_X_pow_odd (hd.mul ⟨i, by rfl⟩), show (2*d)*(2*i+1)=d*(2*i+1)*2 by ring, pow_mul]
  ring

private theorem finEta_pair (d N : ℕ) (hd : Odd d) :
    (finEta d (2*N) * s (finEta d (2*N))) * finEta (4*d) N =
      finEta (2*d) N ^ 2 * finEta (2*d) (2*N) := by
  rw [finEta_split d, map_mul, finEta_sign_even, finEta_split (2*d)]
  have h := finOdd_sign d N hd
  calc
    _ = (finEta (2*d) N)^2 * (finOdd d N * s (finOdd d N)) * finEta (4*d) N := by ring
    _ = _ := by rw [h, show 2*(2*d)=4*d by ring]; ring

private theorem continuous_sign : Continuous (fun p : P => s p) := by
  rw [continuous_iff_continuousAt]
  intro p
  apply (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto _ _ _ _).2
  intro n
  simp only [coeff_rescale]
  exact tendsto_const_nhds.mul
    (PowerSeries.WithPiTopology.continuous_coeff ℤ n).continuousAt

private theorem euler_pair_odd (d : ℕ) (hd : d ≠ 0) (ho : Odd d) :
    ((euler d hd : P) * s (euler d hd)) * euler (4*d) (by positivity) =
      (euler (2*d) (by positivity) : P)^3 := by
  have h := (euler_tendsto (R := ℤ) d hd).comp (tendsto_scale 2 (by decide))
  have hg := (euler_tendsto (R := ℤ) (2*d) (by positivity))
  have h4 := euler_tendsto (R := ℤ) (4*d) (by positivity)
  have hl := (h.mul (continuous_sign.continuousAt.tendsto.comp h)).mul h4
  change Tendsto (fun N => (finEta d (2*N) * s (finEta d (2*N))) * finEta (4*d) N) atTop _ at hl
  simp only [finEta_pair d _ ho] at hl
  have hr := (hg.pow 2).mul (hg.comp (tendsto_scale 2 (by decide)))
  simpa only [← pow_succ] using tendsto_nhds_unique hl hr

private theorem rescale_even {R : Type*} [CommRing R] (d : ℕ) (hd : d ≠ 0) (he : Even d)
    (p : PowerSeries R) : rescale (-1 : R) (expand d hd p) = expand d hd p := by
  ext n
  rw [coeff_rescale, coeff_expand]
  split_ifs with h
  · obtain ⟨t,rfl⟩ := h
    rw [(he.mul_right t).neg_one_pow, one_mul]
  · rw [mul_zero]

private theorem sign_eta_even (d : ℕ) (hd : d ≠ 0) (he : Even d) :
    Units.map (PowerSeries.rescale (-1 : ℤ)).toMonoidHom (etaUnit d hd) = etaUnit d hd := by
  apply Units.ext
  exact rescale_even d hd he _

private theorem sign_eta_odd (d : ℕ) (hd : d ≠ 0) (ho : Odd d) :
    Units.map (PowerSeries.rescale (-1 : ℤ)).toMonoidHom (etaUnit d hd) =
      etaUnit (2*d) (by positivity)^3 / (etaUnit d hd * etaUnit (4*d) (by positivity)) := by
  have hh := euler_pair_odd d hd ho
  apply Units.ext
  apply from_mul_unit (R := P) (a := etaUnit d hd * etaUnit (4*d) (by positivity))
    (b := etaUnit (2*d) (by positivity)^3)
  change s (euler d hd) * (euler d hd * euler (4*d) (by positivity)) =
    (euler (2*d) (by positivity) : P)^3
  rw [← mul_left_comm (euler d hd), ← mul_assoc]
  exact hh

private noncomputable def Nu : Pˣ := u[2]*u[6]/(u[1]^5*u[3])
private noncomputable def N : P := ↑Nu

private theorem H_norm :
    ((H : P) * s H) * expand 2 (by decide) N = 1 := by
  change (↑(Hu (R := ℤ)) : P) * (PowerSeries.rescale (-1 : ℤ)).toMonoidHom ↑(Hu (R := ℤ)) *
    (expand 2 (by decide) (R := ℤ)).toMonoidHom ↑Nu = ↑(1 : Pˣ)
  simp only [coe_unit_map, ← Units.val_mul]
  congr 1
  unfold Hu Nu
  simp only [map_div, map_mul, map_pow, expand_eta, Nat.reduceMul,
    sign_eta_odd 1 (by decide) (by decide), sign_eta_odd 3 (by decide) (by decide),
    sign_eta_even 2 (by decide) (by decide), sign_eta_even 6 (by decide) (by decide),
    Nat.reduceMul]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_inv, ofMul_pow, ofMul_one]
  abel

private theorem F_dissection :
    (F : P) = expand 2 (by decide) N *
      (expand 2 (by decide) H₀ + x*expand 4 (by decide) T) := by
  have hn : (F : P) = expand 2 (by decide) N * s H := by
    calc
      _ = F * ((H * s H) * expand 2 (by decide) N) := by rw [H_norm, mul_one]
      _ = (F * H) * (expand 2 (by decide) N * s H) := by ring
      _ = _ := by rw [FH, one_mul]
  rw [hn, H_dissection, map_sub, map_mul, rescale_even 2 (by decide) (by decide),
    rescale_even 4 (by decide) (by decide)]
  rw [show s x = -x by simpa only [pow_one] using sign_X_pow_odd (n := 1) (by decide)]
  ring

noncomputable def W : P :=
  ↑(u[2]^4*u[6]^4/(u[1]^8*u[3]^4) : Pˣ)

noncomputable def E : P := N^2 * (H₀^2 + x*(expand 2 (by decide) T)^2)

private theorem W_factor : N^2 * H₀ * expand 2 (by decide) T = W := by
  change (↑Nu : P)^2 * ↑(H₀u (R := ℤ)) * (expand 2 (by decide) (R := ℤ)).toMonoidHom
    ↑(Tu (R := ℤ)) = ↑(u[2]^4*u[6]^4/(u[1]^8*u[3]^4) : Pˣ)
  simp only [coe_unit_map, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
  congr 1
  simp only [Nu, H₀u, Tu, map_div, map_mul, map_pow, expand_eta, Nat.reduceMul]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_inv, ofMul_pow, ofMul_one]
  abel

theorem F_square :
    (F : P)^2 = expand 2 (by decide) E + 2*x*expand 2 (by decide) W := by
  rw [E, ← W_factor, F_dissection]
  simp only [map_mul, map_add, map_pow, expand_X]
  rw [← expand_mul]
  ring

private theorem reduce_W : reduce 4 W = (reduce 4 (euler 6 (by decide)))^2 := by
  let g := reduce 4
  let gu := Units.map g.toMonoidHom
  have lift_eta (d : ℕ) (hd : d ≠ 0) :
      gu (etaUnit d hd)^4 = gu (etaUnit (2*d) (by positivity))^2 := by
    apply Units.ext
    change (g (euler d hd))^4 = (g (euler (2*d) (by positivity)))^2
    have h := reduce_lift (euler d hd) 1 0
    change reduce 4 ((euler d hd : P)^4) = reduce 4 (expand 2 (by decide) ((euler d hd : P)^2)) at h
    have he : expand 2 (by decide) (euler d hd : P) = euler (2*d) (by positivity) := by
      exact (expand_mul 2 (by decide) d hd _).symm
    simpa only [map_pow, he, g] using h
  change g.toMonoidHom (↑(u[2]^4*u[6]^4/(u[1]^8*u[3]^4) : Pˣ)) =
    (g.toMonoidHom (↑(u[6] : Pˣ)))^2
  simp only [coe_unit_map, ← Units.val_pow_eq_pow_val]
  congr 1
  change gu (u[2]^4*u[6]^4/(u[1]^8*u[3]^4)) = _
  change gu (u[2]^4*u[6]^4/(u[1]^8*u[3]^4)) = gu u[6] ^ 2
  rw [show 8 = 4*2 by decide, pow_mul]
  simp only [map_div, map_mul, map_pow]
  rw [lift_eta 1 (by decide), lift_eta 3 (by decide)]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_inv, ofMul_pow, ofMul_one]
  abel

theorem W_support (n : ℕ) : (4 : ℤ) ∣ coeff (2*n+1) W := by
  have h6 : (reduce 4 (euler 6 (by decide))) =
      expand 2 (by decide) (reduce 4 (euler 3 (by decide))) := by
    unfold reduce
    rw [← map_expand]
    exact congrArg (PowerSeries.map (Int.castRingHom (ZMod 4)))
      (expand_mul 2 (by decide) 3 (by decide) (pentagonalSeries ℤ))
  apply (coeff_reduce_eq_zero 4 (2*n+1) W).mp
  rw [reduce_W, h6, ← map_pow]
  exact coeff_expand_of_not_dvd _ _ _ (by omega)

end SquareDissection

end D5.S3.Arith.ModularForms.DesignatedSummandEtaDissection
