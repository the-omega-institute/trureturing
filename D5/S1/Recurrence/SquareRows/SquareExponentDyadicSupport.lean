/- GID: D5/S1/Recurrence/SquareRows/SquareExponentDyadicSupport
   generality: G
   mirror-B: D5/B/S1/Recurrence/SquareRows/SquareExponentDyadicSupport
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The integer square-exponent series has exactly the conjectured dyadic odd support. -/

import D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

open PowerSeries

noncomputable section

namespace D5.S1.Recurrence.SquareRows.SquareExponentDyadicSupport

variable {R : Type*} [CommRing R]

private def geom (e : ℕ) : PowerSeries R := mk fun n => (e : R)^n

private theorem geom_eq (e : ℕ) : (1 - C (e : R) * X) * geom (R := R) e = 1 := by
  ext n
  cases n with
  | zero => simp [geom]
  | succ n =>
    rw [sub_mul, one_mul, mul_assoc, map_sub, coeff_C_mul, coeff_succ_X_mul]
    simp [geom, pow_succ, mul_comm]

private theorem geom_derivative (e : ℕ) : derivative R (geom e) = C (e : R) * (geom e)^2 := by
  have h := congrArg (fun f => derivative R f) (geom_eq (R := R) e)
  simp only [Derivation.map_sub, Derivation.leibniz, derivative_one, derivative_C,
    derivative_X, smul_eq_mul, mul_zero, mul_one, zero_sub] at h
  have h' := congrArg (fun f => f * geom (R := R) e) h
  have hg := geom_eq (R := R) e
  linear_combination h' - derivative R (geom e) * hg

private def row (F : PowerSeries R) (n : ℕ) : R :=
  coeff n (F^((n+1)^2) * geom ((n+1)^2))

private def derivRow (F : PowerSeries R) (n : ℕ) : R :=
  coeff (n-1) (F^((n+1)^2-1) * derivative R F * geom ((n+1)^2) +
    F^((n+1)^2) * geom ((n+1)^2)^2)

private def normalized (F : PowerSeries R) (n : ℕ) : R := row F n - (n+2) * derivRow F n


private theorem derivative_row (F : PowerSeries R) (n : ℕ) (hn : 0 < n) :
    (n : R) * row F n = ((n+1)^2 : ℕ) * derivRow F n := by
  have h := congrArg (coeff (n-1)) ((derivative R).leibniz
    (F^((n+1)^2)) (geom ((n+1)^2)))
  rw [coeff_derivative, Nat.sub_add_cancel hn, derivative_pow, geom_derivative] at h
  have hc : (((n+1)^2 : ℕ) : PowerSeries R) = C (((n+1)^2 : ℕ) : R) := by simp
  simp only [smul_eq_mul, hc] at h
  have hfact : F ^ ((n+1)^2) * (C (((n+1)^2 : ℕ) : R) * geom ((n+1)^2)^2) +
      geom ((n+1)^2) * (C (((n+1)^2 : ℕ) : R) * F^((n+1)^2-1) * derivative R F) =
      C (((n+1)^2 : ℕ) : R) *
        (F^((n+1)^2-1) * derivative R F * geom ((n+1)^2) +
        F^((n+1)^2) * geom ((n+1)^2)^2) := by ring
  rw [hfact, coeff_C_mul] at h
  have hncast : ((n-1 : ℕ) : R) + 1 = n := by
    exact (by simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun k : ℕ => (k : R)) (Nat.sub_add_cancel hn))
  simpa only [row, derivRow, hncast, mul_comm] using h


private theorem exact_normalization (F : PowerSeries R) (n : ℕ) (hn : 0 < n) :
    row F n = (((n+1)^2 : ℕ) : R) * normalized F n := by
  have h := derivative_row F n hn
  simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] at h ⊢
  dsimp [normalized]
  linear_combination -(n+2 : R) * h

private abbrev F2 := ZMod 2
private instance : CharP (PowerSeries F2) 2 :=
  CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (by
    simpa only [map_ofNat, map_zero] using
      congrArg (C (R := ZMod 2)) (show (2 : ZMod 2) = 0 by decide))

private theorem square_expand (F : PowerSeries F2) : F^2 = expand 2 (by decide) F := by
  have h := MvPowerSeries.map_frobenius_expand (σ := Unit) (R := ZMod 2)
    2 (by decide) (f := F)
  rw [ZMod.frobenius_zmod, MvPowerSeries.map_id] at h
  exact h.symm

private theorem square_even (F : PowerSeries F2) (n : ℕ) : coeff (2*n) (F^2) = coeff n F := by
  rw [square_expand, coeff_expand_mul]

private theorem square_odd (F : PowerSeries F2) (n : ℕ) : coeff (2*n+1) (F^2) = 0 := by
  rw [square_expand, coeff_expand_of_not_dvd]
  omega

private theorem power_diagonal_zero (F : PowerSeries F2) (n t : ℕ) (hn : 0 < n) :
    coeff n (F^(2*n*t)) = 0 := by
  induction n using Nat.strong_induction_on generalizing t with
  | h n ih =>
    obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' n
    · subst n
      rw [show 2*(2*m)*t = (2*m*t)*2 by ring, pow_mul, square_even]
      exact ih m (by omega) t (by omega)
    · subst n
      rw [show 2*(2*m+1)*t = ((2*m+1)*t)*2 by ring, pow_mul, square_odd]

private def Agree (n : ℕ) (F G : PowerSeries R) : Prop := ∀ k < n, coeff k F = coeff k G

private theorem agree_iff (n : ℕ) (F G : PowerSeries R) :
    Agree n F G ↔ (X : PowerSeries R)^n ∣ F-G := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem agree_pow {n : ℕ} {F G : PowerSeries R} (h : Agree n F G) (e : ℕ) :
    Agree n (F^e) (G^e) :=
  (agree_iff _ _ _).mpr (((agree_iff _ _ _).mp h).trans (sub_dvd_pow_sub_pow F G e))

private theorem agree_mul {n : ℕ} {F G : PowerSeries R} (h : Agree n F G) (H : PowerSeries R) :
    Agree n (F*H) (G*H) := by
  apply (agree_iff _ _ _).mpr
  rw [← sub_mul]
  exact dvd_mul_of_dvd_left ((agree_iff _ _ _).mp h) H

private theorem leading_mul {n : ℕ} {U : PowerSeries R} (h : X^n ∣ U) (V : PowerSeries R) :
    coeff n (U*V) = coeff n U * constantCoeff V := by
  obtain ⟨W,rfl⟩ := h
  have hc (T : PowerSeries R) : coeff n (X^n*T) = constantCoeff T := by
    simpa only [zero_add, coeff_zero_eq_constantCoeff] using coeff_X_pow_mul T n 0
  rw [mul_assoc, hc, hc, map_mul]

private theorem pow_change {n : ℕ} {F G : PowerSeries R}
    (hF : constantCoeff F = 1) (hG : constantCoeff G = 1) (h : Agree n F G) (e : ℕ) :
    coeff n (F^e) - coeff n (G^e) = (e : R)*(coeff n F - coeff n G) := by
  induction e with
  | zero => simp
  | succ e ih =>
    have he : F^(e+1)-G^(e+1) = (F^e-G^e)*F + (F-G)*G^e := by ring
    rw [← map_sub, he, map_add, leading_mul ((agree_iff _ _ _).mp (agree_pow h e)),
      leading_mul ((agree_iff _ _ _).mp h)]
    simp only [map_sub, map_pow, hF, hG, one_pow, mul_one, ih, Nat.cast_add, Nat.cast_one]
    ring

private theorem row_change {n : ℕ} {F G : PowerSeries R}
    (hF : constantCoeff F = 1) (hG : constantCoeff G = 1) (h : Agree n F G) :
    row F n - row G n = (((n+1)^2 : ℕ) : R)*(coeff n F-coeff n G) := by
  dsimp [row]
  rw [← map_sub, ← sub_mul, leading_mul ((agree_iff _ _ _).mp (agree_pow h _))]
  simp only [geom, constantCoeff_mk, pow_zero, mul_one, map_sub]
  exact pow_change hF hG h _

private theorem derivRow_change {n : ℕ} {F G : PowerSeries R} (hn : 0 < n)
    (_hF : constantCoeff F = 1) (hG : constantCoeff G = 1) (h : Agree n F G) :
    derivRow F n - derivRow G n = (n : R)*(coeff n F-coeff n G) := by
  let e := (n+1)^2
  let g : PowerSeries R := geom e
  have hp := agree_mul (agree_pow h e) (g^2)
  have hl := agree_mul (agree_pow h (e-1)) g
  have hd : X^(n-1) ∣ derivative R F - derivative R G := by
    apply X_pow_dvd_iff.mpr
    intro k hk
    rw [map_sub, coeff_derivative, coeff_derivative, h (k+1) (by omega), sub_self]
  have hz : coeff (n-1) ((F^(e-1)*g-G^(e-1)*g)*derivative R F) = 0 := by
    have hdiv := dvd_mul_of_dvd_left ((agree_iff _ _ _).mp hl) (derivative R F)
    exact X_pow_dvd_iff.mp hdiv _ (by omega)
  have he : F^(e-1)*derivative R F*g - G^(e-1)*derivative R G*g =
      (F^(e-1)*g-G^(e-1)*g)*derivative R F +
      (derivative R F-derivative R G)*(G^(e-1)*g) := by ring
  change coeff (n-1) (F^(e-1)*derivative R F*g+F^e*g^2) -
    coeff (n-1) (G^(e-1)*derivative R G*g+G^e*g^2) = _
  rw [map_add, map_add, hp (n-1) (by omega)]
  rw [add_sub_add_right_eq_sub, ← map_sub, he, map_add, hz, zero_add, leading_mul hd]
  have hncast : ((n-1 : ℕ) : R)+1 = n := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      congrArg (fun k : ℕ => (k : R)) (Nat.sub_add_cancel hn)
  simp only [map_sub, coeff_derivative, Nat.sub_add_cancel hn, hncast, map_mul,
    map_pow, hG, one_pow, g, geom, constantCoeff_mk, pow_zero, mul_one]
  ring

private theorem normalized_change {n : ℕ} {F G : PowerSeries R} (hn : 0 < n)
    (hF : constantCoeff F = 1) (hG : constantCoeff G = 1) (h : Agree n F G) :
    normalized F n-normalized G n = coeff n F-coeff n G := by
  have hr := row_change hF hG h
  have ht := derivRow_change hn hF hG h
  simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] at hr
  dsimp [normalized]
  linear_combination hr-(n+2 : R)*ht

private def advance (F : PowerSeries R) : PowerSeries R :=
  mk fun n => if n=0 then 1 else coeff n F - normalized F n

private theorem advance_zero (F : PowerSeries R) : constantCoeff (advance F) = 1 := by
  simp [advance]

private theorem advance_agree {n : ℕ} {F G : PowerSeries R}
    (hF : constantCoeff F = 1) (hG : constantCoeff G = 1) (h : Agree n F G) :
    Agree (n+1) (advance F) (advance G) := by
  intro k hk
  simp only [advance, coeff_mk]
  split_ifs with hk0
  · rfl
  · have hd := normalized_change (by omega : 0 < k) hF hG (fun j hj => h j (by omega))
    linear_combination -hd


private def approximation : ℕ → PowerSeries R
  | 0 => 1
  | n+1 => advance (approximation n)

private theorem approximation_zero (n : ℕ) : constantCoeff (approximation (R := R) n) = 1 := by
  cases n with
  | zero => simp [approximation]
  | succ n => exact advance_zero _

private theorem approximation_stable {d s : ℕ} (h : d ≤ s) :
    Agree d (approximation (R := R) d) (approximation s) := by
  induction d generalizing s with
  | zero => intro k hk; omega
  | succ d ih =>
    cases s with
    | zero => omega
    | succ s => exact advance_agree (approximation_zero d) (approximation_zero s) (ih (by omega))

private def solution : PowerSeries R := mk fun n => coeff n (approximation (R := R) (n+1))

private theorem solution_agree (d : ℕ) : Agree d (solution (R := R)) (approximation d) := by
  intro n hn
  simpa only [solution, coeff_mk] using
    approximation_stable (R := R) (by omega : n+1 ≤ d) n (by omega)

private theorem solution_zero : constantCoeff (solution (R := R)) = 1 := by
  have h := solution_agree (R := R) 1 0 (by omega)
  simpa only [coeff_zero_eq_constantCoeff, approximation_zero] using h

private theorem solution_fixed : solution (R := R) = advance solution := by
  ext n
  exact (solution_agree (n+2) n (by omega)).trans
    (advance_agree solution_zero (approximation_zero (n+1))
      (solution_agree (n+1)) n (by omega)).symm

private theorem solution_normalized (n : ℕ) (hn : 0 < n) : normalized (solution (R := R)) n = 0 := by
  have h := congrArg (coeff n) (solution_fixed (R := R))
  simp only [advance, coeff_mk, if_neg (by omega : n ≠ 0)] at h
  linear_combination h

private theorem normalized_unique (F G : PowerSeries R) (hF : constantCoeff F = 1)
    (hG : constantCoeff G = 1) (hrF : ∀ n, 0 < n → normalized F n = 0)
    (hrG : ∀ n, 0 < n → normalized G n = 0) : F = G := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · subst n; simpa only [coeff_zero_eq_constantCoeff] using hF.trans hG.symm
    have h := normalized_change (by omega : 0 < n) hF hG ih
    rw [hrF n (by omega), hrG n (by omega), sub_self] at h
    exact sub_eq_zero.mp h.symm

private theorem integer_normalized_iff (F : PowerSeries ℤ) (n : ℕ) (hn : 0 < n) :
    normalized F n = 0 ↔ row F n = 0 := by
  rw [exact_normalization F n hn]
  have he : (((n+1)^2 : ℕ) : ℤ) ≠ 0 := by positivity
  simp only [mul_eq_zero, he, false_or]

private theorem geom_cast_congr (e f : ℕ) (h : (e : F2) = (f : F2)) :
    geom (R := F2) e = geom f := by ext n; simp [geom, h]

private theorem geom_zero : geom (R := F2) 0 = 1 := by ext n; simp [geom, zero_pow_eq]

private theorem geom_one_denom : (1+X)*geom (R := F2) 1 = 1 := by
  simpa only [Nat.cast_one, map_one, one_mul, CharTwo.sub_eq_add] using geom_eq (R := F2) 1

private theorem even_X_square (F : PowerSeries F2) (m : ℕ) : coeff (2*m) (X*F^2) = 0 := by
  cases m with
  | zero => simp
  | succ m => rw [show 2*(m+1) = (2*m+1)+1 by omega, coeff_succ_X_mul, square_odd]

private theorem candidate_even (F E O : PowerSeries F2)
    (hF : F = E^2+X*O^2) (hEO : E+X*O=1+X) (m : ℕ) (hm : 0 < m) :
    normalized F (2*m) = 0 := by
  let g : PowerSeries F2 := geom 1
  have hg : (1+X)*g=1 := geom_one_denom
  have hpoly : F*(1+X)=(E+X*O)^2+X*(E+O)^2 := by
    rw [hF, CharTwo.add_sq, CharTwo.add_sq, mul_pow]
    ring
  have hdiv : F*g=1+X*((E+O)*g)^2 := by
    calc
      F*g = (F*(1+X))*g^2 := by linear_combination -F*g*hg
      _ = ((1+X)^2+X*(E+O)^2)*g^2 := by rw [hpoly, hEO]
      _ = 1+X*((E+O)*g)^2 := by linear_combination g*(1+X)*hg+hg
  have hcast : (((2*m+1)^2 : ℕ) : F2)=1 := by
    simp [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, CharTwo.two_eq_zero]
  have hgeom := geom_cast_congr ((2*m+1)^2) 1 (by simpa using hcast)
  have he : (2*m+1)^2 = 2*m*(m+1)*2+1 := by ring
  have hrow : row F (2*m) = 0 := by
    dsimp [row]
    rw [hgeom, he, pow_succ, pow_mul]
    have hr : (F^(2*m*(m+1)))^2*F*geom 1 =
        (F^(2*m*(m+1)))^2+X*(((E+O)*g)*F^(2*m*(m+1)))^2 := by
      change (F^(2*m*(m+1)))^2*F*g = _
      rw [mul_assoc, hdiv]
      ring
    rw [hr, map_add, square_even, even_X_square,
      power_diagonal_zero F m (m+1) hm, zero_add]
  dsimp [normalized]
  rw [hrow]
  have hc : (2*m+2 : F2)=0 := by simp [CharTwo.two_eq_zero]
  simp only [Nat.cast_mul, Nat.cast_ofNat, hc, zero_mul, sub_self]
set_option maxHeartbeats 800000 in

private theorem candidate_odd (F E O : PowerSeries F2)
    (hF : F = E^2+X*O^2) (hEO : E*O=F) (m : ℕ) :
    normalized F (2*m+1) = 0 := by
  have hc : (((2*m+1+1)^2 : ℕ) : F2)=0 := by
    simp [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, CharTwo.two_eq_zero, CharTwo.add_self_eq_zero]
  have hg : geom (R := F2) ((2*m+1+1)^2) = 1 :=
    (geom_cast_congr _ 0 (by simpa using hc)).trans geom_zero
  have he : (2*m+1+1)^2 = (2*(m+1)^2)*2 := by ring
  have hrow : row F (2*m+1) = 0 := by
    rw [row, hg, mul_one, he, pow_mul, square_odd]
  have ht : derivative F2 F = O^2 := by
    rw [hF, Derivation.map_add, Derivation.leibniz, derivative_pow, derivative_pow]
    simp [smul_eq_mul, CharTwo.two_eq_zero]
  have hprod : F*derivative F2 F+F^2=X*(O^2)^2 := by
    calc
      F*derivative F2 F+F^2 = (E^2+X*O^2)*O^2+(E*O)^2 := by rw [ht, ← hF, hEO]
      _ = (E*O)^2+(E*O)^2+X*(O^2)^2 := by ring
      _ = X*(O^2)^2 := by rw [CharTwo.add_self_eq_zero, zero_add]
  have htrow : derivRow F (2*m+1) = 0 := by
    have hpos : 1 ≤ 2*(m+1)^2 := by nlinarith [sq_pos_of_pos (show 0 < m+1 by omega)]
    have hp1 : (2*m+1+1)^2-1 = (2*(m+1)^2-1)*2+1 := by omega
    have hp2 : (2*m+1+1)^2 = (2*(m+1)^2-1)*2+2 := by omega
    rw [derivRow, show 2*m+1-1=2*m by omega, hg, one_pow, mul_one, mul_one]
    have hp : F^((2*m+1+1)^2-1)*derivative F2 F+F^((2*m+1+1)^2) =
        X*(F^(2*(m+1)^2-1)*O^2)^2 := by
      rw [hp1, hp2, pow_succ, pow_add, pow_mul]
      calc
        (F^(2*(m+1)^2-1))^2*F*derivative F2 F+(F^(2*(m+1)^2-1))^2*F^2 =
          (F^(2*(m+1)^2-1))^2*(F*derivative F2 F+F^2) := by ring
        _ = X*(F^(2*(m+1)^2-1)*O^2)^2 := by rw [hprod]; ring
    rw [hp, even_X_square]
  simp only [normalized, hrow, htrow, mul_zero, sub_self]

private theorem geom_map {S : Type*} [CommRing S] (f : R →+* S) (n : ℕ) :
    (geom (R := R) n).map f = geom n := by ext k; simp [geom]

private theorem derivative_map {S : Type*} [CommRing S] (f : R →+* S) (F : PowerSeries R) :
    (derivative R F).map f = derivative S (F.map f) := by ext k; simp [coeff_derivative]

private theorem normalized_map {S : Type*} [CommRing S] (f : R →+* S)
    (F : PowerSeries R) (n : ℕ) : normalized (F.map f) n = f (normalized F n) := by
  have hr : row (F.map f) n = f (row F n) := by
    simp only [row, ← geom_map f, ← map_pow, ← map_mul, coeff_map]
  have ht : derivRow (F.map f) n = f (derivRow F n) := by
    simp only [derivRow, ← geom_map f, ← derivative_map f, ← map_pow, ← map_mul,
      ← map_add, coeff_map]
  simp only [normalized, hr, ht, map_sub, map_mul, map_add, map_natCast, map_ofNat]

private abbrev Upstream := D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.catalanSeries

private def U : PowerSeries F2 :=
  (PowerSeries.catalanSeries.map (Nat.castRingHom F2))

private theorem U_equation : U = 1+X*U^2 := by
  have h := congrArg (PowerSeries.map (Nat.castRingHom F2))
    PowerSeries.catalanSeries_sq_mul_X_add_one
  simpa only [map_add, map_mul, map_pow, map_X, map_one, U, add_comm, mul_comm] using h.symm

private theorem U_zero : constantCoeff U = 1 := by
  have h := congrArg constantCoeff U_equation
  simpa using h

private theorem U_support (n : ℕ) : coeff n U = 1 ↔ ∃ k : ℕ, n+1=2^k := by
  have h := D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.binary_catalan (n+1)
  have hmap : Upstream.map (Int.castRingHom F2) = X*U := by
    change (X*(PowerSeries.catalanSeries.map (Nat.castRingHom ℤ))).map (Int.castRingHom F2) = _
    simp only [map_mul, map_X, U]
    rfl
  rw [hmap, coeff_succ_X_mul] at h
  exact h

private def H : PowerSeries F2 := U^2

private def O : PowerSeries F2 := (1+X)*H

private def E : PowerSeries F2 := 1+X+X*O

private def candidate : PowerSeries F2 := E^2+X*O^2

private theorem H_equation : H = 1+X^2*H^2 := by
  have h := congrArg (fun p : PowerSeries F2 => p^2) U_equation
  simpa only [H, CharTwo.add_sq, one_pow, mul_pow] using h

private theorem EO_add : E+X*O=1+X := by
  rw [E, add_assoc, CharTwo.add_self_eq_zero, add_zero]

private theorem EO_mul : E*O=candidate := by
  have h : (1+X)^2 * (H+1+X^2*H^2) = 0 := by
    have hz : H+1+X^2*H^2 = H+H := by rw [add_assoc, ← H_equation]
    rw [hz, CharTwo.add_self_eq_zero, mul_zero]
  dsimp [E, O, candidate] at *
  simp only [CharTwo.add_sq, mul_pow, one_pow] at *
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) h

private theorem candidate_zero : constantCoeff candidate = 1 := by
  simp [candidate, E]

private theorem candidate_normalized (n : ℕ) (hn : 0 < n) : normalized candidate n = 0 := by
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' n
  · subst n
    exact candidate_even candidate E O rfl EO_add m (by omega)
  · subst n
    exact candidate_odd candidate E O rfl EO_mul m

private theorem solution_mod_two : (solution (R := ℤ)).map (Int.castRingHom F2) = candidate := by
  apply normalized_unique
  · rw [← coeff_zero_eq_constantCoeff]
    simp only [coeff_map, coeff_zero_eq_constantCoeff, solution_zero, map_one]
  · exact candidate_zero
  · intro n hn
    rw [normalized_map, solution_normalized n hn, map_zero]
  · exact candidate_normalized

private theorem O_even (m : ℕ) : coeff (2*m) O = coeff m U := by
  rw [O, H, add_mul, one_mul, map_add, square_even, even_X_square, add_zero]

private theorem O_odd (m : ℕ) : coeff (2*m+1) O = coeff m U := by
  rw [O, H, add_mul, one_mul, map_add, square_odd, coeff_succ_X_mul, square_even, zero_add]

private theorem E_even (m : ℕ) : coeff (2*(m+1)) E = coeff m U := by
  rw [E, map_add, map_add]
  simp only [coeff_one, coeff_X, if_neg (by omega : 2*(m+1) ≠ 0),
    if_neg (by omega : 2*(m+1) ≠ 1), zero_add]
  rw [show 2*(m+1)=(2*m+1)+1 by omega, coeff_succ_X_mul, O_odd]

private theorem E_odd (m : ℕ) (hm : 0 < m) : coeff (2*m+1) E = coeff m U := by
  rw [E, map_add, map_add]
  simp only [coeff_one, coeff_X, if_neg (by omega : 2*m+1 ≠ 0),
    if_neg (by omega : 2*m+1 ≠ 1), zero_add]
  rw [coeff_succ_X_mul, O_even]

private theorem candidate_one (m : ℕ) : coeff (4*m+1) candidate = coeff m U := by
  rw [candidate, map_add, show 4*m+1=2*(2*m)+1 by omega,
    square_odd, coeff_succ_X_mul, square_even, O_even, zero_add]

private theorem candidate_two (m : ℕ) (hm : 0 < m) : coeff (4*m+2) candidate = coeff m U := by
  rw [candidate, map_add, show 4*m+2=2*(2*m+1) by omega,
    square_even, even_X_square, E_odd m hm, add_zero]

private theorem candidate_three (m : ℕ) : coeff (4*m+3) candidate = coeff m U := by
  rw [candidate, map_add, show 4*m+3=2*(2*m+1)+1 by omega,
    square_odd, coeff_succ_X_mul, square_even, O_odd, zero_add]

private theorem candidate_four (m : ℕ) : coeff (4*m+4) candidate = coeff m U := by
  rw [candidate, map_add, show 4*m+4=2*(2*(m+1)) by omega,
    square_even, even_X_square, E_even, add_zero]

private theorem candidate_coeff (n : ℕ) (hn : 2 < n) :
    coeff n candidate = coeff ((n-1)/4) U := by
  set q := (n-1)/4
  have hq : 4*q+1 ≤ n ∧ n ≤ 4*q+4 := by dsimp [q]; omega
  have hc : n=4*q+1 ∨ n=4*q+2 ∨ n=4*q+3 ∨ n=4*q+4 := by omega
  rcases hc with h|h|h|h
  · rw [h, candidate_one]
  · rw [h, candidate_two q (by omega)]
  · rw [h, candidate_three]
  · rw [h, candidate_four]

private theorem support_arithmetic (n : ℕ) (hn : 2 < n) :
    (∃ j : ℕ, (n-1)/4+1=2^j) ↔
      ∃ k : ℕ, 1 < k ∧ (n=2^k ∨ n=2^k-1 ∨ n=2^k-2 ∨ n=2^k-3) := by
  constructor
  · rintro ⟨j,hj⟩
    refine ⟨j+2, by omega, ?_⟩
    have hp : 2^(j+2)=4*2^j := by rw [pow_add]; ring
    rw [hp]
    omega
  · rintro ⟨k,hk,h⟩
    obtain ⟨j,rfl⟩ : ∃ j, k=j+2 := ⟨k-2, by omega⟩
    refine ⟨j, ?_⟩
    have hp : 2^(j+2)=4*2^j := by rw [pow_add]; ring
    have hpos : 0 < 2^j := by positivity
    rw [hp] at h
    rcases h with h|h|h|h <;> omega

/-- The integer generating function A has zero constant coefficient. -/
noncomputable def generatingSeries : PowerSeries ℤ := 1-solution

private theorem geom_inverse (e : ℕ) : geom (R := ℤ) e =
    invOfUnit (1-C (e : ℤ)*X) 1 := by
  have hi := mul_invOfUnit (1-C (e : ℤ)*X) 1 (by simp)
  have hg := geom_eq (R := ℤ) e
  calc
    geom e = geom e * ((1-C (e : ℤ)*X) * invOfUnit (1-C (e : ℤ)*X) 1) := by rw [hi, mul_one]
    _ = invOfUnit (1-C (e : ℤ)*X) 1 := by
      rw [← mul_assoc, mul_comm (geom e), hg, one_mul]

/-- The exact OEIS NAME equation, with division by the constant-one denominator. -/
def DefiningEquation (A : PowerSeries ℤ) : Prop :=
  constantCoeff A = 0 ∧ ∀ m : ℕ, 1 < m →
    coeff (m-1) ((1-A)^(m^2) * invOfUnit (1-C (m^2 : ℤ)*X) 1) = 0


private theorem defining_iff (A : PowerSeries ℤ) : DefiningEquation A ↔
    constantCoeff (1-A) = 1 ∧ ∀ n, 0 < n → row (1-A) n = 0 := by
  constructor
  · rintro ⟨h0,hr⟩
    refine ⟨by simp [h0], ?_⟩
    intro n hn
    simpa only [row, geom_inverse, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
      Nat.add_sub_cancel] using hr (n+1) (by omega)
  · rintro ⟨h0,hr⟩
    refine ⟨by simpa using h0, ?_⟩
    intro m hm
    have h := hr (m-1) (by omega)
    simpa only [row, geom_inverse, Nat.sub_add_cancel (by omega : 1 ≤ m), Nat.cast_pow] using h

/-- An integer series with zero constant term satisfies the source equation. -/
theorem generating_equation : DefiningEquation generatingSeries := by
  apply (defining_iff _).mpr
  have he : 1-generatingSeries = solution := by simp [generatingSeries]
  rw [he]
  exact ⟨solution_zero, fun n hn =>
    (integer_normalized_iff _ n hn).mp (solution_normalized n hn)⟩

/-- Integer existence and uniqueness, without a rational integrality assumption. -/
theorem integer_exists_unique : ∃! A : PowerSeries ℤ, DefiningEquation A := by
  refine ⟨generatingSeries, generating_equation, ?_⟩
  intro A hA
  have h := normalized_unique (1-A) (solution (R := ℤ))
    ((defining_iff A).mp hA).1 solution_zero
    (fun n hn => (integer_normalized_iff _ n hn).mpr (((defining_iff A).mp hA).2 n hn))
    solution_normalized
  dsimp [generatingSeries]
  linear_combination -h

/-- The coefficient a(n) with the source's indexing, extended by a(0)=0. -/
noncomputable def a (n : ℕ) : ℤ := coeff n generatingSeries


private theorem solution_parity (n : ℕ) (hn : 2 < n) :
    Odd (a n) ↔ ∃ k : ℕ, 1 < k ∧
      (n=2^k ∨ n=2^k-1 ∨ n=2^k-2 ∨ n=2^k-3) := by
  have hc : (a n : F2) = coeff n candidate := by
    have h := congrArg (coeff n) solution_mod_two
    simp only [coeff_map] at h
    simp only [a, generatingSeries, map_sub, coeff_one, if_neg (by omega : n ≠ 0),
      zero_sub, Int.cast_neg, CharTwo.neg_eq]
    exact h
  rw [← ZMod.intCast_eq_one_iff_odd, hc, candidate_coeff n hn, U_support, support_arithmetic n hn]
/-- For every integer series in the exact OEIS domain, all n > 2 have the asserted parity. -/
theorem hanna_conjecture (A : PowerSeries ℤ) (hA : DefiningEquation A)
    (n : ℕ) (hn : 2 < n) :
    Odd (coeff n A) ↔ ∃ k : ℕ, 1 < k ∧
      (n=2^k ∨ n=2^k-1 ∨ n=2^k-2 ∨ n=2^k-3) := by
  have h : A = generatingSeries := integer_exists_unique.unique hA generating_equation
  rw [h]
  exact solution_parity n hn
end D5.S1.Recurrence.SquareRows.SquareExponentDyadicSupport
