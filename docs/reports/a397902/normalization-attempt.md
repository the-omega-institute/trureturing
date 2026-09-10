# Checked normalization experiment

This is a Lean experiment, not a deposited theorem or the A397902 conclusion.
`lake env lean /tmp/A397902Normalization.lean` on the preheated tree: EXIT=0.
The two printed axiom closures contain only propext, Classical.choice, Quot.sound.
Source SHA-256: `5326966d90fe4e8804005d340251933de11bf0f46518932a32cd7baebefa649e`.

```lean
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
open PowerSeries
noncomputable section
namespace A397902Attempt
variable {R : Type*} [CommRing R]
def geom (e : ℕ) : PowerSeries R := mk fun n => (e : R)^n
lemma geom_eq (e : ℕ) : (1 - C (e : R) * X) * geom (R := R) e = 1 := by
  ext n
  cases n with
  | zero => simp [geom]
  | succ n =>
    rw [sub_mul, one_mul, mul_assoc, map_sub, coeff_C_mul, coeff_succ_X_mul]
    simp [geom, pow_succ, mul_comm]
lemma geom_derivative (e : ℕ) : derivative R (geom e) = C (e : R) * (geom e)^2 := by
  have h := congrArg (fun f => derivative R f) (geom_eq (R := R) e)
  simp only [Derivation.map_sub, Derivation.leibniz, derivative_one, derivative_C,
    derivative_X, smul_eq_mul, mul_zero, mul_one, zero_sub] at h
  have h' := congrArg (fun f => f * geom (R := R) e) h
  have hg := geom_eq (R := R) e
  linear_combination h' - derivative R (geom e) * hg
lemma coeff_power_divisible (F : PowerSeries ℤ) (n e : ℕ) (hn : 0 < n)
    (hcop : Nat.Coprime e n) : (e : ℤ) ∣ coeff n (F^e) := by
  have h := congrArg (coeff (n-1)) (derivative_pow F e)
  rw [coeff_derivative, Nat.sub_add_cancel hn] at h
  have he : (e : PowerSeries ℤ) = C (e : ℤ) := by simp
  rw [he, mul_assoc, coeff_C_mul] at h
  apply hcop.isCoprime.dvd_of_dvd_mul_left
  refine ⟨coeff (n-1) (F^(e-1) * derivative ℤ F), ?_⟩
  have hncast : ((n-1 : ℕ) : ℤ) + 1 = n := by exact_mod_cast Nat.sub_add_cancel hn
  simpa only [hncast, mul_comm] using h
lemma square_exponent_divisible (F : PowerSeries ℤ) (n : ℕ) (hn : 0 < n) :
    (((n+1)^2 : ℕ) : ℤ) ∣ coeff n (F^((n+1)^2)) := by
  exact coeff_power_divisible F n ((n+1)^2) hn ((Nat.coprime_self_add_left.mpr (Nat.coprime_one_left n)).pow_left 2)

def row (F : PowerSeries R) (n : ℕ) : R :=
  coeff n (F^((n+1)^2) * geom ((n+1)^2))
def derivRow (F : PowerSeries R) (n : ℕ) : R :=
  coeff (n-1) (F^((n+1)^2-1) * derivative R F * geom ((n+1)^2) +
    F^((n+1)^2) * geom ((n+1)^2)^2)
def normalized (F : PowerSeries R) (n : ℕ) : R := row F n - (n+2) * derivRow F n

lemma derivative_row (F : PowerSeries R) (n : ℕ) (hn : 0 < n) :
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

lemma exact_normalization (F : PowerSeries R) (n : ℕ) (hn : 0 < n) :
    row F n = (((n+1)^2 : ℕ) : R) * normalized F n := by
  have h := derivative_row F n hn
  simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] at h ⊢
  dsimp [normalized]
  linear_combination -(n+2 : R) * h

#print axioms coeff_power_divisible
#print axioms exact_normalization
end A397902Attempt
```

## Binary diagonal experiment

With `PowerSeries.Expand` and `ZMod.Basic` additionally imported, the following
was checked in the same file (EXIT=0; standard three axioms only). This generic
vanishing result is a proposed ingredient, not the source conjecture.

```lean
abbrev F2 := ZMod 2
lemma square_expand (F : PowerSeries F2) : F^2 = expand 2 (by decide) F := by
  have h := MvPowerSeries.map_frobenius_expand (σ := Unit) (R := ZMod 2)
    2 (by decide) (f := F)
  rw [ZMod.frobenius_zmod, MvPowerSeries.map_id] at h
  exact h.symm
lemma square_even (F : PowerSeries F2) (n : ℕ) : coeff (2*n) (F^2) = coeff n F := by
  rw [square_expand, coeff_expand_mul]
lemma square_odd (F : PowerSeries F2) (n : ℕ) : coeff (2*n+1) (F^2) = 0 := by
  rw [square_expand, coeff_expand_of_not_dvd]
  omega
lemma power_diagonal_zero (F : PowerSeries F2) (n t : ℕ) (hn : 0 < n) :
    coeff n (F^(2*n*t)) = 0 := by
  induction n using Nat.strong_induction_on generalizing t with
  | h n ih =>
    obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' n
    · subst n
      rw [show 2*(2*m)*t = (2*m*t)*2 by ring, pow_mul, square_even]
      exact ih m (by omega) t (by omega)
    · subst n
      rw [show 2*(2*m+1)*t = ((2*m+1)*t)*2 by ring, pow_mul, square_odd]
```

## Unit coefficient multiplier

The following continuation passed Lean (EXIT=0; `normalized_change` has only
standard axioms). It shows the exact residual depends on the new coefficient
with multiplier one over every commutative ring. Construction and parity
identification are not yet asserted.

```lean
def Agree (n : ℕ) (F G : PowerSeries R) : Prop := ∀ k < n, coeff k F = coeff k G
lemma agree_iff (n : ℕ) (F G : PowerSeries R) :
    Agree n F G ↔ (X : PowerSeries R)^n ∣ F-G := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]
lemma agree_pow {n : ℕ} {F G : PowerSeries R} (h : Agree n F G) (e : ℕ) :
    Agree n (F^e) (G^e) :=
  (agree_iff _ _ _).mpr (((agree_iff _ _ _).mp h).trans (sub_dvd_pow_sub_pow F G e))
lemma agree_mul {n : ℕ} {F G : PowerSeries R} (h : Agree n F G) (H : PowerSeries R) :
    Agree n (F*H) (G*H) := by
  apply (agree_iff _ _ _).mpr
  rw [← sub_mul]
  exact dvd_mul_of_dvd_left ((agree_iff _ _ _).mp h) H
lemma leading_mul {n : ℕ} {U : PowerSeries R} (h : X^n ∣ U) (V : PowerSeries R) :
    coeff n (U*V) = coeff n U * constantCoeff V := by
  obtain ⟨W,rfl⟩ := h
  have hc (T : PowerSeries R) : coeff n (X^n*T) = constantCoeff T := by
    simpa only [zero_add, coeff_zero_eq_constantCoeff] using coeff_X_pow_mul T n 0
  rw [mul_assoc, hc, hc, map_mul]
lemma pow_change {n : ℕ} {F G : PowerSeries R}
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
lemma row_change {n : ℕ} {F G : PowerSeries R}
    (hF : constantCoeff F = 1) (hG : constantCoeff G = 1) (h : Agree n F G) :
    row F n - row G n = (((n+1)^2 : ℕ) : R)*(coeff n F-coeff n G) := by
  dsimp [row]
  rw [← map_sub, ← sub_mul, leading_mul ((agree_iff _ _ _).mp (agree_pow h _))]
  simp only [geom, constantCoeff_mk, pow_zero, mul_one, map_sub]
  exact pow_change hF hG h _
lemma derivRow_change {n : ℕ} {F G : PowerSeries R} (hn : 0 < n)
    (hF : constantCoeff F = 1) (hG : constantCoeff G = 1) (h : Agree n F G) :
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
    map_pow, hG, one_pow, g, geom, constantCoeff_mk, pow_zero, one_mul, mul_one]
  ring
lemma normalized_change {n : ℕ} {F G : PowerSeries R} (hn : 0 < n)
    (hF : constantCoeff F = 1) (hG : constantCoeff G = 1) (h : Agree n F G) :
    normalized F n-normalized G n = coeff n F-coeff n G := by
  have hr := row_change hF hG h
  have ht := derivRow_change hn hF hG h
  simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] at hr
  dsimp [normalized]
  linear_combination hr-(n+2 : R)*ht
```
