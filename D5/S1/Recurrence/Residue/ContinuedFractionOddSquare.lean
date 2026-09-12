/- GID: D5/S1/Recurrence/Residue/ContinuedFractionOddSquare
   generality: G
   mirror-B: D5/B/S1/Recurrence/Residue/ContinuedFractionOddSquare
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Finite-tail stabilization and triangular uniqueness prove Hanna A338636 modulo eight. -/

import Mathlib.RingTheory.PowerSeries.Inverse

/-!
The finite tail with `d` levels begins at numerator `(2*j+1)^2` and
ends in `A`; thus the terminal index is `j+d`. The outer numerator is `X`.
At depth `d`, the defining equation is an equality through degree `d+1`,
not an equality of whole finite continued fractions. Stabilization proves
that these compatible finite equations specify every coefficient.

The construction and contraction argument work over any commutative ring.
Over the integers they construct a normalized solution without division by
an integer other than one. Over `ZMod 8`, the odd squares become one and
finite tails of `1+X` agree with one through their depth. Uniqueness identifies
the reduced solution. Only the mod-eight conjecture of OEIS A338636 is asserted.
-/

open PowerSeries
namespace D5.S1.Recurrence.Residue.ContinuedFractionOddSquare
variable {R : Type*} [CommRing R]

private def Agree (n : ℕ) (f g : PowerSeries R) : Prop :=
  ∀ k < n, coeff k f = coeff k g

private theorem agree_iff (n : ℕ) (f g : PowerSeries R) :
    Agree n f g ↔ (X : PowerSeries R) ^ n ∣ f - g := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem agree_inv {n : ℕ} {f g : PowerSeries R}
    (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) (h : Agree n f g) :
    Agree n (invOfUnit f 1) (invOfUnit g 1) := by
  have hfi := invOfUnit_mul f 1 hf
  have hgi := mul_invOfUnit g 1 hg
  have he : invOfUnit f 1 - invOfUnit g 1 =
      invOfUnit f 1 * (g - f) * invOfUnit g 1 := by
    calc
      _ = invOfUnit f 1 * (g * invOfUnit g 1) -
          (invOfUnit f 1 * f) * invOfUnit g 1 := by rw [hfi, hgi]; ring
      _ = _ := by ring
  apply (agree_iff _ _ _).mpr
  rw [he]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right
    (by rw [← neg_sub f g]; exact dvd_neg.mpr ((agree_iff _ _ _).mp h)) _) _

private theorem agree_shift {n : ℕ} {f g : PowerSeries R} (h : Agree n f g) (c : R) :
    Agree (n + 1) (C c * X * f) (C c * X * g) := by
  apply (agree_iff _ _ _).mpr
  obtain ⟨q, hq⟩ := (agree_iff _ _ _).mp h
  refine ⟨C c * q, ?_⟩
  rw [pow_succ]
  linear_combination C c * X * hq

/-- `finiteTail A j d` starts with numerator `(2*j+1)^2` and has `d`
levels; its terminal denominator is `A`. Division means the unit inverse. -/
noncomputable def finiteTail (A : PowerSeries R) (j : ℕ) : ℕ → PowerSeries R
  | 0 => A
  | d + 1 => A - C (((2 * j + 1 : ℕ) : R) ^ 2) * X *
      invOfUnit (finiteTail A (j + 1) d) 1

private theorem tail_constant (A : PowerSeries R) (j d : ℕ) :
    constantCoeff (finiteTail A j d) = constantCoeff A := by
  cases d <;> simp [finiteTail]

private theorem tail_agree {n : ℕ} {A B : PowerSeries R}
    (hA : constantCoeff A = 1) (hB : constantCoeff B = 1)
    (h : Agree n A B) (j d : ℕ) : Agree n (finiteTail A j d) (finiteTail B j d) := by
  induction d generalizing j with
  | zero => exact h
  | succ d ih =>
    have hi := agree_shift (agree_inv (by simpa [tail_constant] using hA)
      (by simpa [tail_constant] using hB) (ih (j + 1))) (((2*j+1 : ℕ) : R)^2)
    intro k hk
    simp only [finiteTail, map_sub]
    rw [h k hk, hi k (by omega)]

/-- Adding levels preserves all coefficients through the old depth. -/
theorem stabilization (A : PowerSeries R) (hA : constantCoeff A = 1)
    (j d e n : ℕ) (hde : d ≤ e) (hn : n ≤ d) :
    coeff n (finiteTail A j d) = coeff n (finiteTail A j e) := by
  have h : Agree (d + 1) (finiteTail A j d) (finiteTail A j e) := by
    clear hn
    induction d generalizing j e with
    | zero =>
      intro k hk
      have hk0 : k = 0 := by omega
      subst k
      simp [coeff_zero_eq_constantCoeff, tail_constant]
    | succ d ih =>
      cases e with
      | zero => omega
      | succ e =>
        have hi := agree_shift (agree_inv
          (by simpa [tail_constant] using hA) (by simpa [tail_constant] using hA)
          (ih (j + 1) e (by omega))) (((2*j+1 : ℕ) : R)^2)
        intro k hk
        simp only [finiteTail, map_sub]
        rw [hi k hk]
  exact h n (by omega)

private noncomputable def rhs (A : PowerSeries R) (d : ℕ) : PowerSeries R :=
  1 + X * invOfUnit (finiteTail A 1 d) 1

private theorem rhs_constant (A : PowerSeries R) (d : ℕ) :
    constantCoeff (rhs A d) = 1 := by simp [rhs]

private theorem rhs_agree {n : ℕ} {A B : PowerSeries R}
    (hA : constantCoeff A = 1) (hB : constantCoeff B = 1)
    (h : Agree n A B) (d : ℕ) : Agree (n + 1) (rhs A d) (rhs B d) := by
  have hi := agree_shift (agree_inv (by simpa [tail_constant] using hA)
    (by simpa [tail_constant] using hB) (tail_agree hA hB h 1 d)) 1
  simpa only [Agree, rhs, map_add, map_one, one_mul] using fun k hk => congrArg (coeff k (1 : PowerSeries R) + ·) (hi k hk)

private theorem rhs_stable (A : PowerSeries R) (hA : constantCoeff A = 1)
    {d e : ℕ} (hde : d ≤ e) : Agree (d + 2) (rhs A d) (rhs A e) := by
  have ht : Agree (d + 1) (finiteTail A 1 d) (finiteTail A 1 e) :=
    fun k hk => stabilization A hA 1 d e k hde (by omega)
  have hi := agree_shift (agree_inv (by simpa [tail_constant] using hA)
    (by simpa [tail_constant] using hA) ht) 1
  simpa only [Agree, rhs, map_add, map_one, one_mul] using fun k hk => congrArg (coeff k (1 : PowerSeries R) + ·) (hi k hk)

private noncomputable def step (A : PowerSeries R) : PowerSeries R :=
  mk fun n => coeff n (rhs A n)

private theorem step_constant (A : PowerSeries R) : constantCoeff (step A) = 1 := by
  simpa [step, ← coeff_zero_eq_constantCoeff] using rhs_constant A 0

private theorem step_agree {n : ℕ} {A B : PowerSeries R}
    (hA : constantCoeff A = 1) (hB : constantCoeff B = 1) (h : Agree n A B) :
    Agree (n + 1) (step A) (step B) := by
  intro k hk
  simpa only [step, coeff_mk] using rhs_agree hA hB h k k hk

private theorem step_rhs (A : PowerSeries R) (hA : constantCoeff A = 1) (d : ℕ) :
    Agree (d + 2) (step A) (rhs A d) := by
  intro k hk
  simp only [step, coeff_mk]
  by_cases hkd : k ≤ d
  · exact rhs_stable A hA hkd k (by omega)
  · exact (rhs_stable A hA (by omega : d ≤ k) k hk).symm

private noncomputable def approximation : ℕ → PowerSeries R
  | 0 => 1
  | k + 1 => step (approximation k)

private theorem approximation_constant (k : ℕ) :
    constantCoeff (approximation (R := R) k) = 1 := by
  cases k
  · simp [approximation]
  · exact step_constant _

private theorem approximation_stable {d e : ℕ} (hde : d ≤ e) :
    Agree (d + 1) (approximation (R := R) d) (approximation e) := by
  induction d generalizing e with
  | zero =>
    intro k hk
    have : k = 0 := by omega
    subst k
    simp [coeff_zero_eq_constantCoeff, approximation_constant]
  | succ d ih =>
    cases e with
    | zero => omega
    | succ e =>
      exact step_agree (approximation_constant d) (approximation_constant e)
        (ih (by omega))

noncomputable def a (n : ℕ) : ℤ := coeff n (approximation n)

noncomputable def generatingSeries : PowerSeries ℤ := mk a

private theorem generating_agree (d : ℕ) : Agree (d + 1) generatingSeries (approximation d) := by
  intro k hk
  simpa only [generatingSeries, coeff_mk, a] using
    approximation_stable (R := ℤ) (by omega : k ≤ d) k (by omega)

private theorem generating_constant : constantCoeff generatingSeries = 1 := by
  simpa only [coeff_zero_eq_constantCoeff, approximation_constant] using generating_agree 0 0 (by omega)

private theorem generating_fixed : generatingSeries = step generatingSeries := by
  ext k
  exact (generating_agree (k + 1) k (by omega)).trans
    (step_agree generating_constant (approximation_constant k) (generating_agree k) k (by omega)).symm

/-- At every finite depth `d`, the NAME equation holds through degree `d+1`.
All denominator tails have constant coefficient one and are actual units. -/
theorem generating_equation : constantCoeff generatingSeries = 1 ∧
    (∀ j d : ℕ, constantCoeff (finiteTail generatingSeries j d) = 1 ∧
      finiteTail generatingSeries j d * invOfUnit (finiteTail generatingSeries j d) 1 = 1) ∧
    ∀ d n : ℕ, n ≤ d + 1 → coeff n (1 : PowerSeries ℤ) =
      coeff n (generatingSeries - X * invOfUnit (finiteTail generatingSeries 1 d) 1) := by
  refine ⟨generating_constant, ?_, ?_⟩
  · intro j d
    have hz : constantCoeff (finiteTail generatingSeries j d) = 1 :=
      (tail_constant _ _ _).trans generating_constant
    exact ⟨hz, mul_invOfUnit _ 1 hz⟩
  · intro d n hn
    have h := step_rhs generatingSeries generating_constant d n (by omega)
    rw [← generating_fixed] at h
    simp only [rhs, map_add] at h
    simp only [map_sub]
    linear_combination -h

private theorem fixed_unique {A B : PowerSeries R}
    (hA : constantCoeff A = 1) (hB : constantCoeff B = 1)
    (fA : A = step A) (fB : B = step B) : A = B := by
  have h : ∀ n, Agree n A B := by
    intro n
    induction n with
    | zero => intro k hk; omega
    | succ n ih => simpa only [← fA, ← fB] using step_agree hA hB ih
  ext n
  exact h (n + 1) n (by omega)

/-- Triangular uniqueness among normalized solutions of every finite-depth equation. -/
theorem generating_unique (A : PowerSeries ℤ) (hA : constantCoeff A = 1)
    (h : ∀ d n : ℕ, n ≤ d + 1 → coeff n (1 : PowerSeries ℤ) =
      coeff n (A - X * invOfUnit (finiteTail A 1 d) 1)) : A = generatingSeries := by
  apply fixed_unique hA generating_constant _ generating_fixed
  ext n
  have hn := h n n (by omega)
  simp only [map_sub] at hn
  simp only [step, coeff_mk, rhs, map_add]
  linear_combination -hn

private theorem map_inverse {S : Type*} [CommRing S] (hom : R →+* S)
    (A : PowerSeries R) (hA : constantCoeff A = 1) :
    (invOfUnit A 1).map hom = invOfUnit (A.map hom) 1 := by
  have hz : constantCoeff (A.map hom) = 1 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff, hA, map_one]
  apply (isUnit_iff_constantCoeff.mpr (hz ▸ isUnit_one)).mul_left_cancel
  rw [mul_invOfUnit _ 1 hz, ← map_mul, mul_invOfUnit _ 1 hA, map_one]

private theorem map_tail {S : Type*} [CommRing S] (hom : R →+* S)
    (A : PowerSeries R) (hA : constantCoeff A = 1) (j d : ℕ) :
    (finiteTail A j d).map hom = finiteTail (A.map hom) j d := by
  induction d generalizing j with
  | zero => rfl
  | succ d ih =>
    simp only [finiteTail, map_sub, map_mul, map_X, map_pow, map_natCast]
    rw [map_inverse hom _ ((tail_constant _ _ _).trans hA), ih]

private theorem map_rhs {S : Type*} [CommRing S] (hom : R →+* S)
    (A : PowerSeries R) (hA : constantCoeff A = 1) (d : ℕ) :
    (rhs A d).map hom = rhs (A.map hom) d := by
  simp only [rhs, map_add, map_one, map_mul, map_X]
  rw [map_inverse hom _ ((tail_constant _ _ _).trans hA), map_tail hom A hA]

private theorem map_step {S : Type*} [CommRing S] (hom : R →+* S)
    (A : PowerSeries R) (hA : constantCoeff A = 1) :
    (step A).map hom = step (A.map hom) := by
  ext n
  simp only [coeff_map, step, coeff_mk]
  rw [← coeff_map, map_rhs hom A hA]

private theorem odd_square (j : ℕ) : (((2*j+1 : ℕ) : ZMod 8)^2) = 1 := by
  obtain ⟨q, hq⟩ := Nat.two_dvd_mul_add_one j
  have hcast := congrArg (fun n : ℕ => (n : ZMod 8)) hq
  push_cast at hcast ⊢
  have hz : (8 : ZMod 8) = 0 := ZMod.natCast_self 8
  linear_combination 4 * hcast + (q : ZMod 8) * hz

private theorem inverse_one : invOfUnit (1 : PowerSeries R) 1 = 1 := by
  simpa only [one_mul] using mul_invOfUnit (1 : PowerSeries R) 1 (by simp)

private theorem reduced_tail (j d : ℕ) :
    Agree (d + 1) (finiteTail (1 + X : PowerSeries (ZMod 8)) j d) 1 := by
  induction d generalizing j with
  | zero =>
    intro k hk
    have : k = 0 := by omega
    subst k
    simp [finiteTail]
  | succ d ih =>
    have hi := agree_shift (agree_inv
      (by simp [tail_constant]) (by simp : constantCoeff (1 : PowerSeries (ZMod 8)) = 1)
      (ih (j + 1))) 1
    rw [inverse_one] at hi
    simp only [map_one, one_mul, mul_one] at hi
    intro k hk
    simp only [finiteTail, odd_square, map_one, one_mul, map_sub, map_add]
    rw [hi k hk]
    ring

private theorem reduced_fixed : (1 + X : PowerSeries (ZMod 8)) = step (1 + X) := by
  ext n
  have hi := agree_shift (agree_inv
    (by simp [tail_constant]) (by simp : constantCoeff (1 : PowerSeries (ZMod 8)) = 1)
    (reduced_tail 1 n)) 1 n (by omega)
  rw [inverse_one] at hi
  simp only [map_one, one_mul, mul_one] at hi
  simp only [step, coeff_mk, rhs, map_add]
  rw [hi]

/-- Hanna's mod-eight conjecture for the integer coefficients of the continued fraction. -/
theorem hanna_conjecture (n : ℕ) (hn : 1 < n) : (8 : ℤ) ∣ a n := by
  let hom := Int.castRingHom (ZMod 8)
  have hz : constantCoeff (generatingSeries.map hom) = 1 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
      generating_constant, map_one]
  have fixed : generatingSeries = step generatingSeries := by
    ext k
    have hk := generating_equation.2.2 k k (by omega)
    simp only [map_sub] at hk
    simp only [step, coeff_mk, rhs, map_add]
    linear_combination -hk
  have hf : generatingSeries.map hom = step (generatingSeries.map hom) := by
    rw [← map_step hom generatingSeries generating_constant, ← fixed]
  have he := fixed_unique hz (by simp : constantCoeff (1 + X : PowerSeries (ZMod 8)) = 1)
    hf reduced_fixed
  have hc := congrArg (coeff n) he
  have hzero : coeff n (1 + X : PowerSeries (ZMod 8)) = 0 := by
    simp [coeff_X, show n ≠ 0 by omega, show n ≠ 1 by omega]
  rw [hzero] at hc
  have ha : (a n : ZMod 8) = 0 := by simpa [coeff_map, generatingSeries, hom] using hc
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a n) 8).mp ha

#print axioms finiteTail
#print axioms stabilization
#print axioms a
#print axioms generatingSeries
#print axioms generating_equation
#print axioms generating_unique
#print axioms hanna_conjecture

end D5.S1.Recurrence.Residue.ContinuedFractionOddSquare
