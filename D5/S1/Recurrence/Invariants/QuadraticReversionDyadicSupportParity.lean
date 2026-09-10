/- GID: D5/S1/Recurrence/Invariants/QuadraticReversionDyadicSupportParity
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/QuadraticReversionDyadicSupportParity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Quadratic reversion and a lacunary characteristic-two solution prove Hanna parity. -/

import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.FieldTheory.Finite.Basic

open PowerSeries

namespace D5.S1.Recurrence.Invariants.QuadraticReversionDyadicSupportParity

variable {R : Type*} [CommRing R]

private def Agree (d : ℕ) (f g : PowerSeries R) : Prop :=
  ∀ n < d, coeff n f = coeff n g

private theorem agree_iff (d : ℕ) (f g : PowerSeries R) :
    Agree d f g ↔ (X : PowerSeries R) ^ d ∣ f - g := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem agree_pow {d : ℕ} {f g : PowerSeries R}
    (h : Agree d f g) (k : ℕ) : Agree d (f ^ k) (g ^ k) :=
  (agree_iff _ _ _).mpr (((agree_iff _ _ _).mp h).trans (sub_dvd_pow_sub_pow f g k))

private theorem pow_low {f : PowerSeries R} (h : constantCoeff f = 0)
    {n k : ℕ} (hn : n < k) : coeff n (f ^ k) = 0 :=
  X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr h) k) n hn

private theorem pow_diag {f : PowerSeries R} (h0 : constantCoeff f = 0)
    (h1 : coeff 1 f = 1) (n : ℕ) : coeff n (f ^ n) = 1 := by
  obtain ⟨u, rfl⟩ := X_dvd_iff.mpr h0
  have hu : constantCoeff u = 1 := by simpa using h1
  simp [mul_pow, coeff_X_pow_mul', hu]

private theorem subst_inner_agree {d : ℕ} {u v : PowerSeries R}
    (hu : constantCoeff u = 0) (hv : constantCoeff v = 0)
    (h : Agree d u v) (f : PowerSeries R) : Agree d (f.subst u) (f.subst v) := by
  intro n hn
  rw [coeff_subst' (.of_constantCoeff_zero hu), coeff_subst' (.of_constantCoeff_zero hv)]
  exact finsum_congr fun k => by rw [agree_pow h k n hn]

private theorem subst_first_difference {d : ℕ} {f g u : PowerSeries R}
    (h0 : constantCoeff u = 0) (h1 : coeff 1 u = 1) (h : Agree d f g)
    (n : ℕ) (hn : n < d + 1) :
    coeff n ((f - g).subst u) = coeff n (f - g) := by
  rw [coeff_subst' (.of_constantCoeff_zero h0), finsum_eq_single _ n]
  · rw [pow_diag h0 h1, smul_eq_mul, mul_one]
  · intro k hk
    by_cases hkn : k < n
    · have hz : coeff k (f - g) = 0 := by rw [map_sub, h k (by omega), sub_self]
      rw [hz, zero_smul]
    · rw [pow_low h0 (by omega : n < k), smul_zero]

private noncomputable def reciprocal (f : PowerSeries R) : PowerSeries R :=
  invOfUnit (1 - f) 1

private theorem reciprocal_mul {f : PowerSeries R} (hf : constantCoeff f = 0) :
    reciprocal f * (1 - f) = 1 := invOfUnit_mul _ _ (by simp [hf])

private noncomputable def argument (f : PowerSeries R) : PowerSeries R :=
  X - (f * reciprocal f) ^ 2

private theorem argument_zero {f : PowerSeries R} (hf : constantCoeff f = 0) :
    constantCoeff (argument f) = 0 := by simp [argument, hf]

private theorem argument_one {f : PowerSeries R} (hf : constantCoeff f = 0) :
    coeff 1 (argument f) = 1 := by
  rw [argument, map_sub, pow_low (by simp [hf]) (by omega : 1 < 2)]
  simp

private theorem argument_agree {d : ℕ} {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (h : Agree d f g) : Agree (d + 1) (argument f) (argument g) := by
  have he : f * reciprocal f - g * reciprocal g =
      (f - g) * (reciprocal f * reciprocal g) := by
    have hf' := reciprocal_mul hf
    have hg' := reciprocal_mul hg
    linear_combination g * reciprocal g * hf' - f * reciprocal f * hg'
  have hd : X ^ d ∣ f * reciprocal f - g * reciprocal g := by
    rw [he]
    exact dvd_mul_of_dvd_left ((agree_iff _ _ _).mp h) _
  have hz : X ∣ f * reciprocal f + g * reciprocal g := X_dvd_iff.mpr (by simp [hf, hg])
  apply (agree_iff _ _ _).mpr
  have hm := mul_dvd_mul hd hz
  rw [← pow_succ] at hm
  convert dvd_neg.mpr hm using 1
  dsimp [argument]
  ring

private noncomputable def step (f : PowerSeries R) : PowerSeries R :=
  f + X - f.subst (argument f)

private theorem step_zero {f : PowerSeries R} (hf : constantCoeff f = 0) :
    constantCoeff (step f) = 0 := by
  have hz : constantCoeff (f.subst (argument f)) = 0 :=
    constantCoeff_subst_eq_zero (argument_zero hf) _ hf
  simp only [step, map_sub, map_add, hf, constantCoeff_X, hz, add_zero, sub_zero]

private theorem step_agree {d : ℕ} {f g : PowerSeries R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (h : Agree d f g) : Agree (d + 1) (step f) (step g) := by
  intro n hn
  have hi := subst_inner_agree (argument_zero hf) (argument_zero hg)
    (argument_agree hf hg h) f n hn
  have ho := subst_first_difference (argument_zero hg) (argument_one hg) h n hn
  rw [subst_sub (.of_constantCoeff_zero (argument_zero hg)), map_sub, map_sub] at ho
  simp only [step, map_sub, map_add]
  rw [hi]
  linear_combination -ho

private theorem solution_unique {f g : PowerSeries R}
    (hf0 : constantCoeff f = 0) (hg0 : constantCoeff g = 0)
    (hf : f.subst (argument f) = X) (hg : g.subst (argument g) = X) : f = g := by
  have hsf : step f = f := by simp [step, hf]
  have hsg : step g = g := by simp [step, hg]
  have hall : ∀ d, Agree d f g := by
    intro d
    induction d with
    | zero => intro n hn; omega
    | succ d ih => simpa only [hsf, hsg] using step_agree hf0 hg0 ih
  ext n
  exact hall (n + 1) n (by omega)

private noncomputable def approximation : ℕ → PowerSeries R
  | 0 => 0
  | k + 1 => step (approximation k)

private theorem approximation_zero (n : ℕ) :
    constantCoeff (approximation (R := R) n) = 0 := by
  induction n with
  | zero => simp [approximation]
  | succ n ih => exact step_zero ih

private theorem approximation_stable {d k : ℕ} (h : d ≤ k) :
    Agree d (approximation (R := R) d) (approximation k) := by
  induction d generalizing k with
  | zero => intro n hn; omega
  | succ d ih =>
    cases k with
    | zero => omega
    | succ k => exact step_agree (approximation_zero _) (approximation_zero _) (ih (by omega))

private noncomputable def solution : PowerSeries R :=
  mk fun n => coeff n (approximation (n + 1))

private theorem solution_agree (d : ℕ) :
    Agree d (solution (R := R)) (approximation d) := by
  intro n hn
  simpa only [solution, coeff_mk] using
    approximation_stable (R := R) (by omega : n + 1 ≤ d) n (by omega)

private theorem solution_zero : constantCoeff (solution (R := R)) = 0 := by
  have h := solution_agree (R := R) 1 0 (by omega)
  simpa [coeff_zero_eq_constantCoeff, approximation_zero] using h

private theorem solution_equation :
    (solution (R := R)).subst (argument (solution (R := R))) = X := by
  have hf : (solution (R := R)) = step (solution (R := R)) := by
    ext n
    have hg := solution_agree (R := R) (n + 2) n (by omega)
    have hs := step_agree (solution_zero (R := R)) (approximation_zero (R := R) (n + 1))
      (solution_agree (R := R) (n + 1)) n (by omega)
    exact hg.trans hs.symm
  dsimp [step] at hf
  linear_combination hf

private theorem solution_one : coeff 1 (solution (R := R)) = 1 := by
  have h := solution_agree (R := R) 2 1 (by omega)
  have ha : approximation (R := R) 1 = X := by
    have hz : (0 : PowerSeries R).subst (argument (0 : PowerSeries R)) = 0 := by
      simpa only [map_zero] using (subst_C (a := argument (0 : PowerSeries R)) (0 : R))
    simp [approximation, step, hz]
  change coeff 1 solution = coeff 1 (step (approximation 1)) at h
  rw [ha, step, subst_X (.of_constantCoeff_zero (argument_zero (by simp))),
    map_sub, map_add, argument_one (by simp)] at h
  simpa using h

noncomputable def generatingSeries : PowerSeries ℤ := solution

noncomputable def a (n : ℕ) : ℤ := coeff n generatingSeries

noncomputable def innerSeries : PowerSeries ℤ :=
  X - (generatingSeries * invOfUnit (1 - generatingSeries) 1) ^ 2

theorem generating_equation : constantCoeff generatingSeries = 0 ∧
    coeff 1 generatingSeries = 1 ∧ generatingSeries.subst innerSeries = X ∧
    (1 - generatingSeries) ^ 2 * (X - innerSeries) = generatingSeries ^ 2 := by
  refine ⟨solution_zero, solution_one, solution_equation, ?_⟩
  have hv := reciprocal_mul (R := ℤ) solution_zero
  change invOfUnit (1 - generatingSeries) 1 * (1 - generatingSeries) = 1 at hv
  calc
    (1 - generatingSeries) ^ 2 * (X - innerSeries) =
        generatingSeries ^ 2 * (invOfUnit (1 - generatingSeries) 1 *
          (1 - generatingSeries)) ^ 2 := by dsimp [innerSeries]; ring
    _ = generatingSeries ^ 2 := by rw [hv]; ring

theorem generating_unique (f : PowerSeries ℤ) (hf : constantCoeff f = 0)
    (he : f.subst (X - (f * invOfUnit (1 - f) 1) ^ 2) = X) :
    f = generatingSeries := solution_unique hf solution_zero he solution_equation

private def Support (n : ℕ) : Prop :=
  ∃ m : ℕ, n + 2 = 3 * 2 ^ m ∨ n + 2 = 4 * 2 ^ m

private theorem support_zero : ¬ Support 0 := by
  rintro ⟨m, h | h⟩ <;> have hp := Nat.one_le_pow m 2 (by omega) <;> omega

private theorem support_one : Support 1 := ⟨0, Or.inl (by norm_num)⟩

private theorem support_two : Support 2 := ⟨0, Or.inr (by norm_num)⟩

private theorem support_step (n : ℕ) (hn : 1 ≤ n) :
    Support (n + 2) ↔ 2 ∣ n ∧ Support (n / 2) := by
  constructor
  · rintro ⟨m, hm⟩
    cases m with
    | zero => simp at hm; omega
    | succ m =>
      have hp := Nat.one_le_pow m 2 (by omega)
      rw [pow_succ] at hm
      rcases hm with hm | hm
      · have he : n = 2 * (3 * 2 ^ m - 2) := by omega
        refine ⟨⟨3 * 2 ^ m - 2, he⟩, m, Or.inl ?_⟩
        omega
      · have he : n = 2 * (4 * 2 ^ m - 2) := by omega
        refine ⟨⟨4 * 2 ^ m - 2, he⟩, m, Or.inr ?_⟩
        omega
  · rintro ⟨hd, m, hm⟩
    have hz := Nat.mod_eq_zero_of_dvd hd
    refine ⟨m + 1, ?_⟩
    rw [pow_succ]
    rcases hm with hm | hm
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

noncomputable def lacunarySeries : PowerSeries (ZMod 2) := by
  classical
  exact mk fun n => if ∃ m : ℕ, n + 2 = 3 * 2 ^ m ∨ n + 2 = 4 * 2 ^ m then 1 else 0

attribute [local instance] Classical.propDecidable

private theorem lacunary_coeff (n : ℕ) :
    coeff n lacunarySeries = if Support n then 1 else 0 := by
  classical
  simp only [lacunarySeries, coeff_mk, Support]
  split_ifs <;> simp_all

private theorem lacunary_zero : constantCoeff lacunarySeries = 0 := by
  rw [← coeff_zero_eq_constantCoeff, lacunary_coeff, if_neg support_zero]

private theorem square_subst (f : PowerSeries (ZMod 2)) :
    f ^ 2 = f.subst (X ^ 2) := by
  have h := MvPowerSeries.map_frobenius_expand (σ := Unit) (R := ZMod 2)
    2 (by decide) (f := f)
  rw [ZMod.frobenius_zmod, MvPowerSeries.map_id] at h
  exact h.symm.trans (expand_apply 2 (by decide) f)

theorem lacunary_quadratic :
    lacunarySeries = X + X ^ 2 + X ^ 2 * lacunarySeries ^ 2 := by
  classical
  rw [square_subst lacunarySeries]
  ext n
  by_cases h0 : n = 0
  · subst n
    simp [coeff_zero_eq_constantCoeff, lacunary_zero]
  by_cases h1 : n = 1
  · subst n
    simp [lacunary_coeff, support_one, coeff_X_pow_mul']
  by_cases h2 : n = 2
  · subst n
    simp [lacunary_coeff, support_two, support_zero, coeff_X_pow_mul', coeff_X]
  have hn : 2 ≤ n := by omega
  have hs : Support n ↔ 2 ∣ (n - 2) ∧ Support ((n - 2) / 2) := by
    simpa only [Nat.sub_add_cancel hn] using support_step (n - 2) (by omega)
  rw [map_add, map_add]
  have hx : coeff n (X : PowerSeries (ZMod 2)) = 0 := by simp [coeff_X, h1]
  have hx2 : coeff n (X ^ 2 : PowerSeries (ZMod 2)) = 0 := by simp [coeff_X_pow, h2]
  rw [hx, hx2, zero_add, zero_add, coeff_X_pow_mul', if_pos hn,
    coeff_subst_X_pow (by omega : 2 ≠ 0), lacunary_coeff, lacunary_coeff]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, hs]
  split_ifs <;> simp_all

private theorem quadratic_unique (r : PowerSeries R) (hr : constantCoeff r = 0)
    {f g : PowerSeries R} (hf : f = r + r ^ 2 + r ^ 2 * f ^ 2)
    (hg : g = r + r ^ 2 + r ^ 2 * g ^ 2) : f = g := by
  have hall : ∀ d, Agree d f g := by
    intro d
    induction d with
    | zero => intro n hn; omega
    | succ d ih =>
      apply (agree_iff _ _ _).mpr
      have hd := (agree_iff _ _ _).mp (agree_pow ih 2)
      have hz : X ∣ r ^ 2 := (X_dvd_iff.mpr hr).trans (dvd_pow_self r (by omega))
      have hm := mul_dvd_mul hd hz
      rw [← pow_succ] at hm
      convert hm using 1
      linear_combination hf - hg
  ext n
  exact hall (n + 1) n (by omega)

private instance char_two : CharP (PowerSeries (ZMod 2)) 2 :=
  CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (by
    simpa only [map_ofNat, map_zero] using
      congrArg (C (R := ZMod 2)) (show (2 : ZMod 2) = 0 by decide))

-- Clearing the unit denominator turns the quadratic relation into the reversed one.
private theorem reversed_algebra (x z v r : PowerSeries (ZMod 2))
    (hz : z = x + x ^ 2 + x ^ 2 * z ^ 2)
    (hv : v * (1 + z) = 1) (hr : r = x + (z * v) ^ 2) :
    (1 + x) * r = z * v ∧ r + x = (1 + x ^ 2) * r ^ 2 ∧
      x = r + r ^ 2 + r ^ 2 * x ^ 2 := by
  have h2 : (2 : PowerSeries (ZMod 2)) = 0 := CharP.ofNat_eq_zero _ 2
  have hv2 : v ^ 2 * (1 + z) ^ 2 = 1 := by rw [← mul_pow, hv, one_pow]
  have hd : (1 + x) * (x * (1 + z) ^ 2 + z ^ 2) = z * (1 + z) := by
    linear_combination (norm := (ring_nf; simp [h2])) -hz
  have hc : r * (1 + z) ^ 2 = x * (1 + z) ^ 2 + z ^ 2 := by
    linear_combination (1 + z) ^ 2 * hr + z ^ 2 * hv2
  have hfirst : (1 + x) * r = z * v := by
    calc
      (1 + x) * r = (1 + x) * r * (v ^ 2 * (1 + z) ^ 2) := by rw [hv2]; ring
      _ = v ^ 2 * ((1 + x) * (r * (1 + z) ^ 2)) := by ring
      _ = v ^ 2 * (z * (1 + z)) := by rw [hc, hd]
      _ = z * v := by linear_combination z * v * hv
  have hs := congrArg (fun t => t ^ 2) hfirst
  rw [mul_pow, CharTwo.add_sq, one_pow] at hs
  have hsecond : r + x = (1 + x ^ 2) * r ^ 2 := by
    linear_combination (norm := (ring_nf; simp [h2])) hr - hs
  refine ⟨hfirst, hsecond, ?_⟩
  linear_combination (norm := (ring_nf; simp [h2])) hsecond

theorem lacunary_reversion :
    lacunarySeries.subst
      (X - (lacunarySeries * invOfUnit (1 - lacunarySeries) 1) ^ 2) = X := by
  let r := argument lacunarySeries
  have hr : constantCoeff r = 0 := argument_zero lacunary_zero
  have hv : reciprocal lacunarySeries * (1 + lacunarySeries) = 1 := by
    simpa only [CharTwo.sub_eq_add] using reciprocal_mul lacunary_zero
  have ha : r = X + (lacunarySeries * reciprocal lacunarySeries) ^ 2 := by
    exact CharTwo.sub_eq_add _ _
  have hx := (reversed_algebra X lacunarySeries (reciprocal lacunarySeries) r
    lacunary_quadratic hv ha).2.2
  have hp : lacunarySeries.subst r = r + r ^ 2 + r ^ 2 * (lacunarySeries.subst r) ^ 2 := by
    have hs : HasSubst r := .of_constantCoeff_zero hr
    have he := congrArg (subst r) lacunary_quadratic
    simpa only [subst_add hs, subst_mul hs, subst_pow hs, subst_X hs] using he
  exact quadratic_unique r hr hp hx

private theorem map_argument {S : Type*} [CommRing S] (hom : R →+* S)
    (f : PowerSeries R) (hf : constantCoeff f = 0) :
    (argument f).map hom = argument (f.map hom) := by
  have hz : constantCoeff (f.map hom) = 0 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff, hf, map_zero]
  have hv : (reciprocal f).map hom = reciprocal (f.map hom) := by
    have hu : IsUnit (1 - f.map hom) := by
      rw [isUnit_iff_constantCoeff]
      simp [hz]
    apply hu.mul_right_cancel
    rw [reciprocal_mul hz]
    simpa only [map_mul, map_sub, map_one] using
      congrArg (PowerSeries.map hom) (reciprocal_mul hf)
  simp only [argument, map_sub, map_X, map_pow, map_mul, hv]

theorem mod_two_identity :
    generatingSeries.map (Int.castRingHom (ZMod 2)) = lacunarySeries := by
  let hom := Int.castRingHom (ZMod 2)
  have hz : constantCoeff (generatingSeries.map hom) = 0 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
      generating_equation.1, map_zero]
  have he : (generatingSeries.map hom).subst (argument (generatingSeries.map hom)) = X := by
    have hm := congrArg (PowerSeries.map hom) generating_equation.2.2.1
    have hs : PowerSeries.map hom (generatingSeries.subst innerSeries) =
        (generatingSeries.map hom).subst (innerSeries.map hom) :=
      map_subst (.of_constantCoeff_zero (argument_zero generating_equation.1)) _
    rw [hs, map_X] at hm
    change (generatingSeries.map hom).subst ((argument generatingSeries).map hom) = X at hm
    rwa [map_argument hom generatingSeries generating_equation.1] at hm
  exact solution_unique hz lacunary_zero he lacunary_reversion

theorem hanna_conjecture (n : ℕ) (_hn : 1 ≤ n) :
    Odd (a n) ↔ ∃ m : ℕ, n + 2 = 3 * 2 ^ m ∨ n + 2 = 4 * 2 ^ m := by
  have hc := congrArg (coeff n) mod_two_identity
  change (a n : ZMod 2) = coeff n lacunarySeries at hc
  rw [← ZMod.intCast_eq_one_iff_odd, hc, lacunary_coeff]
  split_ifs <;> simp_all [Support]

#print axioms generating_equation
#print axioms generating_unique
#print axioms lacunary_quadratic
#print axioms lacunary_reversion
#print axioms mod_two_identity
#print axioms hanna_conjecture

end D5.S1.Recurrence.Invariants.QuadraticReversionDyadicSupportParity
