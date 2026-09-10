/- GID: D5/S1/Recurrence/Invariants/UnitReversionSquareParity
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/UnitReversionSquareParity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A contracting integer series and a lacunary mod-two fixed point prove A373312. -/

import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.FieldTheory.Finite.Basic

open PowerSeries

namespace D5.S1.Recurrence.Invariants.UnitReversionSquareParity

variable {R : Type*} [CommRing R]

private def Agree (d : ℕ) (f g : PowerSeries R) : Prop :=
  ∀ n < d, coeff n f = coeff n g

private theorem agree_iff (d : ℕ) (f g : PowerSeries R) :
    Agree d f g ↔ (X : PowerSeries R) ^ d ∣ f - g := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem agree_mono {d e : ℕ} {f g : PowerSeries R}
    (h : Agree d f g) (he : e ≤ d) : Agree e f g :=
  fun n hn => h n (lt_of_lt_of_le hn he)

private theorem agree_pow {d : ℕ} {f g : PowerSeries R}
    (h : Agree d f g) (k : ℕ) : Agree d (f ^ k) (g ^ k) :=
  (agree_iff _ _ _).mpr ((agree_iff _ _ _).mp h |>.trans
    (sub_dvd_pow_sub_pow f g k))

private theorem agree_mul {d : ℕ} {f g u v : PowerSeries R}
    (h : Agree d f g) (h' : Agree d u v) : Agree d (f * u) (g * v) := by
  apply (agree_iff _ _ _).mpr
  have h1 := dvd_mul_of_dvd_left ((agree_iff _ _ _).mp h) u
  have h2 := dvd_mul_of_dvd_right ((agree_iff _ _ _).mp h') g
  convert dvd_add h1 h2 using 1
  ring

private theorem agree_X {d : ℕ} {f g : PowerSeries R}
    (h : Agree d f g) : Agree (d + 1) (X * f) (X * g) := by
  intro n hn
  cases n with
  | zero => simp
  | succ n => simpa using h n (by omega)

private theorem pow_low {u : PowerSeries R} (hu : constantCoeff u = 0)
    {n k : ℕ} (h : n < k) : coeff n (u ^ k) = 0 :=
  X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hu) k) n h

private theorem subst_inner_agree {d : ℕ} {u v : PowerSeries R}
    (h : Agree d u v) (f : PowerSeries R)
    (hu : constantCoeff u = 0) (hv : constantCoeff v = 0) :
    Agree d (f.subst u) (f.subst v) := by
  intro n hn
  rw [coeff_subst' (.of_constantCoeff_zero hu), coeff_subst' (.of_constantCoeff_zero hv)]
  exact finsum_congr fun k => by rw [agree_pow h k n hn]

private theorem subst_outer_agree {d : ℕ} {f g u : PowerSeries R}
    (h : Agree d f g) (hu : X ^ 2 ∣ u) :
    Agree (2 * d) (f.subst u) (g.subst u) := by
  have hz : constantCoeff u = 0 := X_dvd_iff.mp ((dvd_pow_self X (by omega)).trans hu)
  intro n hn
  rw [coeff_subst' (.of_constantCoeff_zero hz), coeff_subst' (.of_constantCoeff_zero hz)]
  apply finsum_congr
  intro k
  by_cases hk : k < d
  · rw [h k hk]
  · have hz' : coeff n (u ^ k) = 0 := by
      apply X_pow_dvd_iff.mp (show X ^ (2 * k) ∣ u ^ k by
        simpa only [pow_mul] using pow_dvd_pow_of_dvd hu k)
      omega
    rw [hz', smul_zero, smul_zero]

private noncomputable def reciprocal (b : PowerSeries R) : PowerSeries R :=
  invOfUnit (1 - X * b) 1

private theorem reciprocal_mul (b : PowerSeries R) :
    reciprocal b * (1 - X * b) = 1 :=
  invOfUnit_mul _ _ (by simp)

private theorem reciprocal_zero (b : PowerSeries R) :
    constantCoeff (reciprocal b) = 1 := by
  simp [reciprocal, constantCoeff_invOfUnit]

private theorem reciprocal_agree {d : ℕ} {b c : PowerSeries R}
    (h : Agree d b c) : Agree (d + 1) (reciprocal b) (reciprocal c) := by
  apply (agree_iff _ _ _).mpr
  have hd := (agree_iff _ _ _).mp (agree_X h)
  have he : reciprocal b - reciprocal c =
      (X * b - X * c) * (reciprocal b * reciprocal c) := by
    have hb := reciprocal_mul b
    have hc := reciprocal_mul c
    linear_combination reciprocal c * hb - reciprocal b * hc
  rw [he]
  exact dvd_mul_of_dvd_left hd _

private noncomputable def argument (b : PowerSeries R) : PowerSeries R :=
  X ^ 2 * b * reciprocal b ^ 2

private theorem argument_zero (b : PowerSeries R) : constantCoeff (argument b) = 0 := by
  simp [argument]

private theorem argument_order (b : PowerSeries R) : X ^ 2 ∣ argument b := by
  exact ⟨b * reciprocal b ^ 2, by simp [argument, mul_assoc]⟩

private theorem argument_agree {d : ℕ} {b c : PowerSeries R}
    (h : Agree d b c) : Agree (d + 2) (argument b) (argument c) := by
  have hm := agree_mul h (agree_pow (agree_mono (reciprocal_agree h) (by omega)) 2)
  simpa [argument, pow_two, mul_assoc] using agree_X (agree_X hm)

-- After A = X * B, cancel X^2 * B to obtain this contracting equation for B.
private noncomputable def step (b : PowerSeries R) : PowerSeries R :=
  reciprocal b ^ 2 * b.subst (argument b)

private theorem subst_constant (f u : PowerSeries R) (hu : constantCoeff u = 0) :
    constantCoeff (f.subst u) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff, coeff_subst' (.of_constantCoeff_zero hu)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro k hk
    rw [pow_low hu (by omega : 0 < k), smul_zero]

private theorem step_constant (b : PowerSeries R) : constantCoeff (step b) = constantCoeff b := by
  simp [step, reciprocal_zero, subst_constant _ _ (argument_zero b)]

private theorem step_agree {d : ℕ} {b c : PowerSeries R} (hd : 1 ≤ d)
    (h : Agree d b c) : Agree (d + 1) (step b) (step c) := by
  apply agree_mul (agree_pow (reciprocal_agree h) 2)
  have hi := subst_inner_agree (argument_agree h) b (argument_zero b) (argument_zero c)
  have ho := subst_outer_agree h (argument_order c)
  intro n hn
  exact (hi n (by omega)).trans (ho n (by omega))

private noncomputable def approximation : ℕ → PowerSeries R
  | 0 => 1
  | n + 1 => step (approximation n)

private theorem approximation_constant (n : ℕ) :
    constantCoeff (approximation (R := R) n) = 1 := by
  induction n with
  | zero => simp [approximation]
  | succ n ih => simpa [approximation, step_constant] using ih

private theorem approximation_stable {d n : ℕ} (h : d ≤ n) :
    Agree (d + 1) (approximation (R := R) d) (approximation n) := by
  induction d generalizing n with
  | zero =>
    intro k hk
    have : k = 0 := by omega
    subst k
    simp [coeff_zero_eq_constantCoeff, approximation_constant]
  | succ d ih =>
    cases n with
    | zero => omega
    | succ n => exact step_agree (by omega) (ih (by omega))

private noncomputable def normalizedSeries : PowerSeries ℤ :=
  mk fun n => coeff n (approximation (R := ℤ) n)

private theorem normalized_agree (d : ℕ) :
    Agree (d + 1) normalizedSeries (approximation d) := by
  intro n hn
  simpa only [normalizedSeries, coeff_mk] using
    approximation_stable (R := ℤ) (by omega : n ≤ d) n (by omega)

private theorem normalized_constant : constantCoeff normalizedSeries = 1 := by
  have h := normalized_agree 0 0 (by omega)
  simpa [coeff_zero_eq_constantCoeff, approximation_constant] using h

private theorem normalized_fixed : normalizedSeries = step normalizedSeries := by
  ext n
  have h1 := normalized_agree (n + 1) n (by omega)
  have h2 := step_agree (by omega : 1 ≤ n + 1) (normalized_agree n) n (by omega)
  exact h1.trans h2.symm

noncomputable def generatingSeries : PowerSeries ℤ := X * normalizedSeries

noncomputable def a (n : ℕ) : ℤ := coeff n generatingSeries

noncomputable def innerSeries : PowerSeries ℤ :=
  X * generatingSeries * invOfUnit (1 - generatingSeries) 1 ^ 2

theorem generating_equation : constantCoeff generatingSeries = 0 ∧
    coeff 1 generatingSeries = 1 ∧
    generatingSeries ^ 2 = generatingSeries.subst innerSeries := by
  refine ⟨by simp [generatingSeries], by simp [generatingSeries, normalized_constant], ?_⟩
  have hi : innerSeries = argument normalizedSeries := by
    simp [innerSeries, generatingSeries, argument, reciprocal, pow_two, mul_assoc]
  rw [hi, generatingSeries, subst_mul (.of_constantCoeff_zero (argument_zero _)),
    subst_X (.of_constantCoeff_zero (argument_zero _))]
  have hf := normalized_fixed
  dsimp [step] at hf
  calc
    (X * normalizedSeries) ^ 2 = X ^ 2 * normalizedSeries * normalizedSeries := by ring
    _ = X ^ 2 * normalizedSeries *
        (reciprocal normalizedSeries ^ 2 * normalizedSeries.subst (argument normalizedSeries)) :=
      congrArg (fun t => X ^ 2 * normalizedSeries * t) hf
    _ = _ := by simp [argument, mul_assoc]

private theorem step_unique {b c : PowerSeries R}
    (hc : constantCoeff b = constantCoeff c) (hb : b = step b) (hc' : c = step c) :
    b = c := by
  have ha : ∀ d, Agree (d + 1) b c := by
    intro d
    induction d with
    | zero =>
      intro n hn
      have : n = 0 := by omega
      subst n
      simpa only [coeff_zero_eq_constantCoeff] using hc
    | succ d ih =>
      simpa only [← hb, ← hc'] using step_agree (by omega : 1 ≤ d + 1) ih
  ext n
  exact ha n n (by omega)

theorem generating_unique (f : PowerSeries ℤ)
    (h0 : constantCoeff f = 0) (h1 : coeff 1 f = 1)
    (he : f ^ 2 = f.subst (X * f * invOfUnit (1 - f) 1 ^ 2)) :
    f = generatingSeries := by
  obtain ⟨b, rfl⟩ := X_dvd_iff.mpr h0
  have hb : constantCoeff b = 1 := by simpa using h1
  have hbne : b ≠ 0 := by
    intro hz
    simp [hz] at hb
  have ha : X * (X * b) * invOfUnit (1 - X * b) 1 ^ 2 = argument b := by
    simp [argument, reciprocal, pow_two, mul_assoc]
  rw [ha, subst_mul (.of_constantCoeff_zero (argument_zero b)),
    subst_X (.of_constantCoeff_zero (argument_zero b))] at he
  have hf : b = step b := by
    apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 2 (X_ne_zero (R := ℤ))) hbne)
    dsimp only [argument] at he
    dsimp only [step, argument]
    linear_combination he
  rw [step_unique (hb.trans normalized_constant.symm) hf normalized_fixed]
  rfl

private theorem square_subst (f : PowerSeries (ZMod 2)) :
    f ^ 2 = f.subst (X ^ 2) := by
  have h := MvPowerSeries.map_frobenius_expand (σ := Unit) (R := ZMod 2)
    2 (by decide) (f := f)
  rw [ZMod.frobenius_zmod, MvPowerSeries.map_id] at h
  exact h.symm.trans (expand_apply 2 (by decide) f)

private theorem outer_cancel {f u v : PowerSeries R}
    (hf0 : constantCoeff f = 0) (hf1 : coeff 1 f = 1)
    (hu : constantCoeff u = 0) (hv : constantCoeff v = 0)
    (he : f.subst u = f.subst v) : u = v := by
  have hf : IsUnit (coeff 1 f) := hf1 ▸ isUnit_one
  have h := congrArg (fun t => (f.substInvOfIsUnit hf).subst t) he
  rw [← subst_comp_subst_apply (.of_constantCoeff_zero hf0) (.of_constantCoeff_zero hu),
    ← subst_comp_subst_apply (.of_constantCoeff_zero hf0) (.of_constantCoeff_zero hv),
    subst_substInvOfIsUnit_left f hf0 hf, subst_X (.of_constantCoeff_zero hu),
    subst_X (.of_constantCoeff_zero hv)] at h
  exact h

theorem mod_two_fixed :
    generatingSeries.map (Int.castRingHom (ZMod 2)) =
      X + X * (generatingSeries.map (Int.castRingHom (ZMod 2))).subst (X ^ 2) := by
  let hom := Int.castRingHom (ZMod 2)
  let f := generatingSeries.map hom
  let v := (invOfUnit (1 - generatingSeries) 1).map hom
  let u := innerSeries.map hom
  have hf0 : constantCoeff f = 0 := by
    dsimp only [f]
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
      generating_equation.1, map_zero]
  have hf1 : coeff 1 f = 1 := by
    simpa [f] using congrArg hom generating_equation.2.1
  have hu : u = X * f * v ^ 2 := by simp [u, innerSeries, f, v]
  have hu0 : constantCoeff u = 0 := by simp [hu]
  have hv : v * (1 - f) = 1 := by
    have h := invOfUnit_mul (1 - generatingSeries) (1 : ℤˣ)
      (by simp [generating_equation.1])
    simpa [v, f] using congrArg (PowerSeries.map hom) h
  have he : f ^ 2 = f.subst u := by
    have h := congrArg (PowerSeries.map hom) generating_equation.2.2
    have hz : constantCoeff innerSeries = 0 := by simp [innerSeries]
    have hm : PowerSeries.map hom (generatingSeries.subst innerSeries) = f.subst u :=
      map_subst (.of_constantCoeff_zero hz) _
    rw [hm] at h
    simpa [f, u] using h
  have hx : u = X ^ 2 := outer_cancel hf0 hf1 hu0 (by simp)
    (he.symm.trans (square_subst f))
  have hclear : X * f = X ^ 2 * (1 - f) ^ 2 := by
    calc
      X * f = X * f * (v * (1 - f)) ^ 2 := by rw [hv]; ring
      _ = u * (1 - f) ^ 2 := by rw [hu]; ring
      _ = X ^ 2 * (1 - f) ^ 2 := by rw [hx]
  have hfixed : f = X * (1 - f) ^ 2 := by
    apply mul_left_cancel₀ (X_ne_zero (R := ZMod 2))
    simpa [pow_two, mul_assoc] using hclear
  have hchar : (2 : PowerSeries (ZMod 2)) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (C (R := ZMod 2)) (show (2 : ZMod 2) = 0 by decide)
  have hsquare : (1 - f) ^ 2 = 1 + f ^ 2 := by
    linear_combination -f * hchar
  change f = X + X * f.subst (X ^ 2)
  exact hfixed.trans (by rw [hsquare, mul_add, mul_one, square_subst f])

private theorem mersenne_zero : ¬ ∃ k : ℕ, 1 ≤ k ∧ 0 = 2 ^ k - 1 := by
  rintro ⟨k, hk, he⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hp : 0 < 2 ^ j := pow_pos (by omega) _
  rw [pow_succ] at he
  omega

private theorem mersenne_step (n : ℕ) (hn : 0 < n) :
    (∃ k : ℕ, 1 ≤ k ∧ n + 1 = 2 ^ k - 1) ↔
      2 ∣ n ∧ ∃ k : ℕ, 1 ≤ k ∧ n / 2 = 2 ^ k - 1 := by
  constructor
  · rintro ⟨k, hk, he⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have hp : 0 < 2 ^ j := pow_pos (by omega) _
    rw [pow_succ] at he
    have hj : 1 ≤ j := by
      by_contra hj
      have : j = 0 := by omega
      simp [this] at he
      omega
    have hn' : n = 2 * (2 ^ j - 1) := by omega
    refine ⟨⟨2 ^ j - 1, hn'⟩, j, hj, ?_⟩
    omega
  · rintro ⟨hd, k, hk, he⟩
    have hp : 0 < 2 ^ k := pow_pos (by omega) _
    have hm := Nat.mod_eq_zero_of_dvd hd
    refine ⟨k + 1, by omega, ?_⟩
    rw [pow_succ]
    omega

private theorem lacunary_coeff (f : PowerSeries (ZMod 2))
    (h0 : constantCoeff f = 0) (h1 : coeff 1 f = 1)
    (hf : f = X + X * f.subst (X ^ 2)) (n : ℕ) :
    coeff n f = 1 ↔ ∃ k : ℕ, 1 ≤ k ∧ n = 2 ^ k - 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | n
    · simp [coeff_zero_eq_constantCoeff, h0, mersenne_zero]
    · by_cases hn : n = 0
      · subst n
        simp only [zero_add, h1, true_iff]
        exact ⟨1, by omega, by norm_num⟩
      · have hc := congrArg (coeff (n + 1)) hf
        rw [map_add, coeff_succ_X_mul, coeff_subst_X_pow (by omega : 2 ≠ 0)] at hc
        have hx : coeff (n + 1) (X : PowerSeries (ZMod 2)) = 0 := by
          simp [coeff_X, hn]
        rw [hx, zero_add, Algebra.algebraMap_self, RingHom.id_apply] at hc
        rw [hc, mersenne_step n (by omega)]
        by_cases hd : 2 ∣ n
        · rw [if_pos hd, ih (n / 2) (by omega), and_iff_right hd]
        · simp [hd]

theorem hanna_conjecture (n : ℕ) (_hn : 1 ≤ n) :
    Odd (a n) ↔ ∃ k : ℕ, 1 ≤ k ∧ n = 2 ^ k - 1 := by
  let hom := Int.castRingHom (ZMod 2)
  have h0 : constantCoeff (generatingSeries.map hom) = 0 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
      generating_equation.1, map_zero]
  have h1 : coeff 1 (generatingSeries.map hom) = 1 := by
    simp [generating_equation.2.1]
  have h := lacunary_coeff (generatingSeries.map hom) h0 h1 mod_two_fixed n
  change (a n : ZMod 2) = 1 ↔ ∃ k : ℕ, 1 ≤ k ∧ n = 2 ^ k - 1 at h
  exact ZMod.intCast_eq_one_iff_odd.symm.trans h

#print axioms generating_equation
#print axioms generating_unique
#print axioms mod_two_fixed
#print axioms hanna_conjecture

end D5.S1.Recurrence.Invariants.UnitReversionSquareParity
