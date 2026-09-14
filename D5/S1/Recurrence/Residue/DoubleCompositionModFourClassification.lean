/- GID: D5/S1/Recurrence/Residue/DoubleCompositionModFourClassification
   generality: G
   mirror-B: D5/B/S1/Recurrence/Residue/DoubleCompositionModFourClassification
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Contracting units and rational substitution classify Hanna A372577 modulo four. -/

import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.ReduceModChar

/-! The equation and coefficient conjecture are recorded in
`Library/ArithSums/hanna2024a372577.md`. -/

open PowerSeries
namespace D5.S1.Recurrence.Residue.DoubleCompositionModFourClassification
variable {R : Type*} [CommRing R]

private def Agree (n : ℕ) (f g : PowerSeries R) : Prop :=
  ∀ i < n, coeff i f = coeff i g

private theorem agree_iff (n : ℕ) (f g : PowerSeries R) :
    Agree n f g ↔ (X : PowerSeries R) ^ n ∣ f - g := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem agree_pow {n : ℕ} {f g : PowerSeries R}
    (h : Agree n f g) (k : ℕ) : Agree n (f ^ k) (g ^ k) :=
  (agree_iff _ _ _).mpr (((agree_iff _ _ _).mp h).trans (sub_dvd_pow_sub_pow f g k))

private theorem agree_mul {n : ℕ} {f g u v : PowerSeries R}
    (h : Agree n f g) (j : Agree n u v) : Agree n (f * u) (g * v) := by
  apply (agree_iff _ _ _).mpr
  have hd := dvd_add (dvd_mul_of_dvd_left ((agree_iff _ _ _).mp h) u)
    (dvd_mul_of_dvd_right ((agree_iff _ _ _).mp j) g)
  convert hd using 1
  ring

private theorem agree_X {n : ℕ} {f g : PowerSeries R} (h : Agree n f g) :
    Agree (n + 1) (X * f) (X * g) := by
  apply (agree_iff _ _ _).mpr
  have hd := mul_dvd_mul_left (X : PowerSeries R) ((agree_iff _ _ _).mp h)
  simpa only [pow_succ', mul_sub] using hd

private theorem coeff_pow_vanish {u : PowerSeries R} {r i k : ℕ}
    (hu : X ^ r ∣ u) (hi : i < r * k) : coeff i (u ^ k) = 0 := by
  apply X_pow_dvd_iff.mp _ i hi
  simpa only [← pow_mul] using pow_dvd_pow_of_dvd hu k

private theorem subst_constant (f u : PowerSeries R) (hu : constantCoeff u = 0) :
    constantCoeff (f.subst u) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff, coeff_subst' (.of_constantCoeff_zero hu)]
  rw [finsum_eq_single _ 0]
  · simp [coeff_zero_eq_constantCoeff]
  · intro k hk
    rw [coeff_pow_vanish (r := 1) (by simpa using X_dvd_iff.mpr hu) (by omega)]
    simp

private theorem subst_agree {n : ℕ} (hn : 1 ≤ n) {f g u v : PowerSeries R}
    (hu : X ^ 2 ∣ u) (hv : X ^ 2 ∣ v)
    (h : Agree n f g) (j : Agree (n + 1) u v) :
    Agree (n + 1) (f.subst u) (g.subst v) := by
  have uz : constantCoeff u = 0 := X_dvd_iff.mp ((dvd_pow_self X (by omega : 2 ≠ 0)).trans hu)
  have vz : constantCoeff v = 0 := X_dvd_iff.mp ((dvd_pow_self X (by omega : 2 ≠ 0)).trans hv)
  intro i hi
  rw [coeff_subst' (.of_constantCoeff_zero uz), coeff_subst' (.of_constantCoeff_zero vz)]
  apply finsum_congr
  intro k
  by_cases hk : k < n
  · rw [h k hk, agree_pow j k i hi]
  · rw [coeff_pow_vanish hu (by omega : i < 2 * k),
      coeff_pow_vanish hv (by omega : i < 2 * k), smul_zero, smul_zero]

private noncomputable def argument (f : PowerSeries R) : PowerSeries R :=
  X ^ 2 * f * (1 + X * f)

private theorem argument_zero (f : PowerSeries R) : constantCoeff (argument f) = 0 := by
  simp [argument]

private theorem argument_order (f : PowerSeries R) : X ^ 2 ∣ argument f :=
  ⟨f * (1 + X * f), by simp [argument, mul_assoc]⟩

private theorem argument_agree {n : ℕ} {f g : PowerSeries R} (h : Agree n f g) :
    Agree (n + 1) (argument f) (argument g) := by
  apply (agree_iff _ _ _).mpr
  have hd := dvd_mul_of_dvd_left
    (mul_dvd_mul_left (X : PowerSeries R) ((agree_iff _ _ _).mp h))
    (X * (1 + X * (f + g)))
  convert hd using 1
  · rw [pow_succ']
  · dsimp [argument]; ring

private noncomputable def nested (f : PowerSeries R) : PowerSeries R :=
  argument f * f.subst (argument f)

private theorem nested_zero (f : PowerSeries R) : constantCoeff (nested f) = 0 := by
  simp [nested, argument_zero]

private theorem nested_order (f : PowerSeries R) : X ^ 2 ∣ nested f :=
  dvd_mul_of_dvd_left (argument_order f) _

private theorem nested_agree {n : ℕ} (hn : 1 ≤ n) {f g : PowerSeries R}
    (h : Agree n f g) : Agree (n + 1) (nested f) (nested g) :=
  agree_mul (argument_agree h)
    (subst_agree hn (argument_order f) (argument_order g) h (argument_agree h))

private noncomputable def step (f : PowerSeries R) : PowerSeries R :=
  (1 + X * f) * f.subst (argument f) * f.subst (nested f)

private theorem step_constant {f : PowerSeries R} (h : constantCoeff f = 1) :
    constantCoeff (step f) = 1 := by
  simp [step, subst_constant _ _ (argument_zero f), subst_constant _ _ (nested_zero f), h]

private theorem step_agree {n : ℕ} (hn : 1 ≤ n) {f g : PowerSeries R}
    (h : Agree n f g) : Agree (n + 1) (step f) (step g) := by
  apply agree_mul
  · apply agree_mul
    · intro i hi
      simpa only [map_add] using congrArg (coeff i 1 + ·) (agree_X h i hi)
    · exact subst_agree hn (argument_order f) (argument_order g) h (argument_agree h)
  · exact subst_agree hn (nested_order f) (nested_order g) h (nested_agree hn h)

private theorem fixed_unique {f g : PowerSeries R}
    (hf : constantCoeff f = 1) (hg : constantCoeff g = 1)
    (ef : f = step f) (eg : g = step g) : f = g := by
  have h : ∀ n, Agree (n + 1) f g := by
    intro n
    induction n with
    | zero =>
      intro i hi
      have : i = 0 := by omega
      subst i
      simp [coeff_zero_eq_constantCoeff, hf, hg]
    | succ n ih => simpa only [← ef, ← eg] using step_agree (by omega) ih
  ext i
  exact h i i (by omega)

private noncomputable def approximation : ℕ → PowerSeries ℤ
  | 0 => 1
  | n + 1 => step (approximation n)

private theorem approximation_constant (n : ℕ) : constantCoeff (approximation n) = 1 := by
  induction n with
  | zero => simp [approximation]
  | succ n ih => exact step_constant ih

private theorem approximation_stable {n m : ℕ} (h : n ≤ m) :
    Agree (n + 1) (approximation n) (approximation m) := by
  induction n generalizing m with
  | zero =>
    intro i hi
    have : i = 0 := by omega
    subst i
    simp [coeff_zero_eq_constantCoeff, approximation_constant]
  | succ n ih =>
    cases m with
    | zero => omega
    | succ m => exact step_agree (by omega) (ih (by omega))

private noncomputable def limitUnit : PowerSeries ℤ :=
  mk (fun n => coeff n (approximation n))

private theorem limit_agree (n : ℕ) : Agree (n + 1) limitUnit (approximation n) := by
  intro i hi
  simpa only [limitUnit, coeff_mk] using
    approximation_stable (by omega : i ≤ n) i (by omega)

private theorem limit_constant : constantCoeff limitUnit = 1 := by
  rw [← coeff_zero_eq_constantCoeff, limit_agree 0 0 (by omega),
    coeff_zero_eq_constantCoeff, approximation_constant]

private theorem limit_fixed : limitUnit = step limitUnit := by
  ext i
  exact (limit_agree (i + 1) i (by omega)).trans
    (step_agree (by omega : 1 ≤ i + 1) (limit_agree i) i (by omega)).symm

noncomputable def generatingSeries : PowerSeries ℤ := X * limitUnit

noncomputable def a (n : ℕ) : ℤ := coeff n generatingSeries

private theorem equation_iff (f : PowerSeries R) (hf : constantCoeff f = 1) :
    (X * f) ^ 2 = (X * f).subst ((X * f).subst (X * (X * f) + X * (X * f) ^ 2)) ↔
      f = step f := by
  have ha : X * (X * f) + X * (X * f) ^ 2 = argument f := by dsimp [argument]; ring
  have hb : (X * f).subst (argument f) = nested f := by
    rw [subst_mul (.of_constantCoeff_zero (argument_zero f)),
      subst_X (.of_constantCoeff_zero (argument_zero f))]
    rfl
  rw [ha, hb, subst_mul (.of_constantCoeff_zero (nested_zero f)),
    subst_X (.of_constantCoeff_zero (nested_zero f))]
  have he : nested f * f.subst (nested f) = X ^ 2 * (f * step f) := by
    dsimp [nested, argument, step]; ring
  rw [he, show (X * f) ^ 2 = X ^ 2 * (f * f) by ring, X_pow_mul_inj]
  constructor
  · exact (isUnit_iff_constantCoeff.mpr (hf ▸ isUnit_one)).mul_left_cancel
  · intro h; exact congrArg (f * ·) h

private theorem equation_unique {f g : PowerSeries R}
    (hf0 : constantCoeff f = 0) (hg0 : constantCoeff g = 0)
    (hf1 : coeff 1 f = 1) (hg1 : coeff 1 g = 1)
    (hf : f ^ 2 = f.subst (f.subst (X * f + X * f ^ 2)))
    (hg : g ^ 2 = g.subst (g.subst (X * g + X * g ^ 2))) : f = g := by
  obtain ⟨b, rfl⟩ := X_dvd_iff.mpr hf0
  obtain ⟨c, rfl⟩ := X_dvd_iff.mpr hg0
  have hb : constantCoeff b = 1 := by simpa using hf1
  have hc : constantCoeff c = 1 := by simpa using hg1
  rw [fixed_unique hb hc ((equation_iff b hb).mp hf) ((equation_iff c hc).mp hg)]

theorem generating_equation : constantCoeff generatingSeries = 0 ∧
    coeff 1 generatingSeries = 1 ∧
    generatingSeries ^ 2 = generatingSeries.subst
      (generatingSeries.subst (X * generatingSeries + X * generatingSeries ^ 2)) := by
  refine ⟨by simp [generatingSeries], ?_, ?_⟩
  · simpa [generatingSeries, coeff_zero_eq_constantCoeff] using limit_constant
  · exact (equation_iff limitUnit limit_constant).mpr limit_fixed

theorem generating_unique (f : PowerSeries ℤ) (h0 : constantCoeff f = 0)
    (h1 : coeff 1 f = 1)
    (hf : f ^ 2 = f.subst (f.subst (X * f + X * f ^ 2))) : f = generatingSeries := by
  exact equation_unique h0 generating_equation.1 h1 generating_equation.2.1
    hf generating_equation.2.2

private abbrev S := PowerSeries (ZMod 4)

private noncomputable def num (x : S) : S := x + x ^ 2 + 3 * x ^ 3 + x ^ 4 + x ^ 5 + x ^ 6
private noncomputable def den (x : S) : S := 1 - x ^ 6
private noncomputable def homogeneous (n d : S) : S :=
  n * d ^ 5 + n ^ 2 * d ^ 4 + 3 * n ^ 3 * d ^ 3 + n ^ 4 * d ^ 2 + n ^ 5 * d + n ^ 6
private noncomputable def homogeneousDen (n d : S) : S := d ^ 6 - n ^ 6
private noncomputable def reduced : S := num X * invOfUnit (den X) 1

private theorem den_unit (x : S) (hx : constantCoeff x = 0) : IsUnit (den x) := by
  rw [isUnit_iff_constantCoeff]
  simp [den, hx]

private theorem reduced_zero : constantCoeff reduced = 0 := by simp [reduced, num]

private theorem reduced_den : reduced * den X = num X := by
  rw [reduced, mul_assoc, invOfUnit_mul _ _ (by simp [den]), mul_one]

private theorem reduced_subst_den (u : S) (hu : constantCoeff u = 0) :
    reduced.subst u * den u = num u := by
  have hs : HasSubst u := .of_constantCoeff_zero hu
  have h1 : (1 : S).subst u = 1 := by rw [← coe_substAlgHom hs]; exact map_one _
  have h3 : (3 : S).subst u = 3 := by rw [← coe_substAlgHom hs]; exact map_ofNat _ 3
  have he := congrArg (subst u) reduced_den
  simpa only [num, den, subst_mul hs, subst_add hs, subst_sub hs, subst_pow hs,
    subst_X hs, h1, h3] using he

private theorem cleared_subst (u n d : S) (hu : constantCoeff u = 0) (he : u * d = n) :
    reduced.subst u * homogeneousDen n d = homogeneous n d := by
  rw [← he]
  have h := reduced_subst_den u hu
  dsimp [homogeneous, homogeneousDen, num, den] at *
  linear_combination d ^ 6 * h

private noncomputable def firstNum (x : S) : S :=
  x ^ 2 * (1 + x ^ 4 + x ^ 8) +
    2 * (x ^ 12 + x ^ 11 + x ^ 8 + x ^ 7 + x ^ 6 + x ^ 4 + x ^ 3)
private noncomputable def firstDen (x : S) : S := 1 + x ^ 4 + x ^ 8

set_option maxHeartbeats 0 in
private theorem first_polynomial (x : S) :
    firstNum x * homogeneousDen (x * num x * (den x + num x)) (den x ^ 2) =
      firstDen x * homogeneous (x * num x * (den x + num x)) (den x ^ 2) := by
  dsimp [firstNum, firstDen, homogeneous, homogeneousDen, num, den]
  apply sub_eq_zero.mp
  ring_nf
  simp only [← map_ofNat C]
  reduce_mod_char
  simp

set_option maxHeartbeats 0 in
private theorem second_polynomial (x : S) :
    num x ^ 2 * homogeneousDen (firstNum x) (firstDen x) =
      den x ^ 2 * homogeneous (firstNum x) (firstDen x) := by
  dsimp [firstNum, firstDen, homogeneous, homogeneousDen, num, den]
  apply sub_eq_zero.mp
  ring_nf
  simp only [← map_ofNat C]
  reduce_mod_char
  simp

private theorem reduced_equation :
    reduced ^ 2 = reduced.subst (reduced.subst (X * reduced + X * reduced ^ 2)) := by
  let t : S := X * reduced + X * reduced ^ 2
  have ht : constantCoeff t = 0 := by simp [t]
  have htD : t * den X ^ 2 = X * num X * (den X + num X) := by
    rw [← reduced_den]
    dsimp [t]
    ring
  have hB := cleared_subst t _ _ ht htD
  have hQ : IsUnit (homogeneousDen (X * num X * (den X + num X)) (den X ^ 2)) := by
    rw [isUnit_iff_constantCoeff]
    simp [homogeneousDen, num, den]
  have hfirst : reduced.subst t * firstDen X = firstNum X := by
    apply hQ.mul_right_cancel
    calc
      _ = firstDen X * (reduced.subst t *
          homogeneousDen (X * num X * (den X + num X)) (den X ^ 2)) := by ring
      _ = _ := by rw [hB, first_polynomial]
  have hz : constantCoeff (reduced.subst t) = 0 :=
    constantCoeff_subst_eq_zero ht _ reduced_zero
  have hsecond := cleared_subst (reduced.subst t) _ _ hz hfirst
  have hu : IsUnit (homogeneousDen (firstNum X) (firstDen X)) := by
    rw [isUnit_iff_constantCoeff]
    simp [homogeneousDen, firstNum, firstDen]
  apply hu.mul_right_cancel
  rw [hsecond]
  apply ((den_unit X (by simp)).pow 2).mul_right_cancel
  calc
    _ = (reduced * den X) ^ 2 * homogeneousDen (firstNum X) (firstDen X) := by ring
    _ = _ := by rw [reduced_den, second_polynomial]; ring

private theorem reduced_geometric :
    reduced = X * mk 1 + 2 * X ^ 3 * (mk 1 : S).subst (X ^ 6) := by
  have hs : HasSubst (X ^ 6 : S) := .X_pow (by omega)
  have h1 : (1 : S).subst (X ^ 6 : S) = 1 := by
    rw [← coe_substAlgHom hs]; exact map_one _
  have h6 : (mk 1 : S).subst (X ^ 6) * den X = 1 := by
    have he := congrArg (subst (X ^ 6 : S)) (mk_one_mul_one_sub_eq_one (ZMod 4))
    simpa only [subst_mul hs, subst_sub hs, subst_X hs, h1, den] using he
  have hd : den (X : S) = (1 - X) * (1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5) := by
    dsimp [den]; ring
  have hgeom : (X * mk 1 : S) * den X = X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 := by
    rw [hd]
    calc
      _ = X * ((mk 1 : S) * (1 - X)) * (1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5) := by ring
      _ = _ := by rw [mk_one_mul_one_sub_eq_one]; ring
  apply (den_unit X (by simp)).mul_right_cancel
  rw [reduced_den, add_mul, mul_assoc (2 * X ^ 3), h6, mul_one, hgeom]
  dsimp [num]
  ring

private theorem reduced_coeff (n : ℕ) (hn : 0 < n) :
    coeff n reduced = if n % 6 = 3 then 3 else 1 := by
  rw [reduced_geometric, map_add]
  have hg : coeff n (X * mk 1 : S) = 1 := by
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simp
  rw [hg]
  have h2 : (2 : S) = C (2 : ZMod 4) := (map_ofNat C 2).symm
  rw [h2, mul_assoc, coeff_C_mul]
  by_cases h3 : 3 ≤ n
  · rw [coeff_X_pow_mul', if_pos h3, coeff_subst_X_pow (by omega : 6 ≠ 0), coeff_mk]
    by_cases hd : 6 ∣ n - 3
    · have hr : n % 6 = 3 := by
        have := Nat.mod_eq_zero_of_dvd hd
        omega
      rw [if_pos hd, if_pos hr]
      rfl
    · have hr : n % 6 ≠ 3 := by
        intro he
        apply hd
        apply Nat.dvd_of_mod_eq_zero
        omega
      simp [hd, hr]
  · have hr : n % 6 ≠ 3 := by omega
    rw [coeff_X_pow_mul', if_neg h3, if_neg hr]
    simp

private theorem reduced_one : coeff 1 reduced = 1 := by
  simpa using reduced_coeff 1 (by omega)

private theorem reduction : generatingSeries.map (Int.castRingHom (ZMod 4)) = reduced := by
  let hom := Int.castRingHom (ZMod 4)
  have harg : constantCoeff (X * generatingSeries + X * generatingSeries ^ 2) = 0 := by simp
  have hinner : constantCoeff
      (generatingSeries.subst (X * generatingSeries + X * generatingSeries ^ 2)) = 0 :=
    constantCoeff_subst_eq_zero harg _ generating_equation.1
  have he := congrArg (PowerSeries.map hom) generating_equation.2.2
  have hm1 : PowerSeries.map hom
      (generatingSeries.subst (generatingSeries.subst (X * generatingSeries + X * generatingSeries ^ 2))) =
      (generatingSeries.map hom).subst
        ((generatingSeries.subst (X * generatingSeries + X * generatingSeries ^ 2)).map hom) :=
    map_subst (.of_constantCoeff_zero hinner) _
  have hm2 : MvPowerSeries.map hom
      (generatingSeries.subst (X * generatingSeries + X * generatingSeries ^ 2)) =
      (generatingSeries.map hom).subst ((X * generatingSeries + X * generatingSeries ^ 2).map hom) :=
    map_subst (.of_constantCoeff_zero harg) _
  rw [map_pow, hm1, hm2] at he
  simp only [map_add, map_mul, map_pow, map_X] at he
  have h0 : constantCoeff (generatingSeries.map hom) = 0 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
      generating_equation.1, map_zero]
  have h1 : coeff 1 (generatingSeries.map hom) = 1 := by
    rw [coeff_map, generating_equation.2.1, map_one]
  exact equation_unique h0 reduced_zero h1 reduced_one he reduced_equation

/-- The complete modulo-four classification, including every positive index. -/
theorem hanna_conjecture (n : ℕ) (hn : 0 < n) :
    a n % 4 = if n % 6 = 3 then 3 else 1 := by
  have hc : (a n : ZMod 4) = if n % 6 = 3 then 3 else 1 := by
    have he := congrArg (coeff n) reduction
    simpa only [coeff_map, Int.coe_castRingHom, a, reduced_coeff n hn] using he
  split_ifs at hc ⊢ with h
  · exact (ZMod.intCast_eq_intCast_iff' (a n) 3 4).mp hc
  · exact (ZMod.intCast_eq_intCast_iff' (a n) 1 4).mp hc

/-- Oddness follows from the two possible residues in the classification. -/
theorem odd_coefficients (n : ℕ) (hn : 0 < n) : Odd (a n) := by
  have h := hanna_conjecture n hn
  rw [Int.odd_iff]
  split_ifs at h <;> omega

#print axioms generatingSeries
#print axioms a
#print axioms generating_equation
#print axioms generating_unique
#print axioms hanna_conjecture
#print axioms odd_coefficients
end D5.S1.Recurrence.Residue.DoubleCompositionModFourClassification
