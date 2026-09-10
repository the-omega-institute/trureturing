/- GID: D5/S1/Recurrence/Invariants/CatalanDoubleCompositionPowersOfFour
   generality: I
   mirror-B: D5/B/S1/Recurrence/Invariants/CatalanDoubleCompositionPowersOfFour
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Integer existence and double Catalan composition prove Hanna's powers-of-four parity. -/

import D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity

open PowerSeries hiding catalanSeries
open D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity
  (catalanSeries catalan_equation catalan_unique)

namespace D5.S1.Recurrence.Invariants.CatalanDoubleCompositionPowersOfFour

private noncomputable def minusArgument : PowerSeries ℤ := X - X ^ 2
private noncomputable def plusArgument : PowerSeries ℤ := X + X ^ 2

private theorem minus_zero : constantCoeff minusArgument = 0 := by simp [minusArgument]
private theorem plus_zero : constantCoeff plusArgument = 0 := by simp [plusArgument]

private theorem catalan_right : minusArgument.subst catalanSeries = X := by
  rw [minusArgument, subst_sub (.of_constantCoeff_zero catalan_equation.1),
    subst_X (.of_constantCoeff_zero catalan_equation.1),
    subst_pow (.of_constantCoeff_zero catalan_equation.1),
    subst_X (.of_constantCoeff_zero catalan_equation.1)]
  linear_combination catalan_equation.2.2

private theorem catalan_left : catalanSeries.subst minusArgument = X := by
  have hu : IsUnit (coeff 1 minusArgument) := by simp [minusArgument]
  let inv := minusArgument.substInvOfIsUnit hu
  have hz : constantCoeff inv = 0 := by simp [inv]
  have he : minusArgument.subst inv = X :=
    subst_substInvOfIsUnit_right _ minus_zero hu
  have hfix : inv = X + inv ^ 2 := by
    rw [minusArgument, subst_sub (.of_constantCoeff_zero hz),
      subst_X (.of_constantCoeff_zero hz), subst_pow (.of_constantCoeff_zero hz),
      subst_X (.of_constantCoeff_zero hz)] at he
    linear_combination he
  rw [← catalan_unique inv hz hfix]
  exact subst_substInvOfIsUnit_left _ minus_zero hu

private noncomputable def inner : PowerSeries ℤ := plusArgument.subst catalanSeries

private theorem inner_zero : constantCoeff inner = 0 :=
  constantCoeff_subst_eq_zero catalan_equation.1 _ plus_zero

private noncomputable def step (f : PowerSeries ℤ) : PowerSeries ℤ :=
  catalanSeries + (f.subst inner) ^ 2

private theorem step_zero {f : PowerSeries ℤ} (hf : constantCoeff f = 0) :
    constantCoeff (step f) = 0 := by
  have hz : constantCoeff (f.subst inner) = 0 :=
    constantCoeff_subst_eq_zero inner_zero f hf
  simp only [step, map_add, map_pow, catalan_equation.1,
    hz, zero_pow (by omega : 2 ≠ 0), zero_add]

private def Agree (n : ℕ) (f g : PowerSeries ℤ) : Prop :=
  ∀ i < n, coeff i f = coeff i g

private theorem agree_iff (n : ℕ) (f g : PowerSeries ℤ) :
    Agree n f g ↔ (X : PowerSeries ℤ) ^ n ∣ f - g := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem coeff_pow_zero {R : Type*} [CommRing R] {f : PowerSeries R}
    (hf : constantCoeff f = 0) {i k : ℕ} (hi : i < k) : coeff i (f ^ k) = 0 :=
  X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hf) k) i hi

private theorem subst_agree {n : ℕ} {f g : PowerSeries ℤ} (h : Agree n f g) :
    Agree n (f.subst inner) (g.subst inner) := by
  intro i hi
  rw [coeff_subst' (.of_constantCoeff_zero inner_zero),
    coeff_subst' (.of_constantCoeff_zero inner_zero)]
  apply finsum_congr
  intro k
  by_cases hk : k < n
  · rw [h k hk]
  · rw [coeff_pow_zero inner_zero (by omega : i < k), smul_zero, smul_zero]

-- The zero constant terms give one extra power of X in a difference of squares.
private theorem step_agree {n : ℕ} {f g : PowerSeries ℤ}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) (h : Agree n f g) :
    Agree (n + 1) (step f) (step g) := by
  have hd := (agree_iff _ _ _).mp (subst_agree h)
  have hz : (X : PowerSeries ℤ) ∣ f.subst inner + g.subst inner := by
    apply X_dvd_iff.mpr
    have hzf : constantCoeff (f.subst inner) = 0 :=
      constantCoeff_subst_eq_zero inner_zero f hf
    have hzg : constantCoeff (g.subst inner) = 0 :=
      constantCoeff_subst_eq_zero inner_zero g hg
    simp only [map_add, hzf, hzg, zero_add]
  apply (agree_iff _ _ _).mpr
  have hm := mul_dvd_mul hd hz
  rw [← pow_succ] at hm
  convert hm using 1
  simp only [step]
  ring

private noncomputable def approximation : ℕ → PowerSeries ℤ
  | 0 => 0
  | n + 1 => step (approximation n)

private theorem approximation_zero (n : ℕ) : constantCoeff (approximation n) = 0 := by
  induction n with
  | zero => simp [approximation]
  | succ n ih => exact step_zero ih

private theorem approximation_stable {n m : ℕ} (h : n ≤ m) :
    Agree n (approximation n) (approximation m) := by
  induction n generalizing m with
  | zero => intro i hi; omega
  | succ n ih =>
    cases m with
    | zero => omega
    | succ m => exact step_agree (approximation_zero n) (approximation_zero m) (ih (by omega))

noncomputable def generatingSeries : PowerSeries ℤ :=
  mk (fun n => coeff n (approximation (n + 1)))

noncomputable def a (n : ℕ) : ℤ := coeff n generatingSeries

private theorem generating_agree (n : ℕ) : Agree n generatingSeries (approximation n) := by
  intro i hi
  simpa only [generatingSeries, coeff_mk] using
    approximation_stable (by omega : i + 1 ≤ n) i (by omega)

private theorem generating_zero : constantCoeff generatingSeries = 0 := by
  rw [← coeff_zero_eq_constantCoeff, generating_agree 1 0 (by omega),
    coeff_zero_eq_constantCoeff, approximation_zero]

private theorem generating_fixed : generatingSeries = step generatingSeries := by
  ext i
  exact (generating_agree (i + 2) i (by omega)).trans
    (step_agree generating_zero (approximation_zero (i + 1))
      (generating_agree (i + 1)) i (by omega)).symm

private theorem equation_iff (f : PowerSeries ℤ) :
    (X = f.subst minusArgument - (f.subst plusArgument) ^ 2) ↔ f = step f := by
  have hm : HasSubst minusArgument := .of_constantCoeff_zero minus_zero
  have hp : HasSubst plusArgument := .of_constantCoeff_zero plus_zero
  have hc : HasSubst catalanSeries := .of_constantCoeff_zero catalan_equation.1
  constructor
  · intro he
    have h := congrArg (subst catalanSeries) he
    rw [subst_X hc, subst_sub hc, subst_pow hc,
      subst_comp_subst_apply hm hc, catalan_right, X_subst,
      subst_comp_subst_apply hp hc] at h
    dsimp [step, inner]
    linear_combination -h
  · intro he
    have h := congrArg (subst minusArgument) he
    rw [step, subst_add hm, subst_pow hm, catalan_left,
      subst_comp_subst_apply (.of_constantCoeff_zero inner_zero) hm] at h
    have hi : inner.subst minusArgument = plusArgument := by
      rw [inner, subst_comp_subst_apply hc hm, catalan_left, X_subst]
    rw [hi] at h
    linear_combination -h

theorem generating_equation : constantCoeff generatingSeries = 0 ∧
    coeff 1 generatingSeries = 1 ∧
    X = generatingSeries.subst (X - X ^ 2 : PowerSeries ℤ) -
      (generatingSeries.subst (X + X ^ 2 : PowerSeries ℤ)) ^ 2 := by
  refine ⟨generating_zero, ?_, (equation_iff _).mpr generating_fixed⟩
  have h := congrArg (coeff 1) generating_fixed
  have hz := constantCoeff_subst_eq_zero inner_zero generatingSeries generating_zero
  simpa only [step, map_add, catalan_equation.2.1,
    coeff_pow_zero hz (by omega : 1 < 2), add_zero] using h

theorem generating_unique (f : PowerSeries ℤ) (h0 : constantCoeff f = 0)
    (hf : X = f.subst (X - X ^ 2 : PowerSeries ℤ) -
      (f.subst (X + X ^ 2 : PowerSeries ℤ)) ^ 2) : f = generatingSeries := by
  have hfix := (equation_iff f).mp hf
  have h : ∀ n, Agree n f generatingSeries := by
    intro n
    induction n with
    | zero => intro i hi; omega
    | succ n ih =>
      simpa only [← hfix, ← generating_fixed] using step_agree h0 generating_zero ih
  ext n
  exact h (n + 1) n (by omega)

private noncomputable def binaryCatalan : PowerSeries (ZMod 2) :=
  catalanSeries.map (Int.castRingHom (ZMod 2))

private instance : CharP (PowerSeries (ZMod 2)) 2 :=
  charP_of_injective_ringHom (f := C) C_injective 2

private theorem binary_zero : constantCoeff binaryCatalan = 0 := by
  rw [← coeff_zero_eq_constantCoeff]
  simp only [binaryCatalan, coeff_map, coeff_zero_eq_constantCoeff,
    catalan_equation.1, map_zero]

private theorem binary_equation : binaryCatalan = X + binaryCatalan ^ 2 := by
  simpa [binaryCatalan] using congrArg
    (PowerSeries.map (Int.castRingHom (ZMod 2))) catalan_equation.2.2

private theorem quadratic_unique {f g : PowerSeries (ZMod 2)}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0)
    (ef : f = X + f ^ 2) (eg : g = X + g ^ 2) : f = g := by
  have hu : IsUnit (1 - f - g) := by
    rw [isUnit_iff_constantCoeff]
    simp [hf, hg]
  have he : (1 - f - g) * (f - g) = (1 - f - g) * 0 := by
    linear_combination ef - eg
  exact sub_eq_zero.mp (hu.mul_left_cancel he)

private theorem reduced_zero :
    constantCoeff (generatingSeries.map (Int.castRingHom (ZMod 2))) = 0 := by
  rw [← coeff_zero_eq_constantCoeff, coeff_map, coeff_zero_eq_constantCoeff,
    generating_zero, map_zero]

theorem mod_two_identity :
    (generatingSeries.map (Int.castRingHom (ZMod 2))).subst
      (X + X ^ 2 : PowerSeries (ZMod 2)) =
      catalanSeries.map (Int.castRingHom (ZMod 2)) := by
  let hom := Int.castRingHom (ZMod 2)
  let f := generatingSeries.map hom
  let y : PowerSeries (ZMod 2) := f.subst (X + X ^ 2 : PowerSeries (ZMod 2))
  have hq : constantCoeff (X + X ^ 2 : PowerSeries (ZMod 2)) = 0 := by simp
  have hy : constantCoeff y = 0 :=
    constantCoeff_subst_eq_zero hq f reduced_zero
  have he : (X : PowerSeries (ZMod 2)) = y + y ^ 2 := by
    have e : X = generatingSeries.subst minusArgument -
        (generatingSeries.subst plusArgument) ^ 2 := generating_equation.2.2
    have h := congrArg (PowerSeries.map hom) e
    have hm : PowerSeries.map hom (generatingSeries.subst minusArgument) =
        f.subst (minusArgument.map hom) :=
      map_subst (.of_constantCoeff_zero minus_zero) _
    have hp : PowerSeries.map hom (generatingSeries.subst plusArgument) =
        f.subst (plusArgument.map hom) :=
      map_subst (.of_constantCoeff_zero plus_zero) _
    rw [map_sub, map_pow, hm, hp] at h
    simpa only [minusArgument, plusArgument, map_X, map_sub, map_add,
      map_pow, CharTwo.sub_eq_add] using h
  exact quadratic_unique hy binary_zero
    (CharTwo.add_eq_iff_eq_add.mp he.symm) binary_equation

private theorem binary_right :
    (X + X ^ 2 : PowerSeries (ZMod 2)).subst binaryCatalan = X := by
  rw [subst_add (.of_constantCoeff_zero binary_zero),
    subst_pow (.of_constantCoeff_zero binary_zero),
    subst_X (.of_constantCoeff_zero binary_zero)]
  exact CharTwo.eq_add_iff_add_eq.mp binary_equation

private theorem double_composition :
    generatingSeries.map (Int.castRingHom (ZMod 2)) =
      binaryCatalan.subst binaryCatalan := by
  have he := congrArg (subst binaryCatalan) mod_two_identity
  have hq : constantCoeff (X + X ^ 2 : PowerSeries (ZMod 2)) = 0 := by simp
  rw [subst_comp_subst_apply (.of_constantCoeff_zero hq)
    (.of_constantCoeff_zero binary_zero), binary_right, X_subst] at he
  exact he

-- Composing the Catalan equation twice and squaring cancels the middle square.
private theorem double_quartic :
    binaryCatalan.subst binaryCatalan = X + (binaryCatalan.subst binaryCatalan) ^ 4 := by
  let d : PowerSeries (ZMod 2) := binaryCatalan.subst binaryCatalan
  have hd : d = binaryCatalan + d ^ 2 := by
    have he := congrArg (subst binaryCatalan) binary_equation
    simpa only [subst_add (.of_constantCoeff_zero binary_zero),
      subst_X (.of_constantCoeff_zero binary_zero),
      subst_pow (.of_constantCoeff_zero binary_zero)] using he
  have hdc : d + d ^ 2 = binaryCatalan := CharTwo.eq_add_iff_add_eq.mp hd
  have hc : binaryCatalan + binaryCatalan ^ 2 = X :=
    CharTwo.eq_add_iff_add_eq.mp binary_equation
  rw [← hdc, add_pow_char, ← pow_mul] at hc
  have hzero : d ^ 2 + d ^ 2 = 0 := CharTwo.add_self_eq_zero _
  have hquartic : d + d ^ 4 = X := by
    linear_combination hc - hzero
  exact CharTwo.add_eq_iff_eq_add.mp hquartic

private theorem square_subst (f : PowerSeries (ZMod 2)) : f.subst (X ^ 2) = f ^ 2 := by
  have h := MvPowerSeries.map_frobenius_expand 2 (by decide : 2 ≠ 0) (f := f)
  change (f.expand 2 (by decide)).map (frobenius (ZMod 2) 2) = f ^ 2 at h
  rw [ZMod.frobenius_zmod, PowerSeries.map_id, expand_apply] at h
  exact h

private theorem fourth_subst (f : PowerSeries (ZMod 2)) : f.subst (X ^ 4) = f ^ 4 := by
  have hx : HasSubst (X ^ 2 : PowerSeries (ZMod 2)) := .X_pow (by decide)
  calc
    f.subst (X ^ 4) = PowerSeries.subst (X ^ 2 : PowerSeries (ZMod 2))
        (f.subst (X ^ 2 : PowerSeries (ZMod 2))) := by
      rw [subst_comp_subst_apply hx hx, subst_pow hx, subst_X hx, ← pow_mul]
    _ = f ^ 4 := by rw [square_subst, square_subst, ← pow_mul]

private theorem quartic_support (f : PowerSeries (ZMod 2))
    (h0 : constantCoeff f = 0) (hf : f = X + f ^ 4) (n : ℕ) :
    coeff n f = 1 ↔ ∃ k : ℕ, n = 4 ^ k := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n
      rw [coeff_zero_eq_constantCoeff, h0]
      exact iff_of_false zero_ne_one (by
        rintro ⟨k, hk⟩
        exact (pow_ne_zero k (by decide : (4 : ℕ) ≠ 0)) hk.symm)
    have hc := congrArg (coeff n) hf
    rw [← fourth_subst, map_add, coeff_subst_X_pow (by decide : 4 ≠ 0)] at hc
    simp only [coeff_X, Algebra.algebraMap_self, RingHom.id_apply] at hc
    by_cases hn1 : n = 1
    · subst n
      simp only [if_neg (by decide : ¬4 ∣ 1), add_zero] at hc
      exact iff_of_true hc ⟨0, rfl⟩
    rw [if_neg hn1, zero_add] at hc
    by_cases hd : 4 ∣ n
    · rw [if_pos hd] at hc
      rw [hc, ih (n / 4) (by omega)]
      constructor
      · rintro ⟨k, hk⟩
        refine ⟨k + 1, ?_⟩
        have hm := Nat.mod_eq_zero_of_dvd hd
        rw [pow_succ]
        omega
      · rintro ⟨k, hk⟩
        cases k with
        | zero => simp at hk; omega
        | succ k =>
          refine ⟨k, ?_⟩
          rw [pow_succ] at hk
          omega
    · rw [if_neg hd] at hc
      rw [hc]
      exact iff_of_false zero_ne_one (by
        rintro ⟨k, hk⟩
        cases k with
        | zero => simp at hk; omega
        | succ k =>
          apply hd
          rw [hk, pow_succ]
          exact dvd_mul_left 4 (4 ^ k))

theorem hanna_conjecture (n : ℕ) (_hn : 1 ≤ n) :
    Odd (a n) ↔ ∃ k : ℕ, n = 4 ^ k := by
  rw [← ZMod.intCast_eq_one_iff_odd]
  have hc : (a n : ZMod 2) = coeff n (binaryCatalan.subst binaryCatalan) := by
    simpa [a, coeff_map] using congrArg (coeff n) double_composition
  rw [hc]
  exact quartic_support _
    (constantCoeff_subst_eq_zero binary_zero _ binary_zero) double_quartic n

#print axioms generating_equation
#print axioms generating_unique
#print axioms mod_two_identity
#print axioms hanna_conjecture

end D5.S1.Recurrence.Invariants.CatalanDoubleCompositionPowersOfFour
