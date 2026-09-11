/- GID: D5/S1/Recurrence/Parity/QuadraticSquareReversionModFour
   generality: I
   mirror-B: D5/B/S1/Recurrence/Parity/QuadraticSquareReversionModFour
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Integral quadratic reversion and Catalan reduction prove Hanna A389542 modulo four. -/

import D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity

open PowerSeries

namespace D5.S1.Recurrence.Parity.QuadraticSquareReversionModFour

private def Agree {R : Type*} [CommRing R] (d : ℕ) (f g : PowerSeries R) : Prop :=
  ∀ n < d, coeff n f = coeff n g

private theorem agree_iff {R : Type*} [CommRing R] (d : ℕ) (f g : PowerSeries R) :
    Agree d f g ↔ (X : PowerSeries R) ^ d ∣ f - g := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem subst_agree {R : Type*} [CommRing R] {d : ℕ}
    {f g u : PowerSeries R} (h : Agree d f g) (hu : constantCoeff u = 0) :
    Agree d (f.subst u) (g.subst u) := by
  intro n hn
  rw [coeff_subst' (.of_constantCoeff_zero hu), coeff_subst' (.of_constantCoeff_zero hu)]
  apply finsum_congr
  intro k
  by_cases hk : k < d
  · rw [h k hk]
  · have hz : coeff n (u ^ k) = 0 :=
      X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hu) k) n (by omega)
    rw [hz, smul_zero, smul_zero]

private noncomputable def step (H : PowerSeries ℤ) : PowerSeries ℤ :=
  -X - H ^ 2 - 2 * X * H.subst (4 * X ^ 3)

private theorem step_zero {H : PowerSeries ℤ} (h : constantCoeff H = 0) :
    constantCoeff (step H) = 0 := by simp [step, h]

private theorem step_agree {d : ℕ} {H J : PowerSeries ℤ}
    (hH : constantCoeff H = 0) (hJ : constantCoeff J = 0) (h : Agree d H J) :
    Agree (d + 1) (step H) (step J) := by
  apply (agree_iff _ _ _).mpr
  have hd := (agree_iff _ _ _).mp h
  have hs := (agree_iff _ _ _).mp (subst_agree h (u := 4 * X ^ 3) (by simp))
  have hsum : X ∣ H + J := X_dvd_iff.mpr (by simp [hH, hJ])
  have hfirst : X ^ (d + 1) ∣ (H - J) * (H + J) := by
    simpa only [pow_succ] using mul_dvd_mul hd hsum
  have hsecond : (X : PowerSeries ℤ) ^ (d + 1) ∣
      2 * X * (H.subst (4 * X ^ 3) - J.subst (4 * X ^ 3)) := by
    have hh := dvd_mul_of_dvd_left (mul_dvd_mul (dvd_refl X) hs) (2 : PowerSeries ℤ)
    convert hh using 1
    · rw [pow_succ, mul_comm]
    · ring
  convert dvd_neg.mpr (dvd_add hfirst hsecond) using 1
  dsimp [step]
  ring

private noncomputable def approximation : ℕ → PowerSeries ℤ
  | 0 => 0
  | n + 1 => step (approximation n)

private theorem approximation_zero (n : ℕ) : constantCoeff (approximation n) = 0 := by
  induction n with
  | zero => simp [approximation]
  | succ n ih => exact step_zero ih

private theorem approximation_stable {d n : ℕ} (h : d ≤ n) :
    Agree d (approximation d) (approximation n) := by
  induction d generalizing n with
  | zero => intro i hi; omega
  | succ d ih =>
    cases n with
    | zero => omega
    | succ n => exact step_agree (approximation_zero d) (approximation_zero n) (ih (by omega))

private noncomputable def correction : PowerSeries ℤ :=
  mk fun n => coeff n (approximation (n + 1))

private theorem correction_agree (d : ℕ) : Agree d correction (approximation d) := by
  intro n hn
  simpa only [correction, coeff_mk] using
    approximation_stable (by omega : n + 1 ≤ d) n (by omega)

private theorem correction_zero : constantCoeff correction = 0 := by
  rw [← coeff_zero_eq_constantCoeff, correction_agree 1 0 (by omega),
    coeff_zero_eq_constantCoeff, approximation_zero]

private theorem correction_fixed : correction = step correction := by
  ext n
  exact (correction_agree (n + 2) n (by omega)).trans
    (step_agree correction_zero (approximation_zero (n + 1))
      (correction_agree (n + 1)) n (by omega)).symm

noncomputable def inverseSeries : PowerSeries ℤ := X * (1 + 2 * correction)

private theorem inverse_zero : constantCoeff inverseSeries = 0 := by simp [inverseSeries]

private theorem inverse_one : coeff 1 inverseSeries = 1 := by
  simp [inverseSeries, correction_zero]

private theorem inverse_unit : IsUnit (coeff 1 inverseSeries) := inverse_one ▸ isUnit_one

noncomputable def generatingSeries : PowerSeries ℤ :=
  inverseSeries.substInvOfIsUnit inverse_unit

noncomputable def a (n : ℕ) : ℤ := coeff n generatingSeries

private theorem generating_zero : constantCoeff generatingSeries = 0 :=
  constantCoeff_substInvOfIsUnit _ _

private theorem generating_one : coeff 1 generatingSeries = 1 := by
  rw [generatingSeries, coeff_one_substInvOfIsUnit]
  have hu : inverse_unit.unit = 1 := by apply Units.ext; simpa using inverse_one
  rw [hu]; rfl

private theorem inverse_left : inverseSeries.subst generatingSeries = X :=
  subst_substInvOfIsUnit_right _ inverse_zero _

private theorem inverse_right : generatingSeries.subst inverseSeries = X :=
  subst_substInvOfIsUnit_left _ inverse_zero _

private theorem subst_four {R : Type*} [CommRing R] {u : PowerSeries R}
    (hu : HasSubst u) : (4 : PowerSeries R).subst u = 4 := by
  rw [← coe_substAlgHom hu]
  exact map_ofNat _ 4

theorem inverse_equation :
    inverseSeries ^ 2 = X ^ 2 - inverseSeries.subst (4 * X ^ 3) := by
  have hq : HasSubst (4 * (X : PowerSeries ℤ) ^ 3) := .of_constantCoeff_zero (by
    change constantCoeff (4 * (X : PowerSeries ℤ) ^ 3) = 0
    simp)
  have htwo : (2 : PowerSeries ℤ).subst (4 * (X : PowerSeries ℤ) ^ 3) = 2 := by
    rw [← coe_substAlgHom hq]; exact map_ofNat _ 2
  have hone : (1 : PowerSeries ℤ).subst (4 * (X : PowerSeries ℤ) ^ 3) = 1 := by
    rw [← coe_substAlgHom hq]; exact map_one _
  rw [inverseSeries, subst_mul hq, subst_X hq, subst_add hq, subst_mul hq,
    hone, htwo]
  have he := correction_fixed
  dsimp [step] at he
  linear_combination 4 * X ^ 2 * he

theorem generating_equation : constantCoeff generatingSeries = 0 ∧
    coeff 1 generatingSeries = 1 ∧
    generatingSeries.subst (generatingSeries ^ 2 - X ^ 2) = 4 * generatingSeries ^ 3 := by
  refine ⟨generating_zero, generating_one, ?_⟩
  have hA : HasSubst generatingSeries := .of_constantCoeff_zero generating_zero
  have hq : HasSubst (4 * (X : PowerSeries ℤ) ^ 3) := .of_constantCoeff_zero (by
    change constantCoeff (4 * (X : PowerSeries ℤ) ^ 3) = 0
    simp)
  have he := congrArg (subst generatingSeries) inverse_equation
  rw [subst_pow hA, inverse_left, subst_sub hA, subst_pow hA, subst_X hA,
    subst_comp_subst_apply hq hA, subst_mul hA, subst_four hA,
    subst_pow hA, subst_X hA] at he
  have hi : inverseSeries.subst (4 * generatingSeries ^ 3) = generatingSeries ^ 2 - X ^ 2 := by
    linear_combination he
  have hS : HasSubst (4 * generatingSeries ^ 3) := .of_constantCoeff_zero (by
    change constantCoeff (4 * generatingSeries ^ 3) = 0
    simp [generating_zero])
  rw [← hi, ← subst_comp_subst_apply (.of_constantCoeff_zero inverse_zero) hS,
    inverse_right, subst_X hS]

private theorem unit_equation {R : Type*} [CommRing R] (u : PowerSeries R)
    (he : (X * u) ^ 2 = X ^ 2 - (X * u).subst (4 * X ^ 3)) :
    u ^ 2 = 1 - 4 * X * u.subst (4 * X ^ 3) := by
  have hq : HasSubst (4 * (X : PowerSeries R) ^ 3) := .of_constantCoeff_zero (by
    change constantCoeff (4 * (X : PowerSeries R) ^ 3) = 0
    simp)
  rw [subst_mul hq, subst_X hq] at he
  apply X_pow_mul_cancel (k := 2)
  linear_combination he

private theorem unit_unique (u v : PowerSeries ℚ)
    (hu : constantCoeff u = 1) (hv : constantCoeff v = 1)
    (eu : u ^ 2 = 1 - 4 * X * u.subst (4 * X ^ 3))
    (ev : v ^ 2 = 1 - 4 * X * v.subst (4 * X ^ 3)) : u = v := by
  have hi : IsUnit (u + v) := by
    rw [isUnit_iff_constantCoeff, map_add, hu, hv]
    exact isUnit_iff_ne_zero.mpr (by norm_num)
  have he : (u + v) * (u - v) =
      -4 * X * (u.subst (4 * X ^ 3) - v.subst (4 * X ^ 3)) := by
    linear_combination eu - ev
  have ha : ∀ d, Agree d u v := by
    intro d
    induction d with
    | zero => intro n hn; omega
    | succ d ih =>
      apply (agree_iff _ _ _).mpr
      apply hi.dvd_mul_left.mp
      rw [he]
      have hs := (agree_iff _ _ _).mp (subst_agree ih (u := 4 * X ^ 3) (by simp))
      have hd := dvd_mul_of_dvd_left (mul_dvd_mul (dvd_refl X) hs) (-4 : PowerSeries ℚ)
      convert hd using 1
      · rw [pow_succ, mul_comm]
      · ring
  ext n
  exact ha (n + 1) n (by omega)

private theorem inverse_unique_rational (S T : PowerSeries ℚ)
    (hS0 : constantCoeff S = 0) (hT0 : constantCoeff T = 0)
    (hS1 : coeff 1 S = 1) (hT1 : coeff 1 T = 1)
    (hS : S ^ 2 = X ^ 2 - S.subst (4 * X ^ 3))
    (hT : T ^ 2 = X ^ 2 - T.subst (4 * X ^ 3)) : S = T := by
  obtain ⟨u, rfl⟩ := X_dvd_iff.mpr hS0
  obtain ⟨v, rfl⟩ := X_dvd_iff.mpr hT0
  have hu : constantCoeff u = 1 := by simpa using hS1
  have hv : constantCoeff v = 1 := by simpa using hT1
  rw [unit_unique u v hu hv (unit_equation u hS) (unit_equation v hT)]

private theorem inverse_unique (S : PowerSeries ℤ)
    (h0 : constantCoeff S = 0) (h1 : coeff 1 S = 1)
    (hS : S ^ 2 = X ^ 2 - S.subst (4 * X ^ 3)) : S = inverseSeries := by
  let hom := Int.castRingHom ℚ
  have mapped (T : PowerSeries ℤ) (hT : T ^ 2 = X ^ 2 - T.subst (4 * X ^ 3)) :
      (T.map hom) ^ 2 = X ^ 2 - (T.map hom).subst (4 * X ^ 3) := by
    have hq : HasSubst (4 * (X : PowerSeries ℤ) ^ 3) := .of_constantCoeff_zero (by
      change constantCoeff (4 * (X : PowerSeries ℤ) ^ 3) = 0
      simp)
    have hm : PowerSeries.map hom (T.subst (4 * X ^ 3)) =
        (T.map hom).subst ((4 * (X : PowerSeries ℤ) ^ 3).map hom) := map_subst hq T
    have ht := congrArg (PowerSeries.map hom) hT
    rw [map_pow, map_sub, map_pow, map_X, hm] at ht
    simpa only [map_mul, map_ofNat, map_pow, map_X] using ht
  have he := inverse_unique_rational (S.map hom) (inverseSeries.map hom)
    (by rw [← coeff_zero_eq_constantCoeff]; simp [coeff_zero_eq_constantCoeff, h0])
    (by rw [← coeff_zero_eq_constantCoeff]; simp [coeff_zero_eq_constantCoeff, inverse_zero])
    (by simp [h1]) (by simp [inverse_one]) (mapped S hS) (mapped _ inverse_equation)
  ext n
  have hc := congrArg (coeff n) he
  change (↑(coeff n S) : ℚ) = ↑(coeff n inverseSeries) at hc
  exact_mod_cast hc

theorem generating_unique (B : PowerSeries ℤ)
    (h0 : constantCoeff B = 0) (h1 : coeff 1 B = 1)
    (hB : B.subst (B ^ 2 - X ^ 2) = 4 * B ^ 3) : B = generatingSeries := by
  have hu : IsUnit (coeff 1 B) := h1 ▸ isUnit_one
  let S := B.substInvOfIsUnit hu
  have hs0 : constantCoeff S = 0 := constantCoeff_substInvOfIsUnit B hu
  have hs1 : coeff 1 S = 1 := by
    change coeff 1 (B.substInvOfIsUnit hu) = 1
    rw [coeff_one_substInvOfIsUnit]
    have hh : hu.unit = 1 := by apply Units.ext; simpa using h1
    rw [hh]; rfl
  have hBS : B.subst S = X := subst_substInvOfIsUnit_right B h0 hu
  have hSB : S.subst B = X := subst_substInvOfIsUnit_left B h0 hu
  have hb : HasSubst B := .of_constantCoeff_zero h0
  have hs : HasSubst S := .of_constantCoeff_zero hs0
  have hinner : HasSubst (B ^ 2 - X ^ 2) := .of_constantCoeff_zero (by
    change constantCoeff (B ^ 2 - X ^ 2) = 0
    simp [h0])
  have he := congrArg (subst S) hB
  rw [subst_comp_subst_apply hinner hs, subst_sub hs, subst_pow hs, subst_pow hs, subst_X hs,
    hBS, subst_mul hs, subst_four hs, subst_pow hs, hBS] at he
  have hv : HasSubst (X ^ 2 - S ^ 2) := .of_constantCoeff_zero (by
    change constantCoeff ((X : PowerSeries ℤ) ^ 2 - S ^ 2) = 0
    simp [hs0])
  have hSE : S.subst (4 * X ^ 3) = X ^ 2 - S ^ 2 := by
    rw [← he, ← subst_comp_subst_apply hb hv, hSB, subst_X hv]
  have hSR := inverse_unique S hs0 hs1 (by rw [hSE]; ring)
  calc
    B = PowerSeries.subst generatingSeries (B.subst inverseSeries) := by
      rw [subst_comp_subst_apply (.of_constantCoeff_zero inverse_zero)
        (.of_constantCoeff_zero generating_zero), inverse_left, X_subst]
    _ = generatingSeries := by
      rw [← hSR, hBS, subst_X (.of_constantCoeff_zero generating_zero)]

private theorem two_zero : (2 : PowerSeries (ZMod 2)) = 0 := by
  rw [← map_ofNat C 2, show (2 : ZMod 2) = 0 by decide, map_zero]

private theorem four_zero : (4 : PowerSeries (ZMod 4)) = 0 := by
  rw [← map_ofNat C 4, show (4 : ZMod 4) = 0 by decide, map_zero]

private theorem correction_mod_two : correction.map (Int.castRingHom (ZMod 2)) =
    Invariants.CatalanCompositionSquareParity.catalanSeries.map (Int.castRingHom (ZMod 2)) := by
  let hom := Int.castRingHom (ZMod 2)
  let H := correction.map hom
  let K := Invariants.CatalanCompositionSquareParity.catalanSeries.map hom
  have hH : constantCoeff H = 0 := by
    rw [← coeff_zero_eq_constantCoeff]
    simp [H, coeff_zero_eq_constantCoeff, correction_zero]
  have hK : constantCoeff K = 0 := by
    rw [← coeff_zero_eq_constantCoeff]
    simp [K, coeff_zero_eq_constantCoeff, Invariants.CatalanCompositionSquareParity.catalan_equation.1]
  have he : H = -X - H ^ 2 := by
    simpa [step, H, map_ofNat, two_zero] using congrArg (PowerSeries.map hom) correction_fixed
  have hf : H = X + H ^ 2 := by
    linear_combination he - (X + H ^ 2) * two_zero
  have hk : K = X + K ^ 2 := by
    simpa [K] using congrArg (PowerSeries.map hom)
      Invariants.CatalanCompositionSquareParity.catalan_equation.2.2
  have hu : IsUnit (1 - H - K) := by
    rw [isUnit_iff_constantCoeff]
    simp [hH, hK]
  apply sub_eq_zero.mp
  apply hu.mul_left_cancel
  linear_combination hf - hk

private theorem generating_mod_two : generatingSeries.map (Int.castRingHom (ZMod 2)) = X := by
  let hom := Int.castRingHom (ZMod 2)
  have hR : inverseSeries.map hom = X := by simp [inverseSeries, map_ofNat, two_zero]
  have he := congrArg (PowerSeries.map hom) inverse_left
  have hm : PowerSeries.map hom (inverseSeries.subst generatingSeries) =
      (inverseSeries.map hom).subst (generatingSeries.map hom) :=
    map_subst (.of_constantCoeff_zero generating_zero) _
  rw [hm, hR, map_X] at he
  have hz : constantCoeff (generatingSeries.map hom) = 0 := by
    rw [← coeff_zero_eq_constantCoeff]
    simp [coeff_zero_eq_constantCoeff, generating_zero]
  rw [subst_X (.of_constantCoeff_zero hz)] at he
  exact he

private theorem double_map_eq (f g : PowerSeries ℤ)
    (h : f.map (Int.castRingHom (ZMod 2)) = g.map (Int.castRingHom (ZMod 2))) :
    2 * f.map (Int.castRingHom (ZMod 4)) = 2 * g.map (Int.castRingHom (ZMod 4)) := by
  ext n
  have he := congrArg (coeff n) h
  simp only [coeff_map, Int.coe_castRingHom] at he
  have hi := (ZMod.intCast_eq_intCast_iff' (coeff n f) (coeff n g) 2).mp he
  have hm : (2 * coeff n f) % 4 = (2 * coeff n g) % 4 := by omega
  have hc := (ZMod.intCast_eq_intCast_iff' (2 * coeff n f) (2 * coeff n g) 4).mpr hm
  simpa only [← map_ofNat C 2, coeff_C_mul, coeff_map, Int.coe_castRingHom,
    Int.cast_mul, Int.cast_ofNat] using hc

theorem mod_four_identity : generatingSeries.map (Int.castRingHom (ZMod 4)) =
    X + 2 * X *
      Invariants.CatalanCompositionSquareParity.catalanSeries.map (Int.castRingHom (ZMod 4)) := by
  let hom := Int.castRingHom (ZMod 4)
  let K := Invariants.CatalanCompositionSquareParity.catalanSeries
  have hcomp : PowerSeries.map (Int.castRingHom (ZMod 2)) (correction.subst generatingSeries) =
      K.map (Int.castRingHom (ZMod 2)) := by
    have hm : PowerSeries.map (Int.castRingHom (ZMod 2)) (correction.subst generatingSeries) =
        (correction.map (Int.castRingHom (ZMod 2))).subst
          (generatingSeries.map (Int.castRingHom (ZMod 2))) :=
      map_subst (.of_constantCoeff_zero generating_zero) _
    rw [hm, generating_mod_two, X_subst, correction_mod_two]
  have hd := double_map_eq (generatingSeries * correction.subst generatingSeries) (X * K)
    (by simp only [map_mul, generating_mod_two, hcomp, map_X])
  have hA : HasSubst generatingSeries := .of_constantCoeff_zero generating_zero
  have htwo : (2 : PowerSeries ℤ).subst generatingSeries = 2 := by
    rw [← coe_substAlgHom hA]; exact map_ofNat _ 2
  have hone : (1 : PowerSeries ℤ).subst generatingSeries = 1 := by
    rw [← coe_substAlgHom hA]; exact map_one _
  have hi := inverse_left
  rw [inverseSeries, subst_mul hA, subst_X hA, subst_add hA, subst_mul hA, hone, htwo] at hi
  have he := congrArg (PowerSeries.map hom) hi
  simp only [map_mul, map_add, map_one, map_ofNat, map_X] at he hd
  change generatingSeries.map hom = X + 2 * X * K.map hom
  linear_combination he - hd - X * K.map hom * four_zero

theorem hanna_conjecture (n : ℕ) (hn : 1 < n) :
    (a n % 4 = 2 ↔ ∃ k : ℕ, n = 2 ^ k + 1) ∧
    (a n % 4 = 0 ↔ ¬ ∃ k : ℕ, n = 2 ^ k + 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let c := coeff m Invariants.CatalanCompositionSquareParity.catalanSeries
  have hc := congrArg (coeff (m + 1)) mod_four_identity
  have htwo : (2 : PowerSeries (ZMod 4)) = C 2 := (map_ofNat C 2).symm
  rw [map_add, coeff_X, if_neg (by omega : m + 1 ≠ 1), zero_add,
    htwo, mul_assoc, coeff_C_mul, coeff_succ_X_mul] at hc
  change (a (m + 1) : ZMod 4) = 2 * (c : ZMod 4) at hc
  have he : a (m + 1) % 4 = (2 * c) % 4 := by
    apply (ZMod.intCast_eq_intCast_iff' _ _ 4).mp
    simpa only [Int.cast_mul, Int.cast_ofNat] using hc
  have hs : c % 2 = 1 ↔ ∃ k : ℕ, m + 1 = 2 ^ k + 1 := by
    have hb := Invariants.CatalanCompositionSquareParity.binary_catalan m
    change (c : ZMod 2) = 1 ↔ _ at hb
    rw [show (c : ZMod 2) = 1 ↔ c % 2 = 1 from
      ZMod.intCast_eq_intCast_iff' c 1 2] at hb
    simpa only [Nat.add_right_cancel_iff] using hb
  have hb := Int.emod_nonneg c (by omega : (2 : ℤ) ≠ 0)
  have hu := Int.emod_lt_of_pos c (by omega : (0 : ℤ) < 2)
  have hres : (2 * c) % 4 = 2 * (c % 2) := by omega
  simp only [Nat.succ_eq_add_one, ← hs, he, hres]
  constructor <;> omega

#print axioms inverse_equation
#print axioms generating_equation
#print axioms generating_unique
#print axioms mod_four_identity
#print axioms hanna_conjecture

end D5.S1.Recurrence.Parity.QuadraticSquareReversionModFour
