/- GID: D5/S1/Recurrence/Invariants/CatalanShiftSquareModFour
   generality: I
   mirror-B: D5/B/S1/Recurrence/Invariants/CatalanShiftSquareModFour
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Catalan inversion and an integral two-step lift classify Hanna's coefficients mod four. -/

import D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity

open PowerSeries
open D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity
  (catalan_equation binary_catalan)

namespace D5.S1.Recurrence.Invariants.CatalanShiftSquareModFour

local notation "cat" => CatalanCompositionSquareParity.catalanSeries

variable {R : Type*} [CommRing R]

private def Agree (n : ℕ) (f g : PowerSeries R) : Prop :=
  ∀ i < n, coeff i f = coeff i g

private theorem agree_iff (n : ℕ) (f g : PowerSeries R) :
    Agree n f g ↔ (X : PowerSeries R) ^ n ∣ f - g := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem agree_subst {n : ℕ} {f g c : PowerSeries R}
    (hc : constantCoeff c = 0) (h : Agree n f g) :
    Agree n (f.subst c) (g.subst c) := by
  have hs : HasSubst c := .of_constantCoeff_zero hc
  obtain ⟨d, hd⟩ := (agree_iff _ _ _).mp h
  apply (agree_iff _ _ _).mpr
  rw [← subst_sub hs, hd, subst_mul hs, subst_pow hs, subst_X hs]
  exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hc) n) _

private noncomputable def step (c f : PowerSeries R) : PowerSeries R :=
  c + (f.subst c) ^ 2

private theorem step_zero {c f : PowerSeries R}
    (hc : constantCoeff c = 0) (hf : constantCoeff f = 0) :
    constantCoeff (step c f) = 0 := by
  have hz : constantCoeff (f.subst c) = 0 := constantCoeff_subst_eq_zero hc f hf
  simp only [step, map_add, map_pow, hc, hz, zero_pow (by omega : 2 ≠ 0), add_zero]

private theorem step_agree {n : ℕ} {c f g : PowerSeries R}
    (hc : constantCoeff c = 0) (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) (h : Agree n f g) :
    Agree (n + 1) (step c f) (step c g) := by
  have hd := (agree_iff _ _ _).mp (agree_subst hc h)
  have hfz : constantCoeff (f.subst c) = 0 := constantCoeff_subst_eq_zero hc f hf
  have hgz : constantCoeff (g.subst c) = 0 := constantCoeff_subst_eq_zero hc g hg
  have hz : X ∣ f.subst c + g.subst c := X_dvd_iff.mpr (by
    simp only [map_add, hfz, hgz, add_zero])
  apply (agree_iff _ _ _).mpr
  have hm := mul_dvd_mul hd hz
  rw [← pow_succ] at hm
  convert hm using 1
  dsimp [step]
  ring

private theorem fixed_unique {c f g : PowerSeries R}
    (hc : constantCoeff c = 0) (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) (ef : f = step c f) (eg : g = step c g) : f = g := by
  have h : ∀ n, Agree n f g := by
    intro n
    induction n with
    | zero => intro i hi; omega
    | succ n ih => simpa only [← ef, ← eg] using step_agree hc hf hg ih
  ext n
  exact h (n + 1) n (by omega)

private theorem equation_fixed {c f : PowerSeries R}
    (hc : constantCoeff c = 0) (hinv : c - c ^ 2 = X)
    (he : f.subst (X - X ^ 2) = X + f ^ 2) : f = step c f := by
  have hs : HasSubst c := .of_constantCoeff_zero hc
  have hp : HasSubst (X - X ^ 2 : PowerSeries R) := .of_constantCoeff_zero
    (show constantCoeff (X - X ^ 2 : PowerSeries R) = 0 by simp)
  have h := congrArg (fun s : PowerSeries R => s.subst c) he
  rw [subst_comp_subst_apply hp hs, subst_sub hs, subst_pow hs, subst_X hs,
    hinv, X_subst, subst_add hs, subst_X hs, subst_pow hs] at h
  exact h

private theorem catalan_inverse : (cat).subst (X - X ^ 2 : PowerSeries ℤ) = X := by
  let p : PowerSeries ℤ := X - X ^ 2
  have hp0 : constantCoeff p = 0 := by simp [p]
  have hp1 : IsUnit (coeff 1 p) := by simp [p]
  let q := p.substInvOfIsUnit hp1
  have hq0 : constantCoeff q = 0 := constantCoeff_substInvOfIsUnit p hp1
  have hqc : q = cat := by
    apply CatalanCompositionSquareParity.catalan_unique q hq0
    have h := subst_substInvOfIsUnit_right p hp0 hp1
    have hs : HasSubst q := .of_constantCoeff_zero hq0
    change (X - X ^ 2 : PowerSeries ℤ).subst q = X at h
    rw [subst_sub hs, subst_pow hs, subst_X hs] at h
    linear_combination h
  rw [← hqc]
  exact subst_substInvOfIsUnit_left p hp0 hp1

private noncomputable def approximation : ℕ → PowerSeries ℤ
  | 0 => 0
  | n + 1 => step cat (approximation n)

private theorem approximation_zero (n : ℕ) : constantCoeff (approximation n) = 0 := by
  induction n with
  | zero => simp [approximation]
  | succ n ih => exact step_zero catalan_equation.1 ih

private theorem approximation_stable {n m : ℕ} (h : n ≤ m) :
    Agree n (approximation n) (approximation m) := by
  induction n generalizing m with
  | zero => intro i hi; omega
  | succ n ih =>
    cases m with
    | zero => omega
    | succ m =>
      exact step_agree catalan_equation.1
        (approximation_zero n) (approximation_zero m) (ih (by omega))

noncomputable def a (n : ℕ) : ℤ := coeff n (approximation (n + 1))

noncomputable def generatingSeries : PowerSeries ℤ := mk a

private theorem generating_agree (n : ℕ) :
    Agree n generatingSeries (approximation n) := by
  intro i hi
  simpa only [generatingSeries, coeff_mk, a] using
    approximation_stable (by omega : i + 1 ≤ n) i (by omega)

private theorem generating_zero : constantCoeff generatingSeries = 0 := by
  rw [← coeff_zero_eq_constantCoeff, generating_agree 1 0 (by omega),
    coeff_zero_eq_constantCoeff, approximation_zero]

private theorem generating_fixed : generatingSeries = step cat generatingSeries := by
  ext i
  exact (generating_agree (i + 2) i (by omega)).trans
    (step_agree catalan_equation.1 generating_zero (approximation_zero (i + 1))
      (generating_agree (i + 1)) i (by omega)).symm

theorem generating_equation : constantCoeff generatingSeries = 0 ∧
    coeff 1 generatingSeries = 1 ∧
    generatingSeries.subst (X - X ^ 2) = X + generatingSeries ^ 2 := by
  have hz : constantCoeff (generatingSeries.subst cat) = 0 :=
    constantCoeff_subst_eq_zero catalan_equation.1 _ generating_zero
  refine ⟨generating_zero, ?_, ?_⟩
  · have hd := pow_dvd_pow_of_dvd (X_dvd_iff.mpr hz) 2
    have hc := X_pow_dvd_iff.mp hd 1 (by omega)
    calc
      coeff 1 generatingSeries = coeff 1 (step cat generatingSeries) :=
        congrArg (coeff 1) generating_fixed
      _ = 1 := by simp [step, hc, catalan_equation.2.1]
  · have hp : HasSubst (X - X ^ 2 : PowerSeries ℤ) := .of_constantCoeff_zero
      (show constantCoeff (X - X ^ 2 : PowerSeries ℤ) = 0 by simp)
    have h := congrArg (fun s : PowerSeries ℤ => s.subst (X - X ^ 2 : PowerSeries ℤ))
      generating_fixed
    simpa only [step, subst_add hp, subst_pow hp,
      subst_comp_subst_apply (.of_constantCoeff_zero catalan_equation.1) hp,
      catalan_inverse, X_subst] using h

theorem generating_unique (f : PowerSeries ℤ) (h0 : constantCoeff f = 0)
    (hf : f.subst (X - X ^ 2) = X + f ^ 2) : f = generatingSeries := by
  apply fixed_unique catalan_equation.1 h0 generating_zero
    (equation_fixed catalan_equation.1 (by linear_combination catalan_equation.2.2) hf)
    generating_fixed

private theorem map_equation {S : Type*} [CommRing S] (hom : R →+* S)
    {f : PowerSeries R} (he : f.subst (X - X ^ 2) = X + f ^ 2) :
    (f.map hom).subst (X - X ^ 2) = X + (f.map hom) ^ 2 := by
  have hp : HasSubst (X - X ^ 2 : PowerSeries R) := .of_constantCoeff_zero
    (show constantCoeff (X - X ^ 2 : PowerSeries R) = 0 by simp)
  have h := congrArg (PowerSeries.map hom) he
  have hm : (f.subst (X - X ^ 2)).map hom =
      (f.map hom).subst ((X - X ^ 2 : PowerSeries R).map hom) := map_subst hp f
  simpa using hm.symm.trans h

private noncomputable def binaryCatalan : PowerSeries (ZMod 2) :=
  (cat).map (Int.castRingHom (ZMod 2))

private theorem binary_catalan_zero : constantCoeff binaryCatalan = 0 := by
  rw [← coeff_zero_eq_constantCoeff]
  simp only [binaryCatalan, coeff_map, coeff_zero_eq_constantCoeff, catalan_equation.1,
    map_zero]

private theorem binary_catalan_equation : binaryCatalan = X + binaryCatalan ^ 2 := by
  simpa [binaryCatalan] using
    congrArg (PowerSeries.map (Int.castRingHom (ZMod 2))) catalan_equation.2.2

private theorem binary_catalan_inverse : binaryCatalan - binaryCatalan ^ 2 = X := by
  linear_combination binary_catalan_equation

private theorem two_zero : (2 : PowerSeries (ZMod 2)) = 0 := by
  simpa only [map_ofNat, map_zero] using
    congrArg (C (R := ZMod 2)) (CharP.ofNat_eq_zero (ZMod 2) 2)

theorem mod_two_identity : generatingSeries.map (Int.castRingHom (ZMod 2)) = X := by
  let f := generatingSeries.map (Int.castRingHom (ZMod 2))
  have hf0 : constantCoeff f = 0 := by
    rw [← coeff_zero_eq_constantCoeff]
    simp only [f, coeff_map, coeff_zero_eq_constantCoeff, generating_zero, map_zero]
  have hf : f = step binaryCatalan f := equation_fixed binary_catalan_zero
    binary_catalan_inverse (map_equation _ generating_equation.2.2)
  have hx : (X : PowerSeries (ZMod 2)) = step binaryCatalan X := by
    apply equation_fixed binary_catalan_zero binary_catalan_inverse
    have hp : HasSubst (X - X ^ 2 : PowerSeries (ZMod 2)) := .of_constantCoeff_zero
      (show constantCoeff (X - X ^ 2 : PowerSeries (ZMod 2)) = 0 by simp)
    rw [subst_X hp]
    linear_combination -X ^ 2 * two_zero
  by_contra hne
  have hex : ∃ n, coeff n f ≠ coeff n (X : PowerSeries (ZMod 2)) := by
    by_contra he
    apply hne
    ext n
    by_contra hn
    exact he ⟨n, hn⟩
  have hagree : Agree (Nat.find hex) f X := by
    intro i hi
    exact not_not.mp (Nat.find_min hex hi)
  have hnext := step_agree binary_catalan_zero hf0 (by simp) hagree
    (Nat.find hex) (Nat.lt_succ_self _)
  apply Nat.find_spec hex
  simpa only [← hf, ← hx] using hnext

private noncomputable def halfSeries : PowerSeries ℤ :=
  mk (fun n => coeff n (generatingSeries - X) / 2)

private theorem integral_lift : generatingSeries = X + C (2 : ℤ) * halfSeries := by
  have hz : (generatingSeries - X).map (Int.castRingHom (ZMod 2)) = 0 := by
    simp only [map_sub, mod_two_identity, map_X, sub_self]
  ext n
  have hc : ((coeff n (generatingSeries - X) : ℤ) : ZMod 2) = 0 := by
    simpa only [coeff_map, map_zero, Int.coe_castRingHom] using congrArg (coeff n) hz
  have hd : (2 : ℤ) ∣ coeff n (generatingSeries - X) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hc
  have hdiv := Int.mul_ediv_cancel' hd
  simp only [map_add, coeff_C_mul, halfSeries, coeff_mk]
  rw [hdiv, map_sub]
  ring

-- Dividing the exact integer identity retains the factor two in the quadratic terms.
private theorem half_equation : halfSeries.subst (X - X ^ 2) =
    X ^ 2 + 2 * X * halfSeries + 2 * halfSeries ^ 2 := by
  have hp : HasSubst (X - X ^ 2 : PowerSeries ℤ) := .of_constantCoeff_zero
    (show constantCoeff (X - X ^ 2 : PowerSeries ℤ) = 0 by simp)
  have h := generating_equation.2.2
  rw [integral_lift, subst_add hp, subst_mul hp, subst_C, subst_X hp] at h
  simp only [map_ofNat] at h
  apply mul_left_cancel₀ (show (2 : PowerSeries ℤ) ≠ 0 by
    intro he
    have hc := congrArg constantCoeff he
    norm_num only [map_ofNat, map_zero] at hc)
  linear_combination h

private theorem half_mod_two : halfSeries.map (Int.castRingHom (ZMod 2)) =
    binaryCatalan ^ 2 := by
  let hom := Int.castRingHom (ZMod 2)
  have hp : HasSubst (X - X ^ 2 : PowerSeries ℤ) := .of_constantCoeff_zero
    (show constantCoeff (X - X ^ 2 : PowerSeries ℤ) = 0 by simp)
  have he : (halfSeries.map hom).subst (X - X ^ 2 : PowerSeries (ZMod 2)) = X ^ 2 := by
    have h := congrArg (PowerSeries.map hom) half_equation
    have hm : (halfSeries.subst (X - X ^ 2)).map hom =
        (halfSeries.map hom).subst ((X - X ^ 2 : PowerSeries ℤ).map hom) :=
      map_subst hp halfSeries
    simpa only [map_sub, map_X, map_pow, map_add, map_mul, map_ofNat,
      two_zero, zero_mul, add_zero] using hm.symm.trans h
  have hs : HasSubst binaryCatalan := .of_constantCoeff_zero binary_catalan_zero
  have hp2 : HasSubst (X - X ^ 2 : PowerSeries (ZMod 2)) := .of_constantCoeff_zero
    (show constantCoeff (X - X ^ 2 : PowerSeries (ZMod 2)) = 0 by simp)
  have h := congrArg (fun s : PowerSeries (ZMod 2) => s.subst binaryCatalan) he
  rw [subst_comp_subst_apply hp2 hs, subst_sub hs, subst_pow hs, subst_X hs,
    binary_catalan_inverse, X_subst] at h
  exact h

theorem hanna_conjecture (n : ℕ) (hn : 1 < n) :
    (a n % 4 = 2 ↔ ∃ k : ℕ, n = 2 ^ k) ∧
    (a n % 4 = 0 ↔ ¬ ∃ k : ℕ, n = 2 ^ k) := by
  have hn1 : n ≠ 1 := by omega
  have ha : a n = 2 * coeff n halfSeries := by
    have h := congrArg (coeff n) integral_lift
    simpa only [generatingSeries, coeff_mk, map_add, coeff_X, if_neg hn1,
      zero_add, coeff_C_mul] using h
  have hh : ((coeff n halfSeries : ℤ) : ZMod 2) = coeff n binaryCatalan := by
    have h := congrArg (coeff n) half_mod_two
    have hc := congrArg (coeff n) binary_catalan_equation
    simp only [map_add, coeff_X, if_neg hn1, zero_add] at hc
    simpa only [coeff_map, Int.coe_castRingHom, ← hc] using h
  have hb : coeff n halfSeries % 2 = 1 ↔ ∃ k : ℕ, n = 2 ^ k := by
    have hcast : ((coeff n halfSeries : ℤ) : ZMod 2) = 1 ↔ coeff n halfSeries % 2 = 1 := by
      simpa using (ZMod.intCast_eq_intCast_iff' (coeff n halfSeries) 1 2)
    rw [← hcast, hh]
    exact binary_catalan n
  constructor
  · constructor
    · intro h
      apply hb.mp
      omega
    · intro h
      have := hb.mpr h
      omega
  · constructor
    · intro h hp
      have := hb.mpr hp
      omega
    · intro h
      have hbnot : coeff n halfSeries % 2 ≠ 1 := fun he => h (hb.mp he)
      omega

#print axioms generating_equation
#print axioms generating_unique
#print axioms mod_two_identity
#print axioms hanna_conjecture

end D5.S1.Recurrence.Invariants.CatalanShiftSquareModFour
