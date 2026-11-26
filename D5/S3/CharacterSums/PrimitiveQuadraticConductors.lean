/- GID: D5/S3/CharacterSums/PrimitiveQuadraticConductors
   generality: I
   mirror-B: D5/B/S3/CharacterSums/PrimitiveQuadraticConductors
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Primitive quadratic conductors and uniqueness of all inducing coefficients. -/

import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import D5.S3.Analytic.Zeta.MercaImaginaryCharacter

/-! Native characters for two odd prime factors and the quadratic character of level eight. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open DirichletCharacter
open D5.S3.Analytic.Zeta
open D5.S3.Analytic.Zeta.PrimeQuadraticLValues

namespace D5.S3.CharacterSums.PrimitiveQuadraticConductors

private def join {a b : ℕ} (χ : DirichletCharacter ℂ a) (ψ : DirichletCharacter ℂ b) :
    DirichletCharacter ℂ (a*b) :=
  changeLevel (dvd_mul_right a b) χ * changeLevel (dvd_mul_left b a) ψ

private theorem primitive_join {a b : ℕ} [NeZero (a * b)]
    (χ : DirichletCharacter ℂ a) (ψ : DirichletCharacter ℂ b)
    (hc : a.Coprime b) (hp : χ.IsPrimitive) (hq : ψ.IsPrimitive) : (join χ ψ).IsPrimitive := by
  change (join χ ψ).conductor = a*b
  have h1 := conductor_changeLevel χ (dvd_mul_right a b)
  have h2 := conductor_changeLevel ψ (dvd_mul_left b a)
  change χ.conductor = a at hp
  change ψ.conductor = b at hq
  unfold join
  rw [MercaImaginaryCharacter.conductor_mul_coprime _ _ (by rwa [h1,h2,hp,hq]),h1,h2,hp,hq]

private theorem join_apply {a b : ℕ}
    (χ : DirichletCharacter ℂ a) (ψ : DirichletCharacter ℂ b) (n : ℕ) :
    join χ ψ (n:ZMod (a*b)) = χ (n:ZMod a)*ψ (n:ZMod b) := by
  by_cases h : n.Coprime (a*b)
  · have hi : IsCoprime (n:ℤ) (a*b:ℕ) := by exact_mod_cast (Nat.isCoprime_iff_coprime.mpr h)
    have ha := changeLevel_eq_cast_of_dvd' χ (dvd_mul_right a b) hi
    have hb := changeLevel_eq_cast_of_dvd' ψ (dvd_mul_left b a) hi
    simp only [Int.cast_natCast] at ha hb
    exact congrArg₂ (·*·) ha hb
  · rw [(join χ ψ).map_nonunit (fun hu => h ((ZMod.isUnit_iff_coprime _ _).mp hu))]
    rw [Nat.coprime_mul_iff_right,not_and_or] at h
    rcases h with ha|hb
    · rw [χ.map_nonunit (fun hu => ha ((ZMod.isUnit_iff_coprime _ _).mp hu)),zero_mul]
    · rw [ψ.map_nonunit (fun hu => hb ((ZMod.isUnit_iff_coprime _ _).mp hu)),mul_zero]

private theorem primeChar_value (p n : ℕ) [Fact p.Prime] :
    primeCharacter p (n:ZMod p) = (jacobiSym (n:ℤ) p:ℂ) := by
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  simp [primeCharacter,legendreSym]

private def eightChar : DirichletCharacter ℂ 8 := ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)

private theorem primitive_eightChar : eightChar.IsPrimitive := by
  change eightChar.conductor = 8
  by_contra hc
  have hd := eightChar.conductor_dvd_level
  have h4 : eightChar.conductor ∣ 4 := by
    have := Nat.le_of_dvd (by decide : 0 < 8) hd
    generalize hn : eightChar.conductor = n at *
    interval_cases n <;> norm_num at *
  obtain ⟨h48,χ,hχ⟩ := eightChar.factorsThrough_conductor.mono eightChar h4 (by decide : 4 ∣ 8)
  have h5 := changeLevel_eq_cast_of_dvd' χ h48 (a := 5) (by exact ⟨-3, 2, by norm_num⟩)
  rw [← hχ] at h5
  have val5 : eightChar (5:ZMod 8) = -1 := by
    change ((ZMod.χ₈ (5:ZMod 8):ℤ):ℂ) = -1
    rw [show ZMod.χ₈ (5:ZMod 8) = -1 by decide];norm_num
  norm_num only [Int.cast_ofNat] at h5
  rw [val5,show (5:ZMod 4)=1 by decide,map_one] at h5
  norm_num at h5

/-- A primitive character of the stated level represents the coefficient on every natural input. -/
def represents {R : Type*} [CommMonoidWithZero R] (a : ℕ) (f : ℕ → R) : Prop :=
  ∃ χ : DirichletCharacter R a, χ.IsPrimitive ∧ ∀ n : ℕ, χ (n:ZMod a) = f n

private theorem represents_join {a b : ℕ} [NeZero (a * b)] {f g : ℕ → ℂ} (hab : a.Coprime b)
    (hf : represents a f) (hg : represents b g) : represents (a*b) (fun n => f n*g n) := by
  obtain ⟨χ,hχ,ef⟩ := hf
  obtain ⟨ψ,hψ,eg⟩ := hg
  exact ⟨join χ ψ,primitive_join χ ψ hab hχ hψ,fun n => by rw [join_apply,ef,eg]⟩

/-- Primitive native representatives at all six conductor levels, on every natural input. -/
theorem six_quadratic_levels (q d : ℕ) (hq : q.Prime) (hd : d.Prime)
    (hq2 : q ≠ 2) (hd2 : d ≠ 2) (hqd : q ≠ d) :
    let j (p n : ℕ) : ℂ := (jacobiSym (n:ℤ) p:ℂ)
    let e (n : ℕ) : ℂ := (ZMod.χ₈ (n:ZMod 8):ℤ)
    represents q (j q) ∧ represents (8*q) (fun n => e n*j q n) ∧
    represents d (j d) ∧ represents (8*d) (fun n => e n*j d n) ∧
    represents (q*d) (fun n => j q n*j d n) ∧
    represents (8*(q*d)) (fun n => e n*(j q n*j d n)) := by
  intro j e
  let _ : Fact q.Prime := ⟨hq⟩
  let _ : Fact d.Prime := ⟨hd⟩
  have hq8 : Nat.Coprime 8 q := by
    have h := ((Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2)).pow_left 3
    exact h
  have hd8 : Nat.Coprime 8 d := by
    have h := ((Nat.coprime_primes Nat.prime_two hd).mpr (Ne.symm hd2)).pow_left 3
    exact h
  have rep8 : represents 8 e := ⟨eightChar,primitive_eightChar,fun _ => rfl⟩
  have repQ : represents q (j q) :=
    ⟨primeCharacter q, primeCharacter_primitive q hq2, fun n => primeChar_value q n⟩
  have repD : represents d (j d) :=
    ⟨primeCharacter d, primeCharacter_primitive d hd2, fun n => primeChar_value d n⟩
  have repQD := represents_join ((Nat.coprime_primes hq hd).mpr hqd) repQ repD
  exact ⟨repQ,represents_join hq8 rep8 repQ,repD,represents_join hd8 rep8 repD,repQD,
    represents_join (hq8.mul_right hd8) rep8 repQD⟩

/-- Agreement off an arbitrary positive modulus determines the native level and all values. -/
theorem inducing_level_and_values {R : Type*} [CommMonoidWithZero R]
    {r a M : ℕ} [NeZero r] [NeZero a] [NeZero M]
    (χ : DirichletCharacter R r) (hχ : χ.IsPrimitive) {f : ℕ → R} (ha : represents a f)
    (hi : ∀ n : ℕ, n.Coprime M → χ (n:ZMod r) = f n) :
    r=a ∧ ∀ n : ℕ, χ (n:ZMod r) = f n := by
  obtain ⟨ψ,hψ,hv⟩ := ha
  let k := r*a*M
  have ha : r ∣ k := (dvd_mul_right r a).trans (dvd_mul_right _ M)
  have hb : a ∣ k := (dvd_mul_left a r).trans (dvd_mul_right _ M)
  have hM : M ∣ k := dvd_mul_left M _
  let _ : NeZero k :=
    ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne a)) (NeZero.ne M)⟩
  have eqLift : changeLevel ha χ = changeLevel hb ψ := by
    apply MulChar.ext
    intro u
    let n := (u:ZMod k).val
    have hn : n.Coprime k := ZMod.val_coe_unit_coprime u
    have hunit : IsCoprime (n:ℤ) (k:ℤ) := by exact_mod_cast Nat.isCoprime_iff_coprime.mpr hn
    have e1 := changeLevel_eq_cast_of_dvd' χ ha hunit
    have e2 := changeLevel_eq_cast_of_dvd' ψ hb hunit
    simp only [Int.cast_natCast] at e1 e2
    rw [show (u:ZMod k) = (n:ZMod k) from (ZMod.natCast_zmod_val _).symm,e1,e2]
    exact (hi n (hn.of_dvd_right hM)).trans (hv n).symm
  have e := congrArg DirichletCharacter.conductor eqLift
  rw [conductor_changeLevel,conductor_changeLevel,hχ,hψ] at e
  subst a
  have ef : χ=ψ := changeLevel_injective ha eqLift
  refine ⟨rfl, fun n => ?_⟩
  exact (congrArg (fun f : DirichletCharacter R r => f (n:ZMod r)) ef).trans (hv n)

end D5.S3.CharacterSums.PrimitiveQuadraticConductors
