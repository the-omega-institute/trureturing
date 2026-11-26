/- GID: D5/S3/Arith/CharacterSums/PascadiResonantRectangleEnergy
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiResonantRectangleEnergy
   mirror-E: none(waiver:open-short-frequency-concentration)
   anchors: []
   utility: none
   digest: The complete normalized dual energy of a literal resonant box is at most 9pA². -/

import D5.S3.Arith.CharacterSums.PascadiDualPivotOrthogonality
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! The complete-frequency norm uses integer pivot bounds, not a truncated frequency norm. -/

open scoped BigOperators

namespace D5.S3.Arith.CharacterSums.PascadiResonantRectangleEnergy

open Finset PascadiDualPivotOrthogonality

noncomputable section

variable {p : ℕ} [Fact p.Prime] [NeZero (p ^ 2)]

private abbrev reducePrime : ZMod (p ^ 2) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by decide : (2 : ℕ) ≠ 0)) (ZMod p)

private def high (x : ZMod (p ^ 2)) : Fin p :=
  ⟨x.val / p, (Nat.div_lt_iff_lt_mul (Fact.out : p.Prime).pos).mpr
    (by simpa [pow_two] using x.val_lt)⟩

private lemma val_reduce (x : ZMod (p ^ 2)) : (reducePrime x).val = x.val % p := by
  rw [← ZMod.natCast_zmod_val x]
  simp only [map_natCast, ZMod.val_natCast]
  exact (Nat.mod_mod_of_dvd _ (dvd_pow_self p (by decide : (2 : ℕ) ≠ 0))).symm

private lemma eq_of_reduce_high {x y : ZMod (p ^ 2)}
    (h₁ : reducePrime x = reducePrime y) (h₂ : high x = high y) : x = y := by
  apply ZMod.val_injective
  have h := congrArg ZMod.val h₁
  simp only [val_reduce] at h
  have hh : x.val / p = y.val / p := congrArg Fin.val h₂
  calc
    x.val = x.val % p + p * (x.val / p) := (Nat.mod_add_div _ _).symm
    _ = y.val % p + p * (y.val / p) := by rw [h, hh]
    _ = y.val := Nat.mod_add_div _ _

private lemma isUnit_of_reduce_ne {x : ZMod (p ^ 2)} (hx : reducePrime x ≠ 0) :
    IsUnit x := by
  have h : (x.val : ZMod p) ≠ 0 := by
    rw [← map_natCast (reducePrime (p := p)), ZMod.natCast_zmod_val]
    exact hx
  rw [← ZMod.natCast_zmod_val x]
  exact (ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) (by decide)).2
    (fun hd => h ((ZMod.natCast_eq_zero_iff _ _).2 hd))

private lemma smooth_fiber_injective {h x y t : ZMod (p ^ 2)}
    (hx : IsUnit x) (hy : reducePrime y = reducePrime t)
    (hsm : reducePrime h - reducePrime x - 2 * reducePrime y ≠ 0)
    (heq : x * y * (h - x - y) = x * t * (h - x - t)) : y = t := by
  have hund : IsUnit (h - x - y - t) := isUnit_of_reduce_ne (by
    simp only [map_sub, ← hy]
    rwa [sub_sub (reducePrime h - reducePrime x), ← two_mul])
  have he : (x * (h - x - y - t)) * (y - t) = 0 := by linear_combination heq
  exact sub_eq_zero.mp ((hx.mul hund).mul_left_cancel (by simpa only [mul_zero] using he))

private lemma full_digit_bound (T : Finset (ZMod (p ^ 2) × ZMod (p ^ 2)))
    (b : ZMod p × ZMod p)
    (hb : ∀ z ∈ T, (reducePrime z.1, reducePrime z.2) = b) : T.card ≤ p ^ 2 := by
  let f (z : ZMod (p ^ 2) × ZMod (p ^ 2)) : Fin p × Fin p := (high z.1, high z.2)
  have h : Set.InjOn f T := by
    intro x hx y hy he
    have hxy := (hb x hx).trans (hb y hy).symm
    exact Prod.ext
      (eq_of_reduce_high (congrArg Prod.fst hxy) (congrArg Prod.fst he))
      (eq_of_reduce_high (congrArg Prod.snd hxy) (congrArg Prod.snd he))
  simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using
      (Finset.card_le_card_of_injOn (t := Finset.univ) f (fun _ _ => Finset.mem_univ _) h).trans_eq
        Finset.card_univ

private lemma smooth_digit_bound (T : Finset (ZMod (p ^ 2) × ZMod (p ^ 2)))
    (h v : ZMod (p ^ 2)) (b : ZMod p × ZMod p)
    (hb : ∀ z ∈ T, (reducePrime z.1, reducePrime z.2) = b)
    (hu : ∀ z ∈ T, IsUnit z.1 ∧ IsUnit z.2)
    (hc : ∀ z ∈ T, z.1 * z.2 * (h - z.1 - z.2) = v)
    (hs : b.2 * (reducePrime h - 2 * b.1 - b.2) ≠ 0 ∨
          b.1 * (reducePrime h - b.1 - 2 * b.2) ≠ 0) : T.card ≤ p := by
  rcases hs with hs|hs
  · let f (z : ZMod (p ^ 2) × ZMod (p ^ 2)) : Fin p := high z.2
    have h : Set.InjOn f T := by
      intro x hx y hy he
      have hxy := (hb x hx).trans (hb y hy).symm
      have hyxy := eq_of_reduce_high (congrArg Prod.snd hxy) he
      have hsm : reducePrime h - reducePrime x.2 - 2 * reducePrime x.1 ≠ 0 := by
        rw [show reducePrime x.2 = b.2 from congrArg Prod.snd (hb x hx),
          show reducePrime x.1 = b.1 from congrArg Prod.fst (hb x hx)]
        intro hzero
        apply hs
        rw [show reducePrime h - 2 * b.1 - b.2 = reducePrime h - b.2 - 2 * b.1 by ring,
          hzero, mul_zero]
      have hcurve := (hc x hx).trans (hc y hy).symm
      rw [← hyxy] at hcurve
      have hcurve' : x.2 * x.1 * (h - x.2 - x.1) = x.2 * y.1 * (h - x.2 - y.1) := by
        linear_combination hcurve
      exact Prod.ext (smooth_fiber_injective (hu x hx).2 (congrArg Prod.fst hxy) hsm hcurve') hyxy
    simpa only [Fintype.card_fin] using
      (Finset.card_le_card_of_injOn (t := Finset.univ) f (fun _ _ => Finset.mem_univ _) h).trans_eq
        Finset.card_univ
  · let f (z : ZMod (p ^ 2) × ZMod (p ^ 2)) : Fin p := high z.1
    have h : Set.InjOn f T := by
      intro x hx y hy he
      have hxy := (hb x hx).trans (hb y hy).symm
      have hxxy := eq_of_reduce_high (congrArg Prod.fst hxy) he
      have hsm : reducePrime h - reducePrime x.1 - 2 * reducePrime x.2 ≠ 0 := by
        rw [show reducePrime x.1 = b.1 from congrArg Prod.fst (hb x hx),
          show reducePrime x.2 = b.2 from congrArg Prod.snd (hb x hx)]
        intro hzero
        exact hs (by rw [hzero, mul_zero])
      have hcurve := (hc x hx).trans (hc y hy).symm
      rw [← hxxy] at hcurve
      exact Prod.ext hxxy (smooth_fiber_injective (hu x hx).1 (congrArg Prod.snd hxy) hsm hcurve)
    simpa only [Fintype.card_fin] using
      (Finset.card_le_card_of_injOn (t := Finset.univ) f (fun _ _ => Finset.mem_univ _) h).trans_eq
        Finset.card_univ

private theorem reduced_cubic_card {p : ℕ} [Fact p.Prime]
    (h v : ZMod p) (T : Finset (ZMod p × ZMod p))
    (hT : ∀ z ∈ T, z.1 ≠ 0 ∧ z.1 * z.2 * (h - z.1 - z.2) = v) :
    T.card ≤ 2 * p := by
  classical
  rw [Finset.card_eq_sum_card_image Prod.fst T]
  have hf : ∀ x ∈ T.image Prod.fst, (T.filter (fun z => z.1 = x)).card ≤ 2 := by
    intro x hx
    obtain ⟨z₀, hz₀, hz₀x⟩ := Finset.mem_image.mp hx
    have hx0 : x ≠ 0 := hz₀x ▸ (hT z₀ hz₀).1
    let P : Polynomial (ZMod p) :=
      Polynomial.X ^ 2 - Polynomial.C (h-x) * Polynomial.X + Polynomial.C (v/x)
    have hp0 : P ≠ 0 := by
      intro H
      have H' := congrArg (fun Q : Polynomial (ZMod p) => Q.coeff 2) H
      simp [P, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow] at H'
    have hd1 : (Polynomial.C (h-x) * Polynomial.X).natDegree ≤ 2 := by
      exact (Polynomial.natDegree_mul_le_of_le (by simp : (Polynomial.C (h-x)).natDegree ≤ 0)
        (by simp : (Polynomial.X : Polynomial (ZMod p)).natDegree ≤ 1)).trans (by decide)
    have hd2 : P.natDegree ≤ 2 := by
      unfold P
      apply Polynomial.natDegree_add_le_of_degree_le
      · exact (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp) hd1)
      · simp
    have hm : ∀ z ∈ T.filter (fun z => z.1 = x), z.2 ∈ P.roots.toFinset := by
      intro z hz
      obtain ⟨hzT, hzx⟩ := Finset.mem_filter.mp hz
      have he := (hT z hzT).2
      rw [hzx] at he
      have he' : v / x = z.2 * (h-x-z.2) := by
        apply (div_eq_iff hx0).2
        linear_combination -he
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0]
      change P.eval z.2 = 0
      simp only [P, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
      rw [he']
      ring
    have hi : Set.InjOn Prod.snd (↑(T.filter (fun z => z.1 = x)) : Set (ZMod p × ZMod p)) := by
      intro a ha b hb he
      exact Prod.ext
        ((Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2.trans
          (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2.symm) he
    exact ((Finset.card_le_card_of_injOn _ hm hi).trans
      ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _))).trans hd2
  calc
    _ ≤ ∑ x ∈ T.image Prod.fst, 2 := Finset.sum_le_sum hf
    _ = 2 * (T.image Prod.fst).card := by simp [mul_comm]
    _ ≤ 2 * p := by
      apply Nat.mul_le_mul_left
      simpa only [ZMod.card] using (Finset.card_le_univ (T.image Prod.fst))

private theorem reduced_singular_card {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (h : ZMod p) (T : Finset (ZMod p × ZMod p))
    (hT : ∀ z ∈ T, z.1 ≠ 0 ∧ z.2 ≠ 0) :
    (T.filter (fun z => z.2*(h-2*z.1-z.2)=0 ∧ z.1*(h-z.1-2*z.2)=0)).card ≤ 1 := by
  classical
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro H
    have hdp : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp (by exact H)
    exact (not_le_of_gt hp) (Nat.le_of_dvd (by decide) hdp)
  have hsub : T.filter (fun z => z.2*(h-2*z.1-z.2)=0 ∧ z.1*(h-z.1-2*z.2)=0) ⊆
      {(h/3,h/3)} := by
    intro z hz
    obtain ⟨hzT,hx,hy⟩ := Finset.mem_filter.mp hz
    have hx' := (mul_eq_zero.mp hx).resolve_left (hT z hzT).2
    have hy' := (mul_eq_zero.mp hy).resolve_left (hT z hzT).1
    apply Finset.mem_singleton.mpr
    apply Prod.ext
    · apply (eq_div_iff h3).2
      linear_combination -2*hx' + hy'
    · apply (eq_div_iff h3).2
      linear_combination hx' - 2*hy'
  exact (Finset.card_le_card hsub).trans (by simp)

private lemma prime_square_cubic_card (hp : 3 < p)
    (h v : ZMod (p ^ 2)) (T : Finset (ZMod (p ^ 2) × ZMod (p ^ 2)))
    (hu : ∀ z ∈ T, IsUnit z.1 ∧ IsUnit z.2)
    (hc : ∀ z ∈ T, z.1 * z.2 * (h - z.1 - z.2) = v) : T.card ≤ 3 * p ^ 2 := by
  classical
  let ρ (z : ZMod (p ^ 2) × ZMod (p ^ 2)) := (reducePrime z.1, reducePrime z.2)
  let U := T.image ρ
  let sing (b : ZMod p × ZMod p) :=
    b.2 * (reducePrime h - 2 * b.1 - b.2) = 0 ∧
    b.1 * (reducePrime h - b.1 - 2 * b.2) = 0
  have hU : ∀ b ∈ U, b.1 ≠ 0 ∧ b.2 ≠ 0 ∧
      b.1 * b.2 * (reducePrime h - b.1 - b.2) = reducePrime v := by
    intro b hb
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hb
    refine ⟨((hu z hz).1.map reducePrime).ne_zero, ((hu z hz).2.map reducePrime).ne_zero, ?_⟩
    simpa only [ρ, map_mul, map_sub] using congrArg reducePrime (hc z hz)
  have hUcard : U.card ≤ 2 * p :=
    reduced_cubic_card _ _ U fun b hb => ⟨(hU b hb).1, (hU b hb).2.2⟩
  have hScard : (U.filter sing).card ≤ 1 :=
    reduced_singular_card hp _ U fun b hb => ⟨(hU b hb).1, (hU b hb).2.1⟩
  have hf (b : ZMod p × ZMod p) :
      (T.filter (fun z => ρ z = b)).card ≤ p + if sing b then p ^ 2 else 0 := by
    let V := T.filter fun z => ρ z = b
    have hv (z) (hz : z ∈ V) : z ∈ T ∧ ρ z = b := Finset.mem_filter.mp hz
    by_cases hs : sing b
    · rw [ite_eq_left hs]
      exact (full_digit_bound V b fun z hz => (hv z hz).2).trans (Nat.le_add_left _ _)
    · rw [ite_eq_right hs, add_zero]
      apply smooth_digit_bound V h v b (fun z hz => (hv z hz).2)
        (fun z hz => hu z (hv z hz).1) (fun z hz => hc z (hv z hz).1)
      exact not_and_or.mp hs
  calc
    T.card = ∑ b ∈ U, (T.filter (fun z => ρ z = b)).card :=
      Finset.card_eq_sum_card_image ρ T
    _ ≤ ∑ b ∈ U, (p + if sing b then p ^ 2 else 0) := Finset.sum_le_sum fun b _ => hf b
    _ = U.card * p + (U.filter sing).card * p ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter]
      simp
    _ ≤ (2 * p) * p + 1 * p ^ 2 := by
      exact Nat.add_le_add (Nat.mul_le_mul_right _ hUcard) (Nat.mul_le_mul_right _ hScard)
    _ = 3 * p ^ 2 := by ring

omit [NeZero (p ^ 2)] in
private lemma primitive_reduction (r s : ℤ) (h : IsCoprime r s) :
    (r : ZMod p) ≠ 0 ∨ (s : ZMod p) ≠ 0 := by
  obtain ⟨a, b, hab⟩ := h
  have hab' : (a : ZMod p) * r + (b : ZMod p) * s = 1 := by
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_one] using
      congrArg (fun x : ℤ => (x : ZMod p)) hab
  by_contra! hzero
  rw [hzero.1, hzero.2, mul_zero, mul_zero, add_zero] at hab'
  exact zero_ne_one hab'

omit [NeZero (p ^ 2)] in
private lemma resonance_first_dvd (r s ρ σ a b : ℤ)
    (hpiv : r * ρ + s * σ = p) (hprim : IsCoprime r s)
    (hres : (p : ℤ) ∣ s * a - r * b) :
    (p : ℤ) ∣ ρ * a + σ * b := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hres ⊢
  push_cast at hres ⊢
  have hh : (r : ZMod p) * ρ + (s : ZMod p) * σ = 0 := by
    have h := congrArg (fun x : ℤ => (x : ZMod p)) hpiv
    simpa using h
  rcases primitive_reduction (p := p) r s hprim with hr|hs
  · apply mul_left_cancel₀ hr
    rw [mul_zero]
    linear_combination (a : ZMod p) * hh - (σ : ZMod p) * hres
  · apply mul_left_cancel₀ hs
    rw [mul_zero]
    linear_combination (b : ZMod p) * hh + (ρ : ZMod p) * hres

omit [NeZero (p ^ 2)] in
private lemma resonance_recovers (r s ρ σ a b : ℤ)
    (hpiv : r * ρ + s * σ = p) (hprim : IsCoprime r s)
    (hres : (p : ℤ) ∣ s * a - r * b) :
    r * ((ρ*a + σ*b) / (p : ℤ)) + σ * ((s*a-r*b) / (p : ℤ)) = a ∧
    s * ((ρ*a + σ*b) / (p : ℤ)) - ρ * ((s*a-r*b) / (p : ℤ)) = b := by
  have hs : ((ρ*a + σ*b) / (p : ℤ)) * (p : ℤ) = ρ*a + σ*b :=
    Int.ediv_mul_cancel (resonance_first_dvd r s ρ σ a b hpiv hprim hres)
  have ht : ((s*a-r*b) / (p : ℤ)) * (p : ℤ) = s*a-r*b := Int.ediv_mul_cancel hres
  have hn : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  constructor
  · apply mul_right_cancel₀ hn
    linear_combination r * hs + σ * ht + a * hpiv
  · apply mul_right_cancel₀ hn
    linear_combination s * hs - ρ * ht + b * hpiv

private theorem resonant_card_left {p A : ℕ} [Fact p.Prime]
    (hpA : p ≤ A) (S : Finset (ℤ × ℤ)) (L M : ℤ)
    (s r : ZMod p) (hr : r ≠ 0)
    (hbox : ∀ x ∈ S, L ≤ x.1 ∧ x.1 < L + A ∧ M ≤ x.2 ∧ x.2 < M + A)
    (hres : ∀ x ∈ S, s * (x.1 : ZMod p) = r * (x.2 : ZMod p)) :
    S.card * p ≤ 2 * A ^ 2 := by
  classical
  let code (x : ℤ × ℤ) := ((x.1 - L).toNat, (x.2 - M).toNat / p)
  have hcard : S.card ≤ ((range A) ×ˢ range (A / p + 1)).card := by
    apply Finset.card_le_card_of_injOn code
    · intro x hx
      obtain ⟨hx₁, hx₂, hx₃, hx₄⟩ := hbox x hx
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range, code]
      have h₁ : (x.1 - L).toNat < A := by omega
      have h₂ : (x.2 - M).toNat ≤ A := by omega
      exact ⟨h₁, Nat.lt_succ_of_le (Nat.div_le_div_right h₂)⟩
    · intro x hx y hy he
      have h₁ : (x.1 - L).toNat = (y.1 - L).toNat := congrArg Prod.fst he
      have h₂ : (x.2 - M).toNat / p = (y.2 - M).toNat / p := congrArg Prod.snd he
      obtain ⟨hx₁, _, hx₂, _⟩ := hbox x hx
      obtain ⟨hy₁, _, hy₂, _⟩ := hbox y hy
      have hxy₁ : x.1 = y.1 := by omega
      have hun : (x.2 : ZMod p) = (y.2 : ZMod p) := by
        apply mul_left_cancel₀ hr
        rw [← hres x hx, ← hres y hy, hxy₁]
      have hcastX : ((x.2 - M).toNat : ℤ) = x.2 - M := Int.toNat_of_nonneg (by omega)
      have hcastY : ((y.2 - M).toNat : ℤ) = y.2 - M := Int.toNat_of_nonneg (by omega)
      have hun' : ((x.2 - M).toNat : ZMod p) = ((y.2 - M).toNat : ZMod p) := by
        have eX := congrArg (fun z : ℤ ↦ (z : ZMod p)) hcastX
        have eY := congrArg (fun z : ℤ ↦ (z : ZMod p)) hcastY
        rw [Int.cast_natCast, Int.cast_sub] at eX eY
        rw [eX, eY, hun]
      have hmod : (x.2 - M).toNat % p = (y.2 - M).toNat % p :=
        (ZMod.natCast_eq_natCast_iff' _ _ _).mp hun'
      have hxy₂ : x.2 = y.2 := by
        have u := Nat.mod_add_div (x.2 - M).toNat p
        have v := Nat.mod_add_div (y.2 - M).toNat p
        rw [hmod, h₂, v] at u
        omega
      exact Prod.ext hxy₁ hxy₂
  rw [Finset.card_product, Finset.card_range, Finset.card_range] at hcard
  refine (Nat.mul_le_mul_right p hcard).trans ?_
  have hprod : (A / p + 1) * p ≤ 2 * A := by
    rw [Nat.add_mul, Nat.one_mul]
    have h := Nat.div_mul_le_self A p
    omega
  calc
    A * (A / p + 1) * p = A * ((A / p + 1) * p) := Nat.mul_assoc _ _ _
    _ ≤ A * (2 * A) := Nat.mul_le_mul_left A hprod
    _ = 2 * A ^ 2 := by ring

private theorem resonant_rectangle_card {p A : ℕ} [Fact p.Prime]
    (hpA : p ≤ A) (S : Finset (ℤ × ℤ)) (L M : ℤ)
    (s r : ZMod p) (hprim : r ≠ 0 ∨ s ≠ 0)
    (hbox : ∀ x ∈ S, L ≤ x.1 ∧ x.1 < L + A ∧ M ≤ x.2 ∧ x.2 < M + A)
    (hres : ∀ x ∈ S, s * (x.1 : ZMod p) = r * (x.2 : ZMod p)) :
    S.card * p ≤ 2 * A ^ 2 := by
  classical
  rcases hprim with hr | hs
  · exact resonant_card_left hpA S L M s r hr hbox hres
  · let swap : (ℤ × ℤ) ↪ (ℤ × ℤ) := ⟨Prod.swap, Prod.swap_injective⟩
    rw [← Finset.card_map swap]
    apply resonant_card_left hpA (S.map swap) M L r s hs
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨h₁, h₂, h₃, h₄⟩ := hbox y hy
      exact ⟨h₃, h₄, h₁, h₂⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      exact (hres y hy).symm
private theorem intCast_inj_halfopen {q A : ℕ} (hA : A ≤ q) {L x y : ℤ}
    (hx : L ≤ x ∧ x < L + A) (hy : L ≤ y ∧ y < L + A)
    (hxy : (x : ZMod q) = (y : ZMod q)) : x = y := by
  have hs : ((x - L : ℤ) : ZMod q) = ((y - L : ℤ) : ZMod q) := by
    simp only [Int.cast_sub, hxy]
  have he := (ZMod.intCast_eq_intCast_iff' _ _ _).mp hs
  rw [Int.emod_eq_of_lt (by omega) (by omega),
    Int.emod_eq_of_lt (by omega) (by omega)] at he
  omega

private theorem physical_pair_cast_injOn {q A : ℕ} (hA : A ≤ q)
    (S : Finset (ℤ × ℤ)) (L M : ℤ)
    (hbox : ∀ x ∈ S, L ≤ x.1 ∧ x.1 < L + A ∧ M ≤ x.2 ∧ x.2 < M + A) :
    Set.InjOn (fun x : ℤ × ℤ ↦ ((x.1 : ZMod q), (x.2 : ZMod q))) S := by
  intro x hx y hy hxy
  obtain ⟨hx₁, hx₂, hx₃, hx₄⟩ := hbox x hx
  obtain ⟨hy₁, hy₂, hy₃, hy₄⟩ := hbox y hy
  exact Prod.ext
    (intCast_inj_halfopen hA ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩ (congrArg Prod.fst hxy))
    (intCast_inj_halfopen hA ⟨hx₃, hx₄⟩ ⟨hy₃, hy₄⟩ (congrArg Prod.snd hxy))

/-- Reduction modulo the prime square of the two exact integer resonance quotients. -/
def resonanceReading (p : ℕ) (r s ρ σ : ℤ) (a : ℤ × ℤ) :
    ZMod (p ^ 2) × ZMod (p ^ 2) :=
  (↑((ρ * a.1 + σ * a.2) / (p : ℤ)), ↑((s * a.1 - r * a.2) / (p : ℤ)))

omit [NeZero (p ^ 2)] in
private lemma physical_reading (r s ρ σ : ℤ) (a : ℤ × ℤ)
    (hpiv : r * ρ + s * σ = p) (hprim : IsCoprime r s)
    (hres : (p : ℤ) ∣ s * a.1 - r * a.2) :
    physicalPivot (r : ZMod (p ^ 2)) (s : ZMod (p ^ 2)) (ρ : ZMod (p ^ 2)) (σ : ZMod (p ^ 2))
      (resonanceReading p r s ρ σ a) = ((a.1 : ZMod (p ^ 2)), (a.2 : ZMod (p ^ 2))) := by
  obtain ⟨ha, hb⟩ := resonance_recovers r s ρ σ a.1 a.2 hpiv hprim hres
  apply Prod.ext
  · simpa only [resonanceReading, physicalPivot, Int.cast_add, Int.cast_mul] using
      congrArg (fun x : ℤ => (x : ZMod (p ^ 2))) ha
  · simpa only [resonanceReading, physicalPivot, Int.cast_sub, Int.cast_mul] using
      congrArg (fun x : ℤ => (x : ZMod (p ^ 2))) hb

/-- The exact unit cubic fiber used by the unprojected pivot kernel. -/
def actualFiber (r s ρ σ g h : ZMod (p ^ 2)) (u : ZMod (p ^ 2) × ZMod (p ^ 2)) :
    Finset (ZMod (p ^ 2) × ZMod (p ^ 2)) := by
  classical
  exact Finset.univ.filter (AdmissiblePoint r s ρ σ g h u)

private theorem actualFiber_card (hp : 3 < p) (r s ρ σ g h : ZMod (p ^ 2))
    (hg : IsUnit g) (u : ZMod (p ^ 2) × ZMod (p ^ 2))
    (ha : IsUnit (physicalPivot r s ρ σ u).1) (hb : IsUnit (physicalPivot r s ρ σ u).2) :
    (actualFiber r s ρ σ g h u).card ≤ 3 * p ^ 2 := by
  classical
  by_cases he : (actualFiber r s ρ σ g h u).Nonempty
  · obtain ⟨z₀, hz₀⟩ := he
    have hmem₀ : AdmissiblePoint r s ρ σ g h u z₀ := (Finset.mem_filter.mp hz₀).2
    have hcurve₀ := hmem₀.2.2.2.2.2.2.2.2
    apply prime_square_cubic_card hp h (fixedSumCubic h z₀)
    · intro z hz
      have hmem : AdmissiblePoint r s ρ σ g h u z := (Finset.mem_filter.mp hz).2
      exact ⟨hmem.2.2.1, hmem.2.2.2.1⟩
    · intro z hz
      have hmem : AdmissiblePoint r s ρ σ g h u z := (Finset.mem_filter.mp hz).2
      exact ((hg.mul ha).mul hb).mul_left_cancel (hmem.2.2.2.2.2.2.2.2.trans hcurve₀.symm)
  · rw [Finset.not_nonempty_iff_eq_empty.mp he]
    simp

/-- Literal pivot data and its conditions, with a common bounded multiplier. -/
structure LiteralResonantRectangle where
  p : ℕ
  A : ℕ
  prime : p.Prime
  prime_gt : 3 < p
  side_lower : p ≤ A
  side_upper : A < p ^ 2
  L : ℤ
  M : ℤ
  r : ℤ
  s : ℤ
  ρ : ℤ
  σ : ℤ
  determinant : r * ρ + s * σ = p
  primitive : IsCoprime r s
  g : ZMod (p ^ 2)
  h : ZMod (p ^ 2)
  g_unit : IsUnit g
  pivots : Finset (ℤ × ℤ)
  box : ∀ a ∈ pivots, L ≤ a.1 ∧ a.1 ≤ L + A ∧ M ≤ a.2 ∧ a.2 ≤ M + A
  resonance : ∀ a ∈ pivots, (p : ℤ) ∣ s * a.1 - r * a.2
  units : ∀ a ∈ pivots, IsUnit (a.1 : ZMod (p ^ 2)) ∧ IsUnit (a.2 : ZMod (p ^ 2))
  χ : (ZMod (p ^ 2) × ZMod (p ^ 2)) → ℂ
  mask_bound : ∀ a ∈ pivots, ‖χ (resonanceReading p r s ρ σ a)‖ ≤ 1

/-- Complete dual-frequency energy on the literal pivots, divided by the fourth power of q. -/
def normalizedRectangleEnergy (R : LiteralResonantRectangle)
    (c : (ZMod (R.p ^ 2) × ZMod (R.p ^ 2)) → ℂ) : ℝ := by
  letI : NeZero (R.p ^ 2) := ⟨pow_ne_zero _ R.prime.ne_zero⟩
  let P := R.pivots.image (resonanceReading R.p R.r R.s R.ρ R.σ)
  exact (∑ f : DualFrequency (R.p ^ 2), ‖∑ u ∈ P,
    c u * dualKernel (actualFiber (R.r : ZMod (R.p ^ 2)) (R.s : ZMod (R.p ^ 2))
      R.ρ R.σ R.g R.h) R.χ u f‖ ^ 2) / ((R.p ^ 2 : ℕ) : ℝ) ^ 4

/-- The full dual-frequency energy is O(pA²) on a literal resonant rectangle. -/
theorem complete_resonant_rectangle_energy_le (R : LiteralResonantRectangle)
    (c : (ZMod (R.p ^ 2) × ZMod (R.p ^ 2)) → ℂ)
    (hc : ∀ a ∈ R.pivots, ‖c (resonanceReading R.p R.r R.s R.ρ R.σ a)‖ ≤ 1) :
    normalizedRectangleEnergy R c ≤ 9 * (R.p : ℝ) * (R.A : ℝ) ^ 2 := by
  rcases R with ⟨p, A, hprime, hp, hpA, hAq, L, M, r, s, ρ, σ, hpiv, hprim,
    g, h, hg, T, hbox, hres, hunit, χ, hχ⟩
  let : Fact p.Prime := ⟨hprime⟩
  let : NeZero (p ^ 2) := ⟨pow_ne_zero _ hprime.ne_zero⟩
  classical
  let P := T.image (resonanceReading p r s ρ σ)
  let Z := actualFiber (r : ZMod (p ^ 2)) (s : ZMod (p ^ 2)) ρ σ g h
  have hZ : ∀ u ∈ P, ∀ z ∈ Z u, AdmissiblePoint (r : ZMod (p ^ 2)) (s : ZMod (p ^ 2)) ρ σ g h u z :=
    fun _ _ _ hz => (Finset.mem_filter.mp hz).2
  have hbox' : ∀ a ∈ T,
      L ≤ a.1 ∧ a.1 < L + ((A + 1 : ℕ) : ℤ) ∧
      M ≤ a.2 ∧ a.2 < M + ((A + 1 : ℕ) : ℤ) := by
    intro a ha
    obtain ⟨h1, h2, h3, h4⟩ := hbox a ha
    push_cast
    omega
  have hP : P.card * p ≤ 2 * (A + 1) ^ 2 := by
    have hres' : ∀ a ∈ T, (s : ZMod p) * (a.1 : ZMod p) = (r : ZMod p) * (a.2 : ZMod p) := by
      intro a ha
      have he := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (hres a ha)
      simpa only [Int.cast_sub, Int.cast_mul, sub_eq_zero] using he
    have hboxcount := resonant_rectangle_card (hpA.trans (Nat.le_succ A)) T L M
      (s : ZMod p) (r : ZMod p) (primitive_reduction r s hprim) hbox' hres'
    have hinj : Set.InjOn (resonanceReading p r s ρ σ) T := by
      intro a ha b hb he
      have ea := physical_reading r s ρ σ a hpiv hprim (hres a ha)
      have eb := physical_reading r s ρ σ b hpiv hprim (hres b hb)
      have hab := ea.symm.trans ((congrArg _ he).trans eb)
      exact physical_pair_cast_injOn (Nat.succ_le_of_lt hAq) T L M hbox' ha hb hab
    simpa only [P, Finset.card_image_of_injOn hinj] using hboxcount
  have hWp : ∀ u ∈ P, ‖c u * χ u‖ ^ 2 * ((Z u).card : ℝ) ≤ 3 * (p : ℝ) ^ 2 := by
    intro u hu
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
    have hnorm : ‖c (resonanceReading p r s ρ σ a) * χ (resonanceReading p r s ρ σ a)‖ ≤ 1 := by
      rw [norm_mul]
      calc
        _ ≤ 1 * ‖χ (resonanceReading p r s ρ σ a)‖ :=
          mul_le_mul_of_nonneg_right (hc a ha) (norm_nonneg _)
        _ ≤ 1 := by simpa only [one_mul] using hχ a ha
    have hsq : ‖c (resonanceReading p r s ρ σ a) * χ (resonanceReading p r s ρ σ a)‖ ^ 2 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have hcard : ((Z (resonanceReading p r s ρ σ a)).card : ℝ) ≤ 3 * (p : ℝ) ^ 2 := by
      have hread := physical_reading r s ρ σ a hpiv hprim (hres a ha)
      have hau : IsUnit (physicalPivot (r : ZMod (p ^ 2)) (s : ZMod (p ^ 2)) ρ σ
          (resonanceReading p r s ρ σ a)).1 := by
        rw [hread]
        exact (hunit a ha).1
      have hbu : IsUnit (physicalPivot (r : ZMod (p ^ 2)) (s : ZMod (p ^ 2)) ρ σ
          (resonanceReading p r s ρ σ a)).2 := by
        rw [hread]
        exact (hunit a ha).2
      exact_mod_cast actualFiber_card hp (r : ZMod (p ^ 2)) (s : ZMod (p ^ 2)) ρ σ g h hg
        (resonanceReading p r s ρ σ a) hau hbu
    exact (mul_le_of_le_one_left (by positivity) hsq).trans hcard
  change _ / ((p ^ 2 : ℕ) : ℝ) ^ 4 ≤ _
  rw [complete_dual_energy (r : ZMod (p ^ 2)) (s : ZMod (p ^ 2)) ρ σ g h hg P Z hZ c χ]
  have hboxR : (P.card : ℝ) * (p : ℝ) ≤ 3 * (A : ℝ) ^ 2 := by
    have hcast : (P.card : ℝ) * (p : ℝ) ≤ 2 * ((A : ℝ) + 1) ^ 2 := by exact_mod_cast hP
    have hnat : 5 ≤ A := by
      have hp4 : p ≠ 4 := by
        intro h4
        exact (by decide : ¬ Nat.Prime 4) (h4 ▸ hprime)
      omega
    have hA : (5 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hnat
    apply hcast.trans
    nlinarith [mul_nonneg (show 0 ≤ (A : ℝ) by positivity) (sub_nonneg.mpr hA)]
  calc
    _ ≤ ∑ _u ∈ P, 3 * (p : ℝ) ^ 2 := Finset.sum_le_sum hWp
    _ = (3 * (p : ℝ)) * ((P.card : ℝ) * (p : ℝ)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ (3 * (p : ℝ)) * (3 * (A : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hboxR (by positivity)
    _ = 9 * (p : ℝ) * (A : ℝ) ^ 2 := by ring

#print axioms complete_resonant_rectangle_energy_le

end

end D5.S3.Arith.CharacterSums.PascadiResonantRectangleEnergy
