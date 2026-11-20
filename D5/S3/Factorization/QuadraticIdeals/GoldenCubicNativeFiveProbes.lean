/- GID: D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeFiveProbes
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/GoldenCubicNativeFiveProbes
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Good native reductions give uniform repeated-root and irreducible mod-five Frobenius inputs. -/

import D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeElliptic

set_option autoImplicit false

namespace D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeFiveProbes
open D5.S1.Scale D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeCyclic
open D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeElliptic

/-- Count all actual affine solutions and the unique point at infinity on
the displayed short Weierstrass model over a prime field. -/
def count (p : ℕ) [Fact p.Prime] (l : ZMod p) : ℕ :=
  1 + ((Finset.univ : Finset (ZMod p × ZMod p)).filter
    (fun q => q.2^2 = equation l q.1)).card

open WeierstrassCurve.Affine

private theorem equation_model_iff {F : Type*} [Field F] (l x y : F) :
    (model l 1).Equation x y ↔ y^2 = equation l x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [model, equation, sub_eq_add_neg]

/-- The finite enumeration counts the actual group-carrier points, not
a proxy count; nonsingularity follows from the unit discriminant. -/
private noncomputable def pointCountEquiv (p : ℕ) [Fact p.Prime] (l : ZMod p)
    (hΔ : (model l 1).Δ ≠ 0) :
    (model l 1).Point ≃ Option {q : ZMod p × ZMod p // q.2^2 = equation l q.1} where
  toFun
    | .zero => none
    | .some x y h => some ⟨(x,y), (equation_model_iff l x y).mp h.1⟩
  invFun
    | none => .zero
    | some q => .some q.1.1 q.1.2
        ((WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp
          ((equation_model_iff l q.1.1 q.1.2).mpr q.2))
  left_inv := by intro q; cases q <;> rfl
  right_inv := by rintro (_ | ⟨⟨x,y⟩,h⟩) <;> rfl

theorem card_curve_points (p : ℕ) [Fact p.Prime] (l : ZMod p)
    (hΔ : (model l 1).Δ ≠ 0) : Nat.card (model l 1).Point = count p l := by
  rw [Nat.card_congr (pointCountEquiv p l hΔ), Nat.card_eq_fintype_card,
    Fintype.card_option, Fintype.card_subtype]
  unfold count
  omega

theorem orbit_step {R : Type*} [CommRing R] (j : ℕ) (hj : 1 ≤ j) :
    (goldenLucas (3^(j+1)):R) =
      (goldenLucas (3^j):R)*((goldenLucas (3^j):R)^2+3) := by
  have H := congrArg (Int.castRingHom R) (golden_cubic_lucas_block j hj).2.2.2.2.2
  simpa only [Int.coe_castRingHom, Int.cast_mul, Int.cast_pow, Int.cast_add,
    Int.cast_ofNat] using H

private def phase (n : ℕ) : Fin 4 := ⟨n%4, Nat.mod_lt n (by decide)⟩

private theorem phase_succ (n : ℕ) : phase (n+1) = phase n + 1 := by
  apply Fin.ext
  simp only [phase, Fin.val_add, Fin.isValue]
  omega

private theorem generic_four {p : ℕ} [Fact p.Prime] (u : Fin 4 → ZMod p)
    (h₀ : u 0=4) (hnext : ∀ a : Fin 4, u (a+1) = u a*((u a)^2+3))
    (n : ℕ) : (goldenLucas (3^(n+1)):ZMod p) = u (phase n) := by
  induction n with
  | zero =>
    rw [show phase 0=0 by rfl, h₀]
    change (goldenLucas 3:ZMod p) = 4
    rw [show goldenLucas 3 = 4 by decide]
    norm_num
  | succ n ih =>
    rw [orbit_step (n+1) (by omega), ih, phase_succ, hnext]

private def states11 : Fin 4 → ZMod 11 := ![4,10,7,1]
private def states31 : Fin 4 → ZMod 31 := ![4,14,27,17]
private def states23 : Fin 4 → ZMod 23 := ![4,7,19,16]

private theorem orbit11 (n : ℕ) :
    (goldenLucas (3^(n+1)):ZMod 11) = states11 (phase n) := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  exact generic_four states11 (by decide) (by decide) n

private theorem orbit31 (n : ℕ) :
    (goldenLucas (3^(n+1)):ZMod 31) = states31 (phase n) := by
  let : Fact (Nat.Prime 31) := ⟨by decide⟩
  exact generic_four states31 (by decide) (by decide) n

private theorem orbit23 (n : ℕ) :
    (goldenLucas (3^(n+1)):ZMod 23) = states23 (phase n) := by
  let : Fact (Nat.Prime 23) := ⟨by decide⟩
  exact generic_four states23 (by decide) (by decide) n

private theorem orbit17 {j : ℕ} (hj : 1 ≤ j) :
    let l := (goldenLucas (3^j):ZMod 17)
    l = 4 ∨ l = 8 ∨ l = 9 := by
  obtain ⟨n,rfl⟩ : ∃ n, j = n+1 := ⟨j-1,by omega⟩
  clear hj
  induction n with
  | zero => exact Or.inl (by decide)
  | succ n ih =>
    dsimp only at ih ⊢
    rw [orbit_step (n+1) (by omega)]
    rcases ih with h|h|h
    · right; left; rw [h]; decide
    · right; right; rw [h]; decide
    · right; left; rw [h]; decide

set_option maxRecDepth 16384 in
private theorem counts11 : letI : Fact (Nat.Prime 11) := ⟨by decide⟩
    (∀ a : Fin 4, count 11 (states11 a) = (![9,17,15,7] : Fin 4 → ℕ) a) ∧
      (∀ a : Fin 4, (model (states11 a) 1).Δ ≠ 0) := by decide

set_option maxRecDepth 16384 in
private theorem counts31 : letI : Fact (Nat.Prime 31) := ⟨by decide⟩
    (∀ a : Fin 4, count 31 (states31 a) = (![23,24,41,40] : Fin 4 → ℕ) a) ∧
      (∀ a : Fin 4, (model (states31 a) 1).Δ ≠ 0) := by decide

set_option maxRecDepth 16384 in
private theorem counts17 : letI : Fact (Nat.Prime 17) := ⟨by decide⟩
    (∀ l : ZMod 17, l=4 ∨ l=8 ∨ l=9 → count 17 l = 15 ∧ (model l 1).Δ ≠ 0) := by decide

set_option maxRecDepth 16384 in
private theorem counts23 : letI : Fact (Nat.Prime 23) := ⟨by decide⟩
    (∀ a : Fin 4, count 23 (states23 a) = (![24,16,24,32] : Fin 4 → ℕ) a) ∧
      (∀ a : Fin 4, (model (states23 a) 1).Δ ≠ 0) := by decide

theorem native_good_probe11 {j : ℕ} (hj : 1 ≤ j) (hodd : j%2=1) :
    letI : Fact (Nat.Prime 11) := ⟨by decide⟩
    let l := (goldenLucas (3^j):ZMod 11)
    (count 11 l=9 ∨ count 11 l=15) ∧ (model l 1).Δ ≠ 0 := by
  dsimp only
  obtain ⟨n,rfl⟩ : ∃ n, j=n+1 := ⟨j-1,by omega⟩
  rw [orbit11 n]
  refine ⟨?_,counts11.2 _⟩
  rw [counts11.1]
  have hm : n%4=0 ∨ n%4=2 := by omega
  have hc : (phase n)=0 ∨ (phase n)=2 := by
    rcases hm with h|h
    · left; exact Fin.ext h
    · right; exact Fin.ext h
  rcases hc with h|h <;> rw [h] <;> decide

theorem native_good_probe31 {j : ℕ} (hj : 1 ≤ j) (heven : j%2=0) :
    letI : Fact (Nat.Prime 31) := ⟨by decide⟩
    let l := (goldenLucas (3^j):ZMod 31)
    (count 31 l=24 ∨ count 31 l=40) ∧ (model l 1).Δ ≠ 0 := by
  dsimp only
  obtain ⟨n,rfl⟩ : ∃ n, j=n+1 := ⟨j-1,by omega⟩
  rw [orbit31 n]
  refine ⟨?_,counts31.2 _⟩
  rw [counts31.1]
  have hm : n%4=1 ∨ n%4=3 := by omega
  have hc : (phase n)=1 ∨ (phase n)=3 := by
    rcases hm with h|h
    · left; exact Fin.ext h
    · right; exact Fin.ext h
  rcases hc with h|h <;> rw [h] <;> decide

theorem native_good_probe17 {j : ℕ} (hj : 1 ≤ j) :
    letI : Fact (Nat.Prime 17) := ⟨by decide⟩
    let l := (goldenLucas (3^j):ZMod 17)
    count 17 l=15 ∧ (model l 1).Δ ≠ 0 :=
  counts17 _ (orbit17 hj)

def formalTrace (p n : ℕ) : ℤ := (p:ℤ)+1-(n:ℤ)

/-- At every native level a good prime has the characteristic-polynomial
data of a nontrivial projective order-five probe. Neither the curve
count nor its complementary twist count is divisible by 25. -/
theorem native_repeated_root_probe (j : ℕ) (hj : 1 ≤ j) :
    ∃ p : ℕ, ∃ hp : Fact p.Prime,
      letI := hp
      let l := (goldenLucas (3^j):ZMod p)
      let n := Nat.card (model l 1).Point
      (p=11 ∨ p=31) ∧ (model l 1).Δ ≠ 0 ∧
      (p:ZMod 5)=1 ∧ (formalTrace p n:ZMod 5)^2=4 ∧
      ¬ 25 ∣ n ∧ ¬ 25 ∣ 2*(p+1)-n := by
  by_cases ho : j%2=1
  · let hp : Fact (Nat.Prime 11) := ⟨by decide⟩
    exact ⟨11, hp, by
      intro l n
      obtain ⟨hn,hd⟩ := native_good_probe11 hj ho
      have hd' : (model l 1).Δ ≠ 0 := hd
      have hcard : n = count 11 l := card_curve_points 11 l hd'
      refine ⟨Or.inl rfl, hd', ?_⟩
      rw [hcard]
      rcases hn with h|h <;>
        rw [show count 11 l = _ from h] <;> decide⟩
  · have he : j%2=0 := by omega
    let hp : Fact (Nat.Prime 31) := ⟨by decide⟩
    exact ⟨31, hp, by
      intro l n
      obtain ⟨hn,hd⟩ := native_good_probe31 hj he
      have hd' : (model l 1).Δ ≠ 0 := hd
      have hcard : n = count 31 l := card_curve_points 31 l hd'
      refine ⟨Or.inr rfl, hd', ?_⟩
      rw [hcard]
      rcases hn with h|h <;>
        rw [show count 31 l = _ from h] <;> decide⟩

/-- Prime 23 supplies a root-free quadratic characteristic polynomial for
every native level, using only the exact point count and good discriminant. -/
theorem native_nonsplit_probe23 (j : ℕ) (hj : 1 ≤ j) :
    letI : Fact (Nat.Prime 23) := ⟨by decide⟩
    let l := (goldenLucas (3^j):ZMod 23)
    let n := Nat.card (model l 1).Point
    (model l 1).Δ ≠ 0 ∧
      (∀ x : ZMod 5, x^2-(formalTrace 23 n:ZMod 5)*x+3 ≠ 0) := by
  let : Fact (Nat.Prime 23) := ⟨by decide⟩
  dsimp only
  obtain ⟨n,rfl⟩ : ∃ n, j=n+1 := ⟨j-1,by omega⟩
  rw [orbit23 n]
  refine ⟨counts23.2 _, ?_⟩
  rw [card_curve_points 23 _ (counts23.2 _), counts23.1]
  exact (by decide : ∀ a : Fin 4,
      ∀ x : ZMod 5, x^2-(formalTrace 23 ((![24,16,24,32] : Fin 4→ℕ) a):ZMod 5)*x+3 ≠ 0)
      (phase n)

end D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeFiveProbes
