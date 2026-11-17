/- GID: D5/S3/Arith/CharacterSums/PascadiMinusRows
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiMinusRows
   mirror-E: none(waiver:open-original-prime-cube-count)
   anchors: []
   utility: none
   digest: Original minus-identity returns and their prime-cube row strata. -/

import D5.S3.Arith.CharacterSums.PascadiSixWordFiber
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

open Matrix
open scoped Matrix

namespace D5.S3.Arith.CharacterSums

noncomputable section

/-- The four equations in the original six letters, with no entry inverted. -/
def MinusEquations {R : Type*} [CommRing R] (g a t b d w v : R) : Prop :=
  a + b + w = g * t * a * b ∧ t + d + v = g * w * d * v ∧
    w * d = t * a ∧ w * v = t * b

variable {c : ℕ} [NeZero c]

/-- Exact equivalence for the existing alternating transfer word, including zero entries. -/
theorem sixReturnWord_minus_iff (a₁ a₂ a t b d w v : ZMod c)
    (h₁ : IsUnit a₁) (h₂ : IsUnit a₂) :
    sixReturnWord a₁ a₂ a t b d w v = scalarReturn (-1) ↔
      MinusEquations (a₁ * a₂) a t b d w v := by
  let A := returnStep (a₁ * a) * returnStep (a₂ * t) * returnStep (a₁ * b)
  let B := returnStep (a₂ * d) * returnStep (a₁ * w) * returnStep (a₂ * v)
  let J : Matrix (Fin 2) (Fin 2) (ZMod c) :=
    !![-(a₁ * w), (a₂ * d) * (a₁ * w)-1;
      1-(a₁ * w) * (a₂ * v), (a₂ * d) * (a₁ * w) * (a₂ * v)-(a₂ * d)-(a₂ * v)]
  have hBJ : B * J = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B, J, returnStep, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hJB : J * B = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B, J, returnStep, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hword : sixReturnWord a₁ a₂ a t b d w v = A * B := by
    simp only [sixReturnWord, A, B, mul_assoc]
  have hsplit : sixReturnWord a₁ a₂ a t b d w v = scalarReturn (-1) ↔
      A = scalarReturn (-1) * J := by
    rw [hword]
    constructor
    · intro h
      have hh := congrArg (fun M => M * J) h
      simpa only [mul_assoc, hBJ, mul_one] using hh
    · intro h
      rw [h, mul_assoc, hJB, mul_one]
  rw [hsplit]
  constructor
  · intro h
    have e00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod c) => M 0 0) h
    have e01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod c) => M 0 1) h
    have e10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod c) => M 1 0) h
    have e11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod c) => M 1 1) h
    simp [A, J, returnStep, scalarReturn, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
    have f₁ : a₁ * (a + b + w-(a₁ * a₂) * t * a * b) = a₁ * 0 := by linear_combination -e00
    have f₂ : a₂ * (t + d + v-(a₁ * a₂) * w * d * v) = a₂ * 0 := by linear_combination -e11
    have f₃ : (a₁ * a₂) * (w * d-t * a) = (a₁ * a₂) * 0 := by linear_combination e01
    have f₄ : (a₁ * a₂) * (w * v-t * b) = (a₁ * a₂) * 0 := by linear_combination -e10
    exact ⟨sub_eq_zero.mp (h₁.mul_left_cancel f₁),
      sub_eq_zero.mp (h₂.mul_left_cancel f₂),
      sub_eq_zero.mp ((h₁.mul h₂).mul_left_cancel f₃),
      sub_eq_zero.mp ((h₁.mul h₂).mul_left_cancel f₄)⟩
  · rintro ⟨e₁,e₂,e₃,e₄⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A, J, returnStep, scalarReturn, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination -a₁ * e₁
    · linear_combination (a₁ * a₂) * e₃
    · linear_combination -(a₁ * a₂) * e₄
    · linear_combination -a₂ * e₂

/-- The third minor follows without cancelling any original coordinate. -/
theorem MinusEquations.third_minor {R : Type*} [CommRing R]
    {g a t b d w v : R} (h : MinusEquations g a t b d w v) : a * v = b * d := by
  rcases h with ⟨e₁,e₂,e₃,e₄⟩
  linear_combination v * e₁ - b * e₂ - e₄ - g * b * v * e₃

/-- Even cyclic rotation preserves the fixed alternating coefficients. -/
theorem MinusEquations.even_rotate {R : Type*} [CommRing R]
    {g a t b d w v : R} (h : MinusEquations g a t b d w v) :
    MinusEquations g b d w v a t := by
  have e₅ := h.third_minor
  rcases h with ⟨e₁,e₂,e₃,e₄⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination e₁ - g * b * e₃
  · linear_combination e₂ + g * v * e₃
  · simpa [mul_comm] using e₅
  · linear_combination -e₃

/-- Original integer letters grouped as the two rows (a,b,w) and (d,v,t). -/
abbrev ReturnRows := (Fin 3 → ℤ) × (Fin 3 → ℤ)

/-- The literal, independently bounded integer rows. -/
def literalRowBox (X Y : ℕ) : Finset ReturnRows :=
  (Fintype.piFinset fun _ : Fin 3 => Finset.Icc (-(X : ℤ)) X).product
    (Fintype.piFinset fun _ : Fin 3 => Finset.Icc (-(Y : ℤ)) Y)

/-- Actual minus-identity returns of the existing six-letter word. -/
def minusSolutions (c X Y : ℕ) (a₁ a₂ : ZMod c) : Finset ReturnRows :=
  (literalRowBox X Y).filter fun h =>
    sixReturnWord a₁ a₂ (h.1 0) (h.2 2) (h.1 1) (h.2 0) (h.1 2) (h.2 1) =
      scalarReturn (-1)

/-- The original literal-box minus-identity count. -/
def Nminus (p X Y : ℕ) (a₁ a₂ : ZMod (p ^ 3)) : ℕ :=
  (minusSolutions (p ^ 3) X Y a₁ a₂).card

/-- The same original solutions, with the middle column consisting of units mod p. -/
def Uminus (p X Y : ℕ) (a₁ a₂ : ZMod (p ^ 3)) : ℕ :=
  ((minusSolutions (p ^ 3) X Y a₁ a₂).filter fun h =>
    ¬ (p : ℤ) ∣ h.2 2 * h.1 2).card

/-- Coordinate-free row equations; all three minors are retained. -/
def RowEquations {R : Type*} [CommRing R] (g : R) (x y : Fin 3 → R) : Prop :=
  x 0 + x 1 + x 2 = g * y 2 * x 0 * x 1 ∧
  y 0 + y 1 + y 2 = g * x 2 * y 0 * y 1 ∧
  ∀ i j, x i * y j = x j * y i

/-- The original four equations supply every minor, also at composite moduli. -/
theorem MinusEquations.rows {R : Type*} [CommRing R]
    {g : R} {x y : Fin 3 → R}
    (h : MinusEquations g (x 0) (y 2) (x 1) (y 0) (x 2) (y 1)) :
    RowEquations g x y := by
  refine ⟨h.1, by linear_combination h.2.1, ?_⟩
  intro i j
  have e := h.third_minor
  fin_cases i <;> fin_cases j
  · rfl
  · exact e
  · simpa [mul_comm] using h.2.2.1.symm
  · exact e.symm
  · rfl
  · simpa [mul_comm] using h.2.2.2.symm
  · simpa [mul_comm] using h.2.2.1
  · simpa [mul_comm] using h.2.2.2
  · rfl

/-- A short integer multiple of a positive modulus is zero. -/
private theorem short_dvd_zero {m z : ℤ} (hm : 0 < m) (hd : m ∣ z)
    (hz : -m < z ∧ z < m) : z = 0 := by
  obtain ⟨k,rfl⟩ := hd
  have : k = 0 := by
    by_contra h
    rcases (show k ≤ -1 ∨ 1 ≤ k by omega) with h | h <;> nlinarith [hz.1,hz.2]
  simp [this]

/-- A nonzero p-divisible entry below p² has valuation exactly one. -/
private theorem valuation_one {p : ℕ} (hp : p.Prime) {z : ℤ}
    (hz : z ≠ 0) (hb : -(p : ℤ) ^ 2 < z ∧ z < (p : ℤ) ^ 2)
    (hd : (p : ℤ) ∣ z) : ∃ u : ℤ, z = p * u ∧ ¬ (p : ℤ) ∣ u := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  obtain ⟨u,rfl⟩ := hd
  refine ⟨u,rfl,?_⟩
  intro hu
  apply hz
  apply short_dvd_zero (by positivity) _ hb
  obtain ⟨v,rfl⟩ := hu
  exact ⟨v, by ring⟩

/-- Cancellation of one valuation-one entry leaves modulus p², sufficient for the box. -/
private theorem short_minor_unique {p Y : ℕ} (hp : p.Prime)
    (hY : 2 * Y < p ^ 2) {z u v : ℤ} (hz : z ≠ 0)
    (hzb : -(p : ℤ) ^ 2 < z ∧ z < (p : ℤ) ^ 2) (hzd : (p : ℤ) ∣ z)
    (hu : -(Y : ℤ) ≤ u ∧ u ≤ Y) (hv : -(Y : ℤ) ≤ v ∧ v ≤ Y)
    (he : (z : ZMod (p ^ 3)) * u = z * v) : u = v := by
  obtain ⟨q,hq,hqn⟩ := valuation_one hp hz hzb hzd
  have hd : (p : ℤ) ^ 3 ∣ z * (u-v) := by
    have : ((z * (u-v) : ℤ) : ZMod (p ^ 3)) = 0 := by
      push_cast
      rw [mul_sub, he, sub_self]
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hd' : (p : ℤ) ^ 2 ∣ q * (u-v) := by
    rw [hq] at hd
    have hh : (p : ℤ) * (p : ℤ) ^ 2 ∣ (p : ℤ) * (q * (u-v)) := by
      convert hd using 1 <;> ring
    exact (mul_dvd_mul_iff_left hp0).mp hh
  have hd'' := (Nat.prime_iff_prime_int.mp hp).pow_dvd_of_dvd_mul_left 2 hqn hd'
  have hY' : (2 : ℤ) * Y < (p : ℤ) ^ 2 := by exact_mod_cast hY
  exact sub_eq_zero.mp (short_dvd_zero (by positivity) hd'' (by omega))

/-- A row divisible by p has exact integer sum zero in the short prime-cube box. -/
theorem row_zero_sum {p X : ℕ} (hp : p.Prime) (hX : 3 * X < p ^ 2)
    {g : ZMod (p ^ 3)} {x y : Fin 3 → ℤ}
    (hx : ∀ i, -(X : ℤ) ≤ x i ∧ x i ≤ X)
    (hd : ∀ i, (p : ℤ) ∣ x i)
    (he : RowEquations g (fun i => (x i : ZMod (p ^ 3))) (fun i => (y i : ZMod (p ^ 3)))) :
    x 0 + x 1 + x 2 = 0 := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  let f : ZMod (p ^ 3) →+* ZMod (p ^ 2) :=
    ZMod.castHom (by exact pow_dvd_pow p (by omega)) _
  have hprod : (x 0 : ZMod (p ^ 2)) * (x 1 : ZMod (p ^ 2)) = 0 := by
    obtain ⟨a,ha⟩ := hd 0
    obtain ⟨b,hb⟩ := hd 1
    have hh : (p ^ 2:ℕ) ∣ 0 := dvd_zero _
    have hdab : ((p ^ 2:ℕ):ℤ) ∣ x 0 * x 1 := ⟨a * b, by simp only [Nat.cast_pow]; rw [ha,hb]; ring⟩
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdab
    simpa using this
  have he' := congrArg f he.1
  have hs : ((x 0 + x 1 + x 2 : ℤ) : ZMod (p ^ 2)) = 0 := by
    simp only [map_add, map_mul, map_intCast] at he'
    calc
      _ = f g * (y 2 : ZMod (p ^ 2)) * ((x 0 : ZMod (p ^ 2)) * (x 1 : ZMod (p ^ 2))) := by simpa only [Int.cast_add, mul_assoc] using he'
      _ = 0 := by rw [hprod]; ring
  have hp2 : (0 : ℤ) < ((p ^ 2 : ℕ) : ℤ) := by exact_mod_cast (pow_pos hp.pos 2)
  apply short_dvd_zero hp2 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hs)
  have hX' : (3 : ℤ) * X < (p : ℤ) ^ 2 := by exact_mod_cast hX
  simp only [Nat.cast_pow]
  have := hx 0
  have := hx 1
  have := hx 2
  omega

/-- Literal integer bounds unpacked from the finite box. -/
private theorem mem_literalRowBox {X Y : ℕ} {h : ReturnRows} :
    h ∈ literalRowBox X Y ↔
      (∀ i, -(X : ℤ) ≤ h.1 i ∧ h.1 i ≤ X) ∧
      (∀ i, -(Y : ℤ) ≤ h.2 i ∧ h.2 i ≤ Y) := by
  simp only [literalRowBox, Finset.product_eq_sprod, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_Icc]

private theorem interval_card (X : ℕ) :
    (Finset.Icc (-(X : ℤ)) X).card = 2 * X + 1 := by
  rw [Int.card_Icc]
  omega

private theorem divided_bound {p X : ℕ} (hp : 0 < p) {z : ℤ}
    (hb : -(X : ℤ) ≤ z ∧ z ≤ X) (hd : (p : ℤ) ∣ z) :
    -((X / p : ℕ) : ℤ) ≤ z / p ∧ z / p ≤ ((X / p : ℕ) : ℤ) := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have he := Int.ediv_mul_cancel hd
  have hcast : ((X / p : ℕ) : ℤ) = (X : ℤ) / p := by simp
  rw [hcast]
  constructor
  · have : -(z / (p : ℤ)) ≤ (X : ℤ) / p :=
      (Int.le_ediv_iff_mul_le hp').mpr (by nlinarith [hb.1])
    omega
  · exact (Int.le_ediv_iff_mul_le hp').mpr (by nlinarith [hb.2])

/-- The actual finite row-equation solution set, before any strata are removed. -/
def rowSolutions (p X Y : ℕ) (g : ZMod (p ^ 3)) : Finset ReturnRows :=
  by
  classical
  exact (literalRowBox X Y).filter fun h =>
    RowEquations g (fun i => (h.1 i : ZMod (p ^ 3))) (fun i => (h.2 i : ZMod (p ^ 3)))

private theorem mem_rowSolutions {p X Y : ℕ} {g : ZMod (p ^ 3)} {h : ReturnRows} :
    h ∈ rowSolutions p X Y g ↔ h ∈ literalRowBox X Y ∧
      RowEquations g (fun i => (h.1 i : ZMod (p ^ 3))) (fun i => (h.2 i : ZMod (p ^ 3))) := by
  classical
  simp only [rowSolutions, Finset.mem_filter]

/-- Count one nonzero pivot of a p-divisible row by two normalized row entries and
one original opposite-row coordinate. No scalar lift is independently supplied. -/
private theorem divisible_pivot_count {p X Y : ℕ} (hp : p.Prime)
    (hX : 3 * X < p ^ 2) (hY : 2 * Y < p ^ 2) (g : ZMod (p ^ 3)) (j : Fin 3) :
    ((rowSolutions p X Y g).filter fun h =>
      (∀ i, (p : ℤ) ∣ h.1 i) ∧ h.1 j ≠ 0).card ≤
      (2 * (X / p) + 1) ^ 2 * (2 * Y + 1) := by
  classical
  let s := (rowSolutions p X Y g).filter fun h =>
      (∀ i, (p : ℤ) ∣ h.1 i) ∧ h.1 j ≠ 0
  let I := Finset.Icc (-((X / p : ℕ) : ℤ)) (X / p : ℕ)
  let J := Finset.Icc (-(Y : ℤ)) Y
  have hcard : s.card ≤ ((I.product I).product J).card := by
    apply Finset.card_le_card_of_injOn (fun h : ReturnRows =>
      ((h.1 0 / p, h.1 1 / p), h.2 j))
    · intro h hh
      have hh' := Finset.mem_filter.mp hh
      have hh'' := mem_rowSolutions.mp hh'.1
      have hb := mem_literalRowBox.mp hh''.1
      exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr (divided_bound hp.pos (hb.1 0) (hh'.2.1 0)),
         Finset.mem_Icc.mpr (divided_bound hp.pos (hb.1 1) (hh'.2.1 1))⟩,
        Finset.mem_Icc.mpr (hb.2 j)⟩
    · intro h hh k hk he
      have hh' := Finset.mem_filter.mp hh
      have hk' := Finset.mem_filter.mp hk
      have hh'' := mem_rowSolutions.mp hh'.1
      have hk'' := mem_rowSolutions.mp hk'.1
      have hb := mem_literalRowBox.mp hh''.1
      have kb := mem_literalRowBox.mp hk''.1
      have hs := row_zero_sum hp hX hb.1 hh'.2.1 hh''.2
      have ks := row_zero_sum hp hX kb.1 hk'.2.1 hk''.2
      have e0 : h.1 0 = k.1 0 := by
        have e := congrArg (fun q : (ℤ × ℤ) × ℤ => q.1.1) he
        have := congrArg (fun q : ℤ => q * (p : ℤ)) e
        simpa only [Int.ediv_mul_cancel (hh'.2.1 0), Int.ediv_mul_cancel (hk'.2.1 0)] using this
      have e1 : h.1 1 = k.1 1 := by
        have e := congrArg (fun q : (ℤ × ℤ) × ℤ => q.1.2) he
        have := congrArg (fun q : ℤ => q * (p : ℤ)) e
        simpa only [Int.ediv_mul_cancel (hh'.2.1 1), Int.ediv_mul_cancel (hk'.2.1 1)] using this
      have ex : h.1 = k.1 := by
        funext i
        fin_cases i
        · exact e0
        · exact e1
        · change h.1 2 = k.1 2
          omega
      have eyj : h.2 j = k.2 j := congrArg Prod.snd he
      apply Prod.ext ex
      funext i
      refine short_minor_unique hp hY hh'.2.2 (by
          have hX' : (3 : ℤ) * X < (p : ℤ) ^ 2 := by exact_mod_cast hX
          have := hb.1 j
          omega) (hh'.2.1 j) (hb.2 i) (kb.2 i) ?_
      calc
          (h.1 j : ZMod (p ^ 3)) * h.2 i = (h.1 i : ZMod (p ^ 3)) * h.2 j := hh''.2.2.2 j i
          _ = (k.1 i : ZMod (p ^ 3)) * k.2 j := by rw [ex,eyj]
          _ = (k.1 j : ZMod (p ^ 3)) * k.2 i := (hk''.2.2.2 j i).symm
          _ = (h.1 j : ZMod (p ^ 3)) * k.2 i := by rw [ex]
  simpa only [s,I,J, Finset.product_eq_sprod, Finset.card_product, interval_card, pow_two] using hcard

/-- The exactly zero first row is counted by two original coordinates of the other row. -/
private theorem zero_row_count {p X Y : ℕ} (hp : p.Prime)
    (hY : 3 * Y < p ^ 2) (g : ZMod (p ^ 3)) :
    ((rowSolutions p X Y g).filter fun h => ∀ i, h.1 i = 0).card ≤ (2 * Y + 1) ^ 2 := by
  classical
  let I := Finset.Icc (-(Y : ℤ)) Y
  have hcard : ((rowSolutions p X Y g).filter fun h => ∀ i, h.1 i = 0).card ≤
      (I.product I).card := by
    apply Finset.card_le_card_of_injOn (fun h : ReturnRows => (h.2 0,h.2 1))
    · intro h hh
      have hh' := mem_rowSolutions.mp (Finset.mem_filter.mp hh).1
      have hb := mem_literalRowBox.mp hh'.1
      exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (hb.2 0),Finset.mem_Icc.mpr (hb.2 1)⟩
    · intro h hh k hk he
      have hh' := Finset.mem_filter.mp hh
      have hk' := Finset.mem_filter.mp hk
      have hb := mem_literalRowBox.mp (mem_rowSolutions.mp hh'.1).1
      have kb := mem_literalRowBox.mp (mem_rowSolutions.mp hk'.1).1
      have sum_zero (q : ReturnRows) (hq : q ∈ rowSolutions p X Y g)
          (hz : ∀ i, q.1 i = 0) (hbq : ∀ i, -(Y : ℤ) ≤ q.2 i ∧ q.2 i ≤ Y) :
          q.2 0 + q.2 1 + q.2 2 = 0 := by
        have eqn := (mem_rowSolutions.mp hq).2.2.1
        have hs : ((q.2 0 + q.2 1 + q.2 2 : ℤ) : ZMod (p ^ 3)) = 0 := by
          simpa [hz] using eqn
        have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
        have hY' : (3 : ℤ) * Y < (p : ℤ) ^ 2 := by exact_mod_cast hY
        have hp1 : (1 : ℤ) ≤ p := by exact_mod_cast hp.one_lt.le
        have h23 : (p : ℤ) ^ 2 ≤ (p : ℤ) ^ 3 := by nlinarith [sq_nonneg (p : ℤ)]
        apply short_dvd_zero (by exact_mod_cast pow_pos hp.pos 3)
          ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hs)
        have := hbq 0
        have := hbq 1
        have := hbq 2
        simp only [Nat.cast_pow]
        omega
      have hs := sum_zero h hh'.1 hh'.2 hb.2
      have ks := sum_zero k hk'.1 hk'.2 kb.2
      apply Prod.ext
      · funext i
        rw [hh'.2 i,hk'.2 i]
      · funext i
        have e0 := congrArg Prod.fst he
        have e1 := congrArg Prod.snd he
        fin_cases i
        · exact e0
        · exact e1
        · change h.2 2 = k.2 2
          dsimp only at hs ks e0 e1
          omega
  simpa only [I,Finset.product_eq_sprod,Finset.card_product,interval_card,pow_two] using hcard

/-- Divisible rows, including the exactly zero row, have a genuine finite bound. -/
theorem divisible_row_count {p X Y : ℕ} (hp : p.Prime)
    (hX : 3 * X < p ^ 2) (hY : 3 * Y < p ^ 2) (g : ZMod (p ^ 3)) :
    ((rowSolutions p X Y g).filter fun h => ∀ i, (p : ℤ) ∣ h.1 i).card ≤
      (2 * Y + 1) ^ 2 + 3 * ((2 * (X / p) + 1) ^ 2 * (2 * Y + 1)) := by
  classical
  let Z := (rowSolutions p X Y g).filter fun h => ∀ i, h.1 i = 0
  let S (j : Fin 3) := (rowSolutions p X Y g).filter fun h =>
      (∀ i, (p : ℤ) ∣ h.1 i) ∧ h.1 j ≠ 0
  have hsub : ((rowSolutions p X Y g).filter fun h => ∀ i, (p : ℤ) ∣ h.1 i) ⊆
      Z ∪ Finset.univ.biUnion S := by
    intro h hh
    have hh' := Finset.mem_filter.mp hh
    by_cases hz : ∀ i, h.1 i = 0
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hh'.1,hz⟩)
    · obtain ⟨j,hj⟩ := not_forall.mp hz
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨j,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hh'.1,hh'.2,hj⟩⟩)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hS := Finset.card_biUnion_le_card_mul (Finset.univ : Finset (Fin 3)) S
    ((2 * (X / p) + 1) ^ 2 * (2 * Y + 1)) (fun j _ => divisible_pivot_count hp hX (by omega) g j)
  have hZ := zero_row_count (X := X) hp hY g
  simp only [Finset.card_univ, Fintype.card_fin] at hS
  dsimp only [Z] at hcard
  omega

private theorem normalized_square_bound {p Y : ℕ} (hp : p.Prime)
    (hY : 6 * Y < p ^ 2) : (2 * (Y / p) + 1) ^ 2 ≤ 2 * Y + 1 := by
  have hp0 := hp.pos
  have hk := Nat.div_mul_le_self Y p
  have hkp : 6 * (Y / p) < p := by nlinarith [Nat.mul_le_mul_left 6 hk]
  by_cases hz : Y / p = 0
  · simp [hz]
  · have hk1 : 1 ≤ Y / p := by omega
    nlinarith

/-- Every p-divisible first row costs at most four square interval lengths. This bound
covers all-six-divisible tuples and every exact zero without removing any stratum. -/
theorem divisible_row_count_square {p X Y : ℕ} (hp : p.Prime)
    (hXY : X ≤ Y) (hY : 6 * Y < p ^ 2) (g : ZMod (p ^ 3)) :
    ((rowSolutions p X Y g).filter fun h => ∀ i, (p : ℤ) ∣ h.1 i).card ≤
      4 * (2 * Y + 1) ^ 2 := by
  have h := divisible_row_count (X := X) (Y := Y) hp (by omega) (by omega) g
  have hdiv := Nat.div_le_div_right hXY (c := p)
  have hnorm := normalized_square_bound hp hY
  have hnormX : (2 * (X / p) + 1) ^ 2 ≤ 2 * Y + 1 :=
    (Nat.pow_le_pow_left (by omega : 2 * (X / p) + 1 ≤ 2 * (Y / p) + 1) 2).trans hnorm
  nlinarith

/-- Rank at most one modulo p, with a common unit column whenever neither row vanishes. -/
theorem RowEquations.unit_column {p : ℕ} (hp : p.Prime) {g : ZMod (p ^ 3)}
    {x y : Fin 3 → ℤ}
    (he : RowEquations g (fun i => (x i : ZMod (p ^ 3))) (fun i => (y i : ZMod (p ^ 3))))
    (hx : ¬ ∀ i, (p : ℤ) ∣ x i) (hy : ¬ ∀ i, (p : ℤ) ∣ y i) :
    ∃ j, ¬ (p : ℤ) ∣ x j * y j := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨i,hi⟩ := not_forall.mp hx
  obtain ⟨j,hj⟩ := not_forall.mp hy
  have hxi : (x i : ZMod p) ≠ 0 := by
    exact fun h => hi ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  have hyj : (y j : ZMod p) ≠ 0 := by
    exact fun h => hj ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  let f : ZMod (p ^ 3) →+* ZMod p := ZMod.castHom (dvd_pow_self p (by decide)) _
  have hm := congrArg f (he.2.2 i j)
  simp only [map_mul,map_intCast] at hm
  have hyi : (y i : ZMod p) ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at hm
    exact (mul_ne_zero hxi hyj) hm
  refine ⟨i,?_⟩
  intro hd
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd
  exact (mul_ne_zero hxi hyi) (by simpa only [Int.cast_mul] using hz)

/-- All row minors and the equations are symmetric under exchanging the two rows. -/
theorem RowEquations.transpose_rows {R : Type*} [CommRing R] {g : R} {x y : Fin 3 → R}
    (h : RowEquations g x y) : RowEquations g y x := by
  refine ⟨?_,?_,?_⟩
  · linear_combination h.2.1
  · linear_combination h.1
  · intro i j
    simpa only [mul_comm] using h.2.2 j i

/-- Simultaneously cyclically permuting columns preserves the original row equations. -/
theorem RowEquations.cycle_columns {R : Type*} [CommRing R] {g : R} {x y : Fin 3 → R}
    (h : RowEquations g x y) :
    RowEquations g (fun i => x (i + 1)) (fun i => y (i + 1)) := by
  have hm : MinusEquations g (x 0) (y 2) (x 1) (y 0) (x 2) (y 1) :=
    ⟨h.1,by linear_combination h.2.1,
      by simpa only [mul_comm] using h.2.2 2 0,
      by simpa only [mul_comm] using h.2.2 2 1⟩
  exact MinusEquations.rows (x := fun i => x (i + 1)) (y := fun i => y (i + 1)) hm.even_rotate

/-- Even cyclic rotation on the original literal integer six-tuples. -/
def rotateRows (j : Fin 3) (h : ReturnRows) : ReturnRows :=
  (fun i => h.1 (i + j), fun i => h.2 (i + j))

private theorem rotateRows_injective (j : Fin 3) : Function.Injective (rotateRows j) := by
  intro h k he
  apply Prod.ext <;> funext i
  · have := congrArg (fun q : ReturnRows => q.1 (i-j)) he
    simpa only [rotateRows, sub_add_cancel] using this
  · have := congrArg (fun q : ReturnRows => q.2 (i-j)) he
    simpa only [rotateRows, sub_add_cancel] using this

private theorem rowSolutions_rotate {p X Y : ℕ} {g : ZMod (p ^ 3)}
    {h : ReturnRows} (hh : h ∈ rowSolutions p X Y g) (j : Fin 3) :
    rotateRows j h ∈ rowSolutions p X Y g := by
  have hh' := mem_rowSolutions.mp hh
  have hb := mem_literalRowBox.mp hh'.1
  apply mem_rowSolutions.mpr
  refine ⟨mem_literalRowBox.mpr ⟨fun i => hb.1 _, fun i => hb.2 _⟩,?_⟩
  have e := hh'.2
  have e1 := e.cycle_columns
  have e2 := e1.cycle_columns
  fin_cases j
  · simpa [rotateRows] using e
  · simpa [rotateRows] using e1
  · convert e2 using 1 <;> ext i <;> fin_cases i <;> rfl

private theorem rowSolutions_swap_widen {p X Y : ℕ} (hXY : X ≤ Y) {g : ZMod (p ^ 3)}
    {h : ReturnRows} (hh : h ∈ rowSolutions p X Y g) :
    h.swap ∈ rowSolutions p Y Y g := by
  have hh' := mem_rowSolutions.mp hh
  have hb := mem_literalRowBox.mp hh'.1
  apply mem_rowSolutions.mpr
  refine ⟨mem_literalRowBox.mpr ⟨hb.2,?_⟩,hh'.2.transpose_rows⟩
  intro i
  change -(Y : ℤ) ≤ h.1 i ∧ h.1 i ≤ Y
  have := hb.1 i
  have hXY' : (X : ℤ) ≤ Y := by exact_mod_cast hXY
  exact ⟨by omega,by omega⟩

private theorem divisible_second_row_count_square {p X Y : ℕ} (hp : p.Prime)
    (hXY : X ≤ Y) (hY : 6 * Y < p ^ 2) (g : ZMod (p ^ 3)) :
    ((rowSolutions p X Y g).filter fun h => ∀ i, (p : ℤ) ∣ h.2 i).card ≤
      4 * (2 * Y + 1) ^ 2 := by
  classical
  have hcard : ((rowSolutions p X Y g).filter fun h => ∀ i, (p : ℤ) ∣ h.2 i).card ≤
      ((rowSolutions p Y Y g).filter fun h => ∀ i, (p : ℤ) ∣ h.1 i).card := by
    apply Finset.card_le_card_of_injOn Prod.swap
    · intro h hh
      have hh' := Finset.mem_filter.mp hh
      exact Finset.mem_filter.mpr ⟨rowSolutions_swap_widen hXY hh'.1,hh'.2⟩
    · intro h _ k _ he
      exact Prod.swap_injective he
  exact hcard.trans (divisible_row_count_square hp le_rfl hY g)

private theorem chart_count {p X Y : ℕ} (g : ZMod (p ^ 3)) (j : Fin 3) :
    ((rowSolutions p X Y g).filter fun h => ¬ (p : ℤ) ∣ h.1 j * h.2 j).card ≤
      ((rowSolutions p X Y g).filter fun h => ¬ (p : ℤ) ∣ h.1 2 * h.2 2).card := by
  classical
  apply Finset.card_le_card_of_injOn (rotateRows (j-2))
  · intro h hh
    have hh' := Finset.mem_filter.mp hh
    refine Finset.mem_filter.mpr ⟨rowSolutions_rotate hh'.1 _,?_⟩
    simpa [rotateRows,add_sub_cancel] using hh'.2
  · intro h _ k _ he
    exact rotateRows_injective _ he

/-- All strata are paid for by the three cyclic unit-middle charts and eight square
interval lengths. The finite set contains the original integer coordinates. -/
theorem rowSolutions_count_reduction {p X Y : ℕ} (hp : p.Prime)
    (hXY : X ≤ Y) (hY : 6 * Y < p ^ 2) (g : ZMod (p ^ 3)) :
    (rowSolutions p X Y g).card ≤
      3 * ((rowSolutions p X Y g).filter fun h => ¬ (p : ℤ) ∣ h.1 2 * h.2 2).card + 8 * (2 * Y + 1) ^ 2 := by
  classical
  let s := rowSolutions p X Y g
  let G (j : Fin 3) := s.filter fun h => ¬ (p : ℤ) ∣ h.1 j * h.2 j
  let B := s.filter fun h => ∀ i, (p : ℤ) ∣ h.1 i
  let C := s.filter fun h => ∀ i, (p : ℤ) ∣ h.2 i
  have hsub : s ⊆ Finset.univ.biUnion G ∪ (B ∪ C) := by
    intro h hh
    by_cases hx : ∀ i, (p : ℤ) ∣ h.1 i
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hh,hx⟩))
    by_cases hy : ∀ i, (p : ℤ) ∣ h.2 i
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hh,hy⟩))
    obtain ⟨j,hj⟩ := (mem_rowSolutions.mp hh).2.unit_column hp hx hy
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
      ⟨j,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hh,hj⟩⟩)
  have h0 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h1 := Finset.card_union_le B C
  have h2 := Finset.card_biUnion_le_card_mul (Finset.univ : Finset (Fin 3)) G
    (G 2).card (fun j _ => chart_count g j)
  have hB := divisible_row_count_square hp hXY hY g
  have hC := divisible_second_row_count_square hp hXY hY g
  simp only [Finset.card_univ,Fintype.card_fin] at h2
  change B.card ≤ _ at hB
  change C.card ≤ _ at hC
  change s.card ≤ 3 * (G 2).card + 8 * (2 * Y + 1) ^ 2
  omega

/-- Exact identification of the polynomial row set with the original word solutions. -/
theorem minusSolutions_eq_rowSolutions {p : ℕ} (hp : p.Prime) (X Y : ℕ)
    (a₁ a₂ : ZMod (p ^ 3)) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂) :
    minusSolutions (p ^ 3) X Y a₁ a₂ = rowSolutions p X Y (a₁ * a₂) := by
  haveI : NeZero (p ^ 3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  classical
  ext h
  simp only [minusSolutions,rowSolutions,Finset.mem_filter]
  apply and_congr_right
  intro (_ : h ∈ literalRowBox X Y)
  rw [sixReturnWord_minus_iff _ _ _ _ _ _ _ _ ha₁ ha₂]
  constructor
  · exact MinusEquations.rows (x := fun i => (h.1 i : ZMod (p ^ 3)))
      (y := fun i => (h.2 i : ZMod (p ^ 3)))
  · intro he
    exact ⟨he.1,by linear_combination he.2.1,
      by simpa only [mul_comm] using he.2.2 2 0,
      by simpa only [mul_comm] using he.2.2 2 1⟩

/-- Original prime-cube nonunit-row reduction, for the literal integer box and the
same fixed alternating units. No row-count or coefficient-realization supplier occurs. -/
theorem Nminus_le_three_Uminus {p X Y : ℕ} (hp : p.Prime)
    (hXY : X ≤ Y) (hY : 6 * Y < p ^ 2)
    (a₁ a₂ : ZMod (p ^ 3)) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂) :
    Nminus p X Y a₁ a₂ ≤ 3 * Uminus p X Y a₁ a₂ + 8 * (2 * Y + 1) ^ 2 := by
  have h := rowSolutions_count_reduction hp hXY hY (a₁ * a₂)
  simpa only [Nminus,Uminus,minusSolutions_eq_rowSolutions hp X Y a₁ a₂ ha₁ ha₂,
    mul_comm] using h

end
end D5.S3.Arith.CharacterSums
