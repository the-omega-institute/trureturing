/- GID: D5/S3/ConceptDynamics/Coding/RationalUnitPositiveFamily
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/RationalUnitPositiveFamily
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Given rational augmentation-ideal matrix units admit a synchronized positive family with exact depths and rectangular exchange distances. -/

import D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier
import D5.S3.ConceptDynamics.Coding.InertGroupBlockConjugacy
import D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange
import Mathlib.LinearAlgebra.Matrix.Integer
import Mathlib.Data.Nat.Dist

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.ConceptDynamics.Coding.RationalUnitPositiveFamily

open D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier
open D5.S3.ConceptDynamics.Coding.InertGroupBlockConjugacy
open D5.S3.ConceptDynamics.Coding.InvolutionUniformExchange
open scoped BigOperators

noncomputable section
universe u

/-- Zero extension keeps the input realization and imposes no ambient-unit condition. -/
def extend {R : Type*} [Zero R] {d : ℕ} (e : Fin d → Fin d → R) (a b : ℕ) : R :=
  if ha : a < d then if hb : b < d then e ⟨a, ha⟩ ⟨b, hb⟩ else 0 else 0

/-- The original truncated unit shift; its zero member has positive depth one. -/
def shift {R : Type*} [AddCommMonoid R] (e : ℕ → ℕ → R) (t : ℕ) : R :=
  ∑ a ∈ Finset.range (t - 1), e a (a + 1)

/-- The prefixUnits excludes the last diagonal matrix unit. -/
def prefixUnits {R : Type*} [AddCommMonoid R] (e : ℕ → ℕ → R) (t : ℕ) : R :=
  ∑ a ∈ Finset.range (t - 1), e a a

section UnitAlgebra
variable {R : Type*} [Ring R] {d : ℕ} (e : ℕ → ℕ → R)
variable (hm : ∀ a b c f, a < d → b < d → c < d → f < d →
  e a b * e c f = if b = c then e a f else 0)

include hm

private theorem unit_shift (a b t : ℕ) (ha : a < d) (hb : b < d) (ht : t ≤ d) :
    e a b * shift e t = if b < t - 1 then e a (b + 1) else 0 := by
  classical
  rw [shift, Finset.mul_sum]
  by_cases h : b < t - 1
  · rw [if_pos h, Finset.sum_eq_single b]
    · simpa using hm a b b (b + 1) ha hb hb (by omega)
    · intro k hk hkb
      rw [hm a b k (k + 1) ha hb (by have := Finset.mem_range.mp hk; omega) (by
        have := Finset.mem_range.mp hk; omega), if_neg (Ne.symm hkb)]
    · intro hh
      exact (hh (Finset.mem_range.mpr h)).elim
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [hm a b k (k + 1) ha hb (by omega) (by omega), if_neg (by omega)]

private theorem unit_prefix (a b t : ℕ) (ha : a < d) (hb : b < d) (ht : t ≤ d) :
    e a b * prefixUnits e t = if b < t - 1 then e a b else 0 := by
  classical
  rw [prefixUnits, Finset.mul_sum]
  by_cases h : b < t - 1
  · rw [if_pos h, Finset.sum_eq_single b]
    · simpa using hm a b b b ha hb hb hb
    · intro k hk hkb
      rw [hm a b k k ha hb (by have := Finset.mem_range.mp hk; omega)
        (by have := Finset.mem_range.mp hk; omega), if_neg (Ne.symm hkb)]
    · intro hh
      exact (hh (Finset.mem_range.mpr h)).elim
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [hm a b k k ha hb (by omega) (by omega), if_neg (by omega)]

theorem shift_power (t j : ℕ) (ht : t ≤ d) (hj : 0 < j) :
    shift e t ^ j = ∑ a ∈ Finset.range (t - j), e a (a + j) := by
  classical
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases hj0 : j = 0
    · subst j
      simp [shift]
    · rw [pow_succ, ih (by omega), Finset.sum_mul]
      calc
        (∑ a ∈ Finset.range (t - j), e a (a + j) * shift e t) =
            ∑ a ∈ Finset.range (t - j),
              if a < t - (j + 1) then e a (a + (j + 1)) else 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          have ha' := Finset.mem_range.mp ha
          rw [unit_shift e hm a (a + j) t (by omega) (by omega) ht]
          have he : (a + j < t - 1) ↔ a < t - (j + 1) := by omega
          simp only [he, Nat.add_assoc]
        _ = ∑ a ∈ Finset.range (t - (j + 1)), e a (a + (j + 1)) := by
          rw [← Finset.sum_filter]
          congr 1
          ext a
          simp only [Finset.mem_filter, Finset.mem_range]
          omega

theorem prefix_shift (t : ℕ) (ht : t ≤ d) :
    prefixUnits e t * shift e t = shift e t := by
  classical
  rw [prefixUnits, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  have ha' := Finset.mem_range.mp ha
  rw [unit_shift e hm a a t (by omega) (by omega) ht, if_pos ha']

theorem shift_prefix (t : ℕ) (ht : t ≤ d) :
    shift e t * prefixUnits e t = shift e (t - 1) := by
  classical
  rw [shift, Finset.sum_mul]
  calc
    (∑ a ∈ Finset.range (t - 1), e a (a + 1) * prefixUnits e t) =
        ∑ a ∈ Finset.range (t - 1), if a < (t - 1) - 1 then e a (a + 1) else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      have ha' := Finset.mem_range.mp ha
      rw [unit_prefix e hm a (a + 1) t (by omega) (by omega) ht]
      have he : (a + 1 < t - 1) ↔ a < (t - 1) - 1 := by omega
      simp only [he]
    _ = shift e (t - 1) := by
      rw [← Finset.sum_filter, shift]
      congr 1
      ext a
      simp only [Finset.mem_filter, Finset.mem_range]
      omega

theorem shift_exact_depth (t : ℕ) (ht0 : 0 < t) (ht : t ≤ d)
    (he : e 0 0 ≠ 0) :
    0 < t ∧ shift e t ^ t = 0 ∧
      ∀ j : ℕ, 0 < j → j < t → shift e t ^ j ≠ 0 := by
  classical
  refine ⟨ht0, ?_, ?_⟩
  · rw [shift_power e hm t t ht ht0]
    simp
  · intro j hj hjt hz
    have hrow : e 0 0 * shift e t ^ j = e 0 j := by
      rw [shift_power e hm t j ht hj, Finset.mul_sum, Finset.sum_eq_single 0]
      · simpa using hm 0 0 0 j (by omega) (by omega) (by omega) (by omega)
      · intro a ha ha0
        have ha' := Finset.mem_range.mp ha
        rw [hm 0 0 a (a + j) (by omega) (by omega) (by omega) (by omega),
          if_neg (Ne.symm ha0)]
      · intro h
        exact (h (Finset.mem_range.mpr (by omega))).elim
    have hzero : e 0 j = 0 := by simpa [hz] using hrow.symm
    have hback := hm 0 j j 0 (by omega) (by omega) (by omega) (by omega)
    simp only [if_pos rfl, hzero, zero_mul] at hback
    exact he hback.symm
end UnitAlgebra

variable {H : Type u} [Group H] [Fintype H]

/-- All clauses refer to the one supplied matrix-unit realization. -/
structure PositiveFamily {n d : ℕ}
    (e : Fin d → Fin d → Mat (MonoidAlgebra ℚ H) n n) where
  c : ℕ
  K : ℕ
  c_pos : 0 < c
  K_pos : 0 < K
  clears : ∀ a b i j g, ∃ z : ℤ, ((c : ℚ) • e a b i j).coeff g = (z : ℚ)
  bound : ∀ t, 1 ≤ t → t ≤ d → ∀ i j g,
    |((c : ℚ) • shift (extend e) t i j).coeff g| < (K : ℚ) ∧
    |((c : ℚ) • prefixUnits (extend e) t i j).coeff g| < (K : ℚ)
  B : ℕ → Mat (MonoidAlgebra ℕ H) n n
  R : ℕ → Mat (MonoidAlgebra ℕ H) n n
  S : ℕ → Mat (MonoidAlgebra ℕ H) n n
  factors : ∀ t, 1 ≤ t → t ≤ d →
    let W : Mat (MonoidAlgebra ℚ H) n n := fun _ _ =>
      (K : ℚ) • ∑ g : H, MonoidAlgebra.single g 1
    (rationalMatrix (R t) = W + (c : ℚ) • prefixUnits (extend e) t) ∧
    (rationalMatrix (S t) = W + (c : ℚ) • shift (extend e) t) ∧
    (rationalMatrix (B t) = W ^ 2 + (c : ℚ) ^ 2 • shift (extend e) t)
  positive : ∀ t, 1 ≤ t → t ≤ d → ∀ i j g,
    0 < (R t i j).coeff g ∧ 0 < (S t i j).coeff g ∧ 0 < (B t i j).coeff g
  adjacent : ∀ t, 2 ≤ t → t ≤ d → R t * S t = B t ∧ S t * R t = B (t - 1)
  augmentation : ∀ t, 1 ≤ t → t ≤ d →
    matrixAugmentation (B t) = fun _ _ => Fintype.card H ^ 2 * n * K ^ 2
  depth : ∀ t, 1 ≤ t → t ≤ d → tau (B t) = (t : WithTop ℕ)
  distance : ∀ t r, 1 ≤ t → t ≤ d → 1 ≤ r → r ≤ d →
    Nonempty (ExchangeChain (MonoidAlgebra ℕ H) (B t) (B r) (Nat.dist t r)) ∧
    ∀ L, ExchangeChain (MonoidAlgebra ℕ H) (B t) (B r) L → Nat.dist t r ≤ L

set_option maxHeartbeats 2400000 in
/-- The original positive-family construction with supplied clearing and positivity
constants. The constants remain equal to the supplied values in the resulting family. -/
theorem positiveFamily_with_constants [Nontrivial H] {n d : ℕ}
    (hn : 1 ≤ n) (hd : 1 ≤ d)
    (e : Fin d → Fin d → Mat (MonoidAlgebra ℚ H) n n)
    (hm : ∀ a b c f, e a b * e c f = if b = c then e a f else 0)
    (ha : ∀ a b i j, rationalAugmentation (e a b i j) = 0)
    (he : e ⟨0, hd⟩ ⟨0, hd⟩ ≠ 0)
    (c K : ℕ) (hc : 0 < c) (hK : 0 < K)
    (Z : Fin d → Fin d → Mat (MonoidAlgebra ℤ H) n n)
    (hZ : ∀ a b,
      (MonoidAlgebra.mapRingHom H (Int.castRingHom ℚ)).mapMatrix (Z a b) =
        (c : ℚ) • e a b)
    (hbnd : ∀ t, t ≤ d → ∀ i j g,
      |((shift (extend Z) t) i j).coeff g| < (K : ℤ) ∧
      |((prefixUnits (extend Z) t) i j).coeff g| < (K : ℤ)) :
    ∃ F : PositiveFamily e, F.c = c ∧ F.K = K := by
  classical
  let E := extend e
  have hE (a b c f : ℕ) (ha' : a < d) (hb' : b < d) (hc' : c < d) (hf' : f < d) :
      E a b * E c f = if b = c then E a f else 0 := by
    simpa [E, extend, ha', hb', hc', hf', Fin.ext_iff] using
      hm ⟨a, ha'⟩ ⟨b, hb'⟩ ⟨c, hc'⟩ ⟨f, hf'⟩
  have he0 : E 0 0 ≠ 0 := by
    simpa only [E, extend, dif_pos (show 0 < d from hd)] using he
  have hcq : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hc)
  let castZ : MonoidAlgebra ℤ H →+* MonoidAlgebra ℚ H :=
    MonoidAlgebra.mapRingHom H (Int.castRingHom ℚ)
  let castM : Mat (MonoidAlgebra ℤ H) n n →+* Mat (MonoidAlgebra ℚ H) n n :=
    castZ.mapMatrix
  have hZE (a b : ℕ) : castM (extend Z a b) = (c : ℚ) • E a b := by
    by_cases hab : a < d ∧ b < d
    · simpa only [extend, dif_pos hab.1, dif_pos hab.2, E, castM, castZ] using hZ ⟨a, hab.1⟩ ⟨b, hab.2⟩
    · by_cases hab' : a < d
      · simp [extend, E, hab', show ¬ b < d by omega]
      · simp [extend, E, hab']
  let PZ (t : ℕ) := prefixUnits (extend Z) t
  let NZ (t : ℕ) := shift (extend Z) t
  have hPZ (t : ℕ) : castM (PZ t) = (c : ℚ) • prefixUnits E t := by
    simp only [PZ, prefixUnits, map_sum, hZE, Finset.smul_sum]
  have hNZ (t : ℕ) : castM (NZ t) = (c : ℚ) • shift E t := by
    simp only [NZ, shift, map_sum, hZE, Finset.smul_sum]
  have hbound (t : ℕ) (ht : t ≤ d) (i j : Fin n) (g : H) :
      |(NZ t i j).coeff g| < (K : ℤ) ∧ |(PZ t i j).coeff g| < (K : ℤ) :=
    hbnd t ht i j g
  let WZ : Mat (MonoidAlgebra ℤ H) n n := fun _ _ => (K : ℤ) • uniform H
  let W : Mat (MonoidAlgebra ℚ H) n n := fun _ _ =>
    (K : ℚ) • ∑ g : H, MonoidAlgebra.single g 1
  have huZ (g : H) : (uniform H).coeff g = 1 := by
    simp [uniform, basis, MonoidAlgebra.coeff_sum, Finsupp.sum_apply]
  have huQ (g : H) : (∑ h : H, MonoidAlgebra.single h (1 : ℚ)).coeff g = 1 := by
    simp [MonoidAlgebra.coeff_sum, Finsupp.sum_apply]
  have hwZ (i j : Fin n) (g : H) : (WZ i j).coeff g = (K : ℤ) := by
    change ((K : ℤ) • uniform H).coeff g = (K : ℤ)
    simp only [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, huZ, smul_eq_mul, mul_one]
  have hW : castM WZ = W := by
    ext i j g
    change (castZ (WZ i j)).coeff g = ((K : ℚ) • ∑ h : H,
      MonoidAlgebra.single h 1).coeff g
    rw [MonoidAlgebra.coeff_mapRingHom]
    change ((WZ i j).coeff g : ℚ) = _
    rw [hwZ i j g]
    simp only [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, huQ, smul_eq_mul,
      mul_one, Int.cast_natCast]
  let RZ (t : ℕ) := WZ + PZ t
  let SZ (t : ℕ) := WZ + NZ t
  have hpos (t : ℕ) (ht : t ≤ d) (i j : Fin n) (g : H) :
      0 < (RZ t i j).coeff g ∧ 0 < (SZ t i j).coeff g := by
    have hb := hbound t ht i j g
    change 0 < (WZ i j).coeff g + (PZ t i j).coeff g ∧
      0 < (WZ i j).coeff g + (NZ t i j).coeff g
    rw [hwZ i j g]
    constructor <;> linarith [neg_le_abs ((NZ t i j).coeff g),
      neg_le_abs ((PZ t i j).coeff g)]
  let R (t : ℕ) : Mat (MonoidAlgebra ℕ H) n n := fun i j => toNat (RZ t i j)
  let S (t : ℕ) : Mat (MonoidAlgebra ℕ H) n n := fun i j => toNat (SZ t i j)
  let B (t : ℕ) := R t * S t
  have hR (t : ℕ) (ht : t ≤ d) : rationalMatrix (R t) = W + (c : ℚ) • prefixUnits E t := by
    rw [← hW, ← hPZ, ← map_add]
    ext i j g
    change ((((RZ t i j).coeff g).toNat : ℕ) : ℚ) = _
    change ((((RZ t i j).coeff g).toNat : ℕ) : ℚ) = ((RZ t i j).coeff g : ℚ)
    exact_mod_cast Int.toNat_of_nonneg (hpos t ht i j g).1.le
  have hS (t : ℕ) (ht : t ≤ d) : rationalMatrix (S t) = W + (c : ℚ) • shift E t := by
    rw [← hW, ← hNZ, ← map_add]
    ext i j g
    change ((((SZ t i j).coeff g).toNat : ℕ) : ℚ) = ((SZ t i j).coeff g : ℚ)
    exact_mod_cast Int.toNat_of_nonneg (hpos t ht i j g).2.le
  let aug : Mat (MonoidAlgebra ℚ H) n n →+* Mat ℚ n n :=
    rationalAugmentation.toRingHom.mapMatrix
  let pi : Mat (MonoidAlgebra ℚ H) n n →+* Mat (Reduced H) n n :=
    (Ideal.Quotient.mk (uniformIdeal H)).mapMatrix
  have joint (X : Mat (MonoidAlgebra ℚ H) n n) (hx : aug X = 0) (hy : pi X = 0) : X = 0 := by
    apply Matrix.ext
    intro i j
    apply (augmentationSplit H).injective
    apply Prod.ext
    · exact congrFun (congrFun hx i) j
    · exact congrFun (congrFun hy i) j
  have hpiW : pi W = 0 := by
    ext i j
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    intro g
    simp [W, MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum]
  have haugE (a b : ℕ) : aug (E a b) = 0 := by
    by_cases hab : a < d ∧ b < d
    · ext i j
      change rationalAugmentation (E a b i j) = 0
      simpa [E, extend, hab.1, hab.2] using ha ⟨a, hab.1⟩ ⟨b, hab.2⟩ i j
    · by_cases hab' : a < d
      · simp [E, extend, hab', show ¬ b < d by omega]
      · simp [E, extend, hab']
  have haugP (t : ℕ) : aug (prefixUnits E t) = 0 := by
    simp only [prefixUnits, map_sum, haugE, Finset.sum_const_zero]
  have haugN (t : ℕ) : aug (shift E t) = 0 := by
    simp only [shift, map_sum, haugE, Finset.sum_const_zero]
  have cross (X : Mat (MonoidAlgebra ℚ H) n n) (hx : aug X = 0) :
      W * X = 0 ∧ X * W = 0 := by
    constructor
    · apply joint
      · rw [map_mul, hx, mul_zero]
      · rw [map_mul, hpiW, zero_mul]
    · apply joint
      · rw [map_mul, hx, zero_mul]
      · rw [map_mul, hpiW, mul_zero]
  have products (t : ℕ) (ht : t ≤ d) :
      (W + (c : ℚ) • prefixUnits E t) * (W + (c : ℚ) • shift E t) =
        W ^ 2 + (c : ℚ) ^ 2 • shift E t ∧
      (W + (c : ℚ) • shift E t) * (W + (c : ℚ) • prefixUnits E t) =
        W ^ 2 + (c : ℚ) ^ 2 • shift E (t - 1) := by
    have hp := cross (prefixUnits E t) (haugP t)
    have hnn := cross (shift E t) (haugN t)
    constructor <;>
      simp only [add_mul, mul_add, mul_smul_comm, smul_mul_assoc, smul_smul,
        hp.1, hp.2, hnn.1, hnn.2, smul_zero, add_zero, zero_add,
        prefix_shift E hE t ht, shift_prefix E hE t ht, pow_two]
  have hB (t : ℕ) (ht : t ≤ d) :
      rationalMatrix (B t) = W ^ 2 + (c : ℚ) ^ 2 • shift E t := by
    change rationalMatrix (R t * S t) = _
    rw [map_mul, hR t ht, hS t ht]
    exact (products t ht).1
  have hinj : Function.Injective (rationalMatrix (H := H) (n := n)) := by
    intro A A' h
    ext i j g
    have hh := congrArg (fun X : Mat (MonoidAlgebra ℚ H) n n => (X i j).coeff g) h
    exact Nat.cast_injective hh
  have hNM (t : ℕ) (ht0 : 0 < t) (ht : t ≤ d) :
      ExactDepth ((c : ℚ) ^ 2 • shift E t) t := by
    have hh := shift_exact_depth E hE t ht0 ht he0
    refine ⟨ht0, ?_, ?_⟩
    · rw [smul_pow, hh.2.1, smul_zero]
    · intro j hj hjt
      rw [smul_pow]
      exact smul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hcq)) (hh.2.2 j hj hjt)
  have haugM (t : ℕ) : aug ((c : ℚ) ^ 2 • shift E t) = 0 := by
    ext i j
    change rationalAugmentation ((c : ℚ) ^ 2 • shift E t i j) = 0
    rw [map_smul]
    change (c : ℚ) ^ 2 • aug (shift E t) i j = 0
    rw [haugN]
    exact smul_zero _
  have hpiB (t : ℕ) (ht : t ≤ d) :
      pi (rationalMatrix (B t)) = pi ((c : ℚ) ^ 2 • shift E t) := by
    rw [hB t ht, map_add, map_pow, hpiW]
    simp
  have hdepth (t : ℕ) (ht0 : 0 < t) (ht : t ≤ d) :
      ExactDepth (pi (rationalMatrix (B t))) t := by
    rw [hpiB t ht]
    have hh := hNM t ht0 ht
    refine ⟨ht0, ?_, ?_⟩
    · rw [← map_pow, hh.2.1, map_zero]
    · intro j hj hjt hz
      apply hh.2.2 j hj hjt
      apply joint
      · rw [map_pow, haugM, zero_pow (Nat.ne_of_gt hj)]
      · simpa only [map_pow] using hz
  have hu (A : Mat (MonoidAlgebra ℕ H) n n) :
      UniformMatrix A ↔ pi (rationalMatrix A) = 0 := by
    constructor
    · intro hh
      ext i j
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact (natural_cast_uniform_iff (A i j)).mpr (hh i j)
    · intro hh i j
      apply (natural_cast_uniform_iff (A i j)).mp
      exact Ideal.Quotient.eq_zero_iff_mem.mp (congrFun (congrFun hh i) j)
  have htau (t : ℕ) (ht0 : 0 < t) (ht : t ≤ d) : tau (B t) = (t : WithTop ℕ) := by
    have hh := hdepth t ht0 ht
    have huni : UniformMatrix (B t ^ t) := (hu _).mpr (by
      rw [map_pow, map_pow]
      exact hh.2.1)
    have hU : Uniformizes (B t) := ⟨t, ht0, huni⟩
    have hspec := positiveTau_spec (B t) hU
    have hle := (tau_le_iff_uniform_power (B t) t).mpr ⟨ht0, huni⟩
    have hkle : positiveTau (B t) hU ≤ t := by simpa [tau, hU] using hle
    have hkt : positiveTau (B t) hU = t := by
      by_contra h
      have hklt : positiveTau (B t) hU < t := by omega
      have hz := (hu _).mp hspec.2
      rw [map_pow, map_pow] at hz
      exact hh.2.2 _ hspec.1 hklt hz
    simp [tau, hU, hkt]
  have hadj (t : ℕ) (ht0 : 2 ≤ t) (ht : t ≤ d) :
      R t * S t = B t ∧ S t * R t = B (t - 1) := by
    refine ⟨rfl, hinj ?_⟩
    rw [map_mul, hS t ht, hR t ht, hB (t - 1) (by omega)]
    exact (products t ht).2
  have chains (t r : ℕ) (ht0 : 1 ≤ t) (ht : t ≤ d) (hr0 : 1 ≤ r) (hr : r ≤ d) :
      ExchangeChain (MonoidAlgebra ℕ H) (B t) (B r) (Nat.dist t r) := by
    have up (a k : ℕ) (ha0 : 1 ≤ a) (hak : a + k ≤ d) :
        ExchangeChain (MonoidAlgebra ℕ H) (B a) (B (a + k)) k := by
      induction k generalizing a with
      | zero => simpa using ExchangeChain.nil (B a)
      | succ k ih =>
        have hh := hadj (a + 1) (by omega) (by omega)
        have tail := ih (a + 1) (by omega) (by omega)
        rw [← hh.1] at tail
        have hstart : (a + 1) - 1 = a := by omega
        rw [hstart] at hh
        rw [← hh.2]
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ExchangeChain.cons (S (a + 1)) (R (a + 1)) tail
    have down (a k : ℕ) (ha0 : 1 ≤ a) (hak : a + k ≤ d) :
        ExchangeChain (MonoidAlgebra ℕ H) (B (a + k)) (B a) k := by
      induction k with
      | zero => simpa using ExchangeChain.nil (B a)
      | succ k ih =>
        have hh := hadj (a + k + 1) (by omega) (by omega)
        have hprev : a + k + 1 - 1 = a + k := by omega
        rw [hprev] at hh
        have tail := ih (by omega)
        rw [← hh.2] at tail
        change ExchangeChain (MonoidAlgebra ℕ H) (B (a + k + 1)) (B a) (k + 1)
        rw [← hh.1]
        exact ExchangeChain.cons (R (a + k + 1)) (S (a + k + 1)) tail
    by_cases htr : t ≤ r
    · simpa [Nat.dist_eq_sub_of_le htr, Nat.add_sub_of_le htr] using
        up t (r - t) ht0 (by omega)
    · have hrt : r ≤ t := by omega
      simpa [Nat.dist_eq_sub_of_le_right hrt, Nat.add_sub_of_le hrt] using
        down r (t - r) hr0 (by omega)
  refine ⟨{
    c := c, K := K, c_pos := hc, K_pos := hK,
    clears := ?_, bound := ?_, B := B, R := R, S := S,
    factors := ?_, positive := ?_, adjacent := hadj,
    augmentation := ?_, depth := fun t ht0 ht => htau t ht0 ht,
    distance := ?_ }, by exact ⟨rfl, rfl⟩⟩
  · intro a b i j g
    refine ⟨(Z a b i j).coeff g, ?_⟩
    exact (congrArg (fun X : Mat (MonoidAlgebra ℚ H) n n => (X i j).coeff g) (hZ a b)).symm
  · intro t _ ht i j g
    have h1 := congrArg (fun X : Mat (MonoidAlgebra ℚ H) n n => (X i j).coeff g) (hNZ t)
    have h2 := congrArg (fun X : Mat (MonoidAlgebra ℚ H) n n => (X i j).coeff g) (hPZ t)
    change ((NZ t i j).coeff g : ℚ) = ((c : ℚ) • shift E t i j).coeff g at h1
    change ((PZ t i j).coeff g : ℚ) = ((c : ℚ) • prefixUnits E t i j).coeff g at h2
    have hb := hbound t ht i j g
    change |((c : ℚ) • shift E t i j).coeff g| < (K : ℚ) ∧
      |((c : ℚ) • prefixUnits E t i j).coeff g| < (K : ℚ)
    constructor
    · rw [← h1]
      exact_mod_cast hb.1
    · rw [← h2]
      exact_mod_cast hb.2
  · intro t _ ht
    exact ⟨hR t ht, hS t ht, hB t ht⟩
  · intro t _ ht i j g
    have hfactor (i j : Fin n) (g : H) :
        0 < (R t i j).coeff g ∧ 0 < (S t i j).coeff g := by
      constructor
      · change 0 < ((RZ t i j).coeff g).toNat
        have h := (hpos t ht i j g).1
        omega
      · change 0 < ((SZ t i j).coeff g).toNat
        have h := (hpos t ht i j g).2
        omega
    refine ⟨(hfactor i j g).1, (hfactor i j g).2, ?_⟩
    let k : Fin n := ⟨0, hn⟩
    have hz : 0 < ((R t i k) * (S t k j)).coeff g := by
      rw [MonoidAlgebra.coeff_mul_apply_left,
        Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
      exact lt_of_lt_of_le (Nat.mul_pos (hfactor i k 1).1 (hfactor k j g).2)
        (by simpa only [inv_one, one_mul] using
          (Finset.single_le_sum (f := fun h : H =>
            (R t i k).coeff h * (S t k j).coeff (h⁻¹ * g))
            (fun x _ => Nat.zero_le _) (Finset.mem_univ (1 : H))))
    change 0 < ((R t * S t) i j).coeff g
    rw [Matrix.mul_apply, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    exact lt_of_lt_of_le hz
      (Finset.single_le_sum (f := fun k : Fin n => (R t i k * S t k j).coeff g)
        (fun x _ => Nat.zero_le _) (Finset.mem_univ k))
  · intro t _ ht
    have haugW (i j : Fin n) : aug W i j = (K : ℚ) * Fintype.card H := by
      change rationalAugmentation ((K : ℚ) • ∑ g : H, MonoidAlgebra.single g 1) = _
      rw [map_smul, map_sum]
      simp only [augmentation_single, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_one, smul_eq_mul]
    have haugB : aug (rationalMatrix (B t)) =
        fun _ _ => (Fintype.card H : ℚ) ^ 2 * n * (K : ℚ) ^ 2 := by
      rw [hB t ht, map_add, map_pow, haugM, add_zero]
      apply Matrix.ext
      intro i j
      change ((aug W) ^ 2) i j = _
      rw [pow_two, Matrix.mul_apply]
      simp only [haugW, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    ext i j
    apply Nat.cast_injective (R := ℚ)
    have hg := congrFun (congrFun haugB i) j
    simpa [aug, rationalMatrix, naturalToRational, matrixAugmentation,
      naturalAugmentation_eq_sum, rationalAugmentation_eq_sum, MonoidAlgebra.coeff_mapRingHom]
      using hg
  · intro t r ht0 ht hr0 hr
    refine ⟨⟨chains t r ht0 ht hr0 hr⟩, ?_⟩
    intro L chain
    have mapped := map_exchange_chain
      ((Ideal.Quotient.mk (uniformIdeal H)).toNonUnitalRingHom.comp
        naturalToRational.toNonUnitalRingHom) chain
    have hh := chain_depth_barrier mapped (hdepth t ht0 ht) (hdepth r hr0 hr)
    simp only [Nat.dist]
    omega

set_option maxHeartbeats 2400000 in
/-- Arbitrary given rational augmentation-ideal matrix units produce the full
strictly positive family, actual adjacent factors, exact positive tau and the
shortest distance against every rectangular chain. -/
theorem theorem26_2 [Nontrivial H] {n d : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d)
    (e : Fin d → Fin d → Mat (MonoidAlgebra ℚ H) n n)
    (hm : ∀ a b c f, e a b * e c f = if b = c then e a f else 0)
    (ha : ∀ a b i j, rationalAugmentation (e a b i j) = 0)
    (he : e ⟨0, hd⟩ ⟨0, hd⟩ ≠ 0) : Nonempty (PositiveFamily e) := by
  classical
  let C : Matrix (Fin d × Fin d × Fin n × Fin n) H ℚ :=
    fun p g => (e p.1 p.2.1 p.2.2.1 p.2.2.2).coeff g
  let c := C.den
  have hc : 0 < c := Nat.pos_of_ne_zero C.den_ne_zero
  have hcq : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hc)
  let Z : Fin d → Fin d → Mat (MonoidAlgebra ℤ H) n n :=
    fun a b i j => ∑ g : H, MonoidAlgebra.single g (C.num (a, b, i, j) g)
  let castZ : MonoidAlgebra ℤ H →+* MonoidAlgebra ℚ H :=
    MonoidAlgebra.mapRingHom H (Int.castRingHom ℚ)
  let castM : Mat (MonoidAlgebra ℤ H) n n →+* Mat (MonoidAlgebra ℚ H) n n :=
    castZ.mapMatrix
  have hZ (a b : Fin d) : castM (Z a b) = (c : ℚ) • e a b := by
    ext i j g
    change (castZ (Z a b i j)).coeff g = ((c : ℚ) • e a b i j).coeff g
    rw [MonoidAlgebra.coeff_mapRingHom]
    change ((Z a b i j).coeff g : ℚ) = ((c : ℚ) • e a b i j).coeff g
    have hz : (Z a b i j).coeff g = C.num (a, b, i, j) g := by
      change (∑ h : H, MonoidAlgebra.single h (C.num (a, b, i, j) h)).coeff g = _
      rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single g]
      · exact Finsupp.single_eq_same
      · intro h _ hh
        exact Finsupp.single_eq_of_ne' hh
      · intro hg
        exact (hg (Finset.mem_univ g)).elim
    rw [hz]
    have h := (div_eq_iff hcq).mp (C.num_div_den (a, b, i, j) g)
    simpa only [C, MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul,
      mul_comm] using h
  let PZ (t : ℕ) := prefixUnits (extend Z) t
  let NZ (t : ℕ) := shift (extend Z) t
  let idx := Fin (d + 1) × Fin n × Fin n × H
  let bnd : idx → ℕ := fun p => max
    ((NZ p.1.val p.2.1 p.2.2.1).coeff p.2.2.2).natAbs
    ((PZ p.1.val p.2.1 p.2.2.1).coeff p.2.2.2).natAbs
  let K := (Finset.univ.sup bnd) + 1
  have hK : 0 < K := by dsimp [K]; omega
  have hbound (t : ℕ) (ht : t ≤ d) (i j : Fin n) (g : H) :
      |(NZ t i j).coeff g| < (K : ℤ) ∧ |(PZ t i j).coeff g| < (K : ℤ) := by
    have hb : bnd (⟨t, by omega⟩, i, j, g) < K :=
      Nat.lt_succ_of_le (Finset.le_sup (f := bnd) (Finset.mem_univ _))
    have hb1 : ((NZ t i j).coeff g).natAbs < K :=
      lt_of_le_of_lt (le_max_left _ _) hb
    have hb2 : ((PZ t i j).coeff g).natAbs < K :=
      lt_of_le_of_lt (le_max_right _ _) hb
    constructor
    · have hbi : (((NZ t i j).coeff g).natAbs : ℤ) < (K : ℤ) := by exact_mod_cast hb1
      simpa only [Int.natCast_natAbs] using hbi
    · have hbi : (((PZ t i j).coeff g).natAbs : ℤ) < (K : ℤ) := by exact_mod_cast hb2
      simpa only [Int.natCast_natAbs] using hbi
  obtain ⟨F, _, _⟩ := positiveFamily_with_constants hn hd e hm ha he c K hc hK Z hZ hbound
  exact ⟨F⟩

#print axioms positiveFamily_with_constants
#print axioms theorem26_2

end
end D5.S3.ConceptDynamics.Coding.RationalUnitPositiveFamily
