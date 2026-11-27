/- GID: D5/S3/Arith/CharacterSums/PascadiPrimeSquareHyperbola
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiPrimeSquareHyperbola
   mirror-E: none(waiver:prime-square-hyperbola)
   anchors: []
   utility: none
   digest: Integer level and signed-divisor bounds for shifted modular hyperbolas. -/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Int.Interval
public import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The finite divisor argument for shifted boxes, as in the Cilleruelo–Garaev
method (arXiv:1007.1526v2, Theorem 1), with a unit right side and multiplier
allowing a prime-square modulus. -/

namespace D5.S3.Arith.CharacterSums.Original

@[expose] public section

open scoped BigOperators

/-- The integer polynomial that remains after subtracting the constant term. -/
def hyperbolaLevelForm (t u₁ u₂ : ℤ) (a : ℤ × ℤ) : ℤ :=
  t * a.1 * a.2 + u₂ * a.1 + u₁ * a.2

/-- The common product of the shifted integer factors at level `k`. -/
def hyperbolaLevelProduct (q : ℕ) (t u₁ u₂ b k : ℤ) : ℤ :=
  u₁ * u₂ + t * (b + k * q)

/-- The integer solutions are partitioned by the unique lift of the cleared congruence. -/
theorem shifted_product_iff_integer_level {q : ℕ} (hq : 1 < q)
    {t A₁ A₂ u₁ u₂ b : ℤ} {C : ZMod q} (a : ℤ × ℤ)
    (ht : IsUnit (t : ZMod q))
    (hu₁ : (u₁ : ZMod q) = (t : ZMod q) * A₁)
    (hu₂ : (u₂ : ZMod q) = (t : ZMod q) * A₂)
    (hb : (b : ZMod q) = (t : ZMod q) * (C - (A₁ : ZMod q) * A₂)) :
    ((a.1 + A₁ : ℤ) : ZMod q) * ((a.2 + A₂ : ℤ) : ZMod q) = C ↔
      ∃! k : ℤ, hyperbolaLevelForm t u₁ u₂ a = b + k * q := by
  have hq₀ : (q : ℤ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hcast : ((hyperbolaLevelForm t u₁ u₂ a - b : ℤ) : ZMod q) =
      (t : ZMod q) *
        (((a.1 + A₁ : ℤ) : ZMod q) * ((a.2 + A₂ : ℤ) : ZMod q) - C) := by
    simp only [hyperbolaLevelForm, Int.cast_sub, Int.cast_mul, Int.cast_add, hu₁, hu₂, hb]
    ring
  constructor
  · intro h
    have hz : ((hyperbolaLevelForm t u₁ u₂ a - b : ℤ) : ZMod q) = 0 := by
      rw [hcast, h, sub_self, mul_zero]
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
    refine ⟨k, by linarith only [hk, mul_comm (q : ℤ) k], ?_⟩
    intro j hj
    have he : j * (q : ℤ) = k * q := by linarith only [hj, hk, mul_comm (q : ℤ) k]
    exact mul_right_cancel₀ hq₀ he
  · rintro ⟨k, hk, _⟩
    have hz : ((hyperbolaLevelForm t u₁ u₂ a - b : ℤ) : ZMod q) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ⟨k, by
        linarith only [hk, mul_comm (q : ℤ) k]⟩
    rw [hcast] at hz
    exact sub_eq_zero.mp (ht.mul_left_cancel (hz.trans (mul_zero _).symm))

/-- Every proposed level product has the same unit residue, even on empty levels. -/
theorem hyperbola_level_product_unit {q : ℕ} {t A₁ A₂ u₁ u₂ b : ℤ}
    {C : ZMod q} (k : ℤ)
    (ht : IsUnit (t : ZMod q)) (hC : IsUnit C)
    (hu₁ : (u₁ : ZMod q) = (t : ZMod q) * A₁)
    (hu₂ : (u₂ : ZMod q) = (t : ZMod q) * A₂)
    (hb : (b : ZMod q) = (t : ZMod q) * (C - (A₁ : ZMod q) * A₂)) :
    (hyperbolaLevelProduct q t u₁ u₂ b k : ZMod q) = (t : ZMod q)^2 * C ∧
      IsUnit (hyperbolaLevelProduct q t u₁ u₂ b k : ZMod q) := by
  have hcast : (hyperbolaLevelProduct q t u₁ u₂ b k : ZMod q) =
      (t : ZMod q)^2 * C := by
    simp only [hyperbolaLevelProduct, Int.cast_add, Int.cast_mul, Int.cast_natCast,
      ZMod.natCast_self, mul_zero, add_zero, hu₁, hu₂, hb]
    ring
  refine ⟨hcast, ?_⟩
  rw [hcast]
  exact (ht.pow 2).mul hC

/-- On a nonzero level the first shifted factor determines the entire integer pair,
and belongs to the signed divisor finset. -/
theorem hyperbola_level_card_le {q : ℕ} {t u₁ u₂ b k : ℤ}
    (ht : t ≠ 0) (hn : hyperbolaLevelProduct q t u₁ u₂ b k ≠ 0)
    (F : Finset (ℤ × ℤ))
    (hF : ∀ a ∈ F, hyperbolaLevelForm t u₁ u₂ a = b + k * q) :
    F.card ≤ 2 * (hyperbolaLevelProduct q t u₁ u₂ b k).natAbs.divisors.card := by
  let n := hyperbolaLevelProduct q t u₁ u₂ b k
  let f (a : ℤ × ℤ) := t * a.1 + u₁
  have hf (a : ℤ × ℤ) (ha : a ∈ F) : f a * (t * a.2 + u₂) = n := by
    calc
      _ = u₁ * u₂ + t * hyperbolaLevelForm t u₁ u₂ a := by
        simp only [f, hyperbolaLevelForm]
        ring
      _ = n := by rw [hF a ha]; rfl
  have hc : F.card ≤ n.divisors.card := by
    apply Finset.card_le_card_of_injOn f
    · intro a ha
      exact Int.mem_divisors.mpr ⟨⟨t * a.2 + u₂, (hf a ha).symm⟩, hn⟩
    · intro a ha a' ha' he
      have hf₀ : f a' ≠ 0 := by
        intro hz
        exact hn (by simpa only [hz, zero_mul] using (hf a' ha').symm)
      have he₂ : t * a.2 + u₂ = t * a'.2 + u₂ :=
        mul_left_cancel₀ hf₀ ((he ▸ hf a ha).trans (hf a' ha').symm)
      exact Prod.ext
        (mul_left_cancel₀ ht (add_right_cancel he))
        (mul_left_cancel₀ ht (add_right_cancel he₂))
  have hs : n.divisors.card = 2 * n.natAbs.divisors.card := by
    unfold Int.divisors
    rw [Finset.card_disjUnion, Finset.card_map, Finset.card_map]
    omega
  exact hc.trans_eq hs

/-- The largest absolute level allowed by the absolute coordinate and coefficient bounds. -/
def hyperbolaLevelRadius (q : ℕ) (t u₁ u₂ b X₁ X₂ : ℤ) : ℤ :=
  (t * X₁ * X₂ + |u₂| * X₁ + |u₁| * X₂ + |b|) / q

private theorem hyperbola_integer_level_abs_le {q : ℕ} (hq : 0 < q)
    {t u₁ u₂ b X₁ X₂ k : ℤ} {a : ℤ × ℤ}
    (ht : 0 ≤ t) (ha₁ : |a.1| ≤ X₁) (ha₂ : |a.2| ≤ X₂)
    (hk : hyperbolaLevelForm t u₁ u₂ a = b + k * q) :
    |k| ≤ hyperbolaLevelRadius q t u₁ u₂ b X₁ X₂ := by
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  have hL : |hyperbolaLevelForm t u₁ u₂ a| ≤
      t * X₁ * X₂ + |u₂| * X₁ + |u₁| * X₂ := by
    unfold hyperbolaLevelForm
    calc
      _ ≤ |t * a.1 * a.2 + u₂ * a.1| + |u₁ * a.2| :=
        abs_add_le (t * a.1 * a.2 + u₂ * a.1) (u₁ * a.2)
      _ ≤ |t * a.1 * a.2| + |u₂ * a.1| + |u₁ * a.2| := by
        linarith only [abs_add_le (t * a.1 * a.2) (u₂ * a.1)]
      _ ≤ _ := by
        simp only [abs_mul, abs_of_nonneg ht]
        exact add_le_add
          (add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left ha₁ ht) ha₂
            (abs_nonneg _) (mul_nonneg ht ((abs_nonneg _).trans ha₁)))
            (mul_le_mul_of_nonneg_left ha₁ (abs_nonneg _)))
          (mul_le_mul_of_nonneg_left ha₂ (abs_nonneg _))
  have he : k * (q : ℤ) = hyperbolaLevelForm t u₁ u₂ a - b := by linarith only [hk]
  apply (Int.le_ediv_iff_mul_le hq').mpr
  rw [← abs_of_nonneg hq'.le, ← abs_mul, he, sub_eq_add_neg]
  calc
    _ ≤ |hyperbolaLevelForm t u₁ u₂ a| + |-b| := abs_add_le ..
    _ ≤ _ := by rw [abs_neg]; exact add_le_add_left hL _

/-- The literal interval box count is bounded by the sum of signed divisor bounds
over the bounded integer levels. Coordinates are kept as integers throughout. -/
theorem shifted_hyperbola_box_card_le {q : ℕ} (hq : 1 < q)
    {t A₁ A₂ u₁ u₂ b : ℤ} {C : ZMod q} (ht : 0 < t)
    (htq : IsUnit (t : ZMod q)) (hC : IsUnit C)
    (hu₁ : (u₁ : ZMod q) = (t : ZMod q) * A₁)
    (hu₂ : (u₂ : ZMod q) = (t : ZMod q) * A₂)
    (hb : (b : ZMod q) = (t : ZMod q) * (C - (A₁ : ZMod q) * A₂))
    {l₁ r₁ l₂ r₂ X₁ X₂ : ℤ}
    (hl₁ : -X₁ ≤ l₁) (hr₁ : r₁ ≤ X₁) (hl₂ : -X₂ ≤ l₂) (hr₂ : r₂ ≤ X₂) :
    let R := hyperbolaLevelRadius q t u₁ u₂ b X₁ X₂
    (((Finset.Icc l₁ r₁).product (Finset.Icc l₂ r₂)).filter fun a =>
      ((a.1 + A₁ : ℤ) : ZMod q) * ((a.2 + A₂ : ℤ) : ZMod q) = C).card ≤
      ∑ k ∈ Finset.Icc (-R) R, 2 * (hyperbolaLevelProduct q t u₁ u₂ b k).natAbs.divisors.card := by
  let : Fact (1 < q) := ⟨hq⟩
  have hq₀ : (q : ℤ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  let S := ((Finset.Icc l₁ r₁).product (Finset.Icc l₂ r₂)).filter fun a =>
    ((a.1 + A₁ : ℤ) : ZMod q) * ((a.2 + A₂ : ℤ) : ZMod q) = C
  let level (a : ℤ × ℤ) := (hyperbolaLevelForm t u₁ u₂ a - b) / (q : ℤ)
  let R := hyperbolaLevelRadius q t u₁ u₂ b X₁ X₂
  change S.card ≤ ∑ k ∈ Finset.Icc (-R) R,
    2 * (hyperbolaLevelProduct q t u₁ u₂ b k).natAbs.divisors.card
  have hlevel (a : ℤ × ℤ) (ha : a ∈ S) :
      hyperbolaLevelForm t u₁ u₂ a = b + level a * q := by
    obtain ⟨k, hk, _⟩ := (shifted_product_iff_integer_level hq a htq hu₁ hu₂ hb).mp
      (Finset.mem_filter.mp ha).2
    have hl : level a = k :=
      Int.ediv_eq_of_eq_mul_left hq₀ (by linarith only [hk])
    simpa only [hl] using hk
  have hmaps : (S : Set (ℤ × ℤ)).MapsTo level (Finset.Icc (-R) R) := by
    intro a ha
    have hab := Finset.mem_product.mp (Finset.mem_filter.mp ha).1
    have ha₁ := Finset.mem_Icc.mp hab.1
    have ha₂ := Finset.mem_Icc.mp hab.2
    have h₁ : |a.1| ≤ X₁ := abs_le.mpr ⟨hl₁.trans ha₁.1, ha₁.2.trans hr₁⟩
    have h₂ : |a.2| ≤ X₂ := abs_le.mpr ⟨hl₂.trans ha₂.1, ha₂.2.trans hr₂⟩
    exact Finset.mem_Icc.mpr (abs_le.mp
      (hyperbola_integer_level_abs_le (by omega : 0 < q) ht.le h₁ h₂ (hlevel a ha)))
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_le_sum
  intro k _
  have hn : hyperbolaLevelProduct q t u₁ u₂ b k ≠ 0 := by
    intro hz
    have hu := (hyperbola_level_product_unit k htq hC hu₁ hu₂ hb).2
    exact hu.ne_zero (by simp only [hz, Int.cast_zero])
  apply hyperbola_level_card_le ht.ne' hn
  intro a ha
  obtain ⟨haS, hka⟩ := Finset.mem_filter.mp ha
  simpa only [hka] using hlevel a haS

/-- The residue-field readout of a value in the prime-square ring. -/
def primeSquareReduction (p : ℕ) : ZMod (p ^ 2) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)

private theorem primeSquare_isUnit_iff {p : ℕ} (hp : p.Prime) (v : ZMod (p ^ 2)) :
    IsUnit v ↔ primeSquareReduction p v ≠ 0 := by
  let : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective v
  rw [map_natCast, ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide : 0 < 2),
    ne_eq, ZMod.natCast_eq_zero_iff]

/-- The actual cubic equation factors over the prime-square ring. The two
pair-sum masks force the right side to be a unit. -/
theorem middle_word_unit_hyperbola {p : ℕ} (hp : p.Prime) {d z x₁ x₂ : ZMod (p ^ 2)}
    (hword : x₁ + x₂ + z = d * x₁ * x₂ * z)
    (h₁ : primeSquareReduction p (x₁ + z) ≠ 0)
    (h₂ : primeSquareReduction p (x₂ + z) ≠ 0) :
    (d * z * x₁ - 1) * (d * z * x₂ - 1) = 1 + d * z^2 ∧
      IsUnit (1 + d * z^2) := by
  have hfactor : (d * z * x₁ - 1) * (d * z * x₂ - 1) = 1 + d * z^2 := by
    linear_combination -d * z * hword
  refine ⟨hfactor, (primeSquare_isUnit_iff hp _).mpr ?_⟩
  let : Fact p.Prime := ⟨hp⟩
  let r := primeSquareReduction p
  change r (1 + d * z^2) ≠ 0
  intro hz
  have hz' : 1 + r d * (r z)^2 = 0 := by simpa only [map_add, map_one, map_mul, map_pow] using hz
  have hprod : (r d * r z * r x₁ - 1) * (r d * r z * r x₂ - 1) = 0 := by
    simpa only [map_mul, map_sub, map_one, hz] using congrArg r hfactor
  have hs (x : ZMod (p ^ 2)) (hx : r d * r z * r x - 1 = 0) : r (x + z) = 0 := by
    rw [map_add]
    linear_combination r x * hz' - r z * hx
  rcases mul_eq_zero.mp hprod with h | h
  · exact h₁ (hs x₁ h)
  · exact h₂ (hs x₂ h)

private theorem residue_bin_lt {q P : ℕ} (hq : 0 < (q : ℤ)) {s r : ℤ}
    (he : s * (P : ℤ) / q = r * (P : ℤ) / q) :
    |s - r| * (P : ℤ) < q := by
  let j := s * (P : ℤ) / q
  have hs₁ : j * (q : ℤ) ≤ s * (P : ℤ) := Int.ediv_mul_le _ hq.ne'
  have hs₂ : s * (P : ℤ) < (j + 1) * (q : ℤ) :=
    (Int.ediv_lt_iff_lt_mul hq).mp (by change j < j + 1; omega)
  have hr₁ : j * (q : ℤ) ≤ r * (P : ℤ) := by
    change (s * (P : ℤ) / q) * (q : ℤ) ≤ _
    rw [he]
    exact Int.ediv_mul_le _ hq.ne'
  have hr₂ : r * (P : ℤ) < (j + 1) * (q : ℤ) := by
    apply (Int.ediv_lt_iff_lt_mul hq).mp
    rw [← he]
    change j < j + 1
    omega
  rw [← abs_of_nonneg (Int.natCast_nonneg P), ← abs_mul, abs_lt, sub_mul]
  rw [add_mul, one_mul] at hs₂ hr₂
  constructor <;> linarith only [hs₁, hs₂, hr₁, hr₂]

/-- Two residues can be made small by a common positive multiplier below the
prime. The signed representatives are differences of two residues in the same bins. -/
theorem prime_square_simultaneous_approximation {p P₁ P₂ : ℕ} (hp : p.Prime)
    (hP₁ : 0 < P₁) (hP₂ : 0 < P₂) (hP : P₁ * P₂ < p) (A₁ A₂ : ℤ) :
    ∃ t u₁ u₂ : ℤ, 0 < t ∧ t ≤ (P₁ * P₂ : ℕ) ∧ IsUnit (t : ZMod (p ^ 2)) ∧
      (u₁ : ZMod (p ^ 2)) = (t : ZMod (p ^ 2)) * A₁ ∧
      (u₂ : ZMod (p ^ 2)) = (t : ZMod (p ^ 2)) * A₂ ∧
      |u₁| * (P₁ : ℤ) < (p ^ 2 : ℕ) ∧ |u₂| * (P₂ : ℤ) < (p ^ 2 : ℕ) := by
  let q := p ^ 2
  have hq : 0 < (q : ℤ) := by exact_mod_cast (pow_pos hp.pos 2)
  let residue (A : ℤ) (i : ℕ) := ((i : ℤ) * A) % (q : ℤ)
  let bin (A : ℤ) (P i : ℕ) := residue A i * (P : ℤ) / (q : ℤ)
  let bins (i : ℕ) := (bin A₁ P₁ i, bin A₂ P₂ i)
  let indices := Finset.range (P₁ * P₂ + 1)
  let cells := (Finset.Ico (0 : ℤ) (P₁ : ℤ)).product (Finset.Ico (0 : ℤ) (P₂ : ℤ))
  have hresidue (A : ℤ) (i : ℕ) : 0 ≤ residue A i ∧ residue A i < (q : ℤ) :=
    ⟨Int.emod_nonneg _ hq.ne', Int.emod_lt_of_pos _ hq⟩
  have hbin (A : ℤ) {P : ℕ} (hP' : 0 < P) (i : ℕ) :
      bin A P i ∈ Finset.Ico (0 : ℤ) (P : ℤ) := by
    have hP'' : (0 : ℤ) < P := by exact_mod_cast hP'
    refine Finset.mem_Ico.mpr ⟨Int.ediv_nonneg (mul_nonneg (hresidue A i).1 hP''.le) hq.le, ?_⟩
    apply (Int.ediv_lt_iff_lt_mul hq).mpr
    rw [mul_comm (P : ℤ)]
    exact mul_lt_mul_of_pos_right (hresidue A i).2 hP''
  have hcard : cells.card < indices.card := by
    simp [cells, indices, Finset.card_product, Int.card_Ico]
  have hmaps : (indices : Set ℕ).MapsTo bins cells := by
    intro i _
    exact Finset.mem_product.mpr ⟨hbin A₁ hP₁ i, hbin A₂ hP₂ i⟩
  obtain ⟨i, hi, j, hj, hij, he⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  have ordered : ∃ x ∈ indices, ∃ y ∈ indices, x < y ∧ bins x = bins y := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i, hi, j, hj, h, he⟩
    · exact ⟨j, hj, i, hi, h, he.symm⟩
  obtain ⟨x, hx, y, hy, hxy, hbins⟩ := ordered
  let t := (y : ℤ) - (x : ℤ)
  have hty : y ≤ P₁ * P₂ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hy)
  have ht : 0 < t := by dsimp [t]; omega
  have htP : t ≤ (P₁ * P₂ : ℕ) := by dsimp [t]; omega
  have htp : t.toNat < p := by omega
  have htq : IsUnit (t : ZMod (p ^ 2)) := by
    rw [← Int.toNat_of_nonneg ht.le, Int.cast_natCast]
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide : 0 < 2)).mpr
      (fun hd => (not_le_of_gt htp) (Nat.le_of_dvd (by omega) hd))
  have hcast (A : ℤ) (i : ℕ) : (residue A i : ZMod q) = (i : ZMod q) * A := by
    rw [← Int.cast_natCast i, ← Int.cast_mul]
    exact (ZMod.intCast_eq_intCast_iff' _ _ q).mpr (Int.emod_emod _ _)
  refine ⟨t, residue A₁ y - residue A₁ x, residue A₂ y - residue A₂ x, ht, htP, htq, ?_, ?_, ?_, ?_⟩
  · change ((residue A₁ y - residue A₁ x : ℤ) : ZMod q) = (t : ZMod q) * A₁
    simp only [Int.cast_sub, hcast, t, Int.cast_natCast, sub_mul]
  · change ((residue A₂ y - residue A₂ x : ℤ) : ZMod q) = (t : ZMod q) * A₂
    simp only [Int.cast_sub, hcast, t, Int.cast_natCast, sub_mul]
  · exact residue_bin_lt hq (congrArg Prod.fst hbins.symm)
  · exact residue_bin_lt hq (congrArg Prod.snd hbins.symm)

/-- Substituting the two affine endpoint coordinates from a common unit basis
vector turns the cubic into the shifted hyperbola on the integer coefficients. -/
theorem middle_word_affine_shifted_hyperbola {p : ℕ} (hp : p.Prime)
    {d z E : ZMod (p ^ 2)} (v₁ v₂ : ZMod (p ^ 2))
    (hdz : IsUnit (d * z)) (hE : IsUnit E) :
    ∃ (A₁ A₂ : ℤ) (C : ZMod (p ^ 2)), (d * z * E)^2 * C = 1 + d * z^2 ∧
      ∀ a : ℤ × ℤ,
        let x₁ := E * (a.1 : ZMod (p ^ 2)) + v₁
        let x₂ := E * (a.2 : ZMod (p ^ 2)) + v₂
        x₁ + x₂ + z = d * x₁ * x₂ * z ↔
          ((a.1 + A₁ : ℤ) : ZMod (p ^ 2)) * ((a.2 + A₂ : ℤ) : ZMod (p ^ 2)) = C := by
  let : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let α := d * z * E
  have hα : IsUnit α := hdz.mul hE
  have hinv := ZMod.mul_inv_of_unit α hα
  let C := (α⁻¹)^2 * (1 + d * z^2)
  have hC : α^2 * C = 1 + d * z^2 := by
    rw [show C = (α⁻¹)^2 * (1 + d * z^2) from rfl,
      ← mul_assoc, ← mul_pow, hinv, one_pow, one_mul]
  obtain ⟨s₁, hs₁⟩ := ZMod.natCast_zmod_surjective (α⁻¹ * (d * z * v₁ - 1))
  obtain ⟨s₂, hs₂⟩ := ZMod.natCast_zmod_surjective (α⁻¹ * (d * z * v₂ - 1))
  refine ⟨s₁, s₂, C, hC, ?_⟩
  have hshift (a : ℤ) (s : ℕ) (v : ZMod (p ^ 2))
      (hs : (s : ZMod (p ^ 2)) = α⁻¹ * (d * z * v - 1)) :
      α * ((a + (s : ℤ) : ℤ) : ZMod (p ^ 2)) =
        d * z * (E * (a : ZMod (p ^ 2)) + v) - 1 := by
    rw [Int.cast_add, Int.cast_natCast, mul_add, hs, ← mul_assoc α, hinv, one_mul]
    dsimp [α]
    ring
  intro a
  let x₁ := E * (a.1 : ZMod (p ^ 2)) + v₁
  let x₂ := E * (a.2 : ZMod (p ^ 2)) + v₂
  let y₁ := ((a.1 + (s₁ : ℤ) : ℤ) : ZMod (p ^ 2))
  let y₂ := ((a.2 + (s₂ : ℤ) : ℤ) : ZMod (p ^ 2))
  change x₁ + x₂ + z = d * x₁ * x₂ * z ↔ y₁ * y₂ = C
  have hprod : α^2 * (y₁ * y₂) = (d * z * x₁ - 1) * (d * z * x₂ - 1) := by
    rw [show α^2 * (y₁ * y₂) = (α * y₁) * (α * y₂) by ring]
    exact congrArg₂ (· * ·) (hshift a.1 s₁ v₁ hs₁) (hshift a.2 s₂ v₂ hs₂)
  constructor
  · intro hword
    apply (hα.pow 2).mul_left_cancel
    rw [hprod, hC]
    linear_combination -d * z * hword
  · intro h
    have he : (d * z * x₁ - 1) * (d * z * x₂ - 1) = 1 + d * z^2 := by
      rw [← hprod, h, hC]
    have hz : (d * z) * (x₁ + x₂ + z - d * x₁ * x₂ * z) = 0 := by
      linear_combination -he
    exact sub_eq_zero.mp (hdz.mul_left_cancel (hz.trans (mul_zero _).symm))

/-- The masked cubic in a literal affine box satisfies the divisor sum bound
with the common multiplier and coefficient bounds supplied by pigeonholing. -/
theorem middle_word_affine_box_card_le {p P₁ P₂ : ℕ} (hp : p.Prime)
    (hP₁ : 0 < P₁) (hP₂ : 0 < P₂) (hP : P₁ * P₂ < p)
    {d z E : ZMod (p ^ 2)} (v₁ v₂ : ZMod (p ^ 2))
    (hdz : IsUnit (d * z)) (hE : IsUnit E)
    {l₁ r₁ l₂ r₂ X₁ X₂ : ℤ}
    (hl₁ : -X₁ ≤ l₁) (hr₁ : r₁ ≤ X₁) (hl₂ : -X₂ ≤ l₂) (hr₂ : r₂ ≤ X₂) :
    let S := ((Finset.Icc l₁ r₁).product (Finset.Icc l₂ r₂)).filter fun a =>
      let x₁ := E * (a.1 : ZMod (p ^ 2)) + v₁
      let x₂ := E * (a.2 : ZMod (p ^ 2)) + v₂
      primeSquareReduction p (x₁ + z) ≠ 0 ∧ primeSquareReduction p (x₂ + z) ≠ 0 ∧
        x₁ + x₂ + z = d * x₁ * x₂ * z
    ∃ t u₁ u₂ b : ℤ, 0 < t ∧ t ≤ (P₁ * P₂ : ℕ) ∧ IsUnit (t : ZMod (p ^ 2)) ∧
      |u₁| * (P₁ : ℤ) < (p ^ 2 : ℕ) ∧ |u₂| * (P₂ : ℤ) < (p ^ 2 : ℕ) ∧
      0 ≤ b ∧ b < (p ^ 2 : ℕ) ∧
      (let R := hyperbolaLevelRadius (p ^ 2) t u₁ u₂ b X₁ X₂
       S.card ≤ ∑ k ∈ Finset.Icc (-R) R,
         2 * (hyperbolaLevelProduct (p ^ 2) t u₁ u₂ b k).natAbs.divisors.card) := by
  intro S
  let : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hq : 1 < p ^ 2 := one_lt_pow₀ hp.one_lt (by decide)
  obtain ⟨A₁, A₂, C, hC, hequiv⟩ := middle_word_affine_shifted_hyperbola hp v₁ v₂ hdz hE
  obtain ⟨t, u₁, u₂, ht, htP, htq, hu₁, hu₂, hu₁P, hu₂P⟩ :=
    prime_square_simultaneous_approximation hp hP₁ hP₂ hP A₁ A₂
  let B := (t : ZMod (p ^ 2)) * (C - (A₁ : ZMod (p ^ 2)) * A₂)
  let b : ℤ := B.val
  have hb : (b : ZMod (p ^ 2)) = B := by
    simp only [b, Int.cast_natCast, ZMod.natCast_zmod_val]
  refine ⟨t, u₁, u₂, b, ht, htP, htq, hu₁P, hu₂P, Int.natCast_nonneg _, ?_, ?_⟩
  · change (B.val : ℤ) < (p ^ 2 : ℕ)
    exact_mod_cast B.val_lt
  by_cases hne : S.Nonempty
  · obtain ⟨a, ha⟩ := hne
    obtain ⟨h₁, h₂, hword⟩ := (Finset.mem_filter.mp ha).2
    have hunit := (middle_word_unit_hyperbola hp hword h₁ h₂).2
    rw [← hC] at hunit
    have hunitC : IsUnit C := isUnit_of_mul_isUnit_right hunit
    refine (Finset.card_le_card ?_).trans
      (shifted_hyperbola_box_card_le hq ht htq hunitC hu₁ hu₂ hb hl₁ hr₁ hl₂ hr₂)
    intro a ha
    have h := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr ⟨h.1, (hequiv a).mp h.2.2.2⟩
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.zero_le]

end

end D5.S3.Arith.CharacterSums.Original
