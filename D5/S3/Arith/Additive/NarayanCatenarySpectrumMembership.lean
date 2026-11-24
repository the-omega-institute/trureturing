/- GID: D5/S3/Arith/Additive/NarayanCatenarySpectrumMembership
   generality: I
   mirror-B: D5/B/S3/Arith/Additive/NarayanCatenarySpectrumMembership
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The original atom tuple realizes Narayan's catenary threshold. -/

import D5.S3.Arith.Additive.NarayanExpandedGeneratorDeltaRefutation
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic.Ring

/-! # Catenary spectrum membership for generalized arithmetic generators -/

namespace D5.S3.Arith.Additive.NarayanCatenarySpectrumMembership

set_option autoImplicit false

open NarayanExpandedGeneratorDeltaRefutation (Z)

/-- The atom coordinates are indexed by zero through k. -/
def generators (a h d k : ℕ) (i : Fin (k + 1)) : ℕ :=
  if i = 0 then a else a * h + i.val * d

private def weight {p : ℕ} (g z : Fin p → ℕ) : ℕ := ∑ i, z i * g i

private theorem weight_add {p : ℕ} (g z w : Fin p → ℕ) :
    weight g (z + w) = weight g z + weight g w := by
  simp [weight, Pi.add_apply, Nat.add_mul, Finset.sum_add_distrib]

private theorem weight_basis {p : ℕ} (g : Fin p → ℕ) (i : Fin p) (m : ℕ) :
    weight g (Pi.single i m) = m * g i := by
  classical
  unfold weight
  rw [Fintype.sum_eq_single i]
  · simp
  · intro j hji
    simp [Pi.single_eq_of_ne hji]

private theorem weight_congr_mod {a d u v W I : ℕ} (cop : a.Coprime d)
    (he : a * u + W * d = a * v + I * d) : W ≡ I [MOD a] := by
  apply Nat.ModEq.cancel_right_of_coprime cop
  have heq : a * u + W * d ≡ a * v + I * d [MOD a] := he ▸ Nat.ModEq.refl _
  exact (Nat.modulus_mul_add_modEq_iff.mp (Nat.modulus_mul_add_modEq_iff.mp heq).symm).symm

private theorem residue_decomposition {a W I : ℕ} (hi : I < a) (hm : W ≡ I [MOD a]) :
    W = I + a * (W / a) := by
  change W % a = I % a at hm
  rw [Nat.mod_eq_of_lt hi] at hm
  simpa only [hm] using (Nat.mod_add_div W a).symm

private def count {k : ℕ} (z : Fin (k + 1) → ℕ) : ℕ := ∑ i : Fin k, z i.succ

private def indexWeight {k : ℕ} (z : Fin (k + 1) → ℕ) : ℕ :=
  weight (fun i => i.val) z

private theorem indexWeight_tail {k : ℕ} (z : Fin (k + 1) → ℕ) :
    indexWeight z = ∑ i : Fin k, z i.succ * (i.val + 1) := by
  simp [indexWeight, weight, Fin.sum_univ_succ]

private theorem count_le_indexWeight {k : ℕ} (z : Fin (k + 1) → ℕ) :
    count z ≤ indexWeight z := by
  rw [indexWeight_tail]
  exact Finset.sum_le_sum (fun i _ => Nat.le_mul_of_pos_right _ (Nat.succ_pos i.val))

private theorem indexWeight_le_mul_count {k : ℕ} (z : Fin (k + 1) → ℕ) :
    indexWeight z ≤ k * count z := by
  rw [indexWeight_tail, count, Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left (z i.succ) i.isLt)

private theorem value_formula {a h d k : ℕ} (z : Fin (k + 1) → ℕ) :
    weight (generators a h d k) z = a * (z 0 + h * count z) + indexWeight z * d := by
  rw [weight, Fin.sum_univ_succ, indexWeight_tail, count, Nat.mul_add, ← Nat.mul_assoc,
    Finset.mul_sum, Finset.sum_mul, Nat.add_assoc, ← Finset.sum_add_distrib]
  simp only [generators, Fin.succ_ne_zero, ite_false, Fin.val_succ]
  rw [Nat.mul_comm a (z 0)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem count_add {k : ℕ} (z w : Fin (k + 1) → ℕ) :
    count (z + w) = count z + count w := by
  simp [count, Pi.add_apply, Finset.sum_add_distrib]

private theorem count_basis_zero {k : ℕ} (m : ℕ) :
    count (Pi.single (0 : Fin (k + 1)) m) = 0 := by
  simp [count, Pi.single_eq_of_ne, Fin.succ_ne_zero]

private theorem count_basis_succ {k : ℕ} (i : Fin k) (m : ℕ) :
    count (Pi.single i.succ m) = m := by
  classical
  unfold count
  rw [Fintype.sum_eq_single i]
  · simp
  · intro j hj
    exact Pi.single_eq_of_ne (by simpa using hj) _

private theorem sum_coordinates {k : ℕ} (z : Fin (k + 1) → ℕ) :
    (∑ i, z i) = z 0 + count z := Fin.sum_univ_succ z

private theorem coordinate_le_sum {p : ℕ} (z : Fin p → ℕ) (i : Fin p) :
    z i ≤ ∑ j, z j :=
  Finset.single_le_sum (fun j _ => Nat.zero_le (z j)) (Finset.mem_univ i)

/-- Membership of the generated additive submonoid coincides with existence in the source fiber. -/
private theorem closure_iff_fiber {p : ℕ} (g : Fin p → ℕ) (n : ℕ) :
    n ∈ AddSubmonoid.closure (Set.range g) ↔ (Z g n).Nonempty := by
  constructor
  · intro hn
    induction hn using AddSubmonoid.closure_induction with
    | mem m hm =>
      obtain ⟨i, rfl⟩ := hm
      exact ⟨Pi.single i 1, by change weight g (Pi.single i 1) = g i; simp [weight_basis]⟩
    | zero => exact ⟨0, by change weight g 0 = 0; simp [weight]⟩
    | add m n _ _ hm hn =>
      obtain ⟨z, hz⟩ := hm
      obtain ⟨w, hw⟩ := hn
      change weight g z = m at hz
      change weight g w = n at hw
      exact ⟨z + w, by change weight g (z + w) = m + n; rw [weight_add, hz, hw]⟩
  · rintro ⟨z, hz⟩
    change weight g z = n at hz
    rw [← hz, weight]
    apply AddSubmonoid.sum_mem
    intro i _
    simpa [nsmul_eq_mul] using
      (AddSubmonoid.closure (Set.range g)).nsmul_mem (AddSubmonoid.subset_closure
        (Set.mem_range_self i)) (z i)

/-- A nonzero element is an atom when any decomposition in the monoid has a zero summand. -/
def IsAtom (S : AddSubmonoid ℕ) (n : ℕ) : Prop :=
  n ∈ S ∧ n ≠ 0 ∧ ∀ u ∈ S, ∀ v ∈ S, u + v = n → u = 0 ∨ v = 0

/-- The literal residual-coordinate distance from the catenary definition. -/
def distance {p : ℕ} (z w : Fin p → ℕ) : ℕ :=
  max (∑ i, (z i - min (z i) (w i))) (∑ i, (w i - min (z i) (w i)))

/-- Reachability by a finite chain of bounded-distance edges in the source fiber. -/
def Chain {p : ℕ} (g : Fin p → ℕ) (n B : ℕ) (z w : Z g n) : Prop :=
  Relation.ReflTransGen (fun u v : Z g n => distance u.val v.val ≤ B) z w

/-- The least threshold is expressed directly by connectivity and minimality. -/
def catenarySpectrum {p : ℕ} (g : Fin p → ℕ) : Set ℕ :=
  {N | ∃ (n : ℕ), (Z g n).Nonempty ∧
    IsLeast {B | ∀ z w : Z g n, Chain g n B z w} N}

/-- The ceiling in Conjecture 18.2. -/
def ceilParameter (a k : ℕ) : ℕ := (a - k) ⌈/⌉ (k - 1)

/-- The element attaining the threshold in Conjecture 18.2. -/
def witness (a h d k : ℕ) : ℕ :=
  a * (h * (ceilParameter a k + 1)) + (a + ceilParameter a k) * d

/-- The short-index-weight class in the witnessed fiber. -/
def Low {k : ℕ} (h d t : ℕ) (z : Fin (k + 1) → ℕ) : Prop :=
  indexWeight z = t ∧ z 0 = h * (t + 1 - count z) + d

/-- The long-index-weight class in the witnessed fiber. -/
def High {k : ℕ} (a t : ℕ) (z : Fin (k + 1) → ℕ) : Prop :=
  indexWeight z = a + t ∧ count z = t + 1 ∧ z 0 = 0


private theorem parameter_bounds {a k : ℕ} (hk : 1 < k) (hka : k < a) :
    let t := ceilParameter a k
    let ρ := (a - 2) % (k - 1)
    0 < t ∧ t < a ∧ 2 + ρ ≤ k ∧ k * t + (2 + ρ) = a + t := by
  dsimp only
  have ht : ceilParameter a k = (a - 2) / (k - 1) := by
    rw [ceilParameter, Nat.ceilDiv_eq_add_pred_div, show a - k + (k - 1) - 1 = a - 2 by omega]
  set t := ceilParameter a k
  set ρ := (a - 2) % (k - 1)
  have hρ : ρ < k - 1 := Nat.mod_lt _ (by omega)
  have hdecomp : ρ + (k - 1) * t = a - 2 := by
    rw [ht, Nat.mod_add_div]
  have htpos : 0 < t := by
    rw [ht]
    exact Nat.div_pos (by omega) (by omega)
  have htbound : t < a := by
    rw [ht]
    exact (Nat.div_le_self _ _).trans_lt (by omega)
  have hkt : (k - 1) * t + t = k * t := by
    rw [← Nat.add_one_mul, show k - 1 + 1 = k by omega]
  exact ⟨htpos, htbound, by omega, by omega⟩

private theorem fiber_iff_classes {a h d k : ℕ} (hk : 1 < k) (hka : k < a)
    (hh : 0 < h) (hd : 0 < d) (cop : a.Coprime d) (z : Fin (k + 1) → ℕ) :
    let t := ceilParameter a k
    z ∈ Z (generators a h d k) (witness a h d k) ↔ Low h d t z ∨ High a t z := by
  dsimp only
  set t := ceilParameter a k
  obtain ⟨_, hta, _, htρ⟩ := parameter_bounds hk hka
  change k * t + (2 + (a - 2) % (k - 1)) = a + t at htρ
  have hkt : k * t < a + t := by omega
  have hYW := count_le_indexWeight z
  have hWY := indexWeight_le_mul_count z
  change weight (generators a h d k) z = witness a h d k ↔ _
  rw [value_formula]
  change a * (z 0 + h * count z) + indexWeight z * d =
    a * (h * (t + 1)) + (a + t) * d ↔ _
  constructor
  · intro he
    have he' : a * (z 0 + h * count z) + indexWeight z * d =
        a * (h * (t + 1) + d) + t * d := by rw [he]; ring
    have hres := residue_decomposition hta (weight_congr_mod cop he')
    set q := indexWeight z / a
    change indexWeight z = t + a * q at hres
    by_cases hq : q = 0
    · have hW : indexWeight z = t := by simpa [hq] using hres
      rw [hW, Nat.add_left_inj] at he'
      have hx : z 0 + h * count z = h * (t + 1) + d :=
        Nat.eq_of_mul_eq_mul_left (by omega) he'
      have hY : count z ≤ t + 1 := by omega
      have hsplit : h * (t + 1 - count z) + h * count z = h * (t + 1) := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hY]
      exact Or.inl ⟨hW, by omega⟩
    · have hWmin : a + t ≤ indexWeight z := by
        have := Nat.mul_le_mul_left a (Nat.pos_of_ne_zero hq)
        rw [Nat.mul_one] at this
        omega
      have hprod := Nat.mul_le_mul_right d hWmin
      have hx : z 0 + h * count z ≤ h * (t + 1) := by
        exact Nat.le_of_mul_le_mul_left (c := a) (by omega) (by omega)
      have hY : count z ≤ t + 1 := by
        exact Nat.le_of_mul_le_mul_left (by omega) hh
      have hYeq : count z = t + 1 := by
        by_contra hn
        have hYle : count z ≤ t := by omega
        have := Nat.mul_le_mul_left k hYle
        omega
      have hx0 : z 0 = 0 := by rw [hYeq] at hx; omega
      have hWeq : indexWeight z = a + t := by
        rw [hx0, hYeq, zero_add, Nat.add_right_inj] at he
        exact Nat.eq_of_mul_eq_mul_right hd he
      exact Or.inr ⟨hWeq, hYeq, hx0⟩
  · rintro (⟨hW, hx⟩ | ⟨hW, hY, hx⟩)
    · have hY : count z ≤ t + 1 := by omega
      have hsplit : h * (t + 1 - count z) + h * count z = h * (t + 1) := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hY]
      rw [hW, hx, Nat.add_right_comm, hsplit]
      ring
    · rw [hW, hY, hx, zero_add]

private def first {k : ℕ} (hk : 0 < k) : Fin (k + 1) := (⟨0, hk⟩ : Fin k).succ

private theorem first_ne_zero {k : ℕ} (hk : 0 < k) : first hk ≠ 0 :=
  Fin.succ_ne_zero _

private def lowVector {k : ℕ} (hk : 0 < k) (h d t : ℕ) : Fin (k + 1) → ℕ :=
  Pi.single 0 (h + d) + Pi.single (first hk) t

private theorem lowVector_low {k : ℕ} (hk : 0 < k) (h d t : ℕ) :
    Low h d t (lowVector hk h d t) := by
  have hY : count (lowVector hk h d t) = t := by
    rw [lowVector, count_add, count_basis_zero, zero_add]
    exact count_basis_succ _ _
  constructor
  · simp [lowVector, indexWeight, weight_add, weight_basis, first, Fin.val_succ]
  · rw [hY, show t + 1 - t = 1 by omega, Nat.mul_one]
    simp [lowVector, Pi.add_apply, Pi.single_eq_of_ne (first_ne_zero hk).symm]

private theorem high_inhabited {a h d k : ℕ} (hk : 1 < k) (hka : k < a)
    (hh : 0 < h) (hd : 0 < d) (cop : a.Coprime d) :
    ∃ z : Z (generators a h d k) (witness a h d k), High a (ceilParameter a k) z.val := by
  set t := ceilParameter a k
  set ρ := (a - 2) % (k - 1)
  obtain ⟨_, _, hρ, htρ⟩ := parameter_bounds hk hka
  change 2 + ρ ≤ k at hρ
  change k * t + (2 + ρ) = a + t at htρ
  let i : Fin k := ⟨k - 1, by omega⟩
  let j : Fin k := ⟨1 + ρ, by omega⟩
  let z := Pi.single (M := fun _ => ℕ) i.succ t + Pi.single j.succ 1
  have hz : High a t z := by
    refine ⟨?_, ?_, ?_⟩
    · have hi : i.succ.val = k := by dsimp [i]; omega
      have hj : j.succ.val = 2 + ρ := by dsimp [j]; omega
      simp only [z, indexWeight, weight_add, weight_basis, hi, hj, Nat.one_mul]
      rw [Nat.mul_comm t, htρ]
    · simp [z, count_add, count_basis_succ]
    · simp [z, Pi.add_apply, Pi.single_eq_of_ne (Fin.succ_ne_zero _).symm]
  exact ⟨⟨z, (fiber_iff_classes hk hka hh hd cop z).2 (Or.inr hz)⟩, hz⟩


private def excess {k : ℕ} (z : Fin (k + 1) → ℕ) : ℕ :=
  ∑ i : Fin k, z i.succ * i.val

private theorem indexWeight_eq_count_add_excess {k : ℕ} (z : Fin (k + 1) → ℕ) :
    indexWeight z = count z + excess z := by
  simp only [indexWeight_tail, Nat.mul_add, Nat.mul_one, Finset.sum_add_distrib, count,
    excess, Nat.add_comm]

private theorem high_first_zero {a k : ℕ} (hk : 1 < k) (hka : k < a)
    {z : Fin (k + 1) → ℕ} (hz : High a (ceilParameter a k) z) :
    z (first (by omega)) = 0 := by
  set t := ceilParameter a k
  obtain ⟨_, _, _, htr⟩ := parameter_bounds hk hka
  change k * t + (2 + (a - 2) % (k - 1)) = a + t at htr
  let i0 : Fin k := ⟨0, by omega⟩
  let deficit := fun i : Fin k => z i.succ * (k - (i.val + 1))
  have hsum : indexWeight z + (∑ i, deficit i) = k * count z := by
    rw [indexWeight_tail, count, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [deficit]
    rw [← Nat.mul_add, Nat.add_sub_of_le i.isLt, Nat.mul_comm]
  have hdef : (∑ i, deficit i) < k - 1 := by
    rw [hz.1, hz.2.1, Nat.mul_add, Nat.mul_one] at hsum
    omega
  have hi0 : deficit i0 ≤ ∑ i, deficit i := coordinate_le_sum deficit i0
  change z (first (by omega)) * (k - 1) ≤ _ at hi0
  by_contra hn
  have hone : 1 ≤ z (first (by omega)) := by omega
  have := Nat.mul_le_mul_right (k - 1) hone
  rw [Nat.one_mul] at this
  omega

private theorem low_length {k h d t : ℕ} {z : Fin (k + 1) → ℕ}
    (hh : 0 < h) (hz : Low h d t z) :
    (∑ i, z i) = t + h + d + (h - 1) * (t - count z) := by
  have hY : count z ≤ t := (count_le_indexWeight z).trans_eq hz.1
  have hsplit : t + 1 - count z = (t - count z) + 1 := by omega
  have hmul : h * (t - count z) = (h - 1) * (t - count z) + (t - count z) := by
    rw [← Nat.add_one_mul, Nat.sub_add_cancel hh]
  rw [sum_coordinates, hz.2, hsplit, Nat.mul_add, Nat.mul_one, hmul]
  omega

private theorem residual_add_common {p : ℕ} (z w : Fin p → ℕ) :
    (∑ i, (z i - min (z i) (w i))) + (∑ i, min (z i) (w i)) = ∑ i, z i := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact Nat.sub_add_cancel (min_le_left _ _)

private theorem cross_distance {a h d k : ℕ} (hk : 1 < k) (hka : k < a) (hh : 1 < h)
    {z w : Fin (k + 1) → ℕ} (hz : Low h d (ceilParameter a k) z)
    (hw : High a (ceilParameter a k) w) : ceilParameter a k + h + d ≤ distance z w := by
  set t := ceilParameter a k
  have hw0 := hw.2.2
  have hw1 := high_first_zero hk hka hw
  have hcommon : (∑ i, min (z i) (w i)) ≤ excess z := by
    rw [Fin.sum_univ_succ, hw0, min_zero, zero_add, excess]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : i.val = 0
    · have hfirst : i.succ = first (by omega) := by
        apply Fin.ext
        simpa [first, Fin.val_succ] using hi
      rw [hfirst, hw1, min_zero]
      exact Nat.zero_le _
    · exact (min_le_left _ _).trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hi))
  have hexcess : excess z = t - count z := by
    have he := indexWeight_eq_count_add_excess z
    rw [hz.1] at he
    omega
  have hmul := Nat.le_mul_of_pos_left (t - count z) (show 0 < h - 1 by omega)
  have htotal := low_length (show 0 < h by omega) hz
  have hres := residual_add_common z w
  exact (show t + h + d ≤ ∑ i, (z i - min (z i) (w i)) by omega).trans (le_max_left _ _)

private theorem distance_symm {p : ℕ} (z w : Fin p → ℕ) : distance z w = distance w z := by
  simp only [distance, min_comm (w _) (z _), max_comm]

private theorem distance_le_lengths {p : ℕ} (z w : Fin p → ℕ) :
    distance z w ≤ max (∑ i, z i) (∑ i, w i) := by
  apply max_le
  · exact (Finset.sum_le_sum (fun _ _ => Nat.sub_le _ _)).trans (le_max_left _ _)
  · exact (Finset.sum_le_sum (fun _ _ => Nat.sub_le _ _)).trans (le_max_right _ _)


private theorem generators_pos {a h d k : ℕ} (ha : 0 < a) (hh : 0 < h) :
    ∀ i : Fin (k + 1), 0 < generators a h d k i := by
  intro i
  unfold generators
  split
  · exact ha
  · exact Nat.add_pos_left (Nat.mul_pos ha hh) _

private theorem generators_injective {a h d k : ℕ} (ha : 0 < a) (hh : 1 < h)
    (hd : 0 < d) : Function.Injective (generators a h d k) := by
  intro i j hij
  have hlarge : a < a * h := by
    simpa using Nat.mul_lt_mul_of_pos_left hh ha
  by_cases hi : i = 0 <;> by_cases hj : j = 0
  · exact hi.trans hj.symm
  · simp only [generators, hi, hj, ite_eq_left, ite_false] at hij
    omega
  · simp only [generators, hi, hj, ite_eq_left, ite_false] at hij
    omega
  · simp only [generators, hi, hj, ite_false, Nat.add_right_inj] at hij
    exact Fin.ext (Nat.eq_of_mul_eq_mul_right hd hij)

private theorem generator_length {a h d k : ℕ} (hka : k < a) (hh : 1 < h)
    (cop : a.Coprime d) (i : Fin (k + 1)) {z : Fin (k + 1) → ℕ}
    (hz : z ∈ Z (generators a h d k) (generators a h d k i)) :
    (∑ j, z j) = 1 := by
  have ha : 0 < a := by omega
  change weight (generators a h d k) z = generators a h d k i at hz
  rw [value_formula] at hz
  rw [sum_coordinates]
  by_cases hi : i = 0
  · rw [generators, ite_eq_left hi] at hz
    have hbase : z 0 + h * count z ≤ 1 := by
      apply Nat.le_of_mul_le_mul_left _ ha
      rw [Nat.mul_one]
      omega
    have hY : count z = 0 := by
      by_contra hn
      have hmul := Nat.mul_le_mul_left h (Nat.pos_of_ne_zero hn)
      rw [Nat.mul_one] at hmul
      omega
    have hW : indexWeight z = 0 := by
      simpa [hY] using indexWeight_le_mul_count z
    rw [hY, hW, Nat.mul_zero, zero_mul, add_zero, add_zero] at hz
    rw [hY, add_zero]
    exact Nat.eq_of_mul_eq_mul_left ha (hz.trans (Nat.mul_one a).symm)
  · change a * (z 0 + h * count z) + indexWeight z * d =
      (if i = 0 then a else a * h + i.val * d) at hz
    rw [ite_eq_right hi] at hz
    have hi0 : 0 < i.val := by
      apply Nat.pos_of_ne_zero
      intro hn
      exact hi (Fin.ext hn)
    have hia : i.val < a := by have := i.isLt; omega
    have hres := residue_decomposition hia (weight_congr_mod cop hz)
    have hW : i.val ≤ indexWeight z := by omega
    have hYpos : 0 < count z := by
      by_contra hn
      have hY : count z = 0 := by omega
      have := indexWeight_le_mul_count z
      rw [hY, Nat.mul_zero] at this
      omega
    have hbase : z 0 + h * count z ≤ h := by
      have := Nat.mul_le_mul_right d hW
      exact Nat.le_of_mul_le_mul_left (by omega) ha
    have hYle : count z ≤ 1 := by
      apply Nat.le_of_mul_le_mul_left _ (show 0 < h by omega)
      rw [Nat.mul_one]
      omega
    have hY : count z = 1 := by omega
    rw [hY, Nat.mul_one] at hbase
    omega

private theorem weight_zero_of_total_zero {p : ℕ} (g z : Fin p → ℕ)
    (hz : ∑ i, z i = 0) : weight g z = 0 := by
  have hz0 : z = 0 := by
    funext i
    have := coordinate_le_sum z i
    change z i = 0
    omega
  simp [hz0, weight]

private theorem basis_le {p : ℕ} {z : Fin p → ℕ} {i : Fin p} {c : ℕ}
    (hc : c ≤ z i) : ∀ j, Pi.single (M := fun _ => ℕ) i c j ≤ z j := by
  intro j
  by_cases hji : j = i
  · simpa [Pi.single, hji] using hc
  · simp [Pi.single_eq_of_ne hji]

private theorem split_coordinates {p : ℕ} {z u : Fin p → ℕ}
    (hu : ∀ i, u i ≤ z i) : (fun i => z i - u i) + u = z := by
  funext i
  exact Nat.sub_add_cancel (hu i)

private theorem atoms_iff_generator {a h d k : ℕ} (hka : k < a) (hh : 1 < h)
    (cop : a.Coprime d) (n : ℕ) :
    IsAtom (AddSubmonoid.closure (Set.range (generators a h d k))) n ↔
      n ∈ Set.range (generators a h d k) := by
  set g := generators a h d k
  set S := AddSubmonoid.closure (Set.range g)
  have hg : ∀ i, 0 < g i := generators_pos (by omega) (by omega)
  constructor
  · rintro ⟨hn, hn0, hatom⟩
    obtain ⟨z, hz⟩ := (closure_iff_fiber g n).1 hn
    change weight g z = n at hz
    have hpos : ∃ i, 0 < z i := by
      by_contra! hc
      have hz0 : z = 0 := funext fun i => Nat.eq_zero_of_le_zero (hc i)
      apply hn0
      simpa [hz0, weight] using hz.symm
    obtain ⟨i, hi⟩ := hpos
    let c : Fin (k + 1) → ℕ := fun j => z j - Pi.single (M := fun _ => ℕ) i 1 j
    have he : weight g c + g i = n := by
      calc
        weight g c + g i = weight g (c + Pi.single i 1) := by
          rw [weight_add, weight_basis, Nat.one_mul]
        _ = n := by rw [split_coordinates (basis_le hi), hz]
    have hc : weight g c ∈ S := (closure_iff_fiber g _).2 ⟨c, rfl⟩
    have hgi : g i ∈ S := AddSubmonoid.subset_closure (Set.mem_range_self i)
    rcases hatom _ hc _ hgi he with hc0 | hgi0
    · exact ⟨i, by simpa [hc0] using he⟩
    · exact ((hg i).ne' hgi0).elim
  · rintro ⟨i, rfl⟩
    refine ⟨AddSubmonoid.subset_closure (Set.mem_range_self i), (hg i).ne', ?_⟩
    intro u hu v hv huv
    obtain ⟨z, hz⟩ := (closure_iff_fiber g u).1 hu
    obtain ⟨w, hw⟩ := (closure_iff_fiber g v).1 hv
    change weight g z = u at hz
    change weight g w = v at hw
    have hzww : z + w ∈ Z g (g i) := by
      change weight g (z + w) = g i
      rw [weight_add, hz, hw, huv]
    have hlen := generator_length hka hh cop i hzww
    simp only [Pi.add_apply, Finset.sum_add_distrib] at hlen
    rcases (show (∑ j, z j) = 0 ∨ (∑ j, w j) = 0 by omega) with h | h
    · exact Or.inl (hz.symm.trans (weight_zero_of_total_zero g z h))
    · exact Or.inr (hw.symm.trans (weight_zero_of_total_zero g w h))

private theorem cofinite {a h d k : ℕ} (hk : 0 < k) (ha : 0 < a) (cop : a.Coprime d) :
    ((AddSubmonoid.closure (Set.range (generators a h d k)) : Set ℕ)ᶜ).Finite := by
  set b := a * h + d
  have hb : a.Coprime b := by
    simpa [b, Nat.add_comm] using (Nat.coprime_add_mul_left_right a d h).2 cop
  let residues : Fin a → Fin a := fun i => ⟨i.val * b % a, Nat.mod_lt _ ha⟩
  have hinj : Function.Injective residues := by
    intro i j hij
    have he : i.val * b ≡ j.val * b [MOD a] := congrArg Fin.val hij
    have hc := Nat.ModEq.cancel_right_of_coprime hb he
    apply Fin.ext
    change i.val % a = j.val % a at hc
    simpa [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using hc
  have hsurj := Finite.injective_iff_surjective.1 hinj
  have htail : ∀ n ≥ a * b, n ∈ AddSubmonoid.closure (Set.range (generators a h d k)) := by
    intro n hn
    obtain ⟨i, hi⟩ := hsurj ⟨n % a, Nat.mod_lt _ ha⟩
    have hm : n ≡ i.val * b [MOD a] := (congrArg Fin.val hi).symm
    have hle : i.val * b ≤ n := (Nat.mul_le_mul_right b i.isLt.le).trans hn
    have hdiv : a ∣ n - i.val * b := Nat.modEq_zero_iff_dvd.1
      (by simpa using hm.sub hle (Nat.le_refl (i.val * b)) (Nat.ModEq.refl _))
    obtain ⟨q, hq⟩ := hdiv
    have he : a * q + i.val * b = n := by omega
    apply (closure_iff_fiber _ _).2
    refine ⟨Pi.single 0 q + Pi.single (first hk) i.val, ?_⟩
    change weight (generators a h d k) _ = n
    rw [weight_add, weight_basis, weight_basis]
    simpa [generators, first, Fin.succ_ne_zero, b, Nat.mul_comm q a] using he
  apply (Finset.range (a * b)).finite_toSet.subset
  intro n hn
  exact Finset.mem_range.mpr (lt_of_not_ge (fun hn' => hn (htail n hn')))


private theorem no_cross_chain {a h d k B : ℕ} (hk : 1 < k) (hka : k < a) (hh : 1 < h)
    (hd : 0 < d) (cop : a.Coprime d) (hB : B < ceilParameter a k + h + d)
    {z w : Z (generators a h d k) (witness a h d k)}
    (hz : Low h d (ceilParameter a k) z.val) (hw : High a (ceilParameter a k) w.val) :
    ¬ Chain (generators a h d k) (witness a h d k) B z w := by
  intro hchain
  have propagate (u v : Z (generators a h d k) (witness a h d k))
      (hu : Low h d (ceilParameter a k) u.val) (hedge : distance u.val v.val ≤ B) :
      Low h d (ceilParameter a k) v.val := by
    rcases (fiber_iff_classes hk hka (by omega) hd cop v.val).1 v.property with hv | hv
    · exact hv
    · exact (not_le_of_gt hB ((cross_distance hk hka hh hu hv).trans hedge)).elim
  have hlo : Low h d (ceilParameter a k) w.val := by
    clear hw
    induction hchain with
    | refl => exact hz
    | tail _ hedge ih => exact propagate _ _ ih hedge
  have hW := hlo.1
  have hW' := hw.1
  omega

/-- The generators and the two classes of the exhibited element’s factorization fiber. -/
def WitnessCheckpoint (a h d k : ℕ) : Prop :=
  let g := generators a h d k
  let S := AddSubmonoid.closure (Set.range g)
  let t := ceilParameter a k
  let n := witness a h d k
  let N := t + h + d
  Function.Injective g ∧ (↑S : Set ℕ)ᶜ.Finite ∧ (∀ m, IsAtom S m ↔ m ∈ Set.range g) ∧
  n ∈ S ∧
  (∀ z, z ∈ Z g n ↔ Low h d t z ∨ High a t z) ∧
  (∀ z : Fin (k + 1) → ℕ, ¬ (Low h d t z ∧ High a t z)) ∧
  (∃ z : Z g n, Low h d t z.val) ∧ (∃ w : Z g n, High a t w.val) ∧
  (∀ z w : Fin (k + 1) → ℕ, Low h d t z → High a t w → N ≤ distance z w) ∧
  (∀ B < N, ∀ z w : Z g n, Low h d t z.val → High a t w.val → ¬ Chain g n B z w)

private theorem checkpoint {a h d k : ℕ} (hd : 0 < d) (cop : a.Coprime d)
    (hk : 1 < k) (hka : k < a) (hh : 1 < h) : WitnessCheckpoint a h d k := by
  dsimp only [WitnessCheckpoint]
  have hlo := lowVector_low (show 0 < k by omega) h d (ceilParameter a k)
  have hmem := (fiber_iff_classes hk hka (by omega) hd cop _).2 (Or.inl hlo)
  refine ⟨generators_injective (by omega) hh hd, cofinite (by omega) (by omega) cop,
    atoms_iff_generator hka hh cop, (closure_iff_fiber _ _).2 ⟨_, hmem⟩,
    fiber_iff_classes hk hka (by omega) hd cop, ?_, ⟨⟨_, hmem⟩, hlo⟩,
    high_inhabited hk hka (by omega) hd cop, fun _ _ => cross_distance hk hka hh,
    fun _ hB _ _ => no_cross_chain hk hka hh hd cop hB⟩
  rintro z ⟨hlo', hhi⟩
  have hW := hlo'.1
  have hW' := hhi.1
  omega


private theorem distance_add_common_le {p : ℕ} (c u v : Fin p → ℕ) :
    distance (c + u) (c + v) ≤ max (∑ i, u i) (∑ i, v i) := by
  have hcommon (i : Fin p) : c i ≤ min (c i + u i) (c i + v i) :=
    le_min (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  apply max_le
  · apply le_trans _ (le_max_left _ _)
    apply Finset.sum_le_sum
    intro i _
    have := hcommon i
    change c i + u i - min (c i + u i) (c i + v i) ≤ u i
    omega
  · apply le_trans _ (le_max_right _ _)
    apply Finset.sum_le_sum
    intro i _
    have := hcommon i
    change c i + v i - min (c i + u i) (c i + v i) ≤ v i
    omega

private theorem low_exchange {a h d k : ℕ} (hk : 1 < k) (hka : k < a) (hh : 1 < h)
    (hd : 0 < d) (cop : a.Coprime d) {z : Z (generators a h d k) (witness a h d k)}
    (hz : Low h d (ceilParameter a k) z.val) (hY : count z.val < ceilParameter a k) :
    ∃ w : Z (generators a h d k) (witness a h d k),
      Low h d (ceilParameter a k) w.val ∧
      count w.val = count z.val + 1 ∧ distance z.val w.val ≤ h + 1 := by
  let g := generators a h d k
  set t := ceilParameter a k
  have hidx : ∃ i : Fin k, 0 < i.val ∧ 0 < z.val i.succ := by
    by_contra! hi
    have he : excess z.val = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases h0 : i.val = 0
      · simp [h0]
      · rw [Nat.eq_zero_of_le_zero (hi i (Nat.pos_of_ne_zero h0)), zero_mul]
    have hsum := indexWeight_eq_count_add_excess z.val
    rw [hz.1, he] at hsum
    omega
  obtain ⟨i, hi0, hzi⟩ := hidx
  let j : Fin k := ⟨i.val - 1, by have := i.isLt; omega⟩
  let i₁ := first (show 0 < k by omega)
  let removed : Fin (k + 1) → ℕ := Pi.single (0 : Fin (k + 1)) h + Pi.single i.succ 1
  let added : Fin (k + 1) → ℕ := Pi.single i₁ 1 + Pi.single j.succ 1
  let c : Fin (k + 1) → ℕ := fun l => z.val l - removed l
  have hz0 : h ≤ z.val 0 := by
    rw [hz.2]
    have := Nat.mul_le_mul_left h (show 1 ≤ t + 1 - count z.val by omega)
    rw [Nat.mul_one] at this
    omega
  have hremoved : ∀ l, removed l ≤ z.val l := by
    intro l
    by_cases hl : l = 0
    · subst l
      simpa [removed, Pi.add_apply, Pi.single_eq_of_ne (Fin.succ_ne_zero _).symm] using hz0
    · simpa [removed, Pi.add_apply, Pi.single_eq_of_ne hl] using (basis_le hzi l)
  have hsplit : c + removed = z.val := split_coordinates hremoved
  have hj : j.succ.val = i.val := by dsimp [j]; omega
  have hvalue : weight g removed = weight g added := by
    simp only [g, removed, added, i₁, weight_add, weight_basis, Nat.one_mul, generators,
      ite_true, Fin.succ_ne_zero, first, ite_false, hj, Fin.val_succ, Nat.zero_add]
    ring
  have hweight : indexWeight removed = indexWeight added := by
    simp only [indexWeight, removed, added, i₁, weight_add, weight_basis, Nat.one_mul,
      Fin.val_zero, Nat.mul_zero, zero_add, first, hj, Fin.val_succ]
    omega
  have hcntR : count removed = 1 := by
    simp [removed, count_add, count_basis_zero, count_basis_succ]
  have hcntA : count added = 2 := by
    change count (Pi.single i₁ 1 + Pi.single j.succ 1) = 2
    rw [count_add, count_basis_succ, show count (Pi.single i₁ 1) = 1 from count_basis_succ _ _]
  let w : Z g (witness a h d k) := ⟨c + added, by
    change weight g (c + added) = witness a h d k
    rw [weight_add, ← hvalue, ← weight_add, hsplit]
    exact z.property⟩
  have hwY : count w.val = count z.val + 1 := by
    have h := congrArg count hsplit
    rw [count_add, hcntR] at h
    change count (c + added) = _
    rw [count_add, hcntA]
    omega
  have hwW : indexWeight w.val = t := by
    change indexWeight (c + added) = t
    have hadd : indexWeight (c + added) = indexWeight c + indexWeight added :=
      weight_add _ _ _
    have hrem : indexWeight (c + removed) = indexWeight c + indexWeight removed :=
      weight_add _ _ _
    rw [hadd, ← hweight, ← hrem, hsplit, hz.1]
  have hlow : Low h d t w.val := by
    rcases (fiber_iff_classes hk hka (by omega) hd cop w.val).1 w.property with hlow | hhigh
    · exact hlow
    · have hhW := hhigh.1
      omega
  refine ⟨w, hlow, hwY, ?_⟩
  have hlenR : (∑ l, removed l) = h + 1 := by
    rw [sum_coordinates, hcntR]
    simp [removed, Pi.add_apply, Pi.single_eq_of_ne (Fin.succ_ne_zero _).symm]
  have hlenA : (∑ l, added l) = 2 := by
    rw [sum_coordinates, hcntA]
    simp [added, i₁, Pi.add_apply, Pi.single_eq_of_ne (first_ne_zero _).symm]
  change distance z.val (c + added) ≤ h + 1
  rw [← hsplit]
  exact (distance_add_common_le c removed added).trans
    (by rw [hlenR, hlenA]; exact max_le le_rfl (by omega))

private theorem low_eq_lowVector {k h d t : ℕ} (hk : 0 < k) {z : Fin (k + 1) → ℕ}
    (hz : Low h d t z) (hY : count z = t) : z = lowVector hk h d t := by
  have he : excess z = 0 := by
    have := indexWeight_eq_count_add_excess z
    have hW := hz.1
    omega
  have hvanish (i : Fin k) (hi : i.val ≠ 0) : z i.succ = 0 := by
    have hle := coordinate_le_sum (fun i : Fin k => z i.succ * i.val) i
    change z i.succ * i.val ≤ excess z at hle
    rw [he] at hle
    exact (Nat.mul_eq_zero.mp (Nat.eq_zero_of_le_zero hle)).resolve_right hi
  let i₀ : Fin k := ⟨0, hk⟩
  have hz1 : z (first hk) = t := by
    rw [count, Fintype.sum_eq_single i₀] at hY
    · exact hY
    · intro j hj
      exact hvanish j (fun h => hj (Fin.ext h))
  have hz0 : z 0 = h + d := by
    rw [hz.2, hY, show t + 1 - t = 1 by omega, Nat.mul_one]
  funext l
  refine Fin.cases ?_ (fun i => ?_) l
  · simpa [lowVector, Pi.add_apply, Pi.single_eq_of_ne (first_ne_zero hk).symm]
      using hz0
  · by_cases hi : i = i₀
    · subst i
      change z (first hk) = lowVector hk h d t (first hk)
      simpa [lowVector, Pi.add_apply, Pi.single_eq_of_ne (first_ne_zero hk)] using hz1
    · have h₁ : i.succ ≠ first hk := by
        intro h
        exact hi (Fin.ext (by simpa [first, Fin.val_succ] using congrArg Fin.val h))
      simp [lowVector, Pi.add_apply, Fin.succ_ne_zero, Pi.single_eq_of_ne h₁,
        hvanish i (fun h => hi (Fin.ext h))]

private theorem chain_symm {p n B : ℕ} {g : Fin p → ℕ} {z w : Z g n}
    (h : Chain g n B z w) : Chain g n B w z := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    exact Relation.ReflTransGen.head (by simpa only [distance_symm] using hbc) ih

private theorem chain_mono {p n B B' : ℕ} {g : Fin p → ℕ} {z w : Z g n}
    (hB : B ≤ B') (h : Chain g n B z w) : Chain g n B' z w :=
  Relation.ReflTransGen.mono
    (fun (u v : Z g n) (e : distance u.val v.val ≤ B) => e.trans hB) z w h

private theorem low_chain {a h d k : ℕ} (hk : 1 < k) (hka : k < a) (hh : 1 < h)
    (hd : 0 < d) (cop : a.Coprime d) (z l : Z (generators a h d k) (witness a h d k))
    (hz : Low h d (ceilParameter a k) z.val)
    (hl : l.val = lowVector (show 0 < k by omega) h d (ceilParameter a k)) :
    Chain (generators a h d k) (witness a h d k) (h + 1) z l := by
  set t := ceilParameter a k
  generalize he : t - count z.val = m
  induction m using Nat.strong_induction_on generalizing z with
  | h m ih =>
    have hY : count z.val ≤ t := (count_le_indexWeight z.val).trans_eq hz.1
    by_cases heq : count z.val = t
    · have hzl : z = l := Subtype.ext ((low_eq_lowVector (by omega) hz heq).trans hl.symm)
      rw [hzl]
      exact Relation.ReflTransGen.refl
    · obtain ⟨w, hw, hcnt, hstep⟩ := low_exchange hk hka hh hd cop hz (by omega)
      exact Relation.ReflTransGen.head hstep
        (ih (t - count w.val) (by omega) w hw rfl)

private theorem high_distance {a k t : ℕ} {z w : Fin (k + 1) → ℕ}
    (hz : High a t z) (hw : High a t w) : distance z w ≤ t + 1 := by
  have hzlen : (∑ i, z i) = t + 1 := by rw [sum_coordinates, hz.2.2, hz.2.1, zero_add]
  have hwlen : (∑ i, w i) = t + 1 := by rw [sum_coordinates, hw.2.2, hw.2.1, zero_add]
  exact (distance_le_lengths z w).trans (by rw [hzlen, hwlen, max_self])

private theorem witness_bridge {a h d k : ℕ} (hk : 1 < k) (hka : k < a) (hh : 1 < h)
    {l w : Fin (k + 1) → ℕ} (hl : l = lowVector (show 0 < k by omega) h d (ceilParameter a k))
    (hw : High a (ceilParameter a k) w) :
    distance l w = ceilParameter a k + h + d := by
  subst l
  set t := ceilParameter a k
  have hlo := lowVector_low (show 0 < k by omega) h d t
  have hY : count (lowVector (show 0 < k by omega) h d t) = t := by
    rw [lowVector, count_add, count_basis_zero, zero_add]
    exact count_basis_succ _ _
  have hl_len := low_length (show 0 < h by omega) hlo
  rw [hY, Nat.sub_self, Nat.mul_zero, add_zero] at hl_len
  have hw_len : (∑ i, w i) = t + 1 := by rw [sum_coordinates, hw.2.2, hw.2.1, zero_add]
  refine le_antisymm ((distance_le_lengths _ _).trans ?_) (cross_distance hk hka hh hlo hw)
  rw [hl_len, hw_len]
  exact max_le le_rfl (by omega)


/-- Conjecture 18.2 on the original atoms, with the exact threshold and its two components
at the preceding threshold on the witnessed element. -/
theorem result (a h d k : ℕ) (hd : 0 < d) (cop : a.Coprime d)
    (hk : 1 < k) (hka : k < a) (hh : 1 < h) :
    let g := generators a h d k
    let t := ceilParameter a k
    let n := witness a h d k
    let N := t + h + d
    WitnessCheckpoint a h d k ∧
    (∀ z w : Z g n, Chain g n (N - 1) z w ↔
      (Low h d t z.val ∧ Low h d t w.val) ∨ (High a t z.val ∧ High a t w.val)) ∧
    IsLeast {B | ∀ z w : Z g n, Chain g n B z w} N ∧ N ∈ catenarySpectrum g := by
  dsimp only
  let g := generators a h d k
  let t := ceilParameter a k
  let n := witness a h d k
  let N := t + h + d
  have hc := checkpoint hd cop hk hka hh
  have ht : 0 < t := (parameter_bounds hk hka).1
  have hlo := lowVector_low (show 0 < k by omega) h d t
  have hcParts := hc
  change Function.Injective g ∧ _ at hcParts
  obtain ⟨_, _, _, _, hpartition, _, _, ⟨w₀, hw₀⟩, _, hseparate⟩ := hcParts
  let l : Z g n := ⟨_, (hpartition _).2 (Or.inl hlo)⟩
  have classes (z : Z g n) : Low h d t z.val ∨ High a t z.val :=
    (hpartition z.val).1 z.property
  have low_to_l (z : Z g n) (hz : Low h d t z.val) : Chain g n (N - 1) z l :=
    chain_mono (show h + 1 ≤ N - 1 by dsimp [N]; omega)
      (low_chain hk hka hh hd cop z l hz rfl)
  have hhigh (z w : Z g n) (hz : High a t z.val) (hw : High a t w.val) :
      Chain g n (N - 1) z w :=
    Relation.ReflTransGen.single ((high_distance hz hw).trans (show t + 1 ≤ N - 1 by
      dsimp [N]
      omega))
  have hprev : ∀ z w : Z g n, Chain g n (N - 1) z w ↔
      (Low h d t z.val ∧ Low h d t w.val) ∨ (High a t z.val ∧ High a t w.val) := by
    intro z w
    constructor
    · intro hchain
      have hB : N - 1 < N := by dsimp [N]; omega
      rcases classes z with hz | hz <;> rcases classes w with hw | hw
      · exact Or.inl ⟨hz, hw⟩
      · exact (hseparate _ hB _ _ hz hw hchain).elim
      · exact (hseparate _ hB _ _ hw hz (chain_symm hchain)).elim
      · exact Or.inr ⟨hz, hw⟩
    · rintro (⟨hz, hw⟩ | ⟨hz, hw⟩)
      · exact (low_to_l z hz).trans (chain_symm (low_to_l w hw))
      · exact hhigh z w hz hw
  have to_l (z : Z g n) : Chain g n N z l := by
    rcases classes z with hz | hz
    · exact chain_mono (Nat.sub_le _ _) (low_to_l z hz)
    · exact chain_symm (Relation.ReflTransGen.single (witness_bridge hk hka hh rfl hz).le)
  have hleast : IsLeast {B | ∀ z w : Z g n, Chain g n B z w} N := by
    refine ⟨fun z w => (to_l z).trans (chain_symm (to_l w)), ?_⟩
    intro B hB
    by_contra! hlt
    exact hseparate _ hlt _ _ hlo hw₀ (hB l w₀)
  exact ⟨hc, hprev, hleast, ⟨n, ⟨l.val, l.property⟩, hleast⟩⟩

end D5.S3.Arith.Additive.NarayanCatenarySpectrumMembership
