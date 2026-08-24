/- GID: D5/S3/Observer/ArithmeticTomography/ResidueCoordinateDimension
   generality: G
   mirror-B: D5/B/S3/Observer/ArithmeticTomography/ResidueCoordinateDimension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Three residues on ZMod 30 have minimum complete coordinate count three. -/

import Mathlib.Data.Nat.Find
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Tactic

/- Library-search audit trail (2026-08-24):
   * `rg -n -F 'statistical_dimension_eq_three' D5 Golden/Frozen/accepted`
     returned no matches; broader searches for `D_stat`, statistical dimension,
     `ZMod 30`, and the three stated collision pairs found no public or private
     repository theorem covering this result.
   * Pinned Mathlib provides `ZMod.equivPi`, the exact prime-power Chinese
     remainder equivalence. It supplies the injectivity of all three readings.
   * `D5.S3.Arith.ChineseRemainder.chinese_remainder_bijective` packages the
     two-factor CRT, but does not cover the three-coordinate minimum or any of
     the collision witnesses, so this proof uses the more direct Mathlib CRT.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.ArithmeticTomography.ResidueCoordinateDimension

/-- The three available prime coordinates are the prime factors of thirty. -/
abbrev Coordinate := (30 : Nat).primeFactors

/-- The modulus attached to a prime coordinate, including its multiplicity in
thirty. -/
abbrev coordinateModulus (q : Coordinate) : Nat :=
  q.1 ^ (30 : Nat).factorization q.1

/-- The CRT reading of a state at one prime-power coordinate. -/
noncomputable def reading (q : Coordinate) (x : ZMod 30) : ZMod (coordinateModulus q) :=
  ZMod.equivPi (n := 30) (by norm_num) x q

/-- The joint reading retained by a selected set of coordinates. -/
noncomputable def selectedReading (s : Finset Coordinate) (x : ZMod 30) :
    (q : {q // q ∈ s}) -> ZMod (coordinateModulus q.1) :=
  fun q => reading q.1 x

/-- A coordinate set is complete when its joint reading identifies every
state. -/
def Complete (s : Finset Coordinate) : Prop :=
  Function.Injective (selectedReading s)

/-- Two distinct states merged by the selected coordinates. -/
def Merges (s : Finset Coordinate) (x y : ZMod 30) : Prop :=
  x ≠ y ∧ selectedReading s x = selectedReading s y

/-- The coordinate corresponding to reduction modulo two. -/
def q2 : Coordinate := ⟨2, by norm_num [Nat.mem_primeFactors]⟩

/-- The coordinate corresponding to reduction modulo three. -/
def q3 : Coordinate := ⟨3, by norm_num [Nat.mem_primeFactors]⟩

/-- The coordinate corresponding to reduction modulo five. -/
def q5 : Coordinate := ⟨5, by norm_num [Nat.mem_primeFactors]⟩

private theorem q2_modulus : coordinateModulus q2 = 2 := by
  rw [show coordinateModulus q2 = 2 ^ (30 : Nat).factorization 2 by rfl,
    Nat.factorization_def 30 (by norm_num), show 30 = 2 * 15 by norm_num,
    padicValNat_base_mul (by norm_num) (by norm_num),
    padicValNat.eq_zero_of_not_dvd (by norm_num)]
  norm_num

private theorem q3_modulus : coordinateModulus q3 = 3 := by
  rw [show coordinateModulus q3 = 3 ^ (30 : Nat).factorization 3 by rfl,
    Nat.factorization_def 30 (by norm_num), show 30 = 3 * 10 by norm_num,
    padicValNat_base_mul (by norm_num) (by norm_num),
    padicValNat.eq_zero_of_not_dvd (by norm_num)]
  norm_num

private theorem q5_modulus : coordinateModulus q5 = 5 := by
  rw [show coordinateModulus q5 = 5 ^ (30 : Nat).factorization 5 by rfl,
    Nat.factorization_def 30 (by norm_num), show 30 = 5 * 6 by norm_num,
    padicValNat_base_mul (by norm_num) (by norm_num),
    padicValNat.eq_zero_of_not_dvd (by norm_num)]
  norm_num

private theorem reading_natCast (q : Coordinate) (n : Nat) :
    reading q (n : ZMod 30) = (n : ZMod (coordinateModulus q)) := by
  exact congrFun (map_natCast (ZMod.equivPi (n := 30) (by decide)) n) q

private theorem reading_zero (q : Coordinate) : reading q 0 = 0 := by
  exact congrFun (map_zero (ZMod.equivPi (n := 30) (by decide))) q

/-- The readings modulo two and three merge the distinct states 15 and 21. -/
theorem q2_q3_collision : Merges {q2, q3} 15 21 := by
  constructor
  · decide
  · funext q
    rcases q with ⟨q, hq⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl <;> simp only [selectedReading]
    · calc
        _ = (15 : ZMod (coordinateModulus q2)) := by
          exact reading_natCast q2 15
        _ = 21 := by rw [q2_modulus]; decide
        _ = _ := by
          exact (reading_natCast q2 21).symm
    · calc
        _ = (15 : ZMod (coordinateModulus q3)) := by
          exact reading_natCast q3 15
        _ = 21 := by rw [q3_modulus]; decide
        _ = _ := by
          exact (reading_natCast q3 21).symm

/-- The readings modulo two and five merge the distinct states 0 and 10. -/
theorem q2_q5_collision : Merges {q2, q5} 0 10 := by
  constructor
  · decide
  · funext q
    rcases q with ⟨q, hq⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl <;> simp only [selectedReading]
    · calc
        _ = (0 : ZMod (coordinateModulus q2)) := reading_zero q2
        _ = 10 := by rw [q2_modulus]; decide
        _ = _ := (reading_natCast q2 10).symm
    · calc
        _ = (0 : ZMod (coordinateModulus q5)) := reading_zero q5
        _ = 10 := by rw [q5_modulus]; decide
        _ = _ := (reading_natCast q5 10).symm

/-- The readings modulo three and five merge the distinct states 0 and 15. -/
theorem q3_q5_collision : Merges {q3, q5} 0 15 := by
  constructor
  · decide
  · funext q
    rcases q with ⟨q, hq⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl <;> simp only [selectedReading]
    · calc
        _ = (0 : ZMod (coordinateModulus q3)) := reading_zero q3
        _ = 15 := by rw [q3_modulus]; decide
        _ = _ := (reading_natCast q3 15).symm
    · calc
        _ = (0 : ZMod (coordinateModulus q5)) := reading_zero q5
        _ = 15 := by rw [q5_modulus]; decide
        _ = _ := (reading_natCast q5 15).symm

/-- Every restriction of a merging coordinate set still merges the same
states. -/
theorem merges_of_subset {s t : Finset Coordinate} {x y : ZMod 30}
    (hst : s ⊆ t) (hxy : Merges t x y) : Merges s x y := by
  refine ⟨hxy.1, ?_⟩
  funext q
  exact congrFun hxy.2 ⟨q.1, hst q.2⟩

private theorem coordinate_cases (q : Coordinate) : q = q2 ∨ q = q3 ∨ q = q5 := by
  have hpd : q.1.Prime ∧ q.1 ∣ 30 :=
    ⟨Nat.prime_of_mem_primeFactors q.2, Nat.dvd_of_mem_primeFactors q.2⟩
  have hle : q.1 ≤ 30 := Nat.le_of_dvd (by norm_num) hpd.2
  rcases q with ⟨q, hq⟩
  simp only [q2, q3, q5, Subtype.mk.injEq]
  interval_cases q <;> norm_num at hpd
  all_goals simp

/-- Any selected set with fewer than three coordinates is incomplete. -/
theorem fewer_than_three_incomplete (s : Finset Coordinate) (hs : s.card < 3) :
    ¬Complete s := by
  have not_complete_of_merges {t : Finset Coordinate} {x y : ZMod 30}
      (hxy : Merges t x y) : ¬Complete t := by
    intro hcomplete
    exact hxy.1 (hcomplete hxy.2)
  by_cases h2 : q2 ∈ s
  · by_cases h3 : q3 ∈ s
    · by_cases h5 : q5 ∈ s
      · have hsub : {q2, q3, q5} ⊆ s := by
          intro q hq
          rcases coordinate_cases q with rfl | rfl | rfl <;> assumption
        have hcard := Finset.card_le_card hsub
        have : 3 ≤ s.card := by simpa [q2, q3, q5] using hcard
        omega
      · apply not_complete_of_merges
        apply merges_of_subset _ q2_q3_collision
        intro q hq
        rcases coordinate_cases q with rfl | rfl | rfl
        · simp
        · simp
        · exact (h5 hq).elim
    · apply not_complete_of_merges
      apply merges_of_subset _ q2_q5_collision
      intro q hq
      rcases coordinate_cases q with rfl | rfl | rfl
      · simp
      · exact (h3 hq).elim
      · simp
  · apply not_complete_of_merges
    apply merges_of_subset _ q3_q5_collision
    intro q hq
    rcases coordinate_cases q with rfl | rfl | rfl
    · exact (h2 hq).elim
    · simp
    · simp

/-- All three CRT coordinates jointly identify every state in `ZMod 30`. -/
theorem all_coordinates_complete : Complete Finset.univ := by
  intro x y hxy
  apply (ZMod.equivPi (n := 30) (by decide)).injective
  funext q
  simpa [selectedReading, reading] using
    congrFun hxy ⟨q, Finset.mem_univ q⟩

/-- There is at least one finite complete coordinate selection. -/
theorem complete_coordinate_set_exists :
    ∃ n : Nat, ∃ s : Finset Coordinate, s.card = n ∧ Complete s := by
  have hall : ({q2, q3, q5} : Finset Coordinate) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro q
    rcases coordinate_cases q with rfl | rfl | rfl <;> simp
  refine ⟨3, {q2, q3, q5}, ?_, ?_⟩
  · norm_num [q2, q3, q5]
  · rw [hall]
    exact all_coordinates_complete

/-- The statistical dimension is the least number of retained coordinates
whose joint reading is complete. -/
noncomputable def statisticalDimension : Nat :=
  by
    classical
    exact Nat.find complete_coordinate_set_exists

/-- The three residue coordinates have statistical dimension exactly three:
each pair has an explicit collision, while the full CRT reading is injective. -/
theorem statistical_dimension_eq_three : statisticalDimension = 3 := by
  classical
  rw [statisticalDimension, Nat.find_eq_iff]
  constructor
  · have hall : ({q2, q3, q5} : Finset Coordinate) = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro q
      rcases coordinate_cases q with rfl | rfl | rfl <;> simp
    refine ⟨{q2, q3, q5}, ?_, ?_⟩
    · norm_num [q2, q3, q5]
    · rw [hall]
      exact all_coordinates_complete
  · intro n hn
    rintro ⟨s, hcard, hcomplete⟩
    apply fewer_than_three_incomplete s (by omega)
    exact hcomplete

example : Merges {q2, q3} 15 21 := q2_q3_collision

example : statisticalDimension = 3 := statistical_dimension_eq_three

#print axioms statistical_dimension_eq_three

end D5.S3.Observer.ArithmeticTomography.ResidueCoordinateDimension
