/- GID: D5/S3/Observer/ArithmeticTomography/QuaternaryResidueCoordinateDimension
   generality: G
   mirror-B: D5/B/S3/Observer/ArithmeticTomography/QuaternaryResidueCoordinateDimension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The four-state carrier has dimension three; the ternary subcarrier has dimension two. -/

import D5.S3.Observer.ArithmeticTomography.ResidueCoordinateDimension

/- Library-search audit trail (2026-08-29):
   * The parent module supplies the exact CRT readings, three ambient collision
     calculations, coordinate-subset restriction, and full CRT injectivity.
   * Those ambient collision predicates do not carry the source state set, so
     they are reused only below a new state-subtype interface.
   * Pinned Mathlib supplies `Nat.find_eq_iff` and finite injectivity APIs, but
     no theorem for this concrete four-state minimum. Loogle confirmed those
     API hits; exact GitHub Lean searches for this result returned no hits. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.ArithmeticTomography.QuaternaryResidueCoordinateDimension

open D5.S3.Observer.ArithmeticTomography.ResidueCoordinateDimension

/-- The ambient residue state space used by the three coordinate readings. -/
abbrev State := ZMod 30

/-- The states admitted by a specified finite carrier. -/
abbrev StateOn (carrier : Finset State) := {x : State // x ∈ carrier}

/-- The four-state carrier fixed in the source. -/
def quaternaryCarrier : Finset State := {0, 10, 15, 21}

/-- A three-state carrier that requires only two coordinate readings. -/
def ternaryCarrier : Finset State := {0, 10, 15}

/-- A selected coordinate reading restricted to a finite state carrier. -/
noncomputable def restrictedReading (carrier : Finset State)
    (s : Finset Coordinate) (x : StateOn carrier) :=
  selectedReading s x.1

/-- Two states in the same finite carrier have the same selected coordinate
reading. The public theorem supplies the concrete, distinct source states. -/
def MergesOn (carrier : Finset State) (s : Finset Coordinate)
    (x y : StateOn carrier) : Prop :=
  restrictedReading carrier s x = restrictedReading carrier s y

/-- A coordinate selection distinguishes every state in the finite carrier. -/
def CompleteOn (carrier : Finset State) (s : Finset Coordinate) : Prop :=
  Function.Injective (restrictedReading carrier s)

/-- The four named states as elements of the source carrier. -/
def state0 : StateOn quaternaryCarrier := ⟨0, by simp [quaternaryCarrier]⟩

def state10 : StateOn quaternaryCarrier := ⟨10, by simp [quaternaryCarrier]⟩

def state15 : StateOn quaternaryCarrier := ⟨15, by simp [quaternaryCarrier]⟩

def state21 : StateOn quaternaryCarrier := ⟨21, by simp [quaternaryCarrier]⟩

/-- The three named states as elements of the ternary carrier. -/
def ternary0 : StateOn ternaryCarrier := ⟨0, by simp [ternaryCarrier]⟩

def ternary10 : StateOn ternaryCarrier := ⟨10, by simp [ternaryCarrier]⟩

def ternary15 : StateOn ternaryCarrier := ⟨15, by simp [ternaryCarrier]⟩

private theorem all_coordinates_complete_on (carrier : Finset State) :
    CompleteOn carrier Finset.univ := by
  intro x y hxy
  exact Subtype.ext (all_coordinates_complete hxy)

private theorem complete_coordinate_set_exists_on (carrier : Finset State) :
    ∃ n : Nat, ∃ s : Finset Coordinate, s.card = n /\ CompleteOn carrier s := by
  refine ⟨Finset.univ.card, Finset.univ, rfl, ?_⟩
  exact all_coordinates_complete_on carrier

/-- The least number of coordinates whose joint reading is complete on the
specified finite state carrier. -/
noncomputable def statisticalDimensionOn (carrier : Finset State) : Nat :=
  by
    classical
    exact Nat.find (complete_coordinate_set_exists_on carrier)

private theorem q2_q3_collision_on_quaternary :
    MergesOn quaternaryCarrier {q2, q3} state15 state21 := by
  simpa [MergesOn, restrictedReading, state15, state21, Merges] using q2_q3_collision.2

private theorem q2_q5_collision_on_quaternary :
    MergesOn quaternaryCarrier {q2, q5} state0 state10 := by
  simpa [MergesOn, restrictedReading, state0, state10, Merges] using q2_q5_collision.2

private theorem q3_q5_collision_on_quaternary :
    MergesOn quaternaryCarrier {q3, q5} state0 state15 := by
  simpa [MergesOn, restrictedReading, state0, state15, Merges] using q3_q5_collision.2

private theorem state15_ne_state21 : state15 ≠ state21 := by
  intro h
  apply q2_q3_collision.1
  simpa [state15, state21] using congrArg Subtype.val h

private theorem state0_ne_state10 : state0 ≠ state10 := by
  intro h
  apply q2_q5_collision.1
  simpa [state0, state10] using congrArg Subtype.val h

private theorem state0_ne_state15 : state0 ≠ state15 := by
  intro h
  apply q3_q5_collision.1
  simpa [state0, state15] using congrArg Subtype.val h

private theorem mergesOn_of_subset {carrier : Finset State}
    {s t : Finset Coordinate} {x y : StateOn carrier}
    (hne : x ≠ y) (hst : s ⊆ t) (hxy : MergesOn carrier t x y) :
    MergesOn carrier s x y := by
  have hambient : Merges t x.1 y.1 := by
    refine ⟨?_, hxy⟩
    intro h
    exact hne (Subtype.ext h)
  exact (merges_of_subset hst hambient).2

private theorem mergesOn_not_complete {carrier : Finset State}
    {s : Finset Coordinate} {x y : StateOn carrier}
    (hne : x ≠ y) (hxy : MergesOn carrier s x y) : ¬CompleteOn carrier s := by
  intro hcomplete
  exact hne (hcomplete hxy)

private theorem coordinate_cases (q : Coordinate) : q = q2 ∨ q = q3 ∨ q = q5 := by
  have hpd : q.1.Prime ∧ q.1 ∣ 30 :=
    ⟨Nat.prime_of_mem_primeFactors q.2, Nat.dvd_of_mem_primeFactors q.2⟩
  have hle : q.1 ≤ 30 := Nat.le_of_dvd (by norm_num) hpd.2
  rcases q with ⟨q, hq⟩
  simp only [q2, q3, q5, Subtype.mk.injEq]
  interval_cases q <;> norm_num at hpd
  all_goals simp

private theorem q2_modulus_eq_two : coordinateModulus q2 = 2 := by
  rw [show coordinateModulus q2 = 2 ^ (30 : Nat).factorization 2 by rfl,
    Nat.factorization_def 30 (by norm_num), show 30 = 2 * 15 by norm_num,
    padicValNat_base_mul (by norm_num) (by norm_num),
    padicValNat.eq_zero_of_not_dvd (by norm_num)]
  norm_num

private theorem q3_modulus_eq_three : coordinateModulus q3 = 3 := by
  rw [show coordinateModulus q3 = 3 ^ (30 : Nat).factorization 3 by rfl,
    Nat.factorization_def 30 (by norm_num), show 30 = 3 * 10 by norm_num,
    padicValNat_base_mul (by norm_num) (by norm_num),
    padicValNat.eq_zero_of_not_dvd (by norm_num)]
  norm_num

private theorem reading_natCast_on_ternary (q : Coordinate) (n : Nat) :
    reading q (n : ZMod 30) = (n : ZMod (coordinateModulus q)) := by
  exact congrFun (map_natCast (ZMod.equivPi (n := 30) (by decide)) n) q

private theorem reading_zero_on_ternary (q : Coordinate) : reading q 0 = 0 := by
  exact congrFun (map_zero (ZMod.equivPi (n := 30) (by decide))) q

private theorem q3_reading_zero_ne_ten : reading q3 0 ≠ reading q3 10 := by
  intro h
  have hmod : (0 : ZMod (coordinateModulus q3)) = 10 :=
    (reading_zero_on_ternary q3).symm.trans
      (h.trans (reading_natCast_on_ternary q3 10))
  rw [q3_modulus_eq_three] at hmod
  exact (by decide : (0 : ZMod 3) ≠ 10) hmod

private theorem q2_reading_zero_ne_fifteen : reading q2 0 ≠ reading q2 15 := by
  intro h
  have hmod : (0 : ZMod (coordinateModulus q2)) = 15 :=
    (reading_zero_on_ternary q2).symm.trans
      (h.trans (reading_natCast_on_ternary q2 15))
  rw [q2_modulus_eq_two] at hmod
  exact (by decide : (0 : ZMod 2) ≠ 15) hmod

private theorem q2_reading_ten_ne_fifteen : reading q2 10 ≠ reading q2 15 := by
  intro h
  have hmod : (10 : ZMod (coordinateModulus q2)) = 15 :=
    (reading_natCast_on_ternary q2 10).symm.trans
      (h.trans (reading_natCast_on_ternary q2 15))
  rw [q2_modulus_eq_two] at hmod
  exact (by decide : (10 : ZMod 2) ≠ 15) hmod

private theorem q2_q3_complete_on_ternary :
    CompleteOn ternaryCarrier {q2, q3} := by
  intro x y hxy
  apply Subtype.ext
  have h2 : reading q2 x.1 = reading q2 y.1 := by
    exact congrFun hxy ⟨q2, by simp⟩
  have h3 : reading q3 x.1 = reading q3 y.1 := by
    exact congrFun hxy ⟨q3, by simp⟩
  have hx : x.1 = 0 ∨ x.1 = 10 ∨ x.1 = 15 := by
    simpa only [ternaryCarrier, Finset.mem_insert, Finset.mem_singleton] using x.2
  have hy : y.1 = 0 ∨ y.1 = 10 ∨ y.1 = 15 := by
    simpa only [ternaryCarrier, Finset.mem_insert, Finset.mem_singleton] using y.2
  rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy
  · exact hx.trans hy.symm
  · exfalso
    exact q3_reading_zero_ne_ten (by simpa [hx, hy] using h3)
  · exfalso
    exact q2_reading_zero_ne_fifteen (by simpa [hx, hy] using h2)
  · exfalso
    exact q3_reading_zero_ne_ten (by simpa [hx, hy] using h3.symm)
  · exact hx.trans hy.symm
  · exfalso
    exact q2_reading_ten_ne_fifteen (by simpa [hx, hy] using h2)
  · exfalso
    exact q2_reading_zero_ne_fifteen (by simpa [hx, hy] using h2.symm)
  · exfalso
    exact q2_reading_ten_ne_fifteen (by simpa [hx, hy] using h2.symm)
  · exact hx.trans hy.symm

private theorem q2_q5_collision_on_ternary :
    MergesOn ternaryCarrier {q2, q5} ternary0 ternary10 := by
  simpa [MergesOn, restrictedReading, ternary0, ternary10, Merges] using
    q2_q5_collision.2

private theorem q3_q5_collision_on_ternary :
    MergesOn ternaryCarrier {q3, q5} ternary0 ternary15 := by
  simpa [MergesOn, restrictedReading, ternary0, ternary15, Merges] using
    q3_q5_collision.2

private theorem ternary0_ne_ternary10 : ternary0 ≠ ternary10 := by
  intro h
  have hval := congrArg Subtype.val h
  exact (by decide : (0 : ZMod 30) ≠ 10) (by simpa [ternary0, ternary10] using hval)

private theorem ternary0_ne_ternary15 : ternary0 ≠ ternary15 := by
  intro h
  have hval := congrArg Subtype.val h
  exact (by decide : (0 : ZMod 30) ≠ 15) (by simpa [ternary0, ternary15] using hval)

private theorem fewer_than_two_incomplete_on_ternary
    (s : Finset Coordinate) (hs : s.card < 2) :
    ¬CompleteOn ternaryCarrier s := by
  by_cases h2 : q2 ∈ s
  · by_cases h3 : q3 ∈ s
    · have hsub : {q2, q3} ⊆ s := by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl <;> assumption
      have hcard := Finset.card_le_card hsub
      have : 2 ≤ s.card := by simpa [q2, q3] using hcard
      omega
    · apply mergesOn_not_complete ternary0_ne_ternary10
      apply mergesOn_of_subset ternary0_ne_ternary10 _ q2_q5_collision_on_ternary
      intro q hq
      rcases coordinate_cases q with rfl | rfl | rfl
      · simp
      · exact (h3 hq).elim
      · simp
  · apply mergesOn_not_complete ternary0_ne_ternary15
    apply mergesOn_of_subset ternary0_ne_ternary15 _ q3_q5_collision_on_ternary
    intro q hq
    rcases coordinate_cases q with rfl | rfl | rfl
    · exact (h2 hq).elim
    · simp
    · simp

private theorem fewer_than_three_incomplete_on_quaternary
    (s : Finset Coordinate) (hs : s.card < 3) :
    ¬CompleteOn quaternaryCarrier s := by
  by_cases h2 : q2 ∈ s
  · by_cases h3 : q3 ∈ s
    · by_cases h5 : q5 ∈ s
      · have hsub : {q2, q3, q5} ⊆ s := by
          intro q hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl <;> assumption
        have hcard := Finset.card_le_card hsub
        have : 3 ≤ s.card := by simpa [q2, q3, q5] using hcard
        omega
      · apply mergesOn_not_complete
        · exact state15_ne_state21
        · apply mergesOn_of_subset state15_ne_state21 _ q2_q3_collision_on_quaternary
          intro q hq
          rcases coordinate_cases q with rfl | rfl | rfl
          · simp
          · simp
          · exact (h5 hq).elim
    · apply mergesOn_not_complete
      · exact state0_ne_state10
      · apply mergesOn_of_subset state0_ne_state10 _ q2_q5_collision_on_quaternary
        intro q hq
        rcases coordinate_cases q with rfl | rfl | rfl
        · simp
        · exact (h3 hq).elim
        · simp
  · apply mergesOn_not_complete
    · exact state0_ne_state15
    · apply mergesOn_of_subset state0_ne_state15 _ q3_q5_collision_on_quaternary
      intro q hq
      rcases coordinate_cases q with rfl | rfl | rfl
      · exact (h2 hq).elim
      · simp
      · simp

private theorem quaternary_dimension_eq_three :
    statisticalDimensionOn quaternaryCarrier = 3 := by
  classical
  rw [statisticalDimensionOn, Nat.find_eq_iff]
  constructor
  · have hall : ({q2, q3, q5} : Finset Coordinate) = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro q
      rcases coordinate_cases q with rfl | rfl | rfl <;> simp
    refine ⟨{q2, q3, q5}, ?_, ?_⟩
    · norm_num [q2, q3, q5]
    · rw [hall]
      exact all_coordinates_complete_on quaternaryCarrier
  · intro n hn
    rintro ⟨s, hcard, hcomplete⟩
    apply fewer_than_three_incomplete_on_quaternary s (by omega)
    exact hcomplete

/-- The three-state carrier `{0,10,15}` has statistical dimension two, so the
dimension genuinely depends on the supplied carrier. -/
theorem ternary_dimension_eq_two : statisticalDimensionOn ternaryCarrier = 2 := by
  classical
  rw [statisticalDimensionOn, Nat.find_eq_iff]
  constructor
  · exact ⟨{q2, q3}, by norm_num [q2, q3], q2_q3_complete_on_ternary⟩
  · intro n hn
    rintro ⟨s, hcard, hcomplete⟩
    apply fewer_than_two_incomplete_on_ternary s (by omega)
    exact hcomplete

/-- On the source carrier `X = {0,10,15,21}`, each fixed coordinate pair has
the stated collision and the least complete coordinate count is three. -/
theorem quaternary_statistical_dimension_eq_three
    : MergesOn quaternaryCarrier {q2, q3} state15 state21 /\
      MergesOn quaternaryCarrier {q2, q5} state0 state10 /\
      MergesOn quaternaryCarrier {q3, q5} state0 state15 /\
      statisticalDimensionOn quaternaryCarrier = 3 := by
  exact ⟨q2_q3_collision_on_quaternary,
    q2_q5_collision_on_quaternary,
    q3_q5_collision_on_quaternary,
    quaternary_dimension_eq_three⟩

#print axioms quaternary_statistical_dimension_eq_three
#print axioms ternary_dimension_eq_two

end D5.S3.Observer.ArithmeticTomography.QuaternaryResidueCoordinateDimension
