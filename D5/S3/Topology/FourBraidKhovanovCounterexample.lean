/- GID: D5/S3/Topology/FourBraidKhovanovCounterexample
   generality: I
   mirror-B: D5/B/S3/Topology/FourBraidKhovanovCounterexample
   mirror-E: none(waiver:algebraically-proved)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Finsupp.LinearCombination]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Topology/FourBraidKhovanovCounterexample.gradedExtremeClaim; result=D5/S3/Topology/FourBraidKhovanovCounterexample.gradedExtremeClaim_refuted; claim=D5/S3/Topology/FourBraidKhovanovCounterexample.gradedExtremeClaim
   digest: The extreme integral row contradicts the graded assertion for a closed four-braid. -/

import D5.S3.Topology.FourBraidKhovanovQuantum21
import D5.S3.Topology.FourBraidKhovanovQuantum19
import D5.S3.Topology.FourBraidKhovanovQuantum17


/-! Exact coefficients and contraction identities in the signed integral cube. -/

set_option autoImplicit false

namespace D5.S3.Topology.FourBraidKhovanovCube

/-- Rank of the first nonzero framed quantum row for this diagram. -/
def framedExtremeRank (i : Int) : Nat :=
  if i = -3 then 2 else if i = -5 then 1 else 0

/-- The graded list in Corollary 1.6 of Przytycki–Silvero. The index of
the singleton is greater than or equal to the index of the other summand. -/
def AllowedExtremeRank (rank : Int → Nat) : Prop :=
  (∀ i, rank i = 0) ∨
  (∃ k : Int, ∀ i, rank i = if i = k then 1 else 0) ∨
  (∃ (k i : Int) (r : Nat), i ≤ k ∧ 1 ≤ r ∧ r ≤ 3 ∧
    ∀ t, rank t = (if t = k then 1 else 0) + (if t = i then r else 0))

private def writhe : Int :=
  (braid.map fun (positive, _) => if positive then 1 else -1).sum

private theorem writhe_eq : writhe = 7 := rfl

/-- Remark 2.1 gives the framed homological degree corresponding to
normalized degree `I = k - 2`. -/
theorem framedExtremeRank_convert (k : Nat) :
    framedExtremeRank (writhe - 2 * ((k : Int) - 2)) =
      (if k = 7 then 2 else if k = 8 then 1 else 0) := by
  have h₇ : 7 - 2 * ((k : Int) - 2) = -3 ↔ k = 7 := by omega
  have h₈ : 7 - 2 * ((k : Int) - 2) = -5 ↔ k = 8 := by omega
  simp only [writhe_eq, framedExtremeRank, h₇, h₈]

/-- The rank-two summand is in framed degree minus three, above the
singleton in degree minus five. -/
theorem framedExtremeRank_forbidden : ¬ AllowedExtremeRank framedExtremeRank := by
  rintro (zero | one | two)
  · have h := zero (-3)
    norm_num [framedExtremeRank] at h
  · obtain ⟨k, hk⟩ := one
    have h := hk (-3)
    norm_num [framedExtremeRank] at h
    split_ifs at h; omega
  · obtain ⟨k, i, r, order, _, _, hr⟩ := two
    have h₁ := hr (-3)
    have h₂ := hr (-5)
    norm_num [framedExtremeRank] at h₁ h₂
    split_ifs at h₁ h₂ <;> omega

/-- The actual signed integral cube of the displayed four-braid has no
terms in a possible higher row except at quantum degrees nineteen and
twenty-one, where it is acyclic. Quantum degree seventeen has free
cohomology of rank two at normalized degree five and rank one at six,
and its framed rank function is forbidden by Corollary 1.6. -/
theorem fourBraid_integral_extreme_counterexample :
    (∀ j > 17, j ≠ 19 → j ≠ 21 → ∀ t, stageBasis j t = #[]) ∧
    (integralRow 21).Computes (fun _ => 0) ∧
    (integralRow 19).Computes (fun _ => 0) ∧
    (integralRow 17).Computes
      (fun k => framedExtremeRank (writhe - 2 * ((k : Int) - 2))) ∧
    3 * writhe - 2 * 17 = -13 ∧
    ¬ AllowedExtremeRank framedExtremeRank := by
  refine ⟨?_, quantum21_integral, quantum19_integral, ?_, rfl, framedExtremeRank_forbidden⟩
  · intro j hj hn₁ hn₂ t
    cases t with
    | zero => rfl
    | succ k =>
      have hempty := basis_empty_of_above_or_even j k (by omega)
      simp [stageBasis, hempty]
  · simpa only [framedExtremeRank_convert] using quantum17_integral

/--
info: 'D5.S3.Topology.FourBraidKhovanovCube.fourBraid_integral_extreme_counterexample'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fourBraid_integral_extreme_counterexample


/-- In the displayed four-strand presentation, an actual extreme row is
nonzero and every row above it vanishes. Here the grading is expressed in
normalized quantum degree and the rank function is in framed degree. -/
structure IsHighestIntegralRow (j : Nat) (rank : Int → Nat) : Prop where
  computed : (integralRow j).Computes (fun k => rank (writhe - 2 * ((k : Int) - 2)))
  nonzero : ∃ k : Nat, 0 < rank (writhe - 2 * ((k : Int) - 2))
  higher : ∀ j' > j, (∀ t, stageBasis j' t = #[]) ∨
    (integralRow j').Computes (fun _ => 0)

/-- The graded conjecture of §9.1 implies this assertion for the closure
of the displayed four-strand braid. -/
def gradedExtremeClaim : Prop :=
  ∀ j rank, IsHighestIntegralRow j rank → AllowedExtremeRank rank

/-- The displayed four-strand presentation violates the graded assertion
of §9.1 at normalized quantum degree seventeen. -/
theorem gradedExtremeClaim_refuted : ¬ gradedExtremeClaim := by
  intro claim
  obtain ⟨empty, vanishes21, vanishes19, top, _, forbidden⟩ :=
    fourBraid_integral_extreme_counterexample
  apply forbidden
  apply claim 17 framedExtremeRank
  refine ⟨top, ⟨7, ?_⟩, ?_⟩
  · rw [framedExtremeRank_convert]
    decide
  · intro j hj
    rcases eq_or_ne j 19 with rfl | h19
    · exact Or.inr vanishes19
    rcases eq_or_ne j 21 with rfl | h21
    · exact Or.inr vanishes21
    exact Or.inl (empty j hj h19 h21)

end D5.S3.Topology.FourBraidKhovanovCube
