/- GID: D5/S3/StatisticalMechanics/Percolation/ThreeTerminalFaceSeparation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Percolation/ThreeTerminalFaceSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A forced-open component separates a configuration face exactly when its ac mode is absent. -/

import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusGate

namespace D5.S3.StatisticalMechanics.Percolation.ThreeTerminalFaceSeparation

open SimpleGraph ThreeTerminalBond ThreeTerminalTree ThreeTerminalCactusGate

private lemma mode_ac_iff {V : Type*} (K : SimpleGraph V) (a b c : V) :
    graphMode K a b c = .ac ↔
      ¬ K.Reachable a b ∧ ¬ K.Reachable b c ∧ K.Reachable a c := by
  classical
  by_cases hab : K.Reachable a b <;> by_cases hbc : K.Reachable b c <;>
    by_cases hac : K.Reachable a c <;> simp [graphMode,hab,hbc,hac]

private lemma reachable_closed {V : Type*} (K : SimpleGraph V) (S : Set V)
    (hclosed : ∀ {x y}, K.Adj x y → x ∈ S → y ∈ S)
    {x y : V} (hxy : K.Reachable x y) (hx : x ∈ S) : y ∈ S := by
  obtain ⟨p⟩ := hxy
  have walk_closed {u v : V} (p : K.Walk u v) : u ∈ S → v ∈ S := by
    induction p with
    | nil => exact id
    | cons huv p ih =>
      intro hu
      exact ih (hclosed huv hu)
  exact walk_closed p hx

private lemma avoiding_reachable {V : Type*} (H K U : SimpleGraph V)
    (hHK : H ≤ K) (hKU : K ≤ U) (b : V) {a c : V}
    (hac : K.Reachable a c) (hab : ¬ K.Reachable a b) :
    (sideGraph U {v | ¬ H.Reachable b v}).Reachable a c := by
  obtain ⟨p⟩ := hac
  have lift_walk {x y : V} (p : K.Walk x y) :
      (¬ K.Reachable x b) →
        (sideGraph U {v | ¬ H.Reachable b v}).Reachable x y := by
    induction p with
    | nil =>
      intro _
      exact .rfl
    | @cons x z y hxz p ih =>
      intro hxb
      have hzb : ¬ K.Reachable z b := fun h => hxb (hxz.reachable.trans h)
      have hxB : ¬ H.Reachable b x := fun h => hxb (h.mono hHK).symm
      have hzB : ¬ H.Reachable b z := fun h => hzb (h.mono hHK).symm
      exact (show (sideGraph U {v | ¬ H.Reachable b v}).Adj x z from
        ⟨hKU hxz,hxB,hzB⟩).reachable.trans (ih hzb)
  exact lift_walk p hab

/-- In an interval of allowed open graphs, an ac-separated realization exists
exactly when a and c can connect outside the forced-open component of b.
No finiteness, connectedness or cactus hypothesis is needed. -/
theorem interval_ac_iff_avoiding_forced_component {V : Type*}
    (H U : SimpleGraph V) (hHU : H ≤ U) (a b c : V)
    (ha : ¬ H.Reachable b a) (hc : ¬ H.Reachable b c) :
    (∃ K : SimpleGraph V, H ≤ K ∧ K ≤ U ∧ graphMode K a b c = .ac) ↔
      (sideGraph U {v | ¬ H.Reachable b v}).Reachable a c := by
  constructor
  · rintro ⟨K,hHK,hKU,hmode⟩
    have hm := (mode_ac_iff K a b c).mp hmode
    exact avoiding_reachable H K U hHK hKU b hm.2.2 hm.1
  · intro hac
    let B : Set V := {v | H.Reachable b v}
    let K := H ⊔ sideGraph U Bᶜ
    have hclosed : ∀ {x y}, K.Adj x y → x ∈ B → y ∈ B := by
      intro x y hxy hx
      rcases hxy with hxy | hxy
      · exact hx.trans hxy.reachable
      · exact (hxy.2.1 hx).elim
    have hKb : ¬ K.Reachable a b := by
      intro hab
      exact ha (reachable_closed K B hclosed hab.symm (.rfl : H.Reachable b b))
    have hKc : ¬ K.Reachable b c := by
      intro hbc
      exact hc (reachable_closed K B hclosed hbc (.rfl : H.Reachable b b))
    refine ⟨K,le_sup_left,sup_le hHU ?_,?_⟩
    · intro x y hxy
      exact hxy.1
    · apply (mode_ac_iff K a b c).mpr
      exact ⟨hKb,hKc,hac.mono le_sup_right⟩

/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalFaceSeparation.interval_ac_iff_avoiding_forced_component' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms interval_ac_iff_avoiding_forced_component

end D5.S3.StatisticalMechanics.Percolation.ThreeTerminalFaceSeparation
