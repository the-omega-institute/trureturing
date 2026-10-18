/- GID: D5/S3/StatisticalMechanics/Percolation/ThreeTerminalWiredSeparation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Percolation/ThreeTerminalWiredSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A forced-open separator localizes the two terminal connections to opposite edge coordinates. -/

import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalFaceSeparation

/-! A wired component supports exact localization of all terminal connections. -/

namespace D5.S3.StatisticalMechanics.Percolation.ThreeTerminalWiredSeparation

open SimpleGraph ThreeTerminalBond ThreeTerminalTree ThreeTerminalCactusGate
open ThreeTerminalFaceSeparation

noncomputable section

local instance classical_decidable (P : Prop) : Decidable P := Classical.propDecidable P

/-- The actual edges touching a given vertex set. -/
def touchGraph {V : Type*} (K : SimpleGraph V) (A : Set V) : SimpleGraph V where
  Adj x y := K.Adj x y ∧ (x ∈ A ∨ y ∈ A)
  symm := by
    constructor
    intro x y h
    exact ⟨h.1.symm,h.2.symm⟩
  loopless := by
    constructor
    intro x h
    exact K.irrefl h.1

/-- When the forced-open component of b separates a and c, their connections
to b are determined by disjoint sets of variable edges. The complete actual
partition is consequently read from those two connection bits. -/
theorem wired_separation {V : Type*} (H U K : SimpleGraph V)
    (hHK : H ≤ K) (hKU : K ≤ U) (a b c : V)
    (ha : ¬ H.Reachable b a) (hc : ¬ H.Reachable b c)
    (hsep : ¬ (sideGraph U {v | ¬ H.Reachable b v}).Reachable a c) :
    let A := {v | (sideGraph U {v | ¬ H.Reachable b v}).Reachable a v}
    let L := H ⊔ touchGraph K A
    let R := H ⊔ sideGraph K Aᶜ
    (K.Reachable a b ↔ L.Reachable a b) ∧
      (K.Reachable b c ↔ R.Reachable b c) ∧
      (K.Reachable a c ↔ L.Reachable a b ∧ R.Reachable b c) ∧
      graphMode K a b c =
        if L.Reachable a b then (if R.Reachable b c then .all else .ab)
        else if R.Reachable b c then .bc else .separate := by
  classical
  let F := sideGraph U {v | ¬ H.Reachable b v}
  let A : Set V := {v | F.Reachable a v}
  let L := H ⊔ touchGraph K A
  let R := H ⊔ sideGraph K Aᶜ
  change (K.Reachable a b ↔ L.Reachable a b) ∧
    (K.Reachable b c ↔ R.Reachable b c) ∧
    (K.Reachable a c ↔ L.Reachable a b ∧ R.Reachable b c) ∧
    graphMode K a b c =
      if L.Reachable a b then (if R.Reachable b c then .all else .ab)
      else if R.Reachable b c then .bc else .separate
  have haA : a ∈ A := .rfl
  have hAB {x : V} (hx : x ∈ A) : ¬ H.Reachable b x := by
    by_cases hax : a = x
    · simpa only [← hax] using ha
    · obtain ⟨p⟩ := hx
      exact (p.adj_penultimate (Walk.not_nil_of_ne hax)).2.2
  have hbA : b ∉ A := fun hb => hAB hb .rfl
  have hcA : c ∉ A := hsep
  have boundary {x y : V} (hx : x ∈ A) (hxy : U.Adj x y) (hy : y ∉ A) :
      H.Reachable b y := by
    by_contra hyB
    exact hy (hx.trans (show F.Adj x y from ⟨hxy,hAB hx,hyB⟩).reachable)
  have hLK : L ≤ K := sup_le hHK (fun _ _ h => h.1)
  have hRK : R ≤ K := sup_le hHK (fun _ _ h => h.1)
  have liftL {x y : V} (p : K.Walk x y) :
      ((x ∈ A ∧ L.Reachable a x) ∨ L.Reachable a b) →
        ((y ∈ A ∧ L.Reachable a y) ∨ L.Reachable a b) := by
    induction p with
    | nil => exact id
    | @cons x z y hxz p ih =>
      intro hx
      apply ih
      rcases hx with ⟨hxA,hax⟩ | hab
      · have hl : L.Adj x z := Or.inr ⟨hxz,Or.inl hxA⟩
        have haz : L.Reachable a z := hax.trans hl.reachable
        by_cases hzA : z ∈ A
        · exact Or.inl ⟨hzA,haz⟩
        · exact Or.inr (haz.trans ((boundary hxA (hKU hxz) hzA).mono
            (show H ≤ L from le_sup_left)).symm)
      · exact Or.inr hab
  have liftR {x y : V} (p : K.Walk x y) :
      (x ∈ A ∨ R.Reachable b x) → (y ∈ A ∨ R.Reachable b y) := by
    induction p with
    | nil => exact id
    | @cons x z y hxz p ih =>
      intro hx
      apply ih
      by_cases hzA : z ∈ A
      · exact Or.inl hzA
      · apply Or.inr
        by_cases hxA : x ∈ A
        · exact (boundary hxA (hKU hxz) hzA).mono (show H ≤ R from le_sup_left)
        · rcases hx with hx | hbx
          · exact (hxA hx).elim
          · exact hbx.trans (show R.Adj x z from Or.inr ⟨hxz,hxA,hzA⟩).reachable
  have hleft : K.Reachable a b ↔ L.Reachable a b := by
    constructor
    · rintro ⟨p⟩
      rcases liftL p (Or.inl ⟨haA,.rfl⟩) with h | h
      · exact (hbA h.1).elim
      · exact h
    · exact Reachable.mono hLK
  have hright : K.Reachable b c ↔ R.Reachable b c := by
    constructor
    · rintro ⟨p⟩
      rcases liftR p (Or.inr .rfl) with h | h
      · exact (hcA h).elim
      · exact h
    · exact Reachable.mono hRK
  have hnoac : graphMode K a b c ≠ .ac := by
    intro hmode
    exact hsep ((interval_ac_iff_avoiding_forced_component H U (hHK.trans hKU)
      a b c ha hc).mp ⟨K,hHK,hKU,hmode⟩)
  have hcross : K.Reachable a c ↔ L.Reachable a b ∧ R.Reachable b c := by
    constructor
    · intro hac
      have hab : K.Reachable a b := by
        by_contra hab
        have hbc : ¬ K.Reachable b c := fun h => hab (hac.trans h.symm)
        exact hnoac (by simp [graphMode,hab,hbc,hac])
      exact ⟨hleft.mp hab,hright.mp (hab.symm.trans hac)⟩
    · rintro ⟨hab,hbc⟩
      exact (hleft.mpr hab).trans (hright.mpr hbc)
  refine ⟨hleft,hright,hcross,?_⟩
  by_cases hl : L.Reachable a b <;> by_cases hr : R.Reachable b c <;>
    simp [graphMode,hleft,hright,hcross,hl,hr]

/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalWiredSeparation.wired_separation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wired_separation

end
end D5.S3.StatisticalMechanics.Percolation.ThreeTerminalWiredSeparation
