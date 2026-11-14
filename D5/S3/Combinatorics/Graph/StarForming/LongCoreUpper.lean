/- GID: D5/S3/Combinatorics/Graph/StarForming/LongCoreUpper
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/LongCoreUpper
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Original cell score and adjacent tight-cell obstruction proofs. -/

import D5.S3.Combinatorics.Graph.StarForming.LongCoreWord

/-! Local proof bodies from formal/StarForming/LongCoreUpper.lean,
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69,
Apache-2.0. The hypotheses must be extracted from the actual graph;
no numerical parameter wrapper replaces that extraction. -/


namespace D5.S3.Combinatorics.Graph.StarForming.LongCoreUpper

structure Cell where
  highLeft : Nat
  highRight : Nat
  leafLeft : Nat
  leafRight : Nat
  cut : Nat

def Cell.weight (cell : Cell) : Nat :=
  cell.highLeft + cell.highRight + cell.leafLeft + cell.leafRight + cell.cut

def Valid (cell : Cell) (evenHub oddHub : Nat) : Prop :=
  cell.highLeft ≤ 1 ∧ cell.highRight ≤ 1 ∧
  cell.leafLeft ≤ 1 ∧ cell.leafRight ≤ 1 ∧ cell.cut ≤ 1 ∧
  cell.highLeft + cell.highRight + cell.leafLeft ≤ 2 ∧
  cell.highLeft + cell.highRight + cell.leafRight ≤ 2 ∧
  cell.leafLeft + cell.highLeft + cell.cut ≤ 2 ∧
  cell.leafRight + cell.highRight + cell.cut ≤ 2 ∧
  cell.leafLeft + cell.highLeft + evenHub ≤ 2 ∧
  cell.leafRight + cell.highRight + oddHub ≤ 2 ∧
  cell.leafLeft + cell.cut + evenHub ≤ 2 ∧
  cell.leafRight + cell.cut + oddHub ≤ 2

def Across (first second : Cell) : Prop :=
  first.highLeft + first.highRight + second.highLeft ≤ 2 ∧
  first.leafRight + first.highRight + second.highLeft ≤ 2 ∧
  first.highRight + second.highLeft + second.highRight ≤ 2 ∧
  first.cut + first.leafRight + second.cut ≤ 2

theorem cell_cap (cell : Cell) (evenHub oddHub : Nat)
    (hvalid : Valid cell evenHub oddHub) : cell.weight ≤ 3 := by
  rcases hvalid with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _⟩
  unfold Cell.weight
  omega

theorem one_hub_tight (cell : Cell) (hvalid : Valid cell 1 0)
    (htight : cell.weight = 3) :
    (cell.cut = 0 ∧ cell.leafLeft = 1 ∧ cell.leafRight = 1 ∧
      cell.highLeft = 0 ∧ cell.highRight = 1) ∨
    (cell.cut = 1 ∧ cell.leafLeft = 0 ∧ cell.highLeft = 1 ∧
      cell.highRight + cell.leafRight = 1) := by
  rcases hvalid with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _⟩
  unfold Cell.weight at htight
  omega

theorem two_hub_tight (cell : Cell) (hvalid : Valid cell 1 1)
    (htight : cell.weight = 3) :
    cell.cut = 1 ∧ cell.leafLeft = 0 ∧ cell.leafRight = 0 ∧
      cell.highLeft = 1 ∧ cell.highRight = 1 := by
  rcases hvalid with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _⟩
  unfold Cell.weight at htight
  omega

theorem one_hub_next_cut (first second : Cell)
    (hfirst : Valid first 1 0) (hsecond : Valid second 1 0)
    (htightFirst : first.weight = 3) (htightSecond : second.weight = 3)
    (hacross : Across first second) : second.cut = 0 := by
  have hshapeFirst := one_hub_tight first hfirst htightFirst
  have hshapeSecond := one_hub_tight second hsecond htightSecond
  rcases hacross with ⟨_, _, _, _⟩
  rcases hshapeFirst with ⟨_, _, _, _, _⟩ | ⟨_, _, _, _⟩ <;>
    rcases hshapeSecond with ⟨_, _, _, _, _⟩ | ⟨_, _, _, _⟩ <;> omega

theorem one_hub_block (first middle last : Cell)
    (hfirst : Valid first 1 0) (hmiddle : Valid middle 1 0)
    (hlast : Valid last 1 0) (hfirstAcross : Across first middle)
    (hlastAcross : Across middle last)
    (hhub : middle.leafLeft + last.leafLeft + 1 ≤ 2) :
    3 + first.weight + middle.weight + last.weight + 1 ≤ 12 := by
  have hcapFirst := cell_cap first 1 0 hfirst
  have hcapMiddle := cell_cap middle 1 0 hmiddle
  have hcapLast := cell_cap last 1 0 hlast
  by_cases hall : first.weight = 3 ∧ middle.weight = 3 ∧ last.weight = 3
  · obtain ⟨htightFirst, htightMiddle, htightLast⟩ := hall
    have hcutMiddle := one_hub_next_cut first middle hfirst hmiddle
      htightFirst htightMiddle hfirstAcross
    have hcutLast := one_hub_next_cut middle last hmiddle hlast
      htightMiddle htightLast hlastAcross
    have hshapeMiddle := one_hub_tight middle hmiddle htightMiddle
    have hshapeLast := one_hub_tight last hlast htightLast
    omega
  · omega

theorem two_hub_block (first middle last : Cell)
    (hfirst : Valid first 1 1) (hmiddle : Valid middle 1 1)
    (hlast : Valid last 1 1) (hfirstAcross : Across first middle)
    (hlastAcross : Across middle last) :
    3 + first.weight + middle.weight + last.weight + 2 ≤ 13 ∧
    (3 + first.weight + middle.weight + last.weight + 2 = 13 →
      first.weight = 3 ∧ middle.weight = 2 ∧ last.weight = 3) := by
  have hcapFirst := cell_cap first 1 1 hfirst
  have hcapMiddle := cell_cap middle 1 1 hmiddle
  have hcapLast := cell_cap last 1 1 hlast
  have hnonadjacentFirst : ¬ (first.weight = 3 ∧ middle.weight = 3) := by
    rintro ⟨htightFirst, htightMiddle⟩
    have hshapeFirst := two_hub_tight first hfirst htightFirst
    have hshapeMiddle := two_hub_tight middle hmiddle htightMiddle
    rcases hfirstAcross with ⟨_, _, _, _⟩
    omega
  have hnonadjacentLast : ¬ (middle.weight = 3 ∧ last.weight = 3) := by
    rintro ⟨htightMiddle, htightLast⟩
    have hshapeMiddle := two_hub_tight middle hmiddle htightMiddle
    have hshapeLast := two_hub_tight last hlast htightLast
    rcases hlastAcross with ⟨_, _, _, _⟩
    omega
  omega

end D5.S3.Combinatorics.Graph.StarForming.LongCoreUpper
