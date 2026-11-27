import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.Certificate

/-! Separate the exact corner inequalities from their use by the midpoint cover.
A table row is checked at a margin that can pay for several different cells. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.Factored

open WuCubicLowSpectrumCover (Box CornerWitness Tree checkCell checkPrune)
open WuCubicLowSpectrumRationalCorner (cornerCheck cutBiasRat lowerCoeffRat upperCoeffRat)
open private corner sortedLevels midpoint interpolationLoss from
  D5.S3.Quantum.Semigroups.WuCubicLowSpectrumCover
open private leftBox rightBox from D5.S0.Certificates.BoxCover.CheckedRationalBoxCover
open private half readOverrides from
  D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.Certificate

abbrev Shares := Fin 4 → ℚ

private def witnessAt (r m n q : ℚ) (shares : Shares) : CornerWitness :=
  ⟨shares 0 * lowerCoeffRat r m n q, shares 1 * upperCoeffRat r n q,
    shares 2 * cutBiasRat r m n q 0, shares 3 * cutBiasRat r m n q 2⟩

private def checkWitness (r m n q : ℚ) (w : CornerWitness) (margin : ℚ) : Bool :=
  cornerCheck r m n q w.L w.R w.μ₀ w.μ₂ margin

private theorem checkWitness_mono {r m n q : ℚ} {w : CornerWitness} {a b : ℚ}
    (hab : a ≤ b) (h : checkWitness r m n q w b = true) :
    checkWitness r m n q w a = true := by
  unfold checkWitness cornerCheck at *
  obtain ⟨hr, hm, hmn, hnq, hq, hL, hR, h₀, h₂, hbound⟩ := of_decide_eq_true h
  exact decide_eq_true ⟨hr, hm, hmn, hnq, hq, hL, hR, h₀, h₂, hab.trans_lt hbound⟩

structure Row where
  r : ℚ
  m : ℚ
  n : ℚ
  q : ℚ
  shares : Shares
  margin : ℚ

def Row.check (row : Row) : Bool :=
  checkWitness row.r row.m row.n row.q
    (witnessAt row.r row.m row.n row.q row.shares) row.margin

/-- A binary table addressed by low bits first, with a final sentinel bit. -/
inductive Table where
  | empty
  | entry (row : Row)
  | branch (left right : Table)

def Table.check : Table → Bool
  | .empty => true
  | .entry row => row.check
  | .branch left right => left.check && right.check

def Table.lookup : Table → ℕ → Option Row
  | .empty, _ => none
  | .entry row, key => if key = 1 then some row else none
  | .branch left right, key =>
    if key % 2 = 0 then left.lookup (key / 2) else right.lookup (key / 2)

private theorem Table.lookup_checked (table : Table) (valid : table.check = true)
    {key : ℕ} {row : Row} (found : table.lookup key = some row) : row.check = true := by
  induction table generalizing key with
  | empty => simp [Table.lookup] at found
  | entry entry =>
    simp only [Table.lookup] at found
    split at found
    · cases found
      exact valid
    · cases found
  | branch left right ihLeft ihRight =>
    obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp valid
    simp only [Table.lookup] at found
    split at found
    · exact ihLeft hl found
    · exact ihRight hr found

private def mask (ε : Fin 4 → Bool) : ℕ :=
  Fin.foldl 4 (fun index axis => 2 * index + (ε axis).toNat) 0

private def sharesAt (overrides : List (ℕ × Shares)) (index : ℕ) : Shares :=
  ((overrides.find? fun entry => entry.1.testBit index).map Prod.snd).getD half

private def witness (box : Box) (overrides : List (ℕ × Shares))
    (ε : Fin 4 → Bool) : CornerWitness :=
  let y := corner box ε
  let z := sortedLevels y
  witnessAt (y 0) (z 0) (z 1) (z 2) (sharesAt overrides (mask ε))

private def checkCorner (table : Table) (key : ℕ) (r m n q : ℚ)
    (shares : Shares) (margin : ℚ) : Bool :=
  match table.lookup key with
  | none => false
  | some row => decide (row.r = r ∧ row.m = m ∧ row.n = n ∧ row.q = q ∧
      row.shares = shares ∧ margin ≤ row.margin)

private theorem checkCorner_sound {table : Table} (valid : table.check = true)
    {key : ℕ} {r m n q : ℚ} {shares : Shares} {margin : ℚ}
    (h : checkCorner table key r m n q shares margin = true) :
    checkWitness r m n q (witnessAt r m n q shares) margin = true := by
  unfold checkCorner at h
  split at h
  · cases h
  · rename_i row found
    obtain ⟨hr, hm, hn, hq, hs, hb⟩ := of_decide_eq_true h
    rw [← hr, ← hm, ← hn, ← hq, ← hs]
    exact checkWitness_mono hb (table.lookup_checked valid found)

private def checkLeaf (table : Table) (box : Box) (floor : ℚ)
    (overrides : List (ℕ × Shares)) (keys : ℕ) : Bool :=
  decide (1 ≤ (box 0).1 ∧ (box 0).2 ≤ 6 / 5 ∧
    (∀ i : Fin 3, 0 ≤ (box i.succ).1 ∧ (box i.succ).2 ≤ 1) ∧
    ∀ ε, let y := corner box ε
         let z := sortedLevels y
         let index := mask ε
         let key := (keys >>> (16 * index)) % 65536
         checkCorner table key (y 0) (z 0) (z 1) (z 2) (sharesAt overrides index)
           (floor + interpolationLoss box) = true)

private theorem checkLeaf_sound {table : Table} (valid : table.check = true)
    {box : Box} {floor : ℚ} {overrides : List (ℕ × Shares)} {keys : ℕ}
    (h : checkLeaf table box floor overrides keys = true) :
    checkCell box floor (witness box overrides) = true := by
  unfold checkLeaf at h
  obtain ⟨hrlo, hrhi, hlevels, hcorners⟩ := of_decide_eq_true h
  unfold checkCell
  exact decide_eq_true ⟨hrlo, hrhi, hlevels, fun ε => checkCorner_sound valid (hcorners ε)⟩

/-- A midpoint tree with the original override masks and an additional table
address for each of the sixteen corners at each leaf. -/
inductive PackedTree where
  | leaf (overrides : List (ℕ × Shares)) (keys : ℕ)
  | prune
  | split (axis : Fin 4) (left right : PackedTree)

def PackedTree.toTree : PackedTree → Box → Tree
  | .leaf overrides _, box => .leaf (witness box overrides)
  | .prune, _ => .prune
  | .split axis left right, box =>
    let cut := midpoint box axis
    .split axis (left.toTree (leftBox box axis cut)) (right.toTree (rightBox box axis cut))

def PackedTree.check (table : Table) (floor : ℚ) : PackedTree → Box → Bool
  | .leaf overrides keys, box => checkLeaf table box floor overrides keys
  | .prune, box => checkPrune box
  | .split axis left right, box =>
    let cut := midpoint box axis
    left.check table floor (leftBox box axis cut) && right.check table floor (rightBox box axis cut)

theorem PackedTree.check_sound (tree : PackedTree) {table : Table} (valid : table.check = true)
    {box : Box} {floor : ℚ} (h : tree.check table floor box = true) :
    (tree.toTree box).check floor box = true := by
  induction tree generalizing box with
  | leaf overrides keys => exact checkLeaf_sound valid h
  | prune => exact h
  | split axis left right ihLeft ihRight =>
    obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp h
    exact Bool.and_eq_true_iff.mpr ⟨ihLeft hl, ihRight hr⟩

private def readTree : ℕ → ℕ → Option (PackedTree × ℕ)
  | 0, _ => none
  | depth + 1, code => do
    let tag := code % 8
    let rest := code / 8
    if tag < 4 then
      let (left, rest) ← readTree depth rest
      let (right, suffix) ← readTree depth rest
      return (.split (Fin.ofNat 4 tag) left right, suffix)
    else if tag = 4 then
      return (.prune, rest)
    else
      let (overrides, suffix) ← readOverrides (tag - 5) rest
      return (.leaf overrides (suffix % 2 ^ 256), suffix / 2 ^ 256)

def decode (depth code : ℕ) : Option PackedTree := do
  let (tree, suffix) ← readTree depth code
  if suffix = 1 then some tree else none

abbrev Accepted (table : Table) (box : Box) (decoded : Option PackedTree) : Prop :=
  decoded.map (fun tree => tree.check table (1 / 10000) box) = some true

theorem acceptedSplit {table : Table} {box : Box} (axis : Fin 4) {left right : Option PackedTree}
    (hl : Accepted table (leftBox box axis (midpoint box axis)) left)
    (hr : Accepted table (rightBox box axis (midpoint box axis)) right) :
    Accepted table box (PackedTree.split axis <$> left <*> right) := by
  obtain ⟨leftTree, hLeftTree, hLeft⟩ := Option.map_eq_some_iff.mp hl
  obtain ⟨rightTree, hRightTree, hRight⟩ := Option.map_eq_some_iff.mp hr
  rw [hLeftTree, hRightTree]
  exact congrArg some (Bool.and_eq_true_iff.mpr ⟨hLeft, hRight⟩)

theorem acceptedTree {table : Table} (valid : table.check = true)
    {box : Box} {decoded : Option PackedTree} (h : Accepted table box decoded) :
    ∃ tree : Tree, tree.check (1 / 10000) box = true := by
  obtain ⟨tree, _, accepted⟩ := Option.map_eq_some_iff.mp h
  exact ⟨tree.toTree box, tree.check_sound valid accepted⟩

#print axioms acceptedTree

end D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.Factored
