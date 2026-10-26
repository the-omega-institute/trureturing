/- GID: D5/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/BarkerMinimalGridTransfer
   mirror-E: none(waiver:internal-stage-a)
   anchors: []
   utility: none
   digest: The full open-grid frontier model distinguishes absent columns and real empty masks. -/

import D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridEncoding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Matrix.Basic

/-! The unpruned 4672-state model uses all 64 two-column starts and two absent
terminal checks. No actual-count equality or quotient compatibility is assumed. -/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridTransfer

open D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridEncoding

/-- Real masks are 0 through 7; the absent symbol is 8. -/
abbrev Symbol := Fin 9
abbrev State := Fin 4672
abbrev Window := Fin 5 → Symbol

/-- The three state blocks are (8,8,a,b), (8,a,b,c), and (a,b,c,d),
in that order, with real masks in lexicographic order. -/
def columns (s : State) : Fin 4 → Symbol :=
  if h₀ : s.val < 64 then
    ![8, 8, ⟨s.val / 8, by omega⟩, ⟨s.val % 8, by omega⟩]
  else if h₁ : s.val < 576 then
    ![8, ⟨(s.val - 64) / 64, by omega⟩,
      ⟨(s.val - 64) / 8 % 8, by omega⟩, ⟨(s.val - 64) % 8, by omega⟩]
  else
    ![⟨(s.val - 576) / 512, by omega⟩, ⟨(s.val - 576) / 64 % 8, by omega⟩,
      ⟨(s.val - 576) / 8 % 8, by omega⟩, ⟨(s.val - 576) % 8, by omega⟩]

/-- Appending a real mask drops the first symbol and advances its block. -/
def append (s : State) (m : Fin 8) : State :=
  if h₀ : s.val < 64 then
    ⟨64 + (s.val / 8) * 64 + (s.val % 8) * 8 + m.val, by omega⟩
  else if h₁ : s.val < 576 then
    ⟨576 + ((s.val - 64) / 64) * 512 + ((s.val - 64) / 8 % 8) * 64 +
      ((s.val - 64) % 8) * 8 + m.val, by omega⟩
  else
    ⟨576 + ((s.val - 576) / 64 % 8) * 512 + ((s.val - 576) / 8 % 8) * 64 +
      ((s.val - 576) % 8) * 8 + m.val, by omega⟩

/-- Different appended real masks are different full successors. -/
theorem append_injective (s : State) : Function.Injective (append s) := by
  intro a b hab
  have h := congrArg Fin.val hab
  apply Fin.ext
  by_cases h₀ : s.val < 64 <;> by_cases h₁ : s.val < 576 <;>
    simp [append, h₀, h₁] at h <;> omega

/-- The state encoding performs the literal left shift of its four columns. -/
theorem columns_append (s : State) (m : Fin 8) (i : Fin 4) :
    columns (append s m) i =
      if h : i.val < 3 then columns s ⟨i.val + 1, by omega⟩
      else ⟨m.val, by omega⟩ := by
  apply Fin.ext
  by_cases h₀ : s.val < 64
  · have ha : (append s m).val < 576 := by simp [append, h₀]; omega
    have hb : ¬ (append s m).val < 64 := by simp [append, h₀]; omega
    fin_cases i <;> simp [columns, h₀, ha, hb] <;> simp [append, h₀] <;> omega
  · by_cases h₁ : s.val < 576
    · have ha : ¬ (append s m).val < 576 := by simp [append, h₀, h₁]; omega
      have hb : ¬ (append s m).val < 64 := by omega
      fin_cases i <;> simp [columns, h₀, h₁, ha, hb] <;> simp [append, h₀, h₁] <;> omega
    · have ha : ¬ (append s m).val < 576 := by simp [append, h₀, h₁]; omega
      have hb : ¬ (append s m).val < 64 := by omega
      fin_cases i <;> simp [columns, h₀, h₁, ha, hb] <;> simp [append, h₀, h₁] <;> omega

/-- An absent column has no vertices, even when it would have a zero selection bit. -/
def present (w : Window) (v : Vertex 5) : Bool := decide ((w v.2).val < 8)

/-- Real mask zero has three existing, unselected vertices. -/
def selected (w : Window) (v : Vertex 5) : Bool :=
  present w v && (w v.2).val.testBit v.1.val

private def closed (u v : Vertex 5) : Bool :=
  decide (Nat.dist u.1.val v.1.val + Nat.dist u.2.val v.2.val ≤ 1)

/-- Domination and existential closed private witnesses at the real middle
column. Absent columns supply neither selected vertices nor possible witnesses. -/
def Local (w : Window) : Prop :=
  (∀ r : Fin 3, ∃ z : Vertex 5,
    present w z = true ∧ selected w z = true ∧ closed (r, 2) z = true) ∧
  (∀ r : Fin 3, selected w (r, 2) = true → ∃ z : Vertex 5,
    present w z = true ∧ closed z (r, 2) = true ∧
      ∀ u : Vertex 5, selected w u = true → closed z u = true → u = (r, 2))

instance localDecidable (w : Window) : Decidable (Local w) := by
  unfold Local
  infer_instance

/-- A Boolean accepts existence, without selecting or counting witnesses. -/
def accepts (w : Window) : Bool := decide (Local w)

/-- The window checked when a fifth symbol is appended. -/
def window (s : State) (a : Symbol) : Window := Fin.snoc (columns s) a

/-- The unambiguous directed transition relation on every full state. -/
def Edge (s t : State) : Prop :=
  ∃ m : Fin 8, append s m = t ∧ accepts (window s ⟨m.val, by omega⟩) = true

instance edgeDecidable (s t : State) : Decidable (Edge s t) := by
  unfold Edge
  infer_instance

/-- Each admitted edge has weight one; all other matrix entries are zero. -/
def transition : Matrix State State ℤ := fun s t => if Edge s t then 1 else 0

/-- All and only the 64 two-real-column starts have initial weight one. -/
def initial : State → ℤ := fun s => if s.val < 64 then 1 else 0

/-- Two absent-column checks finish the last two real columns. -/
def terminal : State → ℤ := fun s =>
  if accepts (window s 8) && accepts ![columns s 1, columns s 2, columns s 3, 8, 8]
    then 1 else 0

end D5.S3.Combinatorics.Graph.Domination.BarkerMinimalGridTransfer
