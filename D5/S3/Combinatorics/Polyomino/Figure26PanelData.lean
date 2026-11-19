/- GID: D5/S3/Combinatorics/Polyomino/Figure26PanelData
   generality: I
   mirror-B: none(waiver:covered-by-figure-26-prismaticity-blueprint)
   mirror-E: none(waiver:panel-witness-data)
   anchors: []
   utility: none
   digest: Figure 26 panel coordinates, colorings, and ordered spanning-tree edges. -/

import D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Polyomino.Figure26PanelData

open D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory (Point)

/-- Figure 26 left, in axial coordinates suited to the three arms. -/
def leftPattern : Fin 4 → Point := ![(0, 1), (0, 0), (-1, 0), (1, -1)]

/-- Figure 26 right, in axial coordinates suited to the two columns. -/
def rightPattern : Fin 4 → Point := ![(1, 1), (1, 0), (0, 2), (0, 0)]

def leftBoard : Finset Point :=
  {(0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1),
   (2, 0), (2, 1), (2, 2), (2, 3), (3, -2), (3, -1), (3, 0),
   (3, 1), (3, 2), (3, 3), (4, -2), (4, -1), (4, 0), (4, 1),
   (4, 2), (5, -3), (5, -2), (5, -1), (5, 0), (6, -3), (6, -2)}

private def leftGray : Finset Point :=
  {(1, 0), (1, 2), (2, -1), (2, 1), (2, 2), (3, -1), (3, 0),
   (3, 1), (4, 1), (4, 2), (5, -3), (5, 0), (6, -2)}

def leftColor (p : Point) : Bool := decide (p ∈ leftGray)

def rightBoard : Finset Point :=
  {(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6),
   (0, 7), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5),
   (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5),
   (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 1), (4, 2)}

private def rightGray : Finset Point :=
  {(0, 1), (0, 3), (1, 0), (1, 2), (1, 3), (1, 6), (2, 0),
   (2, 1), (2, 3), (2, 4), (2, 5), (3, 3)}

def rightColor (p : Point) : Bool := decide (p ∈ rightGray)

/-- Convert the left proof coordinates to the issue coordinates. -/
def leftAxes : Point ≃+ Point where
  toFun p := (-p.1, -p.2)
  invFun p := (-p.1, -p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  map_add' p q := by ext <;> simp [add_comm]

/-- Convert the right proof coordinates to the issue coordinates. -/
def rightAxes : Point ≃+ Point where
  toFun p := (-p.2, -p.1)
  invFun p := (-p.2, -p.1)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  map_add' p q := by ext <;> simp [add_comm]

def pointAxes (e : Point ≃+ Point) (s : Point) : Point ↪ Point where
  toFun p := e p + s
  inj' := fun _ _ h => e.injective (add_right_cancel h)

/-- Adjust an anchor by the opposite shift from the glyph offsets. -/
def anchorAxes (e : Point ≃+ Point) (s : Point) : Point ↪ Point where
  toFun t := e t - s
  inj' := fun _ _ h => e.injective (sub_left_inj.mp h)

/-- Spanning-tree edges for the left pattern, listed as (child, parent). -/
def leftPatternTree : List (Point × Point) := [
    ((0, 0), (-1, 0)), ((0, 1), (0, 0)), ((1, -1), (0, 0))]

/-- Spanning-tree edges for the left board, listed as (child, parent). -/
def leftBoardTree : List (Point × Point) := [
    ((1, 0), (0, 0)), ((0, 1), (0, 0)), ((1, -1), (0, 0)), ((2, 0), (1, 0)),
    ((1, 1), (1, 0)), ((2, -1), (1, 0)), ((3, 0), (2, 0)), ((2, 1), (2, 0)),
    ((3, -1), (2, 0)), ((1, 2), (1, 1)), ((3, -2), (2, -1)), ((4, 0), (3, 0)),
    ((3, 1), (3, 0)), ((4, -1), (3, 0)), ((2, 2), (2, 1)), ((4, -2), (3, -1)),
    ((5, 0), (4, 0)), ((4, 1), (4, 0)), ((5, -1), (4, 0)), ((3, 2), (3, 1)),
    ((5, -2), (4, -1)), ((2, 3), (2, 2)), ((5, -3), (4, -2)), ((4, 2), (4, 1)),
    ((6, -2), (5, -1)), ((3, 3), (3, 2)), ((6, -3), (5, -2))]

/-- Spanning-tree edges for the right pattern, listed as (child, parent). -/
def rightPatternTree : List (Point × Point) := [
    ((1, 0), (0, 0)), ((1, 1), (1, 0)), ((0, 2), (1, 1))]

/-- Spanning-tree edges for the right board, listed as (child, parent). -/
def rightBoardTree : List (Point × Point) := [
    ((1, 0), (0, 0)), ((0, 1), (0, 0)), ((2, 0), (1, 0)), ((1, 1), (1, 0)),
    ((0, 2), (0, 1)), ((3, 0), (2, 0)), ((2, 1), (2, 0)), ((1, 2), (1, 1)),
    ((0, 3), (0, 2)), ((3, 1), (3, 0)), ((2, 2), (2, 1)), ((1, 3), (1, 2)),
    ((0, 4), (0, 3)), ((4, 1), (3, 1)), ((3, 2), (3, 1)), ((2, 3), (2, 2)),
    ((1, 4), (1, 3)), ((0, 5), (0, 4)), ((4, 2), (4, 1)), ((3, 3), (3, 2)),
    ((2, 4), (2, 3)), ((1, 5), (1, 4)), ((0, 6), (0, 5)), ((3, 4), (3, 3)),
    ((2, 5), (2, 4)), ((1, 6), (1, 5)), ((0, 7), (0, 6))]

end D5.S3.Combinatorics.Polyomino.Figure26PanelData
