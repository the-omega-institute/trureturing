/- GID: D5/S3/Combinatorics/Graph/SuvagiyaSignedSquareCycleRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/SuvagiyaSignedSquareCycleRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Spectrum, mathlib/module/Mathlib.FieldTheory.IsAlgClosed.Spectrum, mathlib/module/Mathlib.Topology.Order.IntermediateValue]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/SuvagiyaSignedSquareCycleRefutation.claim; result=D5/S3/Combinatorics/Graph/SuvagiyaSignedSquareCycleRefutation.result; claim=D5/S3/Combinatorics/Graph/SuvagiyaSignedSquareCycleRefutation.claim
   digest: A signed square-cycle on 32 vertices refutes Conjecture 28. -/

/-
proof_shape: result: bind-only
escape_witness: none
admission_basis: open-problem-resolution (issue #11744)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000

namespace D5.S3.Combinatorics.Graph.SuvagiyaSignedSquareCycleRefutation

/-- Independent signs of the forward edges of lengths one and two. -/
abbrev Signing (n : Nat) := (Fin n → Bool) × (Fin n → Bool)

/-- A Boolean represents either of the two allowed edge weights. -/
def edgeSign (b : Bool) : ℚ := if b then 1 else -1

/-- Forward edges of the square-cycle, with all signs independent. -/
def forward {n : Nat} (σ : Signing n) : Matrix (Fin n) (Fin n) ℚ := fun i j =>
  if j.val = (i.val + 1) % n then edgeSign (σ.1 i)
  else if j.val = (i.val + 2) % n then edgeSign (σ.2 i) else 0

/-- The actual undirected signed adjacency matrix. -/
def adjacencyRat {n : Nat} (σ : Signing n) : Matrix (Fin n) (Fin n) ℚ :=
  forward σ + (forward σ).transpose

/-- The same matrix over the real numbers. -/
noncomputable def adjacency {n : Nat} (σ : Signing n) : Matrix (Fin n) (Fin n) ℝ :=
  (adjacencyRat σ).map (Rat.castHom ℝ)

def quartic (x : ℝ) : ℝ := x ^ 4 - 2 * x ^ 3 - 6 * x ^ 2 + 12 * x - 4

def quarticRoots : Set ℝ := {x | quartic x = 0}

/-- Attained maximum absolute spectral values, for every independent signing. -/
def radiusValues (n : Nat) : Set ℝ :=
  {s | ∃ σ : Signing n, IsGreatest (abs '' spectrum ℝ (adjacency σ)) s}

/-- The full integer-indexed assertion of Conjecture 28. -/
def claim : Prop := ∀ m : Int, 4 ≤ m →
  ∃ r : ℝ, IsGreatest quarticRoots r ∧ IsLeast (radiusValues (8 * m.toNat)) r

private def witness : Signing 32 :=
  (fun i => decide (i.val ≠ 31),
   fun i => if i.val = 30 then false else if i.val = 31 then true
     else decide (i.val % 8 = 0 ∨ i.val % 8 = 1 ∨ i.val % 8 = 3 ∨ i.val % 8 = 6))

/-- Antiperiodic translation of eight fundamental rows. -/
private def expandRows (T : Matrix (Fin 8) (Fin 32) ℚ) : Matrix (Fin 32) (Fin 32) ℚ :=
  fun i j => (if j.val < 8 * (i.val / 8) then -1 else 1) *
    T ⟨i.val % 8, Nat.mod_lt _ (by decide)⟩
      ⟨(j.val + 32 - 8 * (i.val / 8)) % 32, Nat.mod_lt _ (by decide)⟩

private def squareRows : Matrix (Fin 8) (Fin 32) ℚ :=
  ![
    ![
      4, 0, 1, 2, -1, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, 0, -1, 0
    ],
    ![
      0, 4, 2, 1, 0, 1, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, -1, 0, -1
    ],
    ![
      1, 2, 4, 0, 1, 0, 1, 0,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, -1, 0
    ],
    ![
      2, 1, 0, 4, 0, 1, 0, -1,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 1
    ],
    ![
      -1, 0, 1, 0, 4, 0, 1, -2,
      -1, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0
    ],
    ![
      0, 1, 0, 1, 0, 4, -2, 1,
      0, 1, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0
    ],
    ![
      0, 0, 1, 0, 1, -2, 4, 0,
      1, 0, 1, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0
    ],
    ![
      0, 0, 0, -1, -2, 1, 0, 4,
      0, 1, 0, -1, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0
    ]
  ]

private def hornerRows1 : Matrix (Fin 8) (Fin 32) ℚ :=
  ![
    ![
      -28, 0, 1, 2, -1, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 1, 0, -1, 0
    ],
    ![
      0, -28, 2, 1, 0, 1, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, -1, 0, -1
    ],
    ![
      1, 2, -28, 0, 1, 0, 1, 0,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, -1, 0
    ],
    ![
      2, 1, 0, -28, 0, 1, 0, -1,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 1
    ],
    ![
      -1, 0, 1, 0, -28, 0, 1, -2,
      -1, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0
    ],
    ![
      0, 1, 0, 1, 0, -28, -2, 1,
      0, 1, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0
    ],
    ![
      0, 0, 1, 0, 1, -2, -28, 0,
      1, 0, 1, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0
    ],
    ![
      0, 0, 0, -1, -2, 1, 0, -28,
      0, 1, 0, -1, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0
    ]
  ]

private def hornerRows2 : Matrix (Fin 8) (Fin 32) ℚ :=
  ![
    ![
      312, 4, -24, -48, 25, 2, 0, 0,
      1, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0,
      -1, 0, 0, 0, -25, 2, 24, 0
    ],
    ![
      4, 312, -48, -24, 2, -23, 0, 0,
      0, 1, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, -1, 0, 0, 2, 23, 0, 24
    ],
    ![
      -24, -48, 312, 4, -24, 0, -23, -2,
      0, 0, 1, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 23, -2
    ],
    ![
      -48, -24, 4, 312, 0, -24, -2, 25,
      0, 0, 0, 1, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, -1, 0, 0, -2, -25
    ],
    ![
      25, 2, -24, 0, 312, -4, -24, 48,
      25, -2, 0, 0, 1, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, -1, 0, 0, 0
    ],
    ![
      2, -23, 0, -24, -4, 312, 48, -24,
      -2, -23, 0, 0, 0, 1, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, -1, 0, 0
    ],
    ![
      0, 0, -23, -2, -24, 48, 312, -4,
      -24, 0, -23, 2, 0, 0, 1, 0,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, -1, 0
    ],
    ![
      0, 0, -2, 25, 48, -24, -4, 312,
      0, -24, 2, 25, 0, 0, 0, 1,
      0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, -1
    ]
  ]

private def hornerRows3 : Matrix (Fin 8) (Fin 32) ℚ :=
  ![
    ![
      -1762, -80, 225, 438, -237, -36, -2, 0,
      -21, 2, 1, 2, -1, 0, 0, 0,
      0, 0, 0, 0, 1, 0, -1, 0,
      21, 2, -2, 0, 237, -44, -221, 0
    ],
    ![
      -80, -1758, 438, 225, -44, 197, 0, -2,
      -2, -19, 2, 1, 0, 1, 0, 0,
      0, 0, 0, 0, 0, -1, 0, -1,
      -2, 19, 0, -2, -36, -197, 0, -221
    ],
    ![
      225, 438, -1758, -80, 221, 0, 197, 36,
      2, 0, -19, 2, 1, 0, 1, 0,
      0, 0, 0, 0, 0, 0, -1, 0,
      -1, -2, 19, 2, 2, 0, -197, 44
    ],
    ![
      438, 225, -80, -1762, 0, 221, 44, -237,
      0, 2, -2, -21, 0, 1, 0, -1,
      0, 0, 0, 0, 0, 0, 0, 1,
      -2, -1, -2, 21, 0, 2, 36, 237
    ],
    ![
      -237, -44, 221, 0, -1762, 80, 225, -438,
      -237, 36, -2, 0, -21, -2, 1, -2,
      -1, 0, 0, 0, 0, 0, 0, 0,
      1, 0, -1, 0, 21, -2, -2, 0
    ],
    ![
      -36, 197, 0, 221, 80, -1758, -438, 225,
      44, 197, 0, -2, 2, -19, -2, 1,
      0, 1, 0, 0, 0, 0, 0, 0,
      0, -1, 0, -1, 2, 19, 0, -2
    ],
    ![
      -2, 0, 197, 44, 225, -438, -1758, 80,
      221, 0, 197, -36, 2, 0, -19, -2,
      1, 0, 1, 0, 0, 0, 0, 0,
      0, 0, -1, 0, -1, 2, 19, -2
    ],
    ![
      0, -2, 36, -237, -438, 225, 80, -1762,
      0, 221, -44, -237, 0, 2, 2, -21,
      0, 1, 0, -1, 0, 0, 0, 0,
      0, 0, 0, 1, 2, -1, 2, 21
    ]
  ]

private def hornerRows4 : Matrix (Fin 8) (Fin 32) ℚ :=
  ![
    ![
      5316, 576, -1040, -1888, 1058, 220, 32, 0,
      157, -24, -16, -32, 18, 4, 0, 0,
      0, 0, 0, 0, -18, 4, 16, 0,
      -157, -40, 32, 0, -1058, 348, 976, 0
    ],
    ![
      576, 5252, -1888, -1040, 348, -766, 0, 32,
      40, 125, -32, -16, 4, -14, 0, 0,
      0, 0, 0, 0, 4, 14, 0, 16,
      24, -125, 0, 32, 220, 766, 0, 976
    ],
    ![
      -1040, -1888, 5252, 576, -976, 0, -766, -220,
      -32, 0, 125, -24, -16, 0, -14, -4,
      0, 0, 0, 0, 0, 0, 14, -4,
      16, 32, -125, -40, -32, 0, 766, -348
    ],
    ![
      -1888, -1040, 576, 5316, 0, -976, -348, 1058,
      0, -32, 40, 157, 0, -16, -4, 18,
      0, 0, 0, 0, 0, 0, -4, -18,
      32, 16, 24, -157, 0, -32, -220, -1058
    ],
    ![
      1058, 348, -976, 0, 5316, -576, -1040, 1888,
      1058, -220, 32, 0, 157, 24, -16, 32,
      18, -4, 0, 0, 0, 0, 0, 0,
      -18, -4, 16, 0, -157, 40, 32, 0
    ],
    ![
      220, -766, 0, -976, -576, 5252, 1888, -1040,
      -348, -766, 0, 32, -40, 125, 32, -16,
      -4, -14, 0, 0, 0, 0, 0, 0,
      -4, 14, 0, 16, -24, -125, 0, 32
    ],
    ![
      32, 0, -766, -348, -1040, 1888, 5252, -576,
      -976, 0, -766, 220, -32, 0, 125, 24,
      -16, 0, -14, 4, 0, 0, 0, 0,
      0, 0, 14, 4, 16, -32, -125, 40
    ],
    ![
      0, 32, -220, 1058, 1888, -1040, -576, 5316,
      0, -976, 348, 1058, 0, -32, -40, 157,
      0, -16, 4, 18, 0, 0, 0, 0,
      0, 0, 4, -18, -32, 16, -24, -157
    ]
  ]

private def hornerRows5 : Matrix (Fin 8) (Fin 32) ℚ :=
  ![
    ![
      -8276, -1792, 2422, 3876, -2249, -520, -153, 0,
      -496, 64, 95, 166, -101, -40, -6, 0,
      0, 8, -2, 4, 101, -56, -87, 0,
      496, 256, -175, -6, 2249, -1176, -2094, 0
    ],
    ![
      -1792, -7948, 3876, 2422, -1176, 1305, 0, -153,
      -256, -328, 166, 95, -56, 53, 0, -6,
      -8, 0, 4, -2, -40, -53, 0, -87,
      -64, 328, -6, -175, -520, -1305, 0, -2094
    ],
    ![
      2422, 3876, -7948, -1792, 2094, 0, 1305, 520,
      175, 6, -328, 64, 87, 0, 53, 40,
      2, -4, 0, 8, 6, 0, -53, 56,
      -95, -166, 328, 256, 153, 0, -1305, 1176
    ],
    ![
      3876, 2422, -1792, -8276, 0, 2094, 1176, -2249,
      6, 175, -256, -496, 0, 87, 56, -101,
      -4, 2, -8, 0, 0, 6, 40, 101,
      -166, -95, -64, 496, 0, 153, 520, 2249
    ],
    ![
      -2249, -1176, 2094, 0, -8276, 1792, 2422, -3876,
      -2249, 520, -153, 0, -496, -64, 95, -166,
      -101, 40, -6, 0, 0, -8, -2, -4,
      101, 56, -87, 0, 496, -256, -175, 6
    ],
    ![
      -520, 1305, 0, 2094, 1792, -7948, -3876, 2422,
      1176, 1305, 0, -153, 256, -328, -166, 95,
      56, 53, 0, -6, 8, 0, -4, -2,
      40, -53, 0, -87, 64, 328, 6, -175
    ],
    ![
      -153, 0, 1305, 1176, 2422, -3876, -7948, 1792,
      2094, 0, 1305, -520, 175, -6, -328, -64,
      87, 0, 53, -40, 2, 4, 0, -8,
      6, 0, -53, -56, -95, 166, 328, -256
    ],
    ![
      0, -153, 520, -2249, -3876, 2422, 1792, -8276,
      0, 2094, -1176, -2249, -6, 175, 256, -496,
      0, 87, -56, -101, 4, 2, 8, 0,
      0, 6, -40, 101, 166, -95, 64, 496
    ]
  ]

private def hornerRows6 : Matrix (Fin 8) (Fin 32) ℚ :=
  ![
    ![
      5830, 2208, -2480, -3360, 2045, 374, 200, 0,
      640, 52, -248, -304, 181, 90, 48, 0,
      0, -64, 16, -32, -181, 218, 184, 0,
      -640, -564, 376, 48, -2045, 1526, 1904, 0
    ],
    ![
      2208, 5254, -3360, -2480, 1526, -787, 0, 200,
      564, 320, -304, -248, 218, -27, 0, 48,
      64, 0, -32, 16, 90, 27, 0, 184,
      -52, -320, 48, 376, 374, 787, 0, 1904
    ],
    ![
      -2480, -3360, 5254, 2208, -1904, 0, -787, -374,
      -376, -48, 320, 52, -184, 0, -27, -90,
      -16, 32, 0, -64, -48, 0, 27, -218,
      248, 304, -320, -564, -200, 0, 787, -1526
    ],
    ![
      -3360, -2480, 2208, 5830, 0, -1904, -1526, 2045,
      -48, -376, 564, 640, 0, -184, -218, 181,
      32, -16, 64, 0, 0, -48, -90, -181,
      304, 248, -52, -640, 0, -200, -374, -2045
    ],
    ![
      2045, 1526, -1904, 0, 5830, -2208, -2480, 3360,
      2045, -374, 200, 0, 640, -52, -248, 304,
      181, -90, 48, 0, 0, 64, 16, 32,
      -181, -218, 184, 0, -640, 564, 376, -48
    ],
    ![
      374, -787, 0, -1904, -2208, 5254, 3360, -2480,
      -1526, -787, 0, 200, -564, 320, 304, -248,
      -218, -27, 0, 48, -64, 0, 32, 16,
      -90, 27, 0, 184, 52, -320, -48, 376
    ],
    ![
      200, 0, -787, -1526, -2480, 3360, 5254, -2208,
      -1904, 0, -787, 374, -376, 48, 320, -52,
      -184, 0, -27, 90, -16, -32, 0, 64,
      -48, 0, 27, 218, 248, -304, -320, 564
    ],
    ![
      0, 200, -374, 2045, 3360, -2480, -2208, 5830,
      0, -1904, 1526, 2045, 48, -376, -564, 640,
      0, -184, 218, 181, -32, -16, -64, 0,
      0, -48, 90, -181, -304, 248, 52, -640
    ]
  ]

private def hornerRows7 : Matrix (Fin 8) (Fin 32) ℚ :=
  ![
    ![
      -1282, -640, 667, 802, -570, -4, 9, 0,
      -322, -128, 181, 206, -116, -52, -39, 0,
      0, 52, -13, 26, 116, -156, -129, 0,
      322, 288, -221, -126, 570, -428, -455, 0
    ],
    ![
      -640, -1070, 802, 667, -428, 146, 0, 9,
      -288, -190, 206, 181, -156, 12, 0, -39,
      -52, 0, 26, -13, -52, -12, 0, -129,
      128, 190, -126, -221, -4, -146, 0, -455
    ],
    ![
      667, 802, -1070, -640, 455, 0, 146, 4,
      221, 126, -190, -128, 129, 0, 12, 52,
      13, -26, 0, 52, 39, 0, -12, 156,
      -181, -206, 190, 288, -9, 0, -146, 428
    ],
    ![
      802, 667, -640, -1282, 0, 455, 428, -570,
      126, 221, -288, -322, 0, 129, 156, -116,
      -26, 13, -52, 0, 0, 39, 52, 116,
      -206, -181, 128, 322, 0, -9, 4, 570
    ],
    ![
      -570, -428, 455, 0, -1282, 640, 667, -802,
      -570, 4, 9, 0, -322, 128, 181, -206,
      -116, 52, -39, 0, 0, -52, -13, -26,
      116, 156, -129, 0, 322, -288, -221, 126
    ],
    ![
      -4, 146, 0, 455, 640, -1070, -802, 667,
      428, 146, 0, 9, 288, -190, -206, 181,
      156, 12, 0, -39, 52, 0, -26, -13,
      52, -12, 0, -129, -128, 190, 126, -221
    ],
    ![
      9, 0, 146, 428, 667, -802, -1070, 640,
      455, 0, 146, -4, 221, -126, -190, 128,
      129, 0, 12, -52, 13, 26, 0, -52,
      39, 0, -12, -156, -181, 206, 190, -288
    ],
    ![
      0, 9, 4, -570, -802, 667, 640, -1282,
      0, 455, -428, -570, -126, 221, 288, -322,
      0, 129, -156, -116, 26, 13, 52, 0,
      0, 39, -52, 116, 206, -181, -128, 322
    ]
  ]

private def square : Matrix (Fin 32) (Fin 32) ℚ := expandRows squareRows

private def horner (k : Fin 9) : Matrix (Fin 32) (Fin 32) ℚ :=
  match k.val with
  | 0 => 1
  | 1 => expandRows hornerRows1
  | 2 => expandRows hornerRows2
  | 3 => expandRows hornerRows3
  | 4 => expandRows hornerRows4
  | 5 => expandRows hornerRows5
  | 6 => expandRows hornerRows6
  | 7 => expandRows hornerRows7
  | _ => 0

private def coefficients (k : Fin 8) : ℚ :=
  match k.val with
  | 0 => -32
  | 1 => 416
  | 2 => -2816
  | 3 => 10568
  | 4 => -21632
  | 5 => 22168
  | 6 => -9408
  | _ => 1262

set_option maxHeartbeats 8000000 in
/-- Conjecture 28 fails for the full family of independent undirected edge signings. -/
theorem result : ¬ claim := by
  have square_eq : adjacencyRat witness * adjacencyRat witness = square := by
    decide +kernel
  have recurrence : ∀ k : Fin 8,
      horner k.castSucc * square + coefficients k • (1 : Matrix (Fin 32) (Fin 32) ℚ) =
        horner k.succ := by
    decide +kernel
  classical
  let p : Polynomial ℝ :=
    (((((((Polynomial.X - Polynomial.C 32) * Polynomial.X + Polynomial.C 416) *
      Polynomial.X - Polynomial.C 2816) * Polynomial.X + Polynomial.C 10568) *
      Polynomial.X - Polynomial.C 21632) * Polynomial.X + Polynomial.C 22168) *
      Polynomial.X - Polynomial.C 9408) * Polynomial.X + Polynomial.C 1262
  have annihilator : Polynomial.aeval (adjacency witness ^ 2) p = 0 := by
    have step := fun k => congrArg
      (fun M : Matrix (Fin 32) (Fin 32) ℚ => M.map (Rat.castHom ℝ)) (recurrence k)
    have real_square : (adjacency witness) ^ 2 = square.map (Rat.castHom ℝ) := by
      rw [pow_two, adjacency, ← Matrix.map_mul, square_eq]
    rw [real_square]
    dsimp [p]
    simp (config := { congrConsts := false }) only
      [map_add, map_sub, map_mul, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one]
    have transport : ∀ k : Fin 8,
        (horner k.castSucc).map (Rat.castHom ℝ) * square.map (Rat.castHom ℝ) +
          (coefficients k : ℝ) • (1 : Matrix (Fin 32) (Fin 32) ℝ) =
          (horner k.succ).map (Rat.castHom ℝ) := by
      intro k
      have h := step k
      rw [Matrix.map_add _ (map_add (Rat.castHom ℝ)), Matrix.map_mul,
        Matrix.map_smul' _ _ _ (map_mul (Rat.castHom ℝ)),
        Matrix.map_one _ (map_zero (Rat.castHom ℝ)) (map_one (Rat.castHom ℝ))] at h
      exact h
    have h0 := transport 0
    have h1 := transport 1
    have h2 := transport 2
    have h3 := transport 3
    have h4 := transport 4
    have h5 := transport 5
    have h6 := transport 6
    have h7 := transport 7
    norm_num (config := { congrConsts := false })
      [horner, coefficients, sub_eq_add_neg] at h0 h1 h2 h3 h4 h5 h6 h7 ⊢
    rw [h0, h1, h2, h3, h4, h5, h6, h7]
  have hermitian : (adjacency witness).IsHermitian := by
    ext i j
    change star (((forward witness j i + forward witness i j : ℚ) : ℝ)) =
      ((forward witness i j + forward witness j i : ℚ) : ℝ)
    rw [star_trivial, add_comm (forward witness j i)]
  have bound : ∀ x ∈ spectrum ℝ (adjacency witness), |x| ≤ (279 : ℝ) / 100 := by
    intro x hx
    have sqmem := spectrum.subset_polynomial_aeval (adjacency witness)
      (Polynomial.X ^ 2 : Polynomial ℝ) ⟨x, hx, rfl⟩
    have sqmem' : x ^ 2 ∈ spectrum ℝ (adjacency witness ^ 2) := by simpa using sqmem
    have pmem := spectrum.subset_polynomial_aeval (adjacency witness ^ 2) p ⟨x^2, sqmem', rfl⟩
    rw [annihilator] at pmem
    have root : Polynomial.eval (x ^ 2) p = 0 := by simpa using pmem
    by_contra hn
    have large : (279 : ℝ) / 100 < |x| := lt_of_not_ge hn
    have znonneg : 0 ≤ x ^ 2 - ((279 : ℝ) / 100) ^ 2 := by
      nlinarith [sq_abs x, sq_nonneg (|x| - (279 : ℝ) / 100)]
    let z : ℝ := x ^ 2 - ((279 : ℝ) / 100) ^ 2
    have shifted : Polynomial.eval (x ^ 2) p =

        (6810961358286782272485104951163521 / 100000000000000000000000000000000 : ℝ) +
        (3081091965223297434543430082481 / 1250000000000000000000000000 : ℝ) * z ^ 1 +
        (2710607573017634397895637287 / 250000000000000000000000 : ℝ) * z ^ 2 +
        (171709613917848847596407 / 12500000000000000000 : ℝ) * z ^ 3 +
        (7807872676823446727 / 1000000000000000 : ℝ) * z ^ 4 +
        (288484230100247 / 125000000000 : ℝ) * z ^ 5 +
        (9223588967 / 25000000 : ℝ) * z ^ 6 +
        (37841 / 1250 : ℝ) * z ^ 7 +
        (1 / 1 : ℝ) * z ^ 8 := by
      dsimp [p, z]
      simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_C]
      ring
    have positive : 0 < Polynomial.eval (x ^ 2) p := by
      rw [shifted]
      have hz : 0 ≤ z := znonneg
      positivity
    linarith
  obtain ⟨x, hx, hmax⟩ := Set.exists_max_image (spectrum ℝ (adjacency witness)) abs
    (adjacency witness).finite_real_spectrum
    ⟨hermitian.eigenvalues 0, hermitian.eigenvalues_mem_spectrum_real 0⟩
  have greatest : IsGreatest (abs '' spectrum ℝ (adjacency witness)) |x| :=
    ⟨⟨x, hx, rfl⟩, by rintro _ ⟨y, hy, rfl⟩; exact hmax y hy⟩
  have member : |x| ∈ radiusValues 32 := ⟨witness, greatest⟩
  have cont : Continuous quartic := by unfold quartic; continuity
  have endpoints : quartic ((279 : ℝ) / 100) < 0 ∧ 0 < quartic 3 := by
    norm_num [quartic]
  obtain ⟨t, ht, hroot⟩ := intermediate_value_Ioo
    (show (279 : ℝ) / 100 ≤ 3 by norm_num) cont.continuousOn endpoints
  intro hc
  obtain ⟨r, hr, hleast⟩ := hc 4 (by norm_num)
  have tr : t ≤ r := hr.2 hroot
  have rs : r ≤ |x| := hleast.2 member
  have sb := bound x hx
  linarith [ht.1]

#print axioms result

end D5.S3.Combinatorics.Graph.SuvagiyaSignedSquareCycleRefutation
