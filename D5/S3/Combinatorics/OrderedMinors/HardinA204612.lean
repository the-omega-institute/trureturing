/- GID: D5/S3/Combinatorics/OrderedMinors/HardinA204612
   generality: I
   mirror-B: D5/B/S3/Combinatorics/OrderedMinors/HardinA204612
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Five-column ordered-minor array counts satisfy Hardin's eleven-term recurrence. -/

/-
admission_basis: open-problem-resolution (#22895; Proved)
Public theorem D5.S3.Combinatorics.OrderedMinors.HardinA204612.result:
  proof_shape: content.
  escape_witness: D5.S3.Combinatorics.OrderedMinors.HardinA204612.count_eq_power.
The array-to-transfer-power identity depends on the structural inductions
extension_iff_path and contribution_sum; it survives the normalization-only bypass test.
This mathematical witness is distinct from the unfinished four-slot Reg audit.
Content declarations and their mathematical escape witnesses (in this module's namespace):
  extension_iff_path: proof_shape=content; escape_witness=extension_iff_path.
  contribution_sum: proof_shape=content; escape_witness=contribution_sum.
  pathCount_eq_power: proof_shape=content; escape_witness=contribution_sum.
  ordered_coding: proof_shape=content; escape_witness=extension_iff_path.
  count_rows: proof_shape=content; escape_witness=extension_iff_path.
  count_states: proof_shape=content; escape_witness=extension_iff_path.
  count_eq_power: proof_shape=content; escape_witness=extension_iff_path.
  shifted_recurrence: proof_shape=content; escape_witness=count_eq_power.
  result: proof_shape=content; escape_witness=count_eq_power.
The two structural inductions identify extensions with paths and sum their labeled
contributions. Their conclusions do not follow by normalization of the finite tables.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/26167
Direct frozen dependencies (declaration statement_id, from the source-matching Lean report):
  D5.S3.Combinatorics.NarayanaStrip.CiglerCycleWalkTransfer.weighted_walks_eq_pow
    sha256:0a48c821df6269e2755784a5d9d96495b76527600ae4f593396574cd4f512097
  D5.S3.Combinatorics.NarayanaStrip.CiglerCycleWalkTransfer.wordContribution
    sha256:a8e8be6f5bd332924e7f96a4ce42963c84d7e2a05047d3cff103a67b763b5595
  D5.S3.Combinatorics.NarayanaStrip.CiglerCycleWalkTransfer.wordContribution.congr_simp
    sha256:bdec28924a293cc9855e5c5b8f7487660d3d1f538b1a3d2d2932ee121a99fbd5
  D5.S3.Combinatorics.NarayanaStrip.CiglerCycleWalkTransfer.wordContribution.eq_1
    sha256:01f967b969de7e0233a3e59f6b941124a14d29e65863239be5eb0aec720745d6
The binary matrix carrier is written directly, and Monotone is reused without an alias.
The public count uses the adjacent integer determinant and both monotonicity directions.
Its proof identifies literal arrays with labeled paths by structural induction and
propagates a polynomial residual in a zero-total invariant subspace.
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import D5.S3.Combinatorics.NarayanaStrip.CiglerCycleWalkTransfer
import Mathlib.LinearAlgebra.Matrix.Action

namespace D5.S3.Combinatorics.OrderedMinors.HardinA204612

/-- The integer determinant of the adjacent block starting at (i,j). -/
def minor {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin 5) (Fin 2)) (i : Fin n) (j : Fin 4) : ℤ :=
  Matrix.det !![((A i.castSucc j.castSucc).val : ℤ), ((A i.castSucc j.succ).val : ℤ);
    ((A i.succ j.castSucc).val : ℤ), ((A i.succ j.succ).val : ℤ)]

/-- All adjacent-block determinants are nondecreasing rightwards and downwards. -/
def OrderedMinors {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin 5) (Fin 2)) : Prop :=
  (∀ i : Fin n, Monotone (minor A i)) ∧
    (∀ j : Fin 4, Monotone (fun i : Fin n => minor A i j))

/-- Count actual arrays, independently of any recurrence or transfer presentation. -/
noncomputable def a (n : ℕ) : ℤ :=
  (Nat.card {A : Matrix (Fin (n + 1)) (Fin 5) (Fin 2) // OrderedMinors A} : ℤ)

/-- Hardin's empirical formula, retaining every sign and the strict threshold. -/
def claim : Prop :=
  ∀ n : ℕ, 15 < n →
    a n = 18 * a (n - 1) - 73 * a (n - 2) - 256 * a (n - 3) +
      2060 * a (n - 4) - 1216 * a (n - 5) - 12612 * a (n - 6) +
      18224 * a (n - 7) + 20992 * a (n - 8) - 40064 * a (n - 9) -
      9984 * a (n - 10) + 24576 * a (n - 11)

end D5.S3.Combinatorics.OrderedMinors.HardinA204612

namespace D5.S3.Combinatorics.OrderedMinors.HardinA204612
open scoped BigOperators

private def row : (Fin 32) → (Fin 5 → Fin 2) := ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 1], ![0, 0, 0, 1, 0], ![0, 0, 0, 1, 1], ![0, 0, 1, 0, 0], ![0, 0, 1, 0, 1], ![0, 0, 1, 1, 0], ![0, 0, 1, 1, 1], ![0, 1, 0, 0, 0], ![0, 1, 0, 0, 1], ![0, 1, 0, 1, 0], ![0, 1, 0, 1, 1], ![0, 1, 1, 0, 0], ![0, 1, 1, 0, 1], ![0, 1, 1, 1, 0], ![0, 1, 1, 1, 1], ![1, 0, 0, 0, 0], ![1, 0, 0, 0, 1], ![1, 0, 0, 1, 0], ![1, 0, 0, 1, 1], ![1, 0, 1, 0, 0], ![1, 0, 1, 0, 1], ![1, 0, 1, 1, 0], ![1, 0, 1, 1, 1], ![1, 1, 0, 0, 0], ![1, 1, 0, 0, 1], ![1, 1, 0, 1, 0], ![1, 1, 0, 1, 1], ![1, 1, 1, 0, 0], ![1, 1, 1, 0, 1], ![1, 1, 1, 1, 0], ![1, 1, 1, 1, 1]]

private def delta (b c : (Fin 32)) (j : Fin 4) : ℤ :=
  minor (n := 1) ![row b, row c] 0 j


private def stateRow : (Fin 68) → (Fin 32) := ![0, 1, 1, 2, 3, 3, 3, 4, 5, 6, 7, 7, 8, 9, 9, 10, 11, 11, 12, 13, 14, 15, 15, 16, 16, 17, 17, 17, 17, 18, 18, 19, 19, 19, 19, 19, 19, 20, 21, 22, 23, 23, 24, 24, 24, 25, 25, 25, 25, 25, 25, 26, 26, 27, 27, 27, 27, 27, 28, 28, 29, 29, 30, 30, 31, 31, 31, 31]

private def stateDet : (Fin 68) → Fin 4 → ℤ := ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 1], ![-1, 0, 0, 0], ![0, 0, 0, 0], ![-1, 0, 0, 0], ![-1, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 1], ![-1, 0, 0, 0], ![0, 0, 0, 0], ![-1, 0, 0, 0], ![-1, 0, 0, 1], ![-1, 0, 1, 1], ![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 1], ![-1, -1, 0, 0], ![-1, 0, 0, 0], ![0, 0, 0, 0], ![-1, -1, 0, 0], ![-1, -1, 0, 1], ![-1, 0, 0, 0], ![-1, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 1], ![-1, 0, 0, 0], ![0, 0, 0, 0], ![-1, -1, 1, 1], ![-1, 0, 0, 0], ![-1, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 1], ![-1, 0, 0, 0], ![0, 0, 0, 0], ![-1, 0, 0, 0], ![0, 0, 0, 0], ![-1, 0, 0, 0], ![0, 0, 0, 0], ![-1, 0, 0, 0], ![-1, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 1]]

private def stateOf : (Fin 32) → (Fin 32) → (Fin 68) := ![![0, 1, 3, 4, 7, 8, 9, 10, 12, 13, 15, 16, 18, 19, 20, 21, 24, 27, 30, 34, 37, 38, 39, 40, 44, 49, 52, 56, 59, 61, 63, 66], ![0, 1, 0, 0, 7, 8, 0, 0, 12, 13, 0, 0, 18, 19, 0, 0, 24, 27, 0, 0, 37, 38, 0, 0, 44, 49, 0, 0, 59, 61, 0, 0], ![0, 2, 3, 5, 0, 0, 0, 0, 12, 14, 15, 17, 0, 0, 0, 0, 24, 28, 30, 35, 0, 0, 0, 0, 44, 50, 52, 57, 0, 0, 0, 0], ![0, 2, 0, 4, 0, 0, 0, 0, 12, 14, 0, 16, 0, 0, 0, 0, 24, 28, 0, 34, 0, 0, 0, 0, 44, 50, 0, 56, 0, 0, 0, 0], ![0, 1, 0, 0, 7, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 27, 0, 0, 37, 38, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 7, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 27, 0, 0, 37, 38, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 0, 6, 0, 0, 9, 11, 0, 0, 0, 0, 0, 0, 0, 0, 24, 28, 0, 36, 0, 0, 39, 41, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 24, 28, 0, 0, 0, 0, 0, 40, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 3, 4, 0, 0, 0, 0, 12, 13, 15, 16, 0, 0, 0, 0, 23, 25, 29, 31, 0, 0, 0, 0, 43, 47, 51, 54, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 12, 13, 0, 0, 0, 0, 0, 0, 23, 25, 0, 0, 0, 0, 0, 0, 43, 47, 0, 0, 0, 0, 0, 0], ![0, 2, 3, 5, 0, 0, 0, 0, 12, 14, 15, 17, 0, 0, 0, 0, 23, 26, 29, 32, 0, 0, 0, 0, 43, 48, 51, 55, 0, 0, 0, 0], ![0, 2, 0, 4, 0, 0, 0, 0, 12, 14, 0, 16, 0, 0, 0, 0, 23, 26, 0, 31, 0, 0, 0, 0, 43, 48, 0, 54, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 0, 0, 23, 25, 0, 0, 0, 0, 0, 0, 42, 45, 0, 0, 58, 60, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 19, 0, 0, 23, 25, 0, 0, 0, 0, 0, 0, 42, 45, 0, 0, 58, 60, 0, 0], ![0, 2, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 22, 23, 26, 0, 33, 0, 0, 0, 0, 42, 46, 0, 53, 0, 0, 62, 65], ![0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 23, 26, 0, 0, 0, 0, 0, 0, 42, 46, 0, 0, 0, 0, 0, 64], ![0, 1, 3, 4, 7, 8, 9, 10, 0, 0, 0, 0, 0, 0, 0, 0, 24, 27, 30, 34, 37, 38, 39, 40, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 7, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 27, 0, 0, 37, 38, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 3, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 28, 30, 35, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 28, 0, 34, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 7, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 27, 0, 0, 37, 38, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 7, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 27, 0, 0, 37, 38, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 0, 6, 0, 0, 9, 11, 0, 0, 0, 0, 0, 0, 0, 0, 24, 28, 0, 36, 0, 0, 39, 41, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 24, 28, 0, 0, 0, 0, 0, 40, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 23, 25, 29, 31, 0, 0, 0, 0, 44, 49, 52, 56, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 23, 25, 0, 0, 0, 0, 0, 0, 44, 49, 0, 0, 0, 0, 0, 0], ![0, 2, 3, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 23, 26, 29, 32, 0, 0, 0, 0, 44, 50, 52, 57, 0, 0, 0, 0], ![0, 2, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 23, 26, 0, 31, 0, 0, 0, 0, 44, 50, 0, 56, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 23, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 59, 61, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 23, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 59, 61, 0, 0], ![0, 2, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 23, 26, 0, 33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 63, 67], ![0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 23, 26, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 66]]

private def valid (s : (Fin 68)) (c : (Fin 32)) : Prop :=
  Monotone (delta (stateRow s) c) ∧ ∀ j, stateDet s j ≤ delta (stateRow s) c j
private instance (s : (Fin 68)) (c : (Fin 32)) : Decidable (valid s c) :=
  inferInstanceAs (Decidable (_ ∧ _))


private def incoming : (Fin 68) → Finset (Fin 68) := ![{0, 1, 3, 4, 7, 8, 9, 10, 12, 13, 15, 16, 18, 19, 20, 21, 23, 24, 25, 27, 29, 30, 31, 34, 37, 38, 39, 40, 42, 43, 44, 45, 47, 49, 51, 52, 54, 56, 58, 59, 60, 61, 62, 63, 64, 66}, {0, 1, 7, 8, 12, 13, 18, 19, 23, 24, 25, 27, 37, 38, 42, 43, 44, 45, 47, 49, 58, 59, 60, 61}, {3, 4, 5, 9, 10, 11, 15, 16, 17, 20, 21, 22, 29, 30, 31, 32, 34, 35, 39, 40, 41, 51, 52, 54, 55, 56, 57, 62, 63, 64, 65, 66, 67}, {0, 3, 12, 15, 23, 24, 29, 30, 42, 43, 44, 51, 52}, {0, 4, 12, 16, 23, 24, 31, 34, 42, 43, 44, 54, 56}, {3, 15, 29, 30, 51, 52}, {9, 20, 39, 62, 63}, {0, 1, 7, 8, 23, 24, 25, 27, 37, 38}, {0, 1, 7, 8, 23, 24, 25, 27, 37, 38}, {0, 9, 23, 24, 39}, {0, 10, 23, 24, 40}, {9, 39}, {0, 1, 3, 4, 12, 13, 15, 16}, {0, 1, 12, 13}, {3, 4, 5, 15, 16, 17}, {0, 3, 12, 15}, {0, 4, 12, 16}, {3, 15}, {0, 1, 18, 19}, {0, 1, 18, 19}, {0, 20}, {0, 21}, {20}, {42, 43, 45, 47, 51, 54, 58, 60, 62, 64}, {0, 1, 3, 4, 7, 8, 9, 10, 23, 24, 25, 27, 29, 30, 31, 34, 37, 38, 39, 40}, {42, 43, 45, 47, 58, 60}, {51, 54, 55, 62, 64, 65}, {0, 1, 7, 8, 23, 24, 25, 27, 37, 38}, {3, 4, 5, 9, 10, 11, 29, 30, 31, 32, 34, 35, 39, 40, 41}, {42, 43, 51}, {0, 3, 23, 24, 29, 30}, {42, 43, 54}, {51}, {62}, {0, 4, 23, 24, 31, 34}, {3, 29, 30}, {9, 39}, {0, 1, 7, 8, 23, 24, 25, 27, 37, 38}, {0, 1, 7, 8, 23, 24, 25, 27, 37, 38}, {0, 9, 23, 24, 39}, {0, 10, 23, 24, 40}, {9, 39}, {}, {}, {0, 1, 3, 4, 42, 43, 44, 45, 47, 49, 51, 52, 54, 56}, {}, {}, {}, {}, {0, 1, 42, 43, 44, 45, 47, 49}, {3, 4, 5, 51, 52, 54, 55, 56, 57}, {}, {0, 3, 42, 43, 44, 51, 52}, {}, {}, {}, {0, 4, 42, 43, 44, 54, 56}, {3, 51, 52}, {}, {0, 1, 58, 59, 60, 61}, {}, {0, 1, 58, 59, 60, 61}, {}, {0, 62, 63}, {}, {}, {0, 64, 66}, {62, 63}]

private def T : Matrix (Fin 68) (Fin 68) ℤ := fun t s => if s ∈ incoming t then 1 else 0

private def initial : (Fin 68 → ℤ) := ![32, 16, 16, 8, 8, 4, 4, 8, 8, 4, 4, 2, 8, 4, 4, 4, 4, 2, 4, 4, 2, 2, 1, 16, 16, 8, 8, 8, 8, 4, 4, 4, 2, 2, 4, 2, 2, 8, 8, 4, 4, 2, 4, 4, 8, 2, 2, 2, 2, 4, 4, 2, 4, 1, 2, 1, 4, 2, 2, 4, 2, 4, 1, 2, 1, 1, 2, 1]

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private theorem row_bijective : Function.Bijective row := by
  decide

private noncomputable def rowEquiv : (Fin 32) ≃ (Fin 5 → Fin 2) := Equiv.ofBijective row row_bijective

private theorem state_spec (a b : (Fin 32)) (h : Monotone (delta a b)) :
    stateRow (stateOf a b) = b ∧ stateDet (stateOf a b) = delta a b := by
  revert a b
  decide

private theorem states_horizontal (s : (Fin 68)) : Monotone (stateDet s) := by
  revert s
  decide

private theorem next_spec (s : (Fin 68)) (c : (Fin 32)) (h : valid s c) :
    stateRow ((fun s c => stateOf (stateRow s) c) s c) = c ∧ stateDet ((fun s c => stateOf (stateRow s) c) s c) = delta (stateRow s) c :=
  state_spec _ _ h.1

private theorem transfer_spec (s t : (Fin 68)) :
    T t s = if valid s (stateRow t) ∧ (fun s c => stateOf (stateRow s) c) s (stateRow t) = t then 1 else 0 := by
  revert s t
  simp only [valid, delta, minor, Matrix.det_fin_two]
  decide

private theorem initial_spec (t : (Fin 68)) : initial t =
    ∑ a : (Fin 32), if delta a (stateRow t) = stateDet t then (1 : ℤ) else 0 := by
  revert t
  decide

private theorem step_eq_mulVec (v : (Fin 68 → ℤ)) :
    (fun t => ∑ s ∈ incoming t, v s) = T.mulVec v := by
  funext t
  simp [T, Matrix.mulVec, dotProduct]

end D5.S3.Combinatorics.OrderedMinors.HardinA204612

namespace D5.S3.Combinatorics.OrderedMinors.HardinA204612
open scoped BigOperators

/-- Determinants of the appended rows, including their boundary with the old row. -/
private def newDet {k : ℕ} (b : (Fin 32)) (f : Fin k → (Fin 32)) (i : Fin k) : Fin 4 → ℤ :=
  delta (((Fin.cons b f : Fin (k+1) → (Fin 32))) i.castSucc) (f i)

/-- Local conditions on the extension after a row and its preceding minor vector. -/
private def ExtensionGood {k : ℕ} (b : (Fin 32)) (d : Fin 4 → ℤ) (f : Fin k → (Fin 32)) : Prop :=
  (∀ i, Monotone (newDet b f i)) ∧
    ∀ j, ∀ i : Fin k,
      ((Fin.cons (d j) (fun i => newDet b f i j) : Fin (k+1) → ℤ)) i.castSucc ≤ newDet b f i j

private def PathGood : {k : ℕ} → (Fin 68) → (Fin k → (Fin 32)) → Prop
  | 0, _, _ => True
  | k+1, s, f => valid s (f 0) ∧ PathGood ((fun s c => stateOf (stateRow s) c) s (f 0)) (Fin.tail f)

private instance {k : ℕ} (s : (Fin 68)) (f : Fin k → (Fin 32)) : Decidable (PathGood s f) := by
  induction k generalizing s with
  | zero => exact isTrue True.intro
  | succ k ih => exact instDecidableAnd

private theorem newDet_cons_eq {k : ℕ} (b c : (Fin 32)) (f : Fin k → (Fin 32)) :
    newDet b (Fin.cons c f) =
      (Fin.cons (delta b c) (newDet c f) : Fin (k+1) → (Fin 4 → ℤ)) := by
  funext i
  exact Fin.cases (by rfl) (fun j => by rfl) i

private theorem newDet_cons_coordinate {k : ℕ} (b c : (Fin 32)) (f : Fin k → (Fin 32)) (j : Fin 4) :
    (fun i => newDet b (Fin.cons c f) i j) =
      (Fin.cons (delta b c j) (fun i => newDet c f i j) : Fin (k+1) → ℤ) := by
  rw [newDet_cons_eq]
  exact Fin.comp_cons (fun d : Fin 4 → ℤ => d j) _ _

private theorem extension_cons {k : ℕ} (b c : (Fin 32)) (d : Fin 4 → ℤ) (f : Fin k → (Fin 32)) :
    ExtensionGood b d (Fin.cons c f) ↔
      Monotone (delta b c) ∧ (∀ j, d j ≤ delta b c j) ∧
        ExtensionGood c (delta b c) f := by
  unfold ExtensionGood
  simp_rw [newDet_cons_coordinate]
  rw [newDet_cons_eq]
  constructor
  · rintro ⟨hh,hv⟩
    refine ⟨hh 0, fun j => hv j 0, ?_, ?_⟩
    · intro i
      exact hh i.succ
    · intro j i
      have h := hv j i.succ
      simpa only [Fin.castSucc_succ, Fin.cons_succ] using h
  · rintro ⟨hh,hd,ht,hv⟩
    constructor
    · intro i
      exact Fin.cases hh (fun j => ht j) i
    · intro j i
      refine Fin.cases (hd j) (fun l => ?_) i
      simpa only [Fin.castSucc_succ, Fin.cons_succ] using hv j l

private theorem extension_iff_path {k : ℕ} (s : (Fin 68)) (f : Fin k → (Fin 32)) :
    ExtensionGood (stateRow s) (stateDet s) f ↔ PathGood s f := by
  induction k generalizing s with
  | zero => simp [ExtensionGood, PathGood]
  | succ k ih =>
    have hf : f = Fin.cons (f 0) (Fin.tail f) := (Fin.cons_self_tail f).symm
    rw [hf, extension_cons]
    change _ ↔ valid s (f 0) ∧ PathGood ((fun s c => stateOf (stateRow s) c) s (f 0)) (Fin.tail f)
    constructor
    · rintro ⟨hh, hv, ht⟩
      have h : valid s (f 0) := ⟨hh, hv⟩
      refine ⟨h, (ih ((fun s c => stateOf (stateRow s) c) s (f 0)) (Fin.tail f)).mp ?_⟩
      simpa [(next_spec s (f 0) h).1, (next_spec s (f 0) h).2] using ht
    · rintro ⟨h, ht⟩
      refine ⟨h.1, h.2, ?_⟩
      have hh := (ih ((fun s c => stateOf (stateRow s) c) s (f 0)) (Fin.tail f)).mpr ht
      simpa [(next_spec s (f 0) h).1, (next_spec s (f 0) h).2] using hh

private theorem minor_code {n : ℕ} (f : Fin (n+1) → (Fin 32)) (i : Fin n) (j : Fin 4) :
    minor (fun i => row (f i)) i j = delta (f i.castSucc) (f i.succ) j := by
  exact Int.neg_inj.mp rfl

private theorem ordered_cons {k : ℕ} (b c : (Fin 32)) (f : Fin k → (Fin 32)) :
    OrderedMinors (fun i => row ((Fin.cons b (Fin.cons c f) : Fin (k+2) → (Fin 32)) i)) ↔
      Monotone (delta b c) ∧ ExtensionGood c (delta b c) f := by
  have hm (i : Fin (k+1)) :
      minor (fun i => row ((Fin.cons b (Fin.cons c f) : Fin (k+2) → (Fin 32)) i)) i =
        newDet b (Fin.cons c f) i := by
    funext j
    exact minor_code _ i j
  unfold OrderedMinors
  simp_rw [hm]
  change ((∀ i, Monotone (newDet b (Fin.cons c f) i)) ∧
    ∀ j, Monotone (fun i => newDet b (Fin.cons c f) i j)) ↔ _
  simp_rw [newDet_cons_coordinate]
  rw [newDet_cons_eq]
  simp only [Fin.monotone_iff_le_succ, ExtensionGood]
  constructor
  · rintro ⟨hh,hv⟩
    refine ⟨hh 0, (fun i => hh i.succ), ?_⟩
    intro j i
    have h := hv j i
    exact h
  · rintro ⟨hh,ht,hv⟩
    refine ⟨?_, ?_⟩
    · intro i
      exact Fin.cases hh (fun j => ht j) i
    · intro j i
      exact hv j i

end D5.S3.Combinatorics.OrderedMinors.HardinA204612

namespace D5.S3.Combinatorics.OrderedMinors.HardinA204612
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

private def values : Fin 16 → (Fin 68 → ℤ) := ![![32, 16, 16, 8, 8, 4, 4, 8, 8, 4, 4, 2, 8, 4, 4, 4, 4, 2, 4, 4, 2, 2, 1, 16, 16, 8, 8, 8, 8, 4, 4, 4, 2, 2, 4, 2, 2, 8, 8, 4, 4, 2, 4, 4, 8, 2, 2, 2, 2, 4, 4, 2, 4, 1, 2, 1, 4, 2, 2, 4, 2, 4, 1, 2, 1, 1, 2, 1], ![262, 184, 98, 114, 114, 26, 13, 128, 128, 72, 72, 8, 84, 60, 30, 52, 52, 12, 56, 56, 34, 34, 2, 22, 176, 16, 8, 128, 60, 10, 80, 10, 2, 1, 80, 16, 8, 128, 128, 72, 72, 8, 0, 0, 100, 0, 0, 0, 0, 72, 35, 0, 62, 0, 0, 0, 62, 14, 0, 60, 0, 60, 0, 35, 0, 0, 35, 3], ![2910, 1848, 1153, 962, 962, 318, 213, 1300, 1300, 604, 604, 144, 922, 590, 370, 512, 512, 166, 558, 558, 296, 296, 34, 0, 1996, 0, 0, 1300, 756, 0, 664, 0, 0, 0, 664, 204, 144, 1300, 1300, 604, 604, 144, 0, 0, 970, 0, 0, 0, 0, 618, 392, 0, 538, 0, 0, 0, 538, 176, 0, 566, 0, 566, 0, 297, 0, 0, 297, 35], ![27556, 18602, 10175, 9474, 9474, 2676, 1801, 13254, 13254, 6114, 6114, 1208, 9218, 6270, 3432, 5306, 5306, 1474, 5874, 5874, 3206, 3206, 296, 0, 18922, 0, 0, 13254, 6478, 0, 6532, 0, 0, 0, 6532, 1626, 1208, 13254, 13254, 6114, 6114, 1208, 0, 0, 9346, 0, 0, 0, 0, 6346, 3494, 0, 5380, 0, 0, 0, 5380, 1500, 0, 5890, 0, 5890, 0, 3207, 0, 0, 3207, 297], ![276724, 186058, 100951, 91734, 91734, 26692, 18641, 131350, 131350, 58706, 58706, 12228, 91206, 61646, 33710, 51554, 51554, 14780, 57906, 57906, 30762, 30762, 3206, 0, 187818, 0, 0, 131350, 63186, 0, 62484, 0, 0, 0, 62484, 16006, 12228, 131350, 131350, 58706, 58706, 12228, 0, 0, 91558, 0, 0, 0, 0, 61850, 33884, 0, 51756, 0, 0, 0, 51756, 14854, 0, 57938, 0, 57938, 0, 30763, 0, 0, 30763, 3207], ![2718228, 1845298, 976131, 904834, 904834, 257528, 178937, 1307350, 1307350, 581954, 581954, 117412, 902210, 615634, 328048, 511218, 511218, 143288, 578594, 578594, 307486, 307486, 30762, 0, 1850610, 0, 0, 1307350, 610414, 0, 618760, 0, 0, 0, 618760, 154218, 117412, 1307350, 1307350, 581954, 581954, 117412, 0, 0, 903170, 0, 0, 0, 0, 616190, 328526, 0, 511772, 0, 0, 0, 511772, 143490, 0, 578658, 0, 578658, 0, 307487, 0, 0, 307487, 30763], ![26953524, 18302594, 9645803, 8920802, 8920802, 2546584, 1778881, 12950886, 12950886, 5732746, 5732746, 1163908, 8913474, 6081370, 3232920, 5036490, 5036490, 1416052, 5720714, 5720714, 3025714, 3025714, 307486, 0, 18325890, 0, 0, 12950886, 6021574, 0, 6092432, 0, 0, 0, 6092432, 1523594, 1163908, 12950886, 12950886, 5732746, 5732746, 1163908, 0, 0, 8916098, 0, 0, 0, 0, 6082886, 3234230, 0, 5038004, 0, 0, 0, 5038004, 1416606, 0, 5720842, 0, 5720842, 0, 3025715, 0, 0, 3025715, 307487], ![266422676, 181213378, 95054923, 88196714, 88196714, 25087728, 17516921, 128336438, 128336438, 56744906, 56744906, 11465492, 88165546, 60250962, 31877220, 49824290, 49824290, 13957292, 56697546, 56697546, 29979238, 29979238, 3025714, 0, 181293890, 0, 0, 128336438, 59355446, 0, 60292648, 0, 0, 0, 60292648, 15013234, 11465492, 128336438, 128336438, 56744906, 56744906, 11465492, 0, 0, 88172714, 0, 0, 0, 0, 60255102, 31880802, 0, 49828428, 0, 0, 0, 49828428, 13958806, 0, 56697802, 0, 56697802, 0, 29979239, 0, 0, 29979239, 3025715], ![2637427892, 1794247154, 940180211, 872196906, 872196906, 248142080, 173448289, 1270612134, 1270612134, 561206378, 561206378, 113489812, 872094570, 596052562, 315087028, 492609226, 492609226, 138021004, 561031146, 561031146, 296401914, 296401914, 29979238, 0, 1794570482, 0, 0, 1270612134, 586990294, 0, 596205928, 0, 0, 0, 596205928, 148489362, 113489812, 1270612134, 1270612134, 561206378, 561206378, 113489812, 0, 0, 872114154, 0, 0, 0, 0, 596063870, 315096818, 0, 492620532, 0, 0, 0, 492620532, 138025142, 0, 561031658, 0, 561031658, 0, 296401915, 0, 0, 296401915, 29979239], ![26097455316, 17759756962, 9297314043, 8629839690, 8629839690, 2453632592, 1715216585, 12579306198, 12579306198, 5554411130, 5554411130, 1122412756, 8629434442, 5899822178, 3115775348, 4874328594, 4874328594, 1364806132, 5553737338, 5553737338, 2933829806, 2933829806, 296401914, 0, 17760937378, 0, 0, 12579306198, 5805242246, 0, 5900401208, 0, 0, 0, 5900401208, 1468402834, 1122412756, 12579306198, 12579306198, 5554411130, 5554411130, 1122412756, 0, 0, 8629487946, 0, 0, 0, 0, 5899853070, 3115802098, 0, 4874359484, 0, 0, 0, 4874359484, 1364817438, 0, 5553738362, 0, 5553738362, 0, 2933829807, 0, 0, 2933829807, 296401915], ![258299051380, 175788229682, 92000110035, 85396244058, 85396244058, 24278928976, 16976481873, 124514680646, 124514680646, 54967214954, 54967214954, 11108822260, 85394805466, 58386468898, 30826775292, 48231058042, 48231058042, 13504168284, 54964686954, 54964686954, 29031285122, 29031285122, 2933829806, 0, 175792806962, 0, 0, 124514680646, 57444987254, 0, 58388633592, 0, 0, 0, 58388633592, 14530240898, 11108822260, 124514680646, 124514680646, 54967214954, 54967214954, 11108822260, 0, 0, 85394951642, 0, 0, 0, 0, 58386553294, 30826848378, 0, 48231142436, 0, 0, 0, 48231142436, 13504199174, 0, 54964689002, 0, 54964689002, 0, 29031285123, 0, 0, 29031285123, 2933829807], ![2556363179028, 1739875022466, 910390998027, 845128693578, 845128693578, 240247078128, 167997000153, 1232453491254, 1232453491254, 544026288250, 544026288250, 109934429908, 845123159626, 577868555426, 305037701460, 477321158946, 477321158946, 133627302100, 544016654970, 544016654970, 287330336502, 287330336502, 29031285122, 0, 1739892106370, 0, 0, 1232453491254, 568465429510, 0, 577876735992, 0, 0, 0, 577876735992, 143784877650, 109934429908, 1232453491254, 1232453491254, 544026288250, 544026288250, 109934429908, 0, 0, 845123558986, 0, 0, 0, 0, 577868785998, 305037901138, 0, 477321389516, 0, 0, 0, 477321389516, 133627386494, 0, 544016659066, 0, 544016659066, 0, 287330336503, 0, 0, 287330336503, 29031285123], ![25301170907316, 17220448452242, 9009940529507, 8364149982042, 8364149982042, 2377647978032, 1662713249505, 12198397764134, 12198397764134, 5384307861898, 5384307861898, 1088052576500, 8364129621594, 5719229916546, 3018774085276, 4723936191178, 4723936191178, 1322449852524, 5384271511434, 5384271511434, 2843693515530, 2843693515530, 287330336502, 0, 17220513776274, 0, 0, 12198397764134, 5626016827734, 0, 5719260714968, 0, 0, 0, 5719260714968, 1423005429570, 1088052576500, 12198397764134, 12198397764134, 5384307861898, 5384307861898, 1088052576500, 0, 0, 8364130712666, 0, 0, 0, 0, 5719230546478, 3018774630810, 0, 4723936821108, 0, 0, 0, 4723936821108, 1322450083094, 0, 5384271519626, 0, 5384271519626, 0, 2843693515531, 0, 0, 2843693515531, 287330336503], ![250412501744212, 170437928815906, 89170892097531, 82781228727146, 82781228727146, 23531283709296, 16456002754857, 120734121956502, 120734121956502, 53290300407386, 53290300407386, 10768615723796, 82781151244138, 56604978897698, 29876270176996, 46753386702130, 46753386702130, 13088086173220, 53290162382426, 53290162382426, 28144864422846, 28144864422846, 2843693515530, 0, 170438174798114, 0, 0, 120734121956502, 55680811402214, 0, 56605095380600, 0, 0, 0, 56605095380600, 14083410697010, 10768615723796, 120734121956502, 120734121956502, 53290300407386, 53290300407386, 10768615723796, 0, 0, 82781154225002, 0, 0, 0, 0, 56604980618702, 29876271667426, 0, 46753388423132, 0, 0, 0, 46753388423132, 13088086803150, 0, 53290162398810, 0, 53290162398810, 0, 28144864422847, 0, 0, 28144864422847, 2843693515531], ![2478418987475700, 1686892129688754, 882542343648275, 819306081244474, 819306081244474, 232893099233008, 162870329660465, 1194959215140742, 1194959215140742, 527431277357098, 527431277357098, 106580600814772, 819305791560506, 560236560701954, 295688600741068, 462728268417626, 462728268417626, 129534615429276, 527430755324970, 527430755324970, 278557366167058, 278557366167058, 28144864422846, 0, 1686893064985778, 0, 0, 1194959215140742, 551085775698934, 0, 560237000650072, 0, 0, 0, 560237000650072, 139386324107746, 106580600814772, 1194959215140742, 1194959215140742, 527431277357098, 527431277357098, 106580600814772, 0, 0, 819305799704378, 0, 0, 0, 0, 560236565403822, 295688604813002, 0, 462728273119492, 0, 0, 0, 462728273119492, 129534617150278, 0, 527430755357738, 0, 527430755357738, 0, 278557366167059, 0, 0, 278557366167059, 28144864422847], ![24529761817549972, 16695807996590018, 8734753407355499, 8108923267158026, 8108923267158026, 2304999623431664, 1611977287048313, 11827000257853942, 11827000257853942, 5220174607175674, 5220174607175674, 1054862554714196, 8108922168751114, 5544853469426914, 2926496413986484, 4579759128698306, 4579759128698306, 1282034349662100, 5220172627814394, 5220172627814394, 2756976353642758, 2756976353642758, 278557366167058, 0, 16695811531071426, 0, 0, 11827000257853942, 5454251898187782, 0, 5544855134356024, 0, 0, 0, 5544855134356024, 1379543081894546, 1054862554714196, 11827000257853942, 11827000257853942, 5220174607175674, 5220174607175674, 1054862554714196, 0, 0, 8108922191000586, 0, 0, 0, 0, 5544853482272654, 2926496425111218, 0, 4579759141544044, 0, 0, 0, 4579759141544044, 1282034354363966, 0, 5220172627879930, 0, 5220172627879930, 0, 2756976353642759, 0, 0, 2756976353642759, 278557366167059]]

private def G : Matrix (Fin 68) (Fin 11) ℤ := ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

private def H : Matrix (Fin 11) (Fin 11) ℤ := ![![1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0], ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]]

private def p : Fin 12 → ℤ := ![-24576, 9984, 40064, -20992, -18224, 12612, 1216, -2060, 256, 73, -18, 1]

private def q : Fin 11 → ℤ := ![565248, 327936, 284288, 329600, 329600, 118656, 6144, 6144, -832, -832, -832]

private def residual : (Fin 68 → ℤ) := fun s => ∑ j : Fin 12, p j * values ⟨4 + j.val, by omega⟩ s

private theorem values_zero : values 0 = initial := by exact List.ofFn_inj.mp rfl
end D5.S3.Combinatorics.OrderedMinors.HardinA204612

namespace D5.S3.Combinatorics.OrderedMinors.HardinA204612
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
private theorem values_step (i : Fin 15) : (fun t => ∑ s ∈ incoming t, values i.castSucc s) = values i.succ := by
  fin_cases i <;> decide +kernel

end D5.S3.Combinatorics.OrderedMinors.HardinA204612

namespace D5.S3.Combinatorics.OrderedMinors.HardinA204612
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
private theorem invariant_certificate : T * G = G * H := by
  ext s i
  fin_cases i <;> revert s <;> decide +kernel

private theorem zero_sum_certificate (i : Fin 11) : (∑ s : (Fin 68), G s i) = 0 := by
  fin_cases i <;> decide +kernel

private theorem residual_certificate : residual = G.mulVec q := by
  exact List.ofFn_inj.mp rfl

end D5.S3.Combinatorics.OrderedMinors.HardinA204612

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace D5.S3.Combinatorics.OrderedMinors.HardinA204612
open scoped BigOperators
open D5.S3.Combinatorics.NarayanaStrip.CiglerCycleWalkTransfer

private def cost (s : (Fin 68)) (c : (Fin 32)) : ℤ := if valid s c then 1 else 0

private def pathCount (k : ℕ) (s : (Fin 68)) : ℤ :=
  ∑ f : Fin k → (Fin 32), if PathGood s f then 1 else 0

private theorem aggregate_transition (s t : (Fin 68)) :
    (∑ c : (Fin 32), if (fun s c => stateOf (stateRow s) c) s c = t then cost s c else 0) = T t s := by
  rw [Finset.sum_eq_single (stateRow t)]
  · rw [transfer_spec]
    by_cases h : (fun s c => stateOf (stateRow s) c) s (stateRow t) = t <;>
      by_cases hv : valid s (stateRow t) <;> simp [cost, h, hv]
  · intro c _ hc
    by_cases hv : valid s c
    · have hn : (fun s c => stateOf (stateRow s) c) s c ≠ t := by
        intro he
        have hr := (next_spec s c hv).1
        rw [he] at hr
        exact hc hr.symm
      simp [hn]
    · simp [cost, hv]
  · simp

private theorem contribution_sum {k : ℕ} (s : (Fin 68)) (f : Fin k → (Fin 32)) :
    (∑ t : (Fin 68), wordContribution (fun s c => stateOf (stateRow s) c) cost t s (List.ofFn f)) =
      if PathGood s f then 1 else 0 := by
  induction k generalizing s with
  | zero => simp [wordContribution, PathGood]
  | succ k ih =>
    have hf : f = Fin.cons (f 0) (Fin.tail f) := (Fin.cons_self_tail f).symm
    conv_lhs => rw [hf, List.ofFn_cons]
    simp only [wordContribution, ← Finset.mul_sum]
    rw [ih]
    by_cases hv : valid s (f 0) <;> simp [cost, PathGood, hv]

private theorem pathCount_eq_power (k : ℕ) (s : (Fin 68)) :
    pathCount k s = ∑ t : (Fin 68), (T ^ k) t s := by
  unfold pathCount
  simp_rw [← contribution_sum]
  rw [Finset.sum_comm]
  simp_rw [weighted_walks_eq_pow]
  have h : (Matrix.of fun source destination =>
      ∑ c : (Fin 32), if (fun s c => stateOf (stateRow s) c) source c = destination then cost source c else 0) = T.transpose := by
    ext source destination
    exact aggregate_transition source destination
  rw [h, ← Matrix.transpose_pow]
  rfl

end D5.S3.Combinatorics.OrderedMinors.HardinA204612

namespace D5.S3.Combinatorics.OrderedMinors.HardinA204612
open scoped BigOperators
private theorem states_injective : Function.Injective (fun s : (Fin 68) => (stateRow s, stateDet s)) := by
  let codes : Fin 68 → ℤ := ![0, 81, 82, 162, 243, 244, 247, 324, 405, 486, 567, 568, 648, 729, 730, 810, 891, 892, 972, 1053, 1134, 1215, 1216, 1269, 1296, 1350, 1351, 1377, 1378, 1431, 1458, 1512, 1513, 1516, 1539, 1540, 1543, 1620, 1701, 1782, 1863, 1864, 1908, 1917, 1944, 1989, 1990, 1998, 1999, 2025, 2026, 2079, 2106, 2155, 2160, 2161, 2187, 2188, 2241, 2268, 2322, 2349, 2403, 2430, 2484, 2485, 2511, 2512]
  have hc : ∀ s, codes s = 81 * (stateRow s).val +
      27 * stateDet s 0 + 9 * stateDet s 1 + 3 * stateDet s 2 + stateDet s 3 := by
    decide +kernel
  have hi : Function.Injective codes := by decide +kernel
  intro s t h
  apply hi
  have hr : stateRow s = stateRow t := congrArg Prod.fst h
  have hd : stateDet s = stateDet t := congrArg Prod.snd h
  rw [hc s, hc t, hr, hd]

noncomputable section
open scoped Classical

private def arrayCodingEquiv (k : ℕ) :
    Matrix (Fin (k + 2)) (Fin 5) (Fin 2) ≃ (Fin 32) × ((Fin 32) × (Fin k → (Fin 32))) :=
  (Equiv.piCongrRight fun _ => rowEquiv.symm).trans
    ((Fin.consEquiv fun _ : Fin (k+2) => (Fin 32)).symm.trans
      (Equiv.prodCongr (Equiv.refl (Fin 32))
        (Fin.consEquiv fun _ : Fin (k+1) => (Fin 32)).symm))

private theorem arrayCoding_symm (k : ℕ) (b c : (Fin 32)) (f : Fin k → (Fin 32)) :
    (arrayCodingEquiv k).symm (b,c,f) =
      fun i => row ((Fin.cons b (Fin.cons c f) : Fin (k+2) → (Fin 32)) i) := by
  exact Eq.symm (Matrix.ext fun i => congrFun rfl)

private theorem ordered_coding (k : ℕ) (b c : (Fin 32)) (f : Fin k → (Fin 32)) :
    OrderedMinors ((arrayCodingEquiv k).symm (b,c,f)) ↔
      Monotone (delta b c) ∧ PathGood (stateOf b c) f := by
  rw [arrayCoding_symm, ordered_cons]
  by_cases h : Monotone (delta b c)
  · simp only [h, true_and]
    rw [← extension_iff_path]
    rw [(state_spec b c h).1, (state_spec b c h).2]
  · simp [h]

private theorem cardinal_indicator {α : Type} [Fintype α] (P : α → Prop) :
    (Nat.card {x // P x} : ℤ) = ∑ x : α, if P x then 1 else 0 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.card_eq_sum_ones]
  simp

private theorem count_rows (k : ℕ) :
    a (k+1) = ∑ b : (Fin 32), ∑ c : (Fin 32),
      if Monotone (delta b c) then pathCount k (stateOf b c) else 0 := by
  rw [a, cardinal_indicator]
  rw [← (arrayCodingEquiv k).symm.sum_comp]
  simp only [Fintype.sum_prod_type, ordered_coding]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  by_cases h : Monotone (delta b c) <;> simp [h, pathCount]

private def seedEquiv (b : (Fin 32)) :
    {c : (Fin 32) // Monotone (delta b c)} ≃
      {s : (Fin 68) // delta b (stateRow s) = stateDet s} where
  toFun c := ⟨stateOf b c, by
    rw [(state_spec b c c.property).1, (state_spec b c c.property).2]⟩
  invFun s := ⟨stateRow s, by rw [s.property]; exact states_horizontal s⟩
  left_inv c := by apply Subtype.ext; exact (state_spec b c c.property).1
  right_inv s := by
    apply Subtype.ext
    apply states_injective
    have h : Monotone (delta b (stateRow s)) := by
      rw [s.property]; exact states_horizontal s
    exact Prod.ext (state_spec b (stateRow s) h).1
      ((state_spec b (stateRow s) h).2.trans s.property)

private theorem indicator_subtype {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P] (f : α → ℤ) :
    (∑ x : α, if P x then f x else 0) = ∑ x : {x // P x}, f x := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by intro x; simp) _

private theorem seed_sum (b : (Fin 32)) (f : (Fin 68) → ℤ) :
    (∑ c : (Fin 32), if Monotone (delta b c) then f (stateOf b c) else 0) =
      ∑ s : (Fin 68), if delta b (stateRow s) = stateDet s then f s else 0 := by
  rw [indicator_subtype (fun c : (Fin 32) => Monotone (delta b c)) (fun c => f (stateOf b c)),
    indicator_subtype (fun s : (Fin 68) => delta b (stateRow s) = stateDet s) f]
  exact Fintype.sum_equiv (seedEquiv b) _ _ (fun c => rfl)

private theorem count_states (k : ℕ) : a (k+1) = ∑ s : (Fin 68), initial s * pathCount k s := by
  rw [count_rows]
  simp_rw [seed_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [initial_spec, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : delta b (stateRow s) = stateDet s <;> simp [h]

private theorem count_eq_power (k : ℕ) : a (k+1) = ∑ s : (Fin 68), (T ^ k).mulVec initial s := by
  rw [count_states]
  simp_rw [pathCount_eq_power, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro t _
  ring

end
end D5.S3.Combinatorics.OrderedMinors.HardinA204612

namespace D5.S3.Combinatorics.OrderedMinors.HardinA204612
open scoped BigOperators

private theorem values_eq_power (i : Fin 16) : values i = (T ^ i.val).mulVec initial := by
  induction i using Fin.induction with
  | zero => simp [values_zero]
  | succ i ih =>
    rw [← values_step i, step_eq_mulVec, ih]
    simp only [Fin.val_succ, Fin.val_castSucc, pow_succ', Matrix.mulVec_mulVec]

private theorem sum_G (z : Fin 11 → ℤ) : (∑ s : (Fin 68), G.mulVec z s) = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, zero_sum_certificate, zero_mul]
  simp

private theorem power_G (k : ℕ) (z : Fin 11 → ℤ) :
    ∃ z', (T ^ k).mulVec (G.mulVec z) = G.mulVec z' := by
  have hc : Function.Semiconj G.mulVec (H • ·) (T • ·) := by
    intro x
    change G.mulVec (H.mulVec x) = T.mulVec (G.mulVec x)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, invariant_certificate]
  refine ⟨(H^k).mulVec z, ?_⟩
  calc
    (T^k).mulVec (G.mulVec z) = (T • ·)^[k] (G.mulVec z) :=
      (smul_iterate_apply T k (G.mulVec z)).symm
    _ = G.mulVec ((H • ·)^[k] z) := (hc.iterate_right k z).symm
    _ = G.mulVec ((H^k).mulVec z) := congrArg G.mulVec (smul_iterate_apply H k z)

private theorem invisible_residual (k : ℕ) : (∑ s : (Fin 68), (T ^ k).mulVec residual s) = 0 := by
  rw [residual_certificate]
  obtain ⟨z, hz⟩ := power_G k q
  rw [hz]
  exact sum_G z

private theorem propagate_polynomial (k : ℕ) :
    (T ^ k).mulVec residual =
      fun s => ∑ j : Fin 12, p j * (T ^ (k + 4 + j.val)).mulVec initial s := by
  calc
    (T^k).mulVec residual =
        (T^k).mulVec (∑ j : Fin 12, p j • values ⟨4+j.val, by omega⟩) := by
      rfl
    _ = ∑ j : Fin 12, p j • (T^k).mulVec (values ⟨4+j.val, by omega⟩) := by
      rw [Matrix.mulVec_sum]
      simp_rw [Matrix.mulVec_smul]
    _ = _ := by
      funext s
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [values_eq_power, Matrix.mulVec_mulVec, ← pow_add]
      simp only [Nat.add_assoc]

private theorem scalar_polynomial (k : ℕ) :
    (∑ j : Fin 12, p j * ∑ s : (Fin 68),
      (T ^ (k + 4 + j.val)).mulVec initial s) = 0 := by
  have h := invisible_residual k
  rw [propagate_polynomial] at h
  rw [Finset.sum_comm] at h
  simpa only [Finset.mul_sum] using h

end D5.S3.Combinatorics.OrderedMinors.HardinA204612

namespace D5.S3.Combinatorics.OrderedMinors.HardinA204612
open scoped BigOperators

private theorem shifted_recurrence (k : ℕ) :
    a (k+16) = 18*a (k+15) - 73*a (k+14) - 256*a (k+13) +
      2060*a (k+12) - 1216*a (k+11) - 12612*a (k+10) +
      18224*a (k+9) + 20992*a (k+8) - 40064*a (k+7) -
      9984*a (k+6) + 24576*a (k+5) := by
  have h := scalar_polynomial k
  simp_rw [← count_eq_power] at h
  norm_num [p, Fin.sum_univ_succ, Nat.add_assoc] at h
  linarith

theorem result : claim := by
  intro n hn
  have h := shifted_recurrence (n-16)
  have h16 : n-16+16=n := by exact Nat.sub_add_cancel hn
  have h15 : n-16+15=n-1 := by exact Eq.symm ((fun {n m} => Nat.pred_eq_succ_iff.mpr) (id (Eq.symm h16)))
  have h14 : n-16+14=n-2 := by exact Eq.symm (Nat.sub_eq_of_eq_add (id (Eq.symm h16)))
  have h13 : n-16+13=n-3 := by exact Eq.symm (Nat.sub_eq_of_eq_add (id (Eq.symm h16)))
  have h12 : n-16+12=n-4 := by exact Eq.symm (Nat.sub_eq_of_eq_add (id (Eq.symm h16)))
  have h11 : n-16+11=n-5 := by exact Eq.symm (Nat.sub_eq_of_eq_add (id (Eq.symm h16)))
  have h10 : n-16+10=n-6 := by exact Eq.symm (Nat.sub_eq_of_eq_add (id (Eq.symm h16)))
  have h9 : n-16+9=n-7 := by exact Eq.symm (Nat.sub_eq_of_eq_add (id (Eq.symm h16)))
  have h8 : n-16+8=n-8 := by exact Eq.symm (Nat.sub_eq_of_eq_add (id (Eq.symm h16)))
  have h7 : n-16+7=n-9 := by exact Eq.symm (Nat.sub_eq_of_eq_add (id (Eq.symm h16)))
  have h6 : n-16+6=n-10 := by exact Eq.symm (Nat.sub_eq_of_eq_add (id (Eq.symm h16)))
  have h5 : n-16+5=n-11 := by exact Eq.symm (Nat.sub_eq_of_eq_add (id (Eq.symm h16)))
  simpa only [h16,h15,h14,h13,h12,h11,h10,h9,h8,h7,h6,h5] using h

end D5.S3.Combinatorics.OrderedMinors.HardinA204612
