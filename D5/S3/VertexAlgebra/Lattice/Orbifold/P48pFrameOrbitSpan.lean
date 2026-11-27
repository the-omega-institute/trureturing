import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48pSymmetricCommutantCertificate

/-!
# The signed pair orbits of the P48p frame

Each sorted pair records its outgoing forest edge, transport sign, seed,
and depth. The edge is a frame move followed by transpose when needed.
The two negative closed words force the entries at their seeds to vanish.
-/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48pFrameOrbitSpan

open scoped Matrix BigOperators
open P48pSymmetricCommutantCertificate
open private tIndex tSign uIndex uSign in tFrameMatrix uFrameMatrix

private abbrev FrameIndex := Fin 48
private abbrev FramePair := FrameIndex × FrameIndex
private abbrev FrameMatrix := Matrix FrameIndex FrameIndex ℚ

/-- Rational invariance under the two signed frame matrices and transpose. -/
def FrameInvariant (A : FrameMatrix) : Prop :=
  Aᵀ = A ∧
  (tFrameMatrix.map (fun z : ℤ => (z : ℚ))) * A *
    (tFrameMatrix.map (fun z : ℤ => (z : ℚ)))ᵀ = A ∧
  (uFrameMatrix.map (fun z : ℤ => (z : ℚ))) * A *
    (uFrameMatrix.map (fun z : ℤ => (z : ℚ)))ᵀ = A

private def entry (A : FrameMatrix) (p : FramePair) : ℚ := A p.1 p.2

private inductive Move where
  | t | u | swap

private def movePair : Move → FramePair → FramePair
  | .t, (i,j) => (tIndex i, tIndex j)
  | .u, (i,j) => (uIndex i, uIndex j)
  | .swap, (i,j) => (j,i)

private def moveSign : Move → FramePair → ℤ
  | .t, (i,j) => tSign i * tSign j
  | .u, (i,j) => uSign i * uSign j
  | .swap, _ => 1

private theorem signed_conj_entry (f : FrameIndex → FrameIndex)
    (s : FrameIndex → ℤ) (A : FrameMatrix) (i j : FrameIndex) :
    let O := (signedFrameMatrix f s).map (fun z : ℤ => (z : ℚ))
    (O * A * Oᵀ) i j = (s i : ℚ) * (s j : ℚ) * A (f i) (f j) := by
  let O : FrameMatrix := (signedFrameMatrix f s).map (fun z : ℤ => (z : ℚ))
  change (O * A * Oᵀ) i j = _
  have hO (a b : FrameIndex) : O a b = if f a = b then (s a : ℚ) else 0 := by
    change ((if f a = b then s a else 0 : ℤ) : ℚ) = _
    by_cases h : f a = b <;> simp [h]
  have hleft (k : FrameIndex) : (O * A) i k = (s i : ℚ) * A (f i) k := by
    simp only [Matrix.mul_apply, hO, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, hleft,
    hO, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact mul_right_comm _ _ _

private theorem move_transport (A : FrameMatrix) (hA : FrameInvariant A)
    (g : Move) (p : FramePair) :
    entry A p = (moveSign g p : ℚ) * entry A (movePair g p) := by
  rcases p with ⟨i,j⟩
  cases g with
  | t =>
    have h := congrArg (fun M : FrameMatrix => M i j) hA.2.1
    have hmul := signed_conj_entry tIndex tSign A i j
    exact h.symm.trans (by simpa only [entry, moveSign, movePair, Int.cast_mul] using hmul)
  | u =>
    have h := congrArg (fun M : FrameMatrix => M i j) hA.2.2
    have hmul := signed_conj_entry uIndex uSign A i j
    exact h.symm.trans (by simpa only [entry, moveSign, movePair, Int.cast_mul] using hmul)
  | swap =>
    have h := congrArg (fun M : FrameMatrix => M i j) hA.1
    simpa only [entry, movePair, moveSign, Int.cast_one, one_mul,
      Matrix.transpose_apply] using h.symm

private def wordEnd : List Move → FramePair → FramePair
  | [], p => p
  | g :: gs, p => wordEnd gs (movePair g p)

private def wordSign : List Move → FramePair → ℤ
  | [], _ => 1
  | g :: gs, p => moveSign g p * wordSign gs (movePair g p)

/-- Transport along a word uses the product of the signs of its successive moves. -/
private theorem word_transport (A : FrameMatrix) (hA : FrameInvariant A)
    (word : List Move) (p : FramePair) :
    entry A p = (wordSign word p : ℚ) * entry A (wordEnd word p) := by
  induction word generalizing p with
  | nil => simp only [wordSign, wordEnd, Int.cast_one, one_mul]
  | cons g gs ih =>
    calc
      entry A p = (moveSign g p : ℚ) * entry A (movePair g p) :=
        move_transport A hA g p
      _ = _ := by rw [ih (movePair g p), wordSign, wordEnd, Int.cast_mul, mul_assoc]

private def sortedPair (p : FramePair) : FramePair :=
  if p.1 ≤ p.2 then p else movePair .swap p

private theorem sortedPair_order (p : FramePair) :
    (sortedPair p).1 ≤ (sortedPair p).2 := by
  rcases p with ⟨i,j⟩
  by_cases h : i ≤ j
  · simpa only [sortedPair, if_pos h] using h
  · simpa only [sortedPair, if_neg h, movePair] using (le_of_not_ge h)

private theorem entry_sorted (A : FrameMatrix) (hA : Aᵀ = A)
    (p : FramePair) : entry A p = entry A (sortedPair p) := by
  rcases p with ⟨i,j⟩
  unfold sortedPair
  split
  · rfl
  · change A i j = A j i
    exact (congrArg (fun M : FrameMatrix => M i j) hA).symm

private inductive Orbit where
  | diag0 | off1 | zero02 | off16 | diag1 | zero13
  deriving DecidableEq

private def seed : Orbit → FramePair
  | .diag0 => (0,0)
  | .off1 => (0,1)
  | .zero02 => (0,2)
  | .off16 => (0,16)
  | .diag1 => (1,1)
  | .zero13 => (1,3)

/- Each row starts at its diagonal. The code is
   24 * depth + 4 * orbit + 2 * isNegative + isUMove. -/
private def forestRows : Array (Array Nat) := #[
  #[
    0, 4, 8, 319, 129, 124, 250, 244, 56, 295, 201, 317, 103, 28, 196, 148,
    12, 100, 226, 227, 292, 224, 78, 199, 153, 125, 178, 179, 271, 154, 178, 177,
    174, 292, 80, 107, 221, 176, 202, 316, 128, 200, 104, 220, 34, 153, 270, 54
  ],
  #[
    16, 294, 20, 318, 261, 294, 118, 198, 214, 62, 215, 310, 117, 69, 45, 141,
    140, 29, 124, 93, 175, 238, 191, 151, 167, 55, 77, 285, 270, 318, 245, 260,
    239, 317, 269, 236, 199, 292, 215, 127, 102, 222, 166, 223, 103, 189, 284
  ],
  #[
    144, 221, 249, 148, 203, 269, 251, 244, 226, 222, 268, 295, 245, 173, 172, 158,
    179, 248, 245, 130, 196, 244, 152, 317, 179, 251, 270, 179, 200, 203, 223, 268,
    274, 298, 364, 200, 178, 292, 153, 154, 226, 295, 225, 177, 197, 293
  ],
  #[
    137, 196, 190, 134, 215, 222, 239, 244, 188, 286, 189, 238, 191, 287, 167, 125,
    268, 215, 199, 141, 239, 244, 190, 293, 149, 166, 149, 172, 247, 167, 189, 221,
    220, 191, 247, 246, 165, 293, 199, 223, 215, 316, 175, 263, 140
  ],
  #[
    120, 245, 225, 175, 250, 220, 226, 245, 319, 271, 271, 197, 148, 124, 202, 274,
    268, 200, 132, 343, 177, 271, 129, 177, 246, 155, 130, 226, 223, 223, 202, 224,
    246, 152, 251, 247, 226, 106, 249, 245, 299, 178, 222, 172
  ],
  #[
    136, 244, 238, 246, 214, 294, 189, 213, 164, 191, 215, 237, 212, 220, 247, 236,
    270, 263, 140, 198, 165, 220, 269, 190, 246, 294, 174, 262, 212, 223, 247, 166,
    198, 318, 188, 199, 148, 174, 191, 157, 220, 166, 239
  ],
  #[
    120, 172, 200, 245, 202, 223, 222, 196, 197, 245, 319, 295, 33, 176, 269, 154,
    124, 222, 152, 199, 201, 178, 173, 226, 272, 248, 196, 247, 203, 227, 222, 155,
    226, 269, 130, 202, 275, 222, 154, 272, 318, 150
  ],
  #[
    113, 149, 239, 270, 167, 191, 190, 262, 165, 261, 140, 103, 222, 237, 295, 191,
    143, 293, 237, 244, 245, 286, 157, 246, 245, 236, 191, 292, 198, 215, 198, 125,
    286, 173, 271, 220, 119, 197, 199, 141, 118
  ],
  #[
    145, 223, 226, 340, 173, 244, 172, 159, 220, 199, 250, 224, 221, 177, 269, 247,
    155, 292, 59, 178, 269, 249, 225, 177, 198, 247, 200, 176, 295, 179, 202, 246,
    224, 224, 225, 269, 179, 201, 221, 197
  ],
  #[
    137, 318, 212, 188, 260, 262, 189, 93, 116, 197, 198, 213, 197, 167, 262, 246,
    239, 151, 127, 214, 172, 132, 173, 141, 236, 269, 317, 239, 198, 268, 236, 247,
    223, 221, 263, 221, 292, 215, 263
  ],
  #[
    48, 150, 268, 52, 148, 244, 76, 244, 154, 176, 172, 152, 270, 220, 128, 102,
    176, 58, 294, 202, 226, 226, 293, 174, 274, 250, 270, 176, 274, 244, 104, 275,
    251, 196, 200, 80, 124, 319
  ],
  #[
    137, 214, 46, 190, 212, 167, 165, 268, 268, 287, 220, 166, 239, 196, 310, 175,
    87, 189, 245, 199, 172, 214, 190, 244, 223, 262, 270, 271, 143, 244, 316, 247,
    260, 244, 125, 239, 213
  ],
  #[
    89, 191, 213, 167, 165, 143, 77, 294, 117, 175, 212, 261, 245, 215, 271, 199,
    261, 199, 198, 271, 119, 239, 221, 270, 261, 125, 133, 166, 151, 271, 223, 237,
    269, 244, 239, 93
  ],
  #[
    40, 213, 239, 164, 263, 317, 84, 214, 126, 237, 238, 340, 263, 247, 221, 236,
    148, 124, 102, 70, 311, 222, 148, 213, 174, 220, 116, 223, 76, 245, 92, 245,
    268, 140, 142
  ],
  #[
    136, 215, 236, 191, 173, 269, 212, 196, 213, 166, 222, 142, 244, 173, 238, 221,
    244, 197, 191, 237, 220, 294, 238, 197, 222, 263, 199, 126, 182, 212, 246, 293,
    260, 94
  ],
  #[
    161, 213, 237, 342, 221, 188, 172, 263, 239, 317, 238, 151, 270, 214, 221, 246,
    294, 236, 212, 270, 271, 166, 222, 220, 263, 199, 247, 246, 215, 174, 175, 213,
    190
  ],
  #[
    65, 213, 53, 102, 237, 292, 214, 117, 247, 191, 318, 269, 189, 295, 245, 271,
    215, 71, 244, 126, 143, 151, 173, 260, 292, 269, 268, 260, 198, 247, 286, 190
  ],
  #[
    112, 271, 295, 164, 222, 190, 141, 174, 236, 127, 148, 190, 197, 172, 196, 213,
    189, 151, 270, 310, 292, 196, 165, 221, 246, 175, 215, 220, 269, 214, 260
  ],
  #[
    25, 227, 221, 177, 222, 245, 153, 39, 249, 201, 149, 153, 107, 57, 127, 292,
    227, 201, 246, 249, 131, 223, 177, 129, 81, 246, 200, 201, 151, 246
  ],
  #[
    72, 148, 201, 245, 293, 250, 292, 153, 131, 174, 128, 104, 82, 268, 318, 248,
    202, 244, 154, 200, 198, 129, 200, 251, 174, 155, 248, 294, 76
  ],
  #[
    136, 247, 236, 236, 223, 262, 199, 271, 215, 270, 247, 124, 237, 214, 246, 221,
    140, 221, 318, 190, 317, 86, 196, 263, 221, 199, 164, 164
  ],
  #[
    96, 271, 199, 203, 269, 179, 224, 223, 201, 128, 250, 269, 220, 248, 224, 198,
    202, 155, 110, 202, 128, 104, 150, 176, 248, 245, 102
  ],
  #[
    88, 287, 271, 119, 223, 172, 238, 245, 150, 246, 212, 92, 220, 100, 263, 172,
    268, 188, 268, 196, 247, 118, 223, 149, 140, 164
  ],
  #[
    160, 158, 214, 196, 270, 215, 268, 223, 148, 214, 236, 247, 222, 263, 175, 220,
    236, 245, 172, 293, 239, 271, 196, 117, 237
  ],
  #[
    144, 222, 203, 249, 223, 176, 275, 200, 175, 172, 155, 130, 247, 227, 273, 269,
    178, 178, 248, 175, 224, 273, 270, 148
  ],
  #[
    89, 77, 246, 238, 175, 268, 222, 191, 189, 199, 293, 284, 270, 149, 143, 244,
    295, 247, 95, 173, 293, 215, 215
  ],
  #[
    49, 248, 247, 225, 154, 176, 103, 294, 153, 83, 247, 200, 226, 271, 227, 107,
    274, 244, 200, 225, 63, 175
  ],
  #[
    73, 246, 155, 177, 202, 268, 197, 226, 202, 246, 178, 105, 223, 251, 224, 81,
    222, 227, 274, 101, 220
  ],
  #[
    160, 268, 148, 110, 236, 213, 343, 199, 215, 222, 271, 165, 245, 198, 271, 212,
    223, 198, 191, 70
  ],
  #[
    145, 225, 274, 222, 269, 250, 154, 268, 200, 249, 342, 203, 250, 274, 220, 177,
    128, 196, 246
  ],
  #[
    120, 298, 198, 222, 227, 227, 220, 275, 249, 220, 153, 248, 152, 319, 200, 251,
    223, 292
  ],
  #[
    96, 294, 270, 200, 152, 223, 203, 202, 293, 106, 225, 201, 198, 201, 224, 197,
    244
  ],
  #[
    113, 238, 157, 246, 189, 199, 246, 214, 268, 174, 197, 236, 149, 221, 188, 262
  ],
  #[
    161, 295, 196, 165, 244, 247, 236, 149, 271, 365, 213, 295, 109, 310, 213
  ],
  #[
    145, 227, 269, 179, 201, 245, 249, 80, 224, 196, 273, 131, 175, 270
  ],
  #[
    96, 319, 275, 176, 172, 249, 178, 201, 292, 227, 106, 244, 110
  ],
  #[
    185, 133, 199, 262, 175, 220, 268, 188, 245, 174, 167, 191
  ],
  #[
    121, 249, 223, 272, 129, 178, 246, 178, 224, 295, 247
  ],
  #[
    121, 247, 131, 225, 200, 223, 224, 225, 222, 198
  ],
  #[
    160, 220, 220, 271, 236, 199, 148, 237, 236
  ],
  #[
    121, 225, 225, 135, 248, 224, 246, 223
  ],
  #[
    72, 178, 270, 202, 107, 268, 270
  ],
  #[
    168, 244, 203, 201, 318, 244
  ],
  #[
    160, 270, 221, 213, 239
  ],
  #[
    145, 201, 292, 247
  ],
  #[
    97, 270, 124
  ],
  #[
    113, 214
  ],
  #[
    64
  ]
]

private def negativeWord02 : List Move :=
  [.t, .u, .t, .t, .t, .swap, .u, .u, .u, .t]

private def negativeWord13 : List Move :=
  [.t, .t, .t, .t, .swap, .u, .t, .swap, .t, .swap, .t, .u]

private def routeCode (p : FramePair) : Nat :=
  (forestRows.getD p.1.val #[]).getD (p.2.val - p.1.val) 0

private def depth (p : FramePair) : Nat := routeCode p / 24

private def orbit (p : FramePair) : Orbit :=
  match routeCode p / 4 % 6 with
  | 0 => .diag0
  | 1 => .off1
  | 2 => .zero02
  | 3 => .off16
  | 4 => .diag1
  | _ => .zero13

private def routeSign (p : FramePair) : ℤ :=
  if routeCode p / 2 % 2 = 0 then 1 else -1

private def parentMove (p : FramePair) : Move :=
  if routeCode p % 2 = 0 then .t else .u

private def parent (p : FramePair) : FramePair :=
  sortedPair (movePair (parentMove p) p)

private def activeSign (p : FramePair) : ℤ :=
  match orbit p with
  | .zero02 | .zero13 => 0
  | _ => routeSign p

private def indicator (k : Orbit) (p : FramePair) : ℤ :=
  if orbit p = k then routeSign p else 0

private abbrev EdgeValid (g : Move) (p : FramePair) : Prop :=
  let q := sortedPair (movePair g p)
  orbit p = orbit q ∧ activeSign p = moveSign g p * activeSign q

private abbrev ForestValid (p : FramePair) : Prop :=
  (depth p = 0 → p = seed (orbit p) ∧ routeSign p = 1) ∧
  (depth p ≠ 0 →
    depth (parent p) < depth p ∧
    orbit (parent p) = orbit p ∧
    routeSign p = moveSign (parentMove p) p * routeSign (parent p))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 6000000 in
private theorem forest_rows (i : FrameIndex) :
    ∀ j : FrameIndex, i ≤ j →
      ForestValid (i,j) ∧ EdgeValid .t (i,j) ∧ EdgeValid .u (i,j) := by
  fin_cases i <;> decide +kernel

private abbrev BasisValid (i j : FrameIndex) : Prop :=
  B0 i j = indicator .diag0 (i,j) ∧
  B1 i j = indicator .off1 (i,j) ∧
  B16 i j = indicator .off16 (i,j) ∧
  B11 i j = indicator .diag1 (i,j)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
private theorem basis_rows (i : FrameIndex) :
    ∀ j : FrameIndex, i ≤ j → BasisValid i j := by
  fin_cases i <;> decide +kernel

private theorem forest_transport (A : FrameMatrix) (hA : FrameInvariant A) :
    ∀ n : Nat, ∀ p : FramePair, p.1 ≤ p.2 → depth p = n →
      entry A p = (routeSign p : ℚ) * entry A (seed (orbit p)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p hp hn
    have h := (forest_rows p.1 p.2 hp).1
    change ForestValid p at h
    by_cases hzero : depth p = 0
    · obtain ⟨hseed, hsign⟩ := h.1 hzero
      rw [hsign, Int.cast_one, one_mul, ← hseed]
    · obtain ⟨hlt, horbit, hsign⟩ := h.2 hzero
      have hparent : (parent p).1 ≤ (parent p).2 := sortedPair_order _
      have hrec := ih (depth (parent p)) (by simpa only [hn] using hlt) (parent p) hparent rfl
      calc
        entry A p = (moveSign (parentMove p) p : ℚ) * entry A (parent p) :=
          (move_transport A hA (parentMove p) p).trans
            (congrArg _ (entry_sorted A hA.1 (movePair (parentMove p) p)))
        _ = _ := by rw [hrec, horbit, hsign, Int.cast_mul, mul_assoc]

private theorem zero_of_negative_word (A : FrameMatrix) (hA : FrameInvariant A)
    (p : FramePair) (w : List Move) (he : wordEnd w p = p) (hs : wordSign w p = -1) :
    entry A p = 0 := by
  have h := word_transport A hA w p
  rw [he, hs, Int.cast_neg, Int.cast_one, neg_mul, one_mul] at h
  linarith

private theorem zero02 (A : FrameMatrix) (hA : FrameInvariant A) :
    entry A (seed .zero02) = 0 :=
  zero_of_negative_word A hA _ negativeWord02 (by decide +kernel) (by decide +kernel)

private theorem zero13 (A : FrameMatrix) (hA : FrameInvariant A) :
    entry A (seed .zero13) = 0 :=
  zero_of_negative_word A hA _ negativeWord13 (by decide +kernel) (by decide +kernel)

private def weights (a0 a1 a16 a11 : ℚ) : Orbit → ℚ
  | .diag0 => a0
  | .off1 => a1
  | .off16 => a16
  | .diag1 => a11
  | .zero02 | .zero13 => 0

private def orbitCombination (a0 a1 a16 a11 : ℚ) : FrameMatrix :=
  a0 • B0Rat + a1 • B1Rat + a16 • B16Rat + a11 • B11Rat

private theorem combination_entry (a0 a1 a16 a11 : ℚ)
    (p : FramePair) (hp : p.1 ≤ p.2) :
    entry (orbitCombination a0 a1 a16 a11) p =
      (activeSign p : ℚ) * weights a0 a1 a16 a11 (orbit p) := by
  obtain ⟨h0, h1, h16, h11⟩ := basis_rows p.1 p.2 hp
  change B0 p.1 p.2 = indicator .diag0 p at h0
  change B1 p.1 p.2 = indicator .off1 p at h1
  change B16 p.1 p.2 = indicator .off16 p at h16
  change B11 p.1 p.2 = indicator .diag1 p at h11
  have c0 : B0Rat p.1 p.2 = (indicator .diag0 p : ℚ) :=
    congrArg (fun z : ℤ => (z : ℚ)) h0
  have c1 : B1Rat p.1 p.2 = (indicator .off1 p : ℚ) :=
    congrArg (fun z : ℤ => (z : ℚ)) h1
  have c16 : B16Rat p.1 p.2 = (indicator .off16 p : ℚ) :=
    congrArg (fun z : ℤ => (z : ℚ)) h16
  have c11 : B11Rat p.1 p.2 = (indicator .diag1 p : ℚ) :=
    congrArg (fun z : ℤ => (z : ℚ)) h11
  simp only [entry, orbitCombination, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    c0, c1, c16, c11]
  cases horbit : orbit p <;>
    simp [indicator, activeSign, weights, horbit, mul_comm]

private theorem combination_symmetric (a0 a1 a16 a11 : ℚ) :
    (orbitCombination a0 a1 a16 a11)ᵀ = orbitCombination a0 a1 a16 a11 := by
  apply Matrix.ext
  intro i j
  have h0 : B0Rat j i = B0Rat i j :=
    congrArg (fun M : Matrix FrameIndex FrameIndex ℤ => (M i j : ℚ)) orbitB0_symmetric
  have h1 : B1Rat j i = B1Rat i j :=
    congrArg (fun M : Matrix FrameIndex FrameIndex ℤ => (M i j : ℚ)) orbitB1_symmetric
  have h16 : B16Rat j i = B16Rat i j :=
    congrArg (fun M : Matrix FrameIndex FrameIndex ℤ => (M i j : ℚ)) orbitB16_symmetric
  have h11 : B11Rat j i = B11Rat i j :=
    congrArg (fun M : Matrix FrameIndex FrameIndex ℤ => (M i j : ℚ)) orbitB11_symmetric
  simp only [orbitCombination, Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply,
    h0, h1, h16, h11]

/-- The four coefficients are the entries at the four consistent orbit seeds. -/
theorem frame_orbit_expansion (A : FrameMatrix) (hA : FrameInvariant A) :
    A = A 0 0 • B0Rat + A 0 1 • B1Rat + A 0 16 • B16Rat + A 1 1 • B11Rat := by
  let C := orbitCombination (A 0 0) (A 0 1) (A 0 16) (A 1 1)
  have hz02 : A 0 2 = 0 := zero02 A hA
  have hz13 : A 1 3 = 0 := zero13 A hA
  have hupper (p : FramePair) (hp : p.1 ≤ p.2) : entry A p = entry C p := by
    have h := forest_transport A hA (depth p) p hp rfl
    change entry A p = entry (orbitCombination (A 0 0) (A 0 1) (A 0 16) (A 1 1)) p
    rw [h, combination_entry _ _ _ _ p hp]
    cases horbit : orbit p <;>
      simp [horbit, weights, activeSign, seed, entry, hz02, hz13]
  change A = C
  apply Matrix.ext
  intro i j
  by_cases h : i ≤ j
  · exact hupper (i,j) h
  · have hsA : A j i = A i j := congrArg (fun M : FrameMatrix => M i j) hA.1
    have hsC : C j i = C i j :=
      congrArg (fun M : FrameMatrix => M i j) (combination_symmetric _ _ _ _)
    exact hsA.symm.trans ((hupper (j,i) (le_of_not_ge h)).trans hsC)

private theorem conjugation_of_upper (f : FrameIndex → FrameIndex)
    (s : FrameIndex → ℤ) (A : FrameMatrix) (hsymm : Aᵀ = A)
    (hupper : ∀ i j : FrameIndex, i ≤ j →
      A i j = (s i : ℚ) * (s j : ℚ) * A (f i) (f j)) :
    let O := (signedFrameMatrix f s).map (fun z : ℤ => (z : ℚ))
    O * A * Oᵀ = A := by
  dsimp only
  apply Matrix.ext
  intro i j
  change ((signedFrameMatrix f s).map (fun z : ℤ => (z : ℚ)) * A *
    ((signedFrameMatrix f s).map (fun z : ℤ => (z : ℚ)))ᵀ) i j = A i j
  have hmul := signed_conj_entry f s A i j
  dsimp only at hmul
  rw [hmul]
  by_cases h : i ≤ j
  · exact (hupper i j h).symm
  · have hs (x y : FrameIndex) : A y x = A x y :=
      congrArg (fun M : FrameMatrix => M x y) hsymm
    calc
      (s i : ℚ) * (s j : ℚ) * A (f i) (f j) =
          (s j : ℚ) * (s i : ℚ) * A (f j) (f i) := by
        rw [hs (f i) (f j), mul_comm (s i : ℚ) (s j : ℚ)]
      _ = A j i := (hupper j i (le_of_not_ge h)).symm
      _ = A i j := hs i j

private theorem combination_invariant (a0 a1 a16 a11 : ℚ) :
    FrameInvariant (orbitCombination a0 a1 a16 a11) := by
  let C := orbitCombination a0 a1 a16 a11
  have hs : Cᵀ = C := combination_symmetric a0 a1 a16 a11
  have hedge (g : Move) (p : FramePair) (hp : p.1 ≤ p.2)
      (h : EdgeValid g p) :
      entry C p = (moveSign g p : ℚ) * entry C (movePair g p) := by
    let q := sortedPair (movePair g p)
    have ho : orbit p = orbit q := h.1
    have hsign : activeSign p = moveSign g p * activeSign q := h.2
    calc
      entry C p = (activeSign p : ℚ) * weights a0 a1 a16 a11 (orbit p) :=
        combination_entry a0 a1 a16 a11 p hp
      _ = (moveSign g p : ℚ) *
          ((activeSign q : ℚ) * weights a0 a1 a16 a11 (orbit q)) := by
        rw [hsign, ho, Int.cast_mul, mul_assoc]
      _ = (moveSign g p : ℚ) * entry C q := by
        rw [combination_entry a0 a1 a16 a11 q (sortedPair_order _)]
      _ = _ := by rw [entry_sorted C hs (movePair g p)]
  refine ⟨hs, conjugation_of_upper tIndex tSign C hs ?_,
    conjugation_of_upper uIndex uSign C hs ?_⟩
  · intro i j hij
    simpa only [entry, movePair, moveSign, Int.cast_mul] using
      hedge .t (i,j) hij (forest_rows i j hij).2.1
  · intro i j hij
    simpa only [entry, movePair, moveSign, Int.cast_mul] using
      hedge .u (i,j) hij (forest_rows i j hij).2.2

/-- The invariant symmetric matrices are exactly the span of the four signed orbit matrices. -/
theorem frame_orbit_span_iff (A : FrameMatrix) :
    FrameInvariant A ↔
      ∃ a0 a1 a16 a11 : ℚ, A = a0 • B0Rat + a1 • B1Rat + a16 • B16Rat + a11 • B11Rat := by
  constructor
  · intro hA
    exact ⟨A 0 0, A 0 1, A 0 16, A 1 1, frame_orbit_expansion A hA⟩
  · rintro ⟨a0, a1, a16, a11, rfl⟩
    exact combination_invariant a0 a1 a16 a11

/-- Adding commutation with the skew generator gives the span of the identity and M. -/
theorem j_commuting_frame_invariant_span (A : FrameMatrix) (hA : FrameInvariant A)
    (hJ : A * JRat = JRat * A) :
    ∃ x y : ℚ, A = x • (1 : FrameMatrix) + y • commutantMRat :=
  rational_symmetric_commutant_span (A 0 0) (A 0 1) (A 0 16) (A 1 1) A
    (frame_orbit_expansion A hA) hJ

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48pFrameOrbitSpan
