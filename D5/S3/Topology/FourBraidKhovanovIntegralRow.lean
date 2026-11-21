/- GID: D5/S3/Topology/FourBraidKhovanovIntegralRow
   generality: I
   mirror-B: D5/B/S3/Topology/FourBraidKhovanovIntegralRow
   mirror-E: none(waiver:algebraically-proved)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Finsupp.LinearCombination]
   utility: none
   digest: Integral kernel/image quotients from sparse chain contractions. -/

import D5.S3.Topology.FourBraidKhovanovHomology
import D5.S3.Topology.FourBraidKhovanovResolutions

/-!
The cohomology is the integral kernel/image quotient of the signed,
unreduced crossing-resolution cube. Sparse integral maps certify a chain
contraction of each of the three extreme rows. At quantum degree seventeen
the surviving ranks are two in cohomological degree five and one in degree six.
-/

set_option autoImplicit false

namespace D5.S3.Topology.FourBraidKhovanovCube

abbrev RawColumns := Array (List (Nat × Int))

private def readColumn (dest : Array Enhanced)
    (terms : List (Enhanced × Int)) : Option (List (Nat × Int)) :=
  terms.mapM fun (x, c) => (dest.toList.findIdx? (· == x)).map (·, c)

def calculateMatrix (roots : Nat → Partition) (source dest : Array Enhanced) :
    Option RawColumns :=
  (source.toList.mapM fun x => readColumn dest (differential roots x)).map List.toArray

theorem calculateMatrix_append (roots : Nat → Partition) (a b dest : Array Enhanced) :
    calculateMatrix roots (a ++ b) dest = (do
      let first ← calculateMatrix roots a dest
      let second ← calculateMatrix roots b dest
      return first ++ second) := by
  simp only [calculateMatrix, Array.toList_append, List.mapM_append]
  generalize (a.toList.mapM fun x => readColumn dest (differential roots x)) = x
  generalize (b.toList.mapM fun x => readColumn dest (differential roots x)) = y
  cases x <;> cases y <;> simp

/-- Stage zero is the empty cochain group in degree minus three. Stage
`k + 1` is the group on enhanced resolutions with `k` one-smoothings. -/
def stageBasis (j : Nat) : Nat → Array Enhanced
  | 0 => #[]
  | k + 1 => if k < crossings + 1 then (basis resolve j k).toArray else #[]

/-- The entire signed integral matrix. A missing basis lookup makes this
return `none`, so the certificate checks that no differential term was dropped. -/
def stageMatrix (j t : Nat) : Option RawColumns :=
  calculateMatrix resolve (stageBasis j t) (stageBasis j (t + 1))

private def decode (n m : Nat) (data : RawColumns) : Columns n m :=
  fun i => (data[i.val]?.getD []).filterMap fun (r, a) =>
    if h : r < m then some (⟨r, h⟩, a) else none

/-- A graded integral row with its displayed basis and sparse coefficients. -/
structure IntegralRow where
  basis : Nat → Array Enhanced
  matrix : Nat → Option RawColumns

def integralRow (j : Nat) : IntegralRow := ⟨stageBasis j, stageMatrix j⟩

namespace IntegralRow

def columns (row : IntegralRow) (t : Nat) :
    Columns (row.basis t).size (row.basis (t + 1)).size :=
  decode _ _ ((row.matrix t).getD #[])

noncomputable def d (row : IntegralRow) (t : Nat) :
    Free (row.basis t).size →ₗ[Int] Free (row.basis (t + 1)).size :=
  Sparse.linear (row.columns t)

/-- At stage `k+1` this is the actual kernel modulo the image from stage `k`. -/
abbrev Kh (row : IntegralRow) (k : Nat) (sq : (row.d (k + 1)).comp (row.d k) = 0) :=
  Cohomology (row.d k) (row.d (k + 1)) sq

/-- Integral cohomology of an entire quantum row, with all differentials
defined in its displayed basis and square zero. -/
structure Computes (row : IntegralRow) (rank : Nat → Nat) : Prop where
  defined : ∀ t, (row.matrix t).isSome = true
  square : ∀ k, (row.d (k + 1)).comp (row.d k) = 0
  homology : ∀ k, Nonempty (row.Kh k (square k) ≃ₗ[Int] Free (rank k))

end IntegralRow

structure Contraction where
  rank : Nat → Nat
  p : Nat → RawColumns
  i : Nat → RawColumns
  h : Nat → RawColumns

private def Contraction.projection (c : Contraction) (row : IntegralRow) (k : Nat) :
    Columns (row.basis (k + 1)).size (c.rank k) :=
  decode _ _ (c.p (k + 1))

private def Contraction.inclusion (c : Contraction) (row : IntegralRow) (k : Nat) :
    Columns (c.rank k) (row.basis (k + 1)).size :=
  decode _ _ (c.i (k + 1))

private def Contraction.homotopy (c : Contraction) (row : IntegralRow) (t : Nat) :
    Columns (row.basis (t + 1)).size (row.basis t).size :=
  decode _ _ (c.h (t + 1))

def Contraction.check (c : Contraction) (row : IntegralRow) (k : Nat) : Bool :=
  let e := row.columns k
  let d := row.columns (k + 1)
  let p := c.projection row k
  let i := c.inclusion row k
  Sparse.checkZeroComp d e && Sparse.checkZeroComp p e && Sparse.checkZeroComp d i &&
  Sparse.checkRetract p i &&
  Sparse.checkHomotopy e d (c.homotopy row k) (c.homotopy row (k + 1)) i p

def Contraction.checkBlock (c : Contraction) (row : IntegralRow) (k block : Nat) : Bool :=
  let e := row.columns k
  let d := row.columns (k + 1)
  let p := c.projection row k
  let i := c.inclusion row k
  Sparse.checkZeroCompBlock d e block && Sparse.checkZeroCompBlock p e block &&
  Sparse.checkZeroCompBlock d i block && Sparse.checkRetractBlock p i block &&
  Sparse.checkHomotopyBlock e d (c.homotopy row k) (c.homotopy row (k + 1)) i p block

private def readRaw (m : Nat) (data : RawColumns) (j : Nat) :
    Sparse.IntegerColumn :=
  (data[j]?.getD []).filter fun (r, _) => r < m

private theorem readRaw_eq (n m : Nat) (data : RawColumns) (j : Fin n) :
    readRaw m data j.val = Sparse.eraseIndices (decode n m data j) := by
  unfold readRaw decode
  generalize data[j.val]?.getD [] = xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨r, a⟩
    by_cases hr : r < m
    · simp [Sparse.eraseIndices, hr]
      simpa [Sparse.eraseIndices] using ih
    · simpa [Sparse.eraseIndices, hr] using ih

private def rawData (row : IntegralRow) (t : Nat) : RawColumns :=
  (row.matrix t).getD #[]

/-- Integer coefficient checks use natural indices during evaluation. Dimension
agreement recovers the typed columns in the soundness proof. -/
def Contraction.checkRawBlock (c : Contraction) (row : IntegralRow)
    (k a n b block : Nat) : Bool :=
  let r := c.rank k
  let e := readRaw n (rawData row k)
  let d := readRaw b (rawData row (k + 1))
  let p := readRaw r (c.p (k + 1))
  let i := readRaw n (c.i (k + 1))
  let h₀ := readRaw a (c.h (k + 1))
  let h₁ := readRaw n (c.h (k + 2))
  Sparse.rawBlock a block (fun j => Sparse.rawZero (Sparse.rawApply d (e j))) &&
  Sparse.rawBlock a block (fun j => Sparse.rawZero (Sparse.rawApply p (e j))) &&
  Sparse.rawBlock r block (fun j => Sparse.rawZero (Sparse.rawApply d (i j))) &&
  Sparse.rawBlock r block (fun j => Sparse.rawZero (Sparse.rawApply p (i j) ++ [(j, -1)])) &&
  Sparse.rawBlock n block (fun j => Sparse.rawZero (Sparse.rawApply e (h₀ j) ++
    Sparse.rawApply h₁ (d j) ++ Sparse.rawApply i (p j) ++ [(j, -1)]))

theorem Contraction.checkBlock_of_raw (c : Contraction) (row : IntegralRow)
    (k a n b block : Nat)
    (ha : a = (row.basis k).size) (hn : n = (row.basis (k + 1)).size)
    (hb : b = (row.basis (k + 2)).size)
    (checked : c.checkRawBlock row k a n b block = true) :
    c.checkBlock row k block = true := by
  subst a n b
  unfold Contraction.checkRawBlock at checked
  dsimp only at checked
  unfold Contraction.checkBlock
  dsimp only
  have he : ∀ j : Fin (row.basis k).size, readRaw _ (rawData row k) j.val =
      Sparse.eraseIndices (row.columns k j) := readRaw_eq _ _ _
  have hd : ∀ j : Fin (row.basis (k + 1)).size, readRaw _ (rawData row (k + 1)) j.val =
      Sparse.eraseIndices (row.columns (k + 1) j) := readRaw_eq _ _ _
  have hp : ∀ j : Fin (row.basis (k + 1)).size, readRaw _ (c.p (k + 1)) j.val =
      Sparse.eraseIndices (c.projection row k j) := readRaw_eq _ _ _
  have hi : ∀ j : Fin (c.rank k), readRaw _ (c.i (k + 1)) j.val =
      Sparse.eraseIndices (c.inclusion row k j) := readRaw_eq _ _ _
  have hh₀ : ∀ j : Fin (row.basis (k + 1)).size, readRaw _ (c.h (k + 1)) j.val =
      Sparse.eraseIndices (c.homotopy row k j) := readRaw_eq _ _ _
  have hh₁ : ∀ j : Fin (row.basis (k + 2)).size, readRaw _ (c.h (k + 2)) j.val =
      Sparse.eraseIndices (c.homotopy row (k + 1) j) := readRaw_eq _ _ _
  rw [Sparse.rawZeroComp_eq _ _ _ _ hd he block,
    Sparse.rawZeroComp_eq _ _ _ _ hp he block,
    Sparse.rawZeroComp_eq _ _ _ _ hd hi block,
    Sparse.rawRetract_eq _ _ _ _ hp hi block,
    Sparse.rawHomotopy_eq _ _ _ _ _ _ _ _ _ _ _ _ he hd hh₀ hh₁ hi hp block] at checked
  exact checked

theorem Contraction.check_of_blocks (c : Contraction) (row : IntegralRow) (k blocks : Nat)
    (h₀ : (row.basis k).size ≤ 16 * blocks)
    (h₁ : (row.basis (k + 1)).size ≤ 16 * blocks) (h₂ : c.rank k ≤ 16 * blocks)
    (checked : ∀ b < blocks, c.checkBlock row k b = true) :
    c.check row k = true := by
  have hb (b : Nat) (h : b < blocks) := checked b h
  simp only [Contraction.checkBlock, Bool.and_eq_true] at hb
  simp only [Contraction.check, Bool.and_eq_true]
  exact ⟨⟨⟨⟨Sparse.checkZeroComp_of_blocks _ _ h₀ (fun b h => (hb b h).1.1.1.1),
    Sparse.checkZeroComp_of_blocks _ _ h₀ (fun b h => (hb b h).1.1.1.2)⟩,
    Sparse.checkZeroComp_of_blocks _ _ h₂ (fun b h => (hb b h).1.1.2)⟩,
    Sparse.checkRetract_of_blocks _ _ h₂ (fun b h => (hb b h).1.2)⟩,
    Sparse.checkHomotopy_of_blocks _ _ _ _ _ _ h₁ (fun b h => (hb b h).2)⟩

theorem Contraction.check_empty (c : Contraction) (row : IntegralRow) (k : Nat)
    (h₀ : (row.basis k).size = 0) (h₁ : (row.basis (k + 1)).size = 0) (h₂ : c.rank k = 0) :
    c.check row k = true := by
  unfold Contraction.check
  dsimp only
  have hzero {a b m : Nat} (ha : a = 0) (f : Columns b m) (g : Columns a b) :
      Sparse.checkZeroComp f g = true := by subst a; apply Sparse.checkZeroComp_empty
  have hretract {n m : Nat} (hm : m = 0) (f : Columns n m) (g : Columns m n) :
      Sparse.checkRetract f g = true := by subst m; apply Sparse.checkRetract_empty
  have hhomotopy {a n b r : Nat} (hn : n = 0)
      (e : Columns a n) (d : Columns n b) (h : Columns n a) (h' : Columns b n)
      (i : Columns r n) (p : Columns n r) :
      Sparse.checkHomotopy e d h h' i p = true := by subst n; apply Sparse.checkHomotopy_empty
  rw [hzero h₀, hzero h₀, hzero h₂, hretract h₂, hhomotopy h₁]
  rfl

theorem Contraction.sound (c : Contraction) (row : IntegralRow)
    (defined : ∀ t, (row.matrix t).isSome = true) (valid : ∀ k, c.check row k = true) :
    row.Computes c.rank := by
  have checks (k : Nat) := valid k
  simp only [Contraction.check, Bool.and_eq_true] at checks
  have square (k : Nat) := Sparse.zeroComp _ _ (checks k).1.1.1.1
  refine ⟨defined, square, fun k => ⟨?_⟩⟩
  exact cohomologyEquiv _ _ (square k) _ _ _ _
    (Sparse.zeroComp _ _ (checks k).1.1.1.2)
    (Sparse.zeroComp _ _ (checks k).1.1.2)
    (Sparse.retract _ _ (checks k).1.2)
    (Sparse.homotopy _ _ _ _ _ _ (checks k).2)

def replayStageBasis (j : Nat) : Nat → Array Enhanced
  | 0 => #[]
  | k + 1 => if k < crossings + 1 then (replayBasis j k).toArray else #[]

theorem replayStageBasis_eq (j : Nat) (hj : 17 ≤ j) :
    replayStageBasis j = stageBasis j := by
  funext t
  cases t with
  | zero => rfl
  | succ k => simp [replayStageBasis, stageBasis, replayBasis_eq j k hj]

theorem stageMatrix_eq_replay (j t : Nat) (hj : 17 ≤ j) :
    stageMatrix j t =
      calculateMatrix replayResolution (replayStageBasis j t) (replayStageBasis j (t + 1)) := by
  rw [replayResolution_eq, replayStageBasis_eq j hj]
  rfl


end D5.S3.Topology.FourBraidKhovanovCube
