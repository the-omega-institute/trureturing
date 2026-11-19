/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/CubeBitMoves
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/CubeBitMoves
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Finite]
   utility: none
   digest: Represent cube vertices and their coordinate moves as bit vectors. -/

import Mathlib.Data.BitVec
import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
import Batteries.Tactic.OpenPrivate

/-! Bit encodings and coordinate moves for cube embeddings. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical

/-- Little-endian encoding of a cube vertex for the integer certificate data. -/
def cubeBitVec (n : ℕ) : BitVec n ≃ (Fin n → Bool) where
  toFun x i := x.getLsbD i.val
  invFun x := (BitVec.ofBoolListLE (List.ofFn x)).cast List.length_ofFn
  left_inv x := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
      List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hi, Option.getD_some]
  right_inv x := by
    funext i
    simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
      List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left i.isLt, Option.getD_some]

/-- XOR by a single bit is the corresponding coordinate flip in the cube. -/
theorem cubeBitVec_xor_single {n : ℕ} (x : BitVec n) (i : Fin n) :
    cubeBitVec n (x ^^^ BitVec.ofNat n (2 ^ i.val)) =
      Function.update (cubeBitVec n x) i (!(cubeBitVec n x i)) := by
  funext j
  change (x ^^^ BitVec.ofNat n (2 ^ i.val)).getLsbD j.val = _
  rw [BitVec.getLsbD_xor, BitVec.getLsbD_ofNat, Nat.testBit_two_pow]
  by_cases h : j = i
  · subst j
    simp [cubeBitVec, i.isLt]
  · have h' : i.val ≠ j.val := fun he => h (Fin.ext he.symm)
    simp [Function.update_of_ne h, cubeBitVec, h']

#print axioms cubeBitVec_xor_single

end D5.S3.Combinatorics.Graph.HypercubeCritical

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeBitMoves

open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (flip_adj)
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth

private def toggle (x : BitVec 9) (i : Fin 9) : BitVec 9 :=
  x ^^^ BitVec.ofNat 9 (2 ^ i.val)

private def hasTwoSetBits (x : BitVec 9) : Bool :=
  let y := x &&& (x - 1)
  y != 0 && (y &&& (y - 1)) == 0

private theorem hasTwoSetBits_of_two_toggles (i j : Fin 9) (h : i ≠ j) :
    hasTwoSetBits (toggle (toggle 0 i) j) = true := by
  fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel

private def hasOneSetBit (d : BitVec 9) : Bool :=
  d != 0 && (d &&& (d - 1)) == 0

private theorem hasOneSetBit_iff (d : BitVec 9) :
    hasOneSetBit d = true ↔ ∃ i : Fin 9, d = BitVec.ofNat 9 (2 ^ i.val) := by
  have h : ∀ a : Fin (2 ^ 9),
      hasOneSetBit (BitVec.ofFin a) = true ↔
        ∃ i : Fin 9, BitVec.ofFin a = BitVec.ofNat 9 (2 ^ i.val) := by
    decide +kernel
  exact h d.toFin

private def adjacent (x y : BitVec 9) : Bool :=
  hasOneSetBit (x ^^^ y)

private theorem adjacent_iff (x y : BitVec 9) :
    adjacent x y = true ↔ (hypercube 9).Adj (cubeBitVec 9 x) (cubeBitVec 9 y) := by
  rw [adjacent, hasOneSetBit_iff]
  constructor
  · rintro ⟨i, hi⟩
    have hx : toggle x i = y := by
      rw [toggle, ← hi, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    rw [← hx, toggle, cubeBitVec_xor_single]
    exact flip_adj _ _
  · intro h
    obtain ⟨i, hi⟩ := adjacent_exists_flip h
    have hx : toggle x i = y := by
      apply (cubeBitVec 9).injective
      rw [toggle, cubeBitVec_xor_single, hi]
      rfl
    refine ⟨i, ?_⟩
    rw [← hx, toggle, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

private def moves (x : BitVec 9) : List (BitVec 9) :=
  (List.finRange 9).flatMap fun a =>
    ((List.finRange 9).filter (a < ·)).map fun b => toggle (toggle x a) b

private theorem two_toggles_mem_moves (x : BitVec 9) (a b : Fin 9) (h : a ≠ b) :
    toggle (toggle x a) b ∈ moves x := by
  unfold moves
  rcases lt_or_gt_of_ne h with hab | hba
  · exact List.mem_flatMap.mpr ⟨a, List.mem_finRange _, List.mem_map.mpr
      ⟨b, List.mem_filter.mpr ⟨List.mem_finRange _, decide_eq_true hab⟩, rfl⟩⟩
  · refine List.mem_flatMap.mpr ⟨b, List.mem_finRange _, List.mem_map.mpr
      ⟨a, List.mem_filter.mpr ⟨List.mem_finRange _, decide_eq_true hba⟩, ?_⟩⟩
    simp only [toggle, BitVec.xor_assoc x, BitVec.xor_comm (BitVec.ofNat 9 (2 ^ b.val))]

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeBitMoves
