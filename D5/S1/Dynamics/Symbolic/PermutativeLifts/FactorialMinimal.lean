/- GID: D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialMinimal
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/PermutativeLifts/FactorialMinimal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform recurrence and minimality of the actual factorial-word subshift. -/

import D5.S1.Dynamics.Symbolic.PermutativeLifts.FactorialSubshift
import Mathlib.Data.List.OfFn
import Mathlib.Dynamics.Minimal
import Mathlib.Topology.Constructions

set_option autoImplicit false

open Set SymbolicDynamics.FullShift
open scoped BigOperators

namespace D5.S1.Dynamics.Symbolic.PermutativeLifts

/-- Literal occurrence, with the same physical integer origin for every letter. -/
def WordOccursAt (w : List Bool) (y : ℤ → Bool) (t : ℤ) : Prop :=
  ∀ (j : ℕ) (hj : j < w.length), y (t + (j : ℤ)) = w[j]

/-- A finite consecutive window in an actual two-sided point. -/
def factorialWindow (y : ℤ → Bool) (t : ℤ) (r : ℕ) : List Bool :=
  List.ofFn fun j : Fin r => y (t + (j.val : ℤ))

@[simp] theorem factorialWindow_length (y : ℤ → Bool) (t : ℤ) (r : ℕ) :
    (factorialWindow y t r).length = r := by simp [factorialWindow]

private theorem readTile_coordinate (W : Bool → List Bool) (s : TileState W)
    (a : Bool) (p : ℕ) (hp : p < (W a).length)
    (ht : s.1 = a) (ho : s.2.val = p) : readTile W s = (W a)[p] := by
  rcases s with ⟨b, q⟩
  dsimp at ht ho
  subst a
  subst p
  rfl

theorem marked_block_occurs (W : Bool → List Bool) (x : MarkedTiling W)
    (b : ℤ) (hb : (x.1 b).2.val = 0) :
    WordOccursAt (W (x.1 b).1) (readTiling W x) b := by
  intro j hj
  have hp := tiled_forwards W x.2 b j (by simpa only [hb, zero_add] using hj)
  exact readTile_coordinate W (x.1 (b + (j : ℤ))) (x.1 b).1 j hj hp.1
    (by simpa only [hb, zero_add] using hp.2)

theorem occurs_of_infix {u v : List Bool} {y : ℤ → Bool} {t : ℤ}
    (huv : u <:+: v) (hv : WordOccursAt v y t) :
    ∃ k : ℕ, k + u.length ≤ v.length ∧ WordOccursAt u y (t + (k : ℤ)) := by
  obtain ⟨pre, post, rfl⟩ := huv
  refine ⟨pre.length, ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · intro j hj
    have hij : pre.length + j < (pre ++ u ++ post).length := by
      simp only [List.length_append]
      omega
    have hread := hv (pre.length + j) hij
    have hletter : (pre ++ u ++ post)[pre.length + j]'hij = u[j] := by
      have hpre : pre.length + j < (pre ++ u).length := by
        simp only [List.length_append]
        omega
      rw [List.getElem_append_left hpre, List.getElem_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left]
    simpa only [Int.natCast_add, add_assoc] using hread.trans hletter

theorem infix_of_coordinates {u v : List Bool} {p : ℕ}
    (hp : p + u.length ≤ v.length)
    (hletters : ∀ (j : ℕ) (hj : j < u.length),
      u[j] = v[p + j]'(by omega)) : u <:+: v := by
  have heq : u = (v.drop p).take u.length := by
    apply List.ext_getElem
    · simp only [List.length_take, List.length_drop]
      omega
    · intro j hj hj'
      simpa only [List.getElem_take, List.getElem_drop] using hletters j hj
  rw [heq]
  exact (List.take_prefix _ _).isInfix.trans (List.drop_suffix p v).isInfix

/-- A window shorter than every block meets only its current block and the next.
The proof uses actual marked physical coordinates, not an assumed recurrence. -/
theorem factorialWindow_infix_pair (n : ℕ) (y : FactorialPoint) (t : ℤ) (r : ℕ)
    (hr : ∀ a, r ≤ (word n a).length) :
    ∃ a b : Bool, factorialWindow y.1 t r <:+: word n a ++ word n b := by
  let x := decode n y
  let a := (x.1 t).1
  let p := (x.1 t).2.val
  let b : ℤ := t + (((word n a).length - p : ℕ) : ℤ)
  let c := (x.1 b).1
  have hp : p < (word n a).length := (x.1 t).2.isLt
  have hb : (x.1 b).2.val = 0 := tiled_boundary_ahead (word n) x.2 t
  refine ⟨a, c, infix_of_coordinates (p := p) ?_ ?_⟩
  · simp only [factorialWindow_length, List.length_append]
    have hrc := hr c
    omega
  · intro j hj
    have hjr : j < r := by simpa only [factorialWindow_length] using hj
    have hread : y.1 (t + (j : ℤ)) = readTile (word n) (x.1 (t + (j : ℤ))) := by
      exact (congrFun (read_decode n y) (t + (j : ℤ))).symm
    simp only [factorialWindow, List.getElem_ofFn]
    rw [hread]
    by_cases hfirst : p + j < (word n a).length
    · have hs := tiled_forwards (word n) x.2 t j hfirst
      rw [List.getElem_append_left hfirst]
      exact readTile_coordinate (word n) (x.1 (t + (j : ℤ))) a (p + j) hfirst
        hs.1 hs.2
    · let q : ℕ := p + j - (word n a).length
      have hq : q < (word n c).length := by
        have hrc := hr c
        dsimp [q]
        omega
      have hindex : t + (j : ℤ) = b + (q : ℤ) := by dsimp [b, q]; omega
      have hs := tiled_forwards (word n) x.2 b q (by simpa only [hb, zero_add] using hq)
      rw [List.getElem_append_right (by omega), hindex]
      exact readTile_coordinate (word n) (x.1 (b + (q : ℤ))) c q hq hs.1
        (by simpa only [hb, zero_add] using hs.2)

/-- Every occurring finite window lies in every sufficiently high actual block. -/
theorem factorialWindow_infix_block (y : FactorialPoint) (t : ℤ) (r : ℕ)
    (a : Bool) : factorialWindow y.1 t r <:+: word (r + 3) a := by
  have hr (b : Bool) : r ≤ (word (r + 1) b).length := by
    have := word_length_lower_bound (r + 1) b
    omega
  obtain ⟨b, c, hpair⟩ := factorialWindow_infix_pair (r + 1) y t r hr
  exact hpair.trans (word_pair_infix (r + 1) (by omega) a b c)

/-- The explicit recurrence bound is twice the longer level-(r+3) block.
It works uniformly over every point and every integer starting position. -/
theorem factorialWindow_uniform_recurrence (y : FactorialPoint) (t : ℤ) (r : ℕ) :
    ∃ M : ℕ, ∀ (z : FactorialPoint) (u : ℤ), ∃ s : ℤ,
      u ≤ s ∧ s ≤ u + (M : ℤ) ∧ WordOccursAt (factorialWindow y.1 t r) z.1 s := by
  let n := r + 3
  let H := (word n true).length
  refine ⟨2 * H, ?_⟩
  intro z u
  let x := decode n z
  let b := u + (((word n (x.1 u).1).length - (x.1 u).2.val : ℕ) : ℤ)
  have hb : (x.1 b).2.val = 0 := tiled_boundary_ahead (word n) x.2 u
  have hblock : WordOccursAt (word n (x.1 b).1) z.1 b := by
    rw [← read_decode n z]
    exact marked_block_occurs (word n) x b hb
  obtain ⟨k, hk, hocc⟩ := occurs_of_infix
    (factorialWindow_infix_block y t r (x.1 b).1) hblock
  have hle (a : Bool) : (word n a).length ≤ H := by
    cases a
    · exact word_false_length_le_true n
    · exact le_refl _
  have hheight := hle (x.1 u).1
  have hkheight := hle (x.1 b).1
  have hk' : k + (factorialWindow y.1 t r).length ≤ (word n (x.1 b).1).length := hk
  have hk_bound : k ≤ H := by omega
  have hdist : (word n (x.1 u).1).length - (x.1 u).2.val ≤ H :=
    (Nat.sub_le _ _).trans hheight
  have hb_bounds : u ≤ b ∧ b ≤ u + (H : ℤ) := by
    dsimp only [b]
    constructor <;> omega
  refine ⟨b + (k : ℤ), ?_, ?_, hocc⟩ <;> omega

theorem factorialWindow_occurs_everywhere (y z : FactorialPoint) (t : ℤ) (r : ℕ) :
    ∃ s : ℤ, WordOccursAt (factorialWindow y.1 t r) z.1 s := by
  obtain ⟨M, hM⟩ := factorialWindow_uniform_recurrence y t r
  obtain ⟨s, _, _, hs⟩ := hM z 0
  exact ⟨s, hs⟩

/-- Every finite coordinate pattern of one point is met by the orbit of every
other point. The interval window includes negative coordinates as well. -/
theorem factorial_finite_pattern (y z : FactorialPoint) (I : Finset ℤ) :
    ∃ g : ℤ, ∀ i ∈ I, (shiftFactorial g y).1 i = z.1 i := by
  classical
  let N : ℕ := ∑ i ∈ I, i.natAbs
  have hbound (i : ℤ) (hi : i ∈ I) : -(N : ℤ) ≤ i ∧ i ≤ (N : ℤ) := by
    have habs : i.natAbs ≤ N := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
    have hpos : i ≤ (i.natAbs : ℤ) := Int.le_natAbs
    have hneg : -i ≤ (i.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -i))
    omega
  obtain ⟨s, hs⟩ := factorialWindow_occurs_everywhere z y (-(N : ℤ)) (2 * N + 1)
  refine ⟨s + (N : ℤ), ?_⟩
  intro i hi
  have hib := hbound i hi
  let j := (i + (N : ℤ)).toNat
  have hj : j < (factorialWindow z.1 (-(N : ℤ)) (2 * N + 1)).length := by
    simp only [factorialWindow_length]
    dsimp [j]
    omega
  have hh := hs j hj
  simp only [factorialWindow, List.getElem_ofFn] at hh
  change y.1 ((s + (N : ℤ)) + i) = z.1 i
  have hleft : s + (j : ℤ) = (s + (N : ℤ)) + i := by dsimp [j]; omega
  have hright : -(N : ℤ) + (j : ℤ) = i := by dsimp [j]; omega
  rwa [hleft, hright] at hh

/-- Actual integer shift orbits are dense in the constructed compact subshift. -/
theorem factorial_orbit_dense (y : FactorialPoint) :
    DenseRange (fun g : ℤ => shiftFactorial g y) := by
  classical
  change Dense (Set.range (fun g : ℤ => shiftFactorial g y))
  apply dense_iff_inter_open.mpr
  intro U hU hUne
  obtain ⟨z, hz⟩ := hUne
  obtain ⟨V, hV, hUV⟩ := isOpen_induced_iff.mp hU
  have hzV : z.1 ∈ V := by rw [← hUV] at hz; exact hz
  obtain ⟨I, O, hO, hOV⟩ := isOpen_pi_iff.mp hV z.1 hzV
  obtain ⟨g, hg⟩ := factorial_finite_pattern y z I
  refine ⟨shiftFactorial g y, ?_, g, rfl⟩
  rw [← hUV]
  apply hOV
  intro i hi
  rw [hg i hi]
  exact (hO i hi).2

instance factorialShiftAction : AddAction ℤ FactorialPoint where
  vadd := shiftFactorial
  zero_vadd y := by
    change shiftFactorial 0 y = y
    apply Subtype.ext
    funext i
    change y.1 (0 + i) = y.1 i
    exact congrArg y.1 (zero_add i)
  add_vadd a b y := by
    change shiftFactorial (a + b) y = shiftFactorial a (shiftFactorial b y)
    apply Subtype.ext
    funext i
    change y.1 ((a + b) + i) = y.1 (b + (a + i))
    exact congrArg y.1 (by omega : (a + b) + i = b + (a + i))

instance factorialShiftMinimal : AddAction.IsMinimal ℤ FactorialPoint where
  dense_orbit := factorial_orbit_dense

end D5.S1.Dynamics.Symbolic.PermutativeLifts
