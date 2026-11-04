/- GID: D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Recognizable balanced factorial towers, compact subshift and aperiodicity. -/

import D5.S1.Dynamics.Symbolic.PermutativeLifts.BalancedWords
import D5.S1.Dynamics.Symbolic.PermutativeLifts.EqualLengthTiling
import D5.S1.Dynamics.Symbolic.PermutativeLifts.TwoRunRefinement

/-! Unique marked tilings of the equal-height balanced words give an actual
nonempty compact subshift, continuous compatible decoders and aperiodic points. -/

set_option autoImplicit false

open Set SymbolicDynamics.FullShift

namespace D5.S1.Dynamics.Symbolic.PermutativeLifts.Balanced

/-- Literal refinement into the two positive runs in a balanced parent word. -/
def refineBalancedTiling (n : ℕ) (x : MarkedTiling (balancedWord (n + 1))) :
    MarkedTiling (balancedWord n) :=
  TwoRunRefinement.refineTiling (balancedWord n)
    (fun a => by rw [balancedWord_length]; exact height_pos n)
    (fun a => (if a then 1 else 2) * (n + 1).factorial)
    (fun a => (if a then 2 else 1) * (n + 1).factorial)
    (fun a => by cases a <;> simp [Nat.factorial_pos])
    (fun a => by cases a <;> simp [Nat.factorial_pos]) x

theorem read_refineBalancedTiling (n : ℕ)
    (x : MarkedTiling (balancedWord (n + 1))) :
    readTiling (balancedWord n) (refineBalancedTiling n x) =
      readTiling (balancedWord (n + 1)) x := by
  exact TwoRunRefinement.readTiling_refineTiling (balancedWord n)
    (fun a => by rw [balancedWord_length]; exact height_pos n)
    (fun a => (if a then 1 else 2) * (n + 1).factorial)
    (fun a => (if a then 2 else 1) * (n + 1).factorial)
    (fun a => by cases a <;> simp [Nat.factorial_pos])
    (fun a => by cases a <;> simp [Nat.factorial_pos]) x

/-- Adjacent physical positions of types 1 and 0 identify exactly a parent start. -/
theorem refineBalancedTiling_boundary_iff (n : ℕ)
    (x : MarkedTiling (balancedWord (n + 1))) (i : ℤ) :
    (x.1 i).2.val = 0 ↔
      ((refineBalancedTiling n x).1 (i - 1)).1 = true ∧
      ((refineBalancedTiling n x).1 i).1 = false := by
  exact TwoRunRefinement.refineTiling_boundary_iff (balancedWord n)
    (fun a => by rw [balancedWord_length]; exact height_pos n)
    (fun a => (if a then 1 else 2) * (n + 1).factorial)
    (fun a => (if a then 2 else 1) * (n + 1).factorial)
    (fun a => by cases a <;> simp [Nat.factorial_pos])
    (fun a => by cases a <;> simp [Nat.factorial_pos]) x i

/-- The actual equal-height words have unique marked tilings. Equal boundaries
identify offsets, and distinct words identify types even though their heights agree. -/
theorem balancedReadTiling_injective (n : ℕ) :
    Function.Injective (readTiling (balancedWord n)) := by
  induction n with
  | zero =>
    intro x y hxy
    apply equal_length_tiling_eq_of_read_boundaries (balancedWord 0) (height 0)
      (balancedWord_length 0) (balancedWord_injective 0) x y hxy
    intro i
    have hx : (x.1 i).2.val = 0 := by
      have h := (x.1 i).2.isLt
      simp only [balancedWord_zero, List.length_singleton] at h
      omega
    have hy : (y.1 i).2.val = 0 := by
      have h := (y.1 i).2.isLt
      simp only [balancedWord_zero, List.length_singleton] at h
      omega
    simp only [hx, hy]
  | succ n ih =>
    intro x y hxy
    have hr : refineBalancedTiling n x = refineBalancedTiling n y := by
      apply ih
      rw [read_refineBalancedTiling, read_refineBalancedTiling, hxy]
    apply equal_length_tiling_eq_of_read_boundaries (balancedWord (n + 1))
      (height (n + 1)) (balancedWord_length (n + 1))
      (balancedWord_injective (n + 1)) x y hxy
    intro i
    rw [refineBalancedTiling_boundary_iff, refineBalancedTiling_boundary_iff, hr]

/-- Each upper tiling supplies a lower tiling of precisely the same visible point. -/
theorem balanced_subshift_succ_subset (n : ℕ) :
    (tiledSubshift (balancedWord (n + 1))).carrier ⊆
      (tiledSubshift (balancedWord n)).carrier := by
  rintro y ⟨x, rfl⟩
  exact ⟨refineBalancedTiling n x, read_refineBalancedTiling n x⟩

/-- The simultaneous balanced-word subshift is an actual closed intersection. -/
def balancedSubshift : Subshift Bool ℤ where
  carrier := ⋂ n : ℕ, (tiledSubshift (balancedWord n)).carrier
  isClosed := isClosed_iInter fun n => (tiledSubshift (balancedWord n)).isClosed
  mapsTo := by
    intro k y hy
    simp only [Set.mem_iInter] at hy ⊢
    exact fun n => (tiledSubshift (balancedWord n)).mapsTo k (hy n)

theorem balanced_subshift_nonempty : balancedSubshift.carrier.Nonempty := by
  exact IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => (tiledSubshift (balancedWord n)).carrier)
    balanced_subshift_succ_subset
    (fun n => tiledSubshift_nonempty (balancedWord n)
      (fun a => by rw [balancedWord_length]; exact height_pos n))
    (tiledSubshift (balancedWord 0)).isClosed.isCompact
    (fun n => (tiledSubshift (balancedWord n)).isClosed)

abbrev BalancedPoint := {y : ℤ → Bool // y ∈ balancedSubshift.carrier}

instance balancedPointNonempty : Nonempty BalancedPoint :=
  balanced_subshift_nonempty.to_subtype

instance balancedPointCompact : CompactSpace BalancedPoint :=
  isCompact_iff_compactSpace.mp balancedSubshift.isClosed.isCompact

/-- The unique decoder is chosen from the actual compact intersection. -/
noncomputable def decode (n : ℕ) (y : BalancedPoint) : MarkedTiling (balancedWord n) :=
  Classical.choose (Set.mem_iInter.mp y.2 n)

theorem read_decode (n : ℕ) (y : BalancedPoint) :
    readTiling (balancedWord n) (decode n y) = y.1 :=
  Classical.choose_spec (Set.mem_iInter.mp y.2 n)

theorem continuous_decode (n : ℕ) : Continuous (decode n) := by
  rw [continuous_iff_isClosed]
  intro s hs
  have hclosed : IsClosed (readTiling (balancedWord n) '' s) :=
    (hs.isCompact.image (continuous_readTiling (balancedWord n))).isClosed
  have heq : decode n ⁻¹' s = Subtype.val ⁻¹' (readTiling (balancedWord n) '' s) := by
    ext y
    constructor
    · exact fun hy => ⟨decode n y, hy, read_decode n y⟩
    · rintro ⟨x, hx, hxy⟩
      have he : x = decode n y :=
        balancedReadTiling_injective n (hxy.trans (read_decode n y).symm)
      change decode n y ∈ s
      rwa [he] at hx
  rw [heq]
  exact hclosed.preimage continuous_subtype_val

def shiftBalanced (g : ℤ) (y : BalancedPoint) : BalancedPoint :=
  ⟨shift g y.1, balancedSubshift.mapsTo g y.2⟩

theorem decode_shift (n : ℕ) (g : ℤ) (y : BalancedPoint) :
    decode n (shiftBalanced g y) = shiftTiling (balancedWord n) g (decode n y) := by
  apply balancedReadTiling_injective n
  rw [read_decode, readTiling_shift, read_decode]
  rfl

theorem refine_decode (n : ℕ) (y : BalancedPoint) :
    refineBalancedTiling n (decode (n + 1) y) = decode n y := by
  apply balancedReadTiling_injective n
  rw [read_refineBalancedTiling, read_decode, read_decode]

/-- A positive period would move a recognizable boundary into a longer tile's interior. -/
theorem balanced_no_positive_period (y : BalancedPoint) {p : ℕ} (hp : 0 < p) :
    shift (p : ℤ) y.1 ≠ y.1 := by
  intro hperiod
  let n := p + 1
  let x := decode n y
  have hxperiod : shiftTiling (balancedWord n) (p : ℤ) x = x := by
    apply balancedReadTiling_injective n
    rw [readTiling_shift]
    change shift (p : ℤ) (readTiling (balancedWord n) (decode n y)) =
      readTiling (balancedWord n) (decode n y)
    rw [read_decode]
    exact hperiod
  let b : ℤ := 0 - ((x.1 0).2.val : ℤ)
  have hb : (x.1 b).2.val = 0 := (tiled_boundary_behind (balancedWord n) x.2 0).2
  have hlen : n + 1 ≤ (balancedWord n (x.1 b).1).length := by
    rw [balancedWord_length]
    exact height_lower_bound n
  have hinside : (x.1 b).2.val + p < (balancedWord n (x.1 b).1).length := by
    have hn : p < n := by dsimp [n]; omega
    omega
  have hforward := (tiled_forwards (balancedWord n) x.2 b p hinside).2
  have hsame := congrArg (fun z : MarkedTiling (balancedWord n) => (z.1 b).2.val) hxperiod
  change (x.1 ((p : ℤ) + b)).2.val = (x.1 b).2.val at hsame
  rw [add_comm] at hsame
  omega

theorem balanced_nat_orbit_injective (y : BalancedPoint) :
    Function.Injective (fun n : ℕ => shiftBalanced (n : ℤ) y) := by
  have hlt (m n : ℕ) (hmn : m < n) :
      shiftBalanced (m : ℤ) y ≠ shiftBalanced (n : ℤ) y := by
    intro h
    have he := congrArg (fun z : BalancedPoint => shift (-(m : ℤ)) z.1) h
    change shift (-(m : ℤ)) (shift (m : ℤ) y.1) =
      shift (-(m : ℤ)) (shift (n : ℤ) y.1) at he
    rw [← shift_add, ← shift_add, add_neg_cancel, shift_zero] at he
    apply balanced_no_positive_period y (Nat.sub_pos_of_lt hmn)
    simpa only [Nat.cast_sub (Nat.le_of_lt hmn), sub_eq_add_neg] using he.symm
  intro m n h
  rcases lt_trichotomy m n with hm | hm | hm
  · exact False.elim (hlt m n hm h)
  · exact hm
  · exact False.elim (hlt n m hm h.symm)

instance balancedPointInfinite : Infinite BalancedPoint := by
  obtain ⟨y⟩ := (inferInstance : Nonempty BalancedPoint)
  exact Infinite.of_injective _ (balanced_nat_orbit_injective y)

end D5.S1.Dynamics.Symbolic.PermutativeLifts.Balanced
