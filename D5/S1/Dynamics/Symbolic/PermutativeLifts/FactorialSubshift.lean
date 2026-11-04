/- GID: D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialSubshift
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/PermutativeLifts/FactorialSubshift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Canonical decoding and aperiodicity of the actual factorial-word subshift. -/

import D5.S1.Dynamics.Symbolic.PermutativeLifts.FactorialRefinement

set_option autoImplicit false

open SymbolicDynamics.FullShift

namespace D5.S1.Dynamics.Symbolic.PermutativeLifts

abbrev FactorialPoint := {y : ℤ → Bool // y ∈ factorialSubshift.carrier}

instance factorialPointNonempty : Nonempty FactorialPoint :=
  factorial_subshift_nonempty.to_subtype

instance factorialPointCompact : CompactSpace FactorialPoint :=
  isCompact_iff_compactSpace.mp factorialSubshift.isClosed.isCompact

/-- Existence is supplied by the actual compact intersection, and uniqueness
by the marker recognizability theorem. No tiling is assumed as extra input. -/
noncomputable def decode (n : ℕ) (y : FactorialPoint) : MarkedTiling (word n) :=
  Classical.choose (Set.mem_iInter.mp y.2 n)

theorem read_decode (n : ℕ) (y : FactorialPoint) :
    readTiling (word n) (decode n y) = y.1 :=
  Classical.choose_spec (Set.mem_iInter.mp y.2 n)

theorem continuous_decode (n : ℕ) : Continuous (decode n) := by
  rw [continuous_iff_isClosed]
  intro s hs
  have hclosed : IsClosed (readTiling (word n) '' s) :=
    (hs.isCompact.image (continuous_readTiling (word n))).isClosed
  have heq : decode n ⁻¹' s = Subtype.val ⁻¹' (readTiling (word n) '' s) := by
    ext y
    constructor
    · exact fun hy => ⟨decode n y, hy, read_decode n y⟩
    · rintro ⟨x, hx, hxy⟩
      have he : x = decode n y := readTiling_injective n (hxy.trans (read_decode n y).symm)
      change decode n y ∈ s
      rwa [he] at hx
  rw [heq]
  exact hclosed.preimage continuous_subtype_val

def shiftFactorial (g : ℤ) (y : FactorialPoint) : FactorialPoint :=
  ⟨shift g y.1, factorialSubshift.mapsTo g y.2⟩

theorem decode_shift (n : ℕ) (g : ℤ) (y : FactorialPoint) :
    decode n (shiftFactorial g y) = shiftTiling (word n) g (decode n y) := by
  apply readTiling_injective n
  rw [read_decode, readTiling_shift, read_decode]
  rfl

/-- A positive period would translate a recognizable boundary to the interior
of a block longer than that period. -/
theorem factorial_no_positive_period (y : FactorialPoint) {p : ℕ} (hp : 0 < p) :
    shift (p : ℤ) y.1 ≠ y.1 := by
  intro hperiod
  let n := p + 1
  let x := decode n y
  have hxperiod : shiftTiling (word n) (p : ℤ) x = x := by
    apply readTiling_injective n
    rw [readTiling_shift]
    change shift (p : ℤ) (readTiling (word n) (decode n y)) =
      readTiling (word n) (decode n y)
    rw [read_decode]
    exact hperiod
  let b : ℤ := 0 - ((x.1 0).2.val : ℤ)
  have hb : (x.1 b).2.val = 0 := (tiled_boundary_behind (word n) x.2 0).2
  have hlen := word_length_lower_bound n (x.1 b).1
  have hinside : (x.1 b).2.val + p < (word n (x.1 b).1).length := by
    have hn : p < n := by dsimp [n]; omega
    omega
  have hforward := (tiled_forwards (word n) x.2 b p hinside).2
  have hsame := congrArg (fun z : MarkedTiling (word n) => (z.1 b).2.val) hxperiod
  change (x.1 ((p : ℤ) + b)).2.val = (x.1 b).2.val at hsame
  rw [add_comm] at hsame
  omega

theorem factorial_nat_orbit_injective (y : FactorialPoint) :
    Function.Injective (fun n : ℕ => shiftFactorial (n : ℤ) y) := by
  have hlt (m n : ℕ) (hmn : m < n) :
      shiftFactorial (m : ℤ) y ≠ shiftFactorial (n : ℤ) y := by
    intro h
    have he := congrArg (fun z : FactorialPoint => shift (-(m : ℤ)) z.1) h
    change shift (-(m : ℤ)) (shift (m : ℤ) y.1) =
      shift (-(m : ℤ)) (shift (n : ℤ) y.1) at he
    rw [← shift_add, ← shift_add, add_neg_cancel, shift_zero] at he
    apply factorial_no_positive_period y (Nat.sub_pos_of_lt hmn)
    simpa only [Nat.cast_sub (Nat.le_of_lt hmn), sub_eq_add_neg] using he.symm
  intro m n h
  rcases lt_trichotomy m n with hm | hm | hm
  · exact False.elim (hlt m n hm h)
  · exact hm
  · exact False.elim (hlt n m hm h.symm)

instance factorialPointInfinite : Infinite FactorialPoint := by
  obtain ⟨y⟩ := (inferInstance : Nonempty FactorialPoint)
  exact Infinite.of_injective _ (factorial_nat_orbit_injective y)

end D5.S1.Dynamics.Symbolic.PermutativeLifts
