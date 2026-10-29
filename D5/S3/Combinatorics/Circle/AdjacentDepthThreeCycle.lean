/- GID: D5/S3/Combinatorics/Circle/AdjacentDepthThreeCycle
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/AdjacentDepthThreeCycle
   mirror-E: none(waiver:audit-open-22063)
   anchors: [D5/S3/Combinatorics/Circle/NativeSeedChains,
     D5/S3/Combinatorics/Circle/SourceWidth]
   utility: none
   digest: Native adjacent-depth long seeds carry a physical order-three cycle.
   The global mixed root-only sweep remains a later theorem. -/
module
public import D5.S3.Combinatorics.Circle.NativeSeedChains
public import Mathlib.Logic.Equiv.Defs

/-! # Native long-seed physical three-cycles

For a native chain the labels are physical occurrences in `Fin k`.  When its
first-hit length is one larger than the common lower depth, the lower seed,
its predecessor negative, and its predecessor root form the literal packet
`[root, negative, seed]`.  The packet is rotated to `[seed, root, negative]`.
The permutation below is written with its inverse rather than inferred from an
involution: this is the order-three map used by the adjacent-depth design.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.AdjacentDepthThreeCycle

open SourceWidth ExpandingSourcePath NativeSeedChains

def cycleForward {α : Type*} [DecidableEq α] (a b c : α) (x : α) : α :=
  if x = a then c else if x = b then a else if x = c then b else x

def cycleBackward {α : Type*} [DecidableEq α] (a b c : α) (x : α) : α :=
  if x = a then b else if x = b then c else if x = c then a else x

private theorem cycleForward_backward {α : Type*} [DecidableEq α]
    {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (x : α) :
    cycleForward a b c (cycleBackward a b c x) = x := by
  by_cases hxa : x = a
  · subst x
    simp [cycleForward, cycleBackward, hab, hac, hbc]
  · by_cases hxb : x = b
    · subst x
      simp [cycleForward, cycleBackward, hab, hac, hbc]
    · by_cases hxc : x = c
      · subst x
        simp [cycleForward, cycleBackward, hab, hac, hbc]
      · simp [cycleForward, cycleBackward, hxa, hxb, hxc]

private theorem cycleBackward_forward {α : Type*} [DecidableEq α]
    {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (x : α) :
    cycleBackward a b c (cycleForward a b c x) = x := by
  by_cases hxa : x = a
  · subst x
    simp [cycleForward, cycleBackward, hab, hac, hbc]
  · by_cases hxb : x = b
    · subst x
      simp [cycleForward, cycleBackward, hab, hac, hbc]
    · by_cases hxc : x = c
      · subst x
        simp [cycleForward, cycleBackward, hab, hac, hbc]
      · simp [cycleForward, cycleBackward, hxa, hxb, hxc]

/-- The physical three-cycle, with its actual inverse exposed in the API. -/
def physicalThreeCycle {α : Type*} [DecidableEq α]
    (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : Equiv.Perm α :=
  Equiv.ofBijective (cycleForward a b c)
    ⟨fun x y h => by
      have := congrArg (cycleBackward a b c) h
      simpa [cycleBackward_forward hab hac hbc] using this,
      ⟨cycleBackward a b c, cycleForward_backward hab hac hbc,
        cycleBackward_forward hab hac hbc⟩⟩

theorem physicalThreeCycle_apply_root {α : Type*} [DecidableEq α]
    (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    physicalThreeCycle a b c hab hac hbc a = c := by
  simp [physicalThreeCycle, cycleForward, hab, hac]

theorem physicalThreeCycle_apply_negative {α : Type*} [DecidableEq α]
    (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    physicalThreeCycle a b c hab hac hbc b = a := by
  simp [physicalThreeCycle, cycleForward, hab, hbc]

theorem physicalThreeCycle_apply_seed {α : Type*} [DecidableEq α]
    (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    physicalThreeCycle a b c hab hac hbc c = b := by
  simp [physicalThreeCycle, cycleForward, hac, hbc]

theorem physicalThreeCycle_inverse {α : Type*} [DecidableEq α]
    (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (x : α) :
    (physicalThreeCycle a b c hab hac hbc).symm x = cycleBackward a b c x := by
  apply Equiv.injective (physicalThreeCycle a b c hab hac hbc)
  simp only [Equiv.apply_symm_apply]
  exact (cycleForward_backward hab hac hbc x).symm

private theorem native_distinct {k t : ℕ} (hk : 3 ≤ k)
    {root neg next : Fin k} {p : ℤ}
    (hroot : actualSource k t root = p)
    (hneg : actualSource k t neg = 2 * p - modulus k)
    (hnext : actualSource k t next = 4 * p - modulus k)
    (hrootpos : 0 < p) (hrootbound : 3 * p ≤ modulus k) :
    root ≠ neg ∧ root ≠ next ∧ neg ≠ next := by
  have hN : 0 < modulus k := (source_geometry hk).2.2.2
  have hnegval : 2 * p - modulus k < 0 := by omega
  have hnextval : 0 < 4 * p - modulus k := by
    have hQ := (source_geometry hk).1
    have hpQ : quarter k ≤ p := by
      have hNQ := (source_geometry hk).2.1
      omega
    omega
  constructor
  · intro h
    have := congrArg (actualSource k t) h
    omega
  constructor
  · intro h
    have := congrArg (actualSource k t) h
    omega
  · intro h
    have := congrArg (actualSource k t) h
    omega

theorem native_long_seed_three_cycle {k t : ℕ} (hk : 3 ≤ k)
    (hsmall : ∀ i : Fin k, |actualSource k t i| < quarter k →
      0 < actualSource k t i)
    (n : Fin k) (hn : actualSource k t n < 0)
    (h : ℕ) (hh : 1 ≤ h) :
    ∃ (a root neg next : Fin k) (r : ℕ),
      r = h + 1 ∧
      root = phase (by omega) a r ∧
      neg = phase (by omega) a (r + 1) ∧
      next = phase (by omega) a (r + 2) ∧
      0 < actualSource k t a ∧
      actualSource k t root = (2 : ℤ) ^ r * actualSource k t a ∧
      quarter k ≤ actualSource k t root ∧
      3 * actualSource k t root ≤ modulus k ∧
      actualSource k t neg = 2 * actualSource k t root - modulus k ∧
      actualSource k t neg < 0 ∧
      actualSource k t next = 4 * actualSource k t root - modulus k ∧
      0 < actualSource k t next ∧
      (physicalThreeCycle root neg next · root) = next ∧
      (physicalThreeCycle root neg next · neg) = root ∧
      (physicalThreeCycle root neg next · next) = neg ∧
      (physicalThreeCycle root neg next).symm =
        physicalThreeCycle next root neg (by omega) (by omega) (by omega) ∧
      let N := modulus k
      let U := fun z : ℤ => z + if z < 0 then N else 0
      U (actualSource k t neg) - U (actualSource k t root) =
        actualSource k t root ∧
      U (actualSource k t next) - U (actualSource k t neg) =
        actualSource k t neg := by
  obtain ⟨r, hr, hnodup, ha, hamod, hpre, hdyadic, hroot, hrootQ, hrootupper,
    hneg, hneglt, hnext, hnextpos, _, _, _⟩ :=
    native_chain_extraction hk hsmall n hn
  by_cases he : r = h + 1
  · let a := phase (by omega : 0 < k) n 1
    let root := phase (by omega : 0 < k) a r
    let neg := phase (by omega : 0 < k) a (r + 1)
    let next := phase (by omega : 0 < k) a (r + 2)
    have hrootnegnext : (root ≠ neg ∧ root ≠ next ∧ neg ≠ next) := by
      exact native_distinct hk hroot hneg hnext (by omega) hrootupper
    rcases hrootnegnext with ⟨hrn, hrx, hnx⟩
    refine ⟨a, root, neg, next, r, rfl, rfl, rfl, rfl, ha, hroot, hrootQ,
      hrootupper, hneg, hneglt, hnext, hnextpos, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact physicalThreeCycle_apply_root root neg next hrn hrx hnx
    · exact physicalThreeCycle_apply_negative root neg next hrn hrx hnx
    · exact physicalThreeCycle_apply_seed root neg next hrn hrx hnx
    · apply Equiv.ext
      intro x
      apply congrArg (physicalThreeCycle root neg next hrn hrx hnx).symm
      by_cases hxroot : x = root
      · subst x
        simp [physicalThreeCycle, cycleBackward, cycleForward, hrn, hrx, hnx]
      · by_cases hxneg : x = neg
        · subst x
          simp [physicalThreeCycle, cycleBackward, cycleForward, hrn, hrx, hnx]
        · by_cases hxnext : x = next
          · subst x
            simp [physicalThreeCycle, cycleBackward, cycleForward, hrn, hrx, hnx]
          · simp [physicalThreeCycle, cycleBackward, cycleForward, hxroot, hxneg, hxnext]
    · dsimp
      rw [hneg, hroot]
      have hN := (source_geometry hk).2.2.2
      have hn : 2 * (actualSource k t root) - modulus k < 0 := by omega
      simp [if_pos hn, if_neg (by omega : ¬ actualSource k t root < 0)]
      omega
    · dsimp
      rw [hnext, hneg]
      have hN := (source_geometry hk).2.2.2
      have hn : actualSource k t neg < 0 := hneglt
      have hp : 0 < actualSource k t next := hnextpos
      simp [if_pos hn, if_neg (by omega : ¬ actualSource k t root < 0)]
      omega
  · omega

end D5.S3.Combinatorics.Circle.AdjacentDepthThreeCycle

#print axioms D5.S3.Combinatorics.Circle.AdjacentDepthThreeCycle.native_long_seed_three_cycle
