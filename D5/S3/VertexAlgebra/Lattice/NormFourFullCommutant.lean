/- GID: D5/S3/VertexAlgebra/Lattice/NormFourFullCommutant
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/NormFourFullCommutant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Equality of the literal annihilator and full actual cyclic-vacuum commutant. -/

import D5.S3.VertexAlgebra.Lattice.NormFourCommutant
import D5.S3.VertexAlgebra.Lattice.NormFourVacuumIrreducible
import Batteries.Tactic.OpenPrivate

/-! The cyclic space is exactly NormFourVacuumIrreducible.vacuumDescendants.
Its private negative words are reused without altering their definition.
The proof uses the actual all-state iterate of LatticeAllStateReconstruction;
its residue calculus retains the Carnahan / Matsuo--Nagatomo attribution.
The lattice fields retain their Bakalov--Kac attribution, and the norm-four
state its Dong--Mason--Zhu / Shimakura attribution. No independent Ising VOA
carrier identification or new irreducibility assertion is made here. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open private word from D5.S3.VertexAlgebra.Lattice.NormFourVacuumIrreducible

namespace D5.S3.VertexAlgebra.Lattice.NormFourFullCommutant

open LatticeGeneratingFieldLocality LatticeAllStateField
open LatticeAllStateReconstruction NormFourVirasoroVector
open NormFourVacuumIrreducible
open scoped BigOperators VertexOperator

noncomputable section

/-- All actual nonnegative coefficients of all states in the supplied cyclic span. -/
def fullStateCommutant (D : LatticeData) (a : Charge D) (s : ℂ) :
    Submodule ℂ (Carrier D) where
  carrier := {v | ∀ u ∈ vacuumDescendants D a s,
    ∀ j : ℤ, 0 ≤ j → mu D u j v = 0}
  zero_mem' := by intro u hu j hj; exact map_zero _
  add_mem' := by
    intro v w hv hw u hu j hj
    change ((Y D u)[[j]]) (v + w) = 0
    rw [map_add]
    change mu D u j v + mu D u j w = 0
    rw [hv u hu j hj, hw u hu j hj, add_zero]
  smul_mem' := by
    intro c v hv u hu j hj
    change ((Y D u)[[j]]) (c • v) = 0
    rw [map_smul]
    change c • mu D u j v = 0
    rw [hv u hu j hj, smul_zero]

/-- For fixed v, the actual states whose full nonnegative fields annihilate v. -/
private def annihilatingStates (D : LatticeData) (v : Carrier D) :
    Submodule ℂ (Carrier D) where
  carrier := {u | ∀ j : ℤ, 0 ≤ j → mu D u j v = 0}
  zero_mem' := by intro j hj; simp [mu]
  add_mem' := by
    intro u w hu hw j hj
    unfold mu
    rw [map_add, map_add]
    change mu D u j v + mu D w j v = 0
    rw [hu j hj, hw j hj, add_zero]
  smul_mem' := by
    intro c u hu j hj
    unfold mu
    rw [map_smul, map_smul]
    change c • mu D u j v = 0
    rw [hu j hj, smul_zero]

private theorem vacuum_annihilates (D : LatticeData) (v : Carrier D) :
    vacuum D ∈ annihilatingStates D v := by
  intro j hj
  simp [mu, stateField_vacuum, identity_modes, show j ≠ -1 by omega]

/-- Both full finite iterate families vanish termwise, including every tail. -/
private theorem iterate_annihilates (D : LatticeData) (v e b : Carrier D)
    (he : e ∈ annihilatingStates D v) (hb : b ∈ annihilatingStates D v) (r : ℤ) :
    mu D e r b ∈ annihilatingStates D v := by
  intro n hn
  have actual := stateField_iterate D e b v r n
  have first (i : ℕ) :
      (((-1 : ℂ)^i) * ((Ring.choose r i : ℤ) : ℂ)) •
        mu D e (r - i) (mu D b (n + i) v) = 0 := by
    rw [hb (n + i) (by omega)]
    simp only [mu, map_zero, smul_zero]
  have second (i : ℕ) :
      (((-1 : ℂ)^i) * ((Ring.choose r i : ℤ) : ℂ)) •
        mu D b (r + n - i) (mu D e i v) = 0 := by
    rw [he i (by omega)]
    simp only [mu, map_zero, smul_zero]
  have identity := actual.2.2
  change mu D (mu D e r b) n v =
    (∑ᶠ i : ℕ, (((-1 : ℂ)^i) * ((Ring.choose r i : ℤ) : ℂ)) •
      mu D e (r - i) (mu D b (n + i) v)) -
    ((-1 : ℂ)^r) • (∑ᶠ i : ℕ, (((-1 : ℂ)^i) * ((Ring.choose r i : ℤ) : ℂ)) •
      mu D b (r + n - i) (mu D e i v)) at identity
  simpa only [first, second, finsum_zero, smul_zero, sub_zero] using identity

private theorem word_annihilates (D : LatticeData) (a : Charge D) (s : ℂ)
    (v : Carrier D) (hv : v ∈ NormFourCommutant.space D a s) (w : List ℕ) :
    word D a s w ∈ annihilatingStates D v := by
  induction w with
  | nil => exact vacuum_annihilates D v
  | cons k w ih =>
      have step := iterate_annihilates D v (vector D a s) (word D a s w) hv ih (-(k : ℤ))
      simpa only [word, mode, mu, show -((k : ℤ) + 1) + 1 = -(k : ℤ) by omega] using step

private theorem generator_mem (D : LatticeData) (a : Charge D) (s : ℂ) :
    vector D a s ∈ vacuumDescendants D a s := by
  apply Submodule.subset_span
  refine ⟨[1], ?_⟩
  simpa only [word, mode, Nat.cast_one, show -((1 : ℤ) + 1) + 1 = -1 by omega] using
    stateField_creation D (vector D a s)

/-- Equality on the full production carrier, with every integer j at least zero,
for arbitrary lattice data, charge and scalar. No Virasoro or norm hypothesis is needed. -/
theorem space_eq_full_state_commutant (D : LatticeData) (a : Charge D) (s : ℂ) :
    NormFourCommutant.space D a s = fullStateCommutant D a s := by
  apply le_antisymm
  · intro v hv u hu
    have included : vacuumDescendants D a s ≤ annihilatingStates D v := by
      apply Submodule.span_le.mpr
      rintro u ⟨w, rfl⟩
      exact word_annihilates D a s v hv w
    exact included hu
  · intro v hv j hj
    exact hv (vector D a s) (generator_mem D a s) j hj

end
end D5.S3.VertexAlgebra.Lattice.NormFourFullCommutant
