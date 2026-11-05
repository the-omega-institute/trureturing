/- GID: D5/S3/VertexAlgebra/Lattice/NormFourTensorCommutantModes
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/NormFourTensorCommutantModes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All commutant states and integer modes intertwine the actual tensor map. -/

import D5.S3.VertexAlgebra.Lattice.NormFourTensorEmbedding

/-! The tensor map and the full-state commutant equality are reused on their
literal production subspaces. The actual iterate and mode commutator retain
the Carnahan and Matsuo--Nagatomo residue attribution; the lattice fields
retain Bakalov--Kac attribution and the norm-four construction retains
Dong--Mason--Zhu and Shimakura attribution from the imported sources. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.NormFourTensorCommutantModes

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticeActualStateFieldCalculus NormFourVacuumIrreducible NormFourTensorEmbedding
open scoped BigOperators VertexOperator TensorProduct

open private tensorMap_tmul from D5.S3.VertexAlgebra.Lattice.NormFourTensorEmbedding

noncomputable section

private theorem commutant_annihilates (D : LatticeData) (a : Charge D) (s : ℂ)
    (c : NormFourCommutant.space D a s) (u : vacuumDescendants D a s)
    (n : ℤ) (hn : 0 ≤ n) : mu D c.val n u.val = 0 := by
  have hc : c.val ∈ NormFourFullCommutant.fullStateCommutant D a s := by
    rw [← NormFourFullCommutant.space_eq_full_state_commutant]
    exact c.property
  have comm : ((Y D u.val)[[-1]]) * ((Y D c.val)[[n]]) -
      ((Y D c.val)[[n]]) * ((Y D u.val)[[-1]]) = 0 := by
    rw [mode_commutator]
    have vanish (j : ℕ) : commutatorTerm D u.val c.val (-1) n j = 0 := by
      simp [commutatorTerm, hc u.val u.property (j : ℤ) (by omega)]
    simp only [vanish, finsum_zero]
  have h := LinearMap.congr_fun comm (vacuum D)
  change mu D u.val (-1) (mu D c.val n (vacuum D)) -
    mu D c.val n (mu D u.val (-1) (vacuum D)) = 0 at h
  rw [show mu D c.val n (vacuum D) = 0 from stateField_creativity D c.val n hn,
    show mu D u.val (-1) (vacuum D) = u.val from stateField_creation D u.val] at h
  simpa only [mu, map_zero, zero_sub, neg_eq_zero] using h

private theorem product_mode (D : LatticeData) (a : Charge D) (s : ℂ)
    (b c : NormFourCommutant.space D a s) (u : vacuumDescendants D a s) (q : ℤ) :
    mu D (mu D b.val q c.val) (-1) u.val =
      mu D b.val q (mu D c.val (-1) u.val) := by
  have actual := stateField_iterate D b.val c.val u.val q (-1)
  have first (i : ℕ) (hi : i ≠ 0) :
      (((-1 : ℂ)^i) * ((Ring.choose q i : ℤ) : ℂ)) •
        mu D b.val (q - i) (mu D c.val (-1 + i) u.val) = 0 := by
    rw [commutant_annihilates D a s c u (-1 + i) (by omega)]
    simp only [mu, map_zero, smul_zero]
  have second (i : ℕ) :
      (((-1 : ℂ)^i) * ((Ring.choose q i : ℤ) : ℂ)) •
        mu D c.val (q + -1 - i) (mu D b.val i u.val) = 0 := by
    rw [commutant_annihilates D a s b u i (by omega)]
    simp only [mu, map_zero, smul_zero]
  have first_sum := finsum_eq_single (fun i : ℕ =>
      (((-1 : ℂ)^i) * ((Ring.choose q i : ℤ) : ℂ)) •
        mu D b.val (q - i) (mu D c.val (-1 + i) u.val)) 0 first
  have identity := actual.2.2
  change mu D (mu D b.val q c.val) (-1) u.val =
    (∑ᶠ i : ℕ, (((-1 : ℂ)^i) * ((Ring.choose q i : ℤ) : ℂ)) •
      mu D b.val (q - i) (mu D c.val (-1 + i) u.val)) -
    ((-1 : ℂ)^q) • (∑ᶠ i : ℕ,
      (((-1 : ℂ)^i) * ((Ring.choose q i : ℤ) : ℂ)) •
        mu D c.val (q + -1 - i) (mu D b.val i u.val)) at identity
  rw [first_sum] at identity
  simpa only [second, finsum_zero, smul_zero, sub_zero, pow_zero,
    Ring.choose_zero_right, Int.cast_one, mul_one, one_smul, Nat.cast_zero,
    sub_zero, add_zero] using identity

/-- Every integer coefficient of every commutant state intertwines the same
actual tensor map on the entire algebraic tensor product, for arbitrary D,a,s. -/
theorem actual_commutant_mode_intertwining (D : LatticeData) (a : Charge D) (s : ℂ)
    (b : NormFourCommutant.space D a s) (q : ℤ)
    (z : vacuumDescendants D a s ⊗[ℂ] NormFourCommutant.space D a s) :
    tensorMap D a s (TensorProduct.map LinearMap.id
      (((NormFourCommutant.restrictedVertexAlgebra D a s).stateField b)[[q]]) z) =
      mu D b.val q (tensorMap D a s z) := by
  induction z using TensorProduct.inductionOn with
  | tmul u c =>
      rw [TensorProduct.map_tmul, LinearMap.id_apply, tensorMap_tmul, tensorMap_tmul]
      have coefficient := (NormFourCommutant.actual_closure D a s).2.2.2 b c q
      change mu D
        ((((NormFourCommutant.restrictedVertexAlgebra D a s).stateField b)[[q]]) c).val
        (-1) u.val = _
      rw [show ((((NormFourCommutant.restrictedVertexAlgebra D a s).stateField b)[[q]]) c).val =
        mu D b.val q c.val from coefficient]
      exact product_mode D a s b c u q
  | add x y hx hy => simpa only [mu, map_add] using congrArg₂ (· + ·) hx hy

end
end D5.S3.VertexAlgebra.Lattice.NormFourTensorCommutantModes
