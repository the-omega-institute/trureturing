/- GID: D5/S3/VertexAlgebra/LatticeAllStateLocality
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeAllStateLocality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Derivative, Dong and finite-sum locality give every actual state field and its integer residues. -/

import D5.S3.VertexAlgebra.FieldNormalProductLocality
import D5.S3.VertexAlgebra.LatticeActualChargedLocality
import D5.S3.VertexAlgebra.LatticeActualMixedLocality
import D5.S3.VertexAlgebra.LatticeSugawaraCurrents
import D5.S3.VertexAlgebra.StateFieldResidueReconstruction

/- The released all-sector Heisenberg law gives uniform neutral locality. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeActualCurrentLocality
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open FieldNormalProductLocality
open scoped VertexOperator

/-- Uniform neutral locality on every charge and polynomial, with order two. -/
theorem actual_neutral_neutral_locality (D : LatticeData) (i j : Fin D.rank) :
    delta^[2] (FieldNormalProductLocality.commutator (neutralField D i) (neutralField D j)) = 0 := by
  funext left right
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, delta,
    FieldNormalProductLocality.commutator, LatticeAllStateField.neutral_modes]
  simp_rw [LatticeSugawaraCurrents.neutralMode_heisenberg]
  rw [show left+1+1+right = left+right+2 by omega,
    show left+1+(right+1) = left+right+2 by omega,
    show left+(right+1+1) = left+right+2 by omega]
  by_cases h : left+right+2 = 0
  · simp only [if_pos h, Pi.zero_apply]
    push_cast
    module
  · simp [h]

end D5.S3.VertexAlgebra.LatticeActualCurrentLocality

/- Generic finite field-locality calculus.
Proof text adapted from sealed PolynomialFockStateField at a9f81b99,
sha256 fe5e0d8b243f58e8c73b8e2986a235309b772e361366665840dab14cda3aa9b5.
Only generic linear-map/finite-support arguments are reused; no Fock theorem
or carrier transfer is imported. Dong and derivative proofs are consumed
from the exact compiled FieldNormalProductLocality supplier. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.FiniteFieldLocality
open FieldNormalProduct FieldNormalProductLocality
open scoped VertexOperator
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
def Local (A B : VertexOperator ℂ V) : Prop :=
  ∃ n : ℕ, delta^[n] (FieldNormalProductLocality.commutator A B) = 0
theorem symmetry (first second : VertexOperator ℂ V) (order : ℕ)
    (killed : delta^[order] (FieldNormalProductLocality.commutator first second) = 0) :
    delta^[order] (FieldNormalProductLocality.commutator second first) = 0 := by
  have flipDelta (distribution : ℤ → ℤ → Module.End ℂ V) :
      delta (flipDistribution distribution) = -flipDistribution (delta distribution) := by
    funext left right
    dsimp [delta, flipDistribution]
    abel
  have scaledDelta (scalar : ℂ) (distribution : ℤ → ℤ → Module.End ℂ V) :
      delta (scalar • distribution) = scalar • delta distribution := by
    funext left right
    simp [delta, smul_sub]
  have flipIterate (distribution : ℤ → ℤ → Module.End ℂ V) (degree : ℕ) :
      delta^[degree] (flipDistribution distribution) =
        ((-1 : ℂ) ^ degree) • flipDistribution (delta^[degree] distribution) := by
    induction degree with
    | zero => simp
    | succ degree inductionHypothesis =>
      rw [Function.iterate_succ_apply', inductionHypothesis, scaledDelta, flipDelta]
      rw [← Function.iterate_succ_apply' (f := delta) degree distribution]
      rw [pow_succ]
      funext left right
      simp only [Pi.smul_apply, Pi.neg_apply]
      module
  have reversed : FieldNormalProductLocality.commutator second first = -flipDistribution
    (FieldNormalProductLocality.commutator first second) := by
    funext left right
    dsimp [FieldNormalProductLocality.commutator, flipDistribution]
    abel
  rw [reversed]
  have negDelta (distribution : ℤ → ℤ → Module.End ℂ V) :
      delta^[order] (-distribution) = -delta^[order] distribution := by
    change (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ V))^[order] (-distribution) =
      -(deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ V))^[order] distribution
    rw [← Module.End.pow_apply, ← Module.End.pow_apply, map_neg]
  rw [negDelta, flipIterate, killed, map_zero, smul_zero, neg_zero]
theorem monotone (distribution : ℤ → ℤ → Module.End ℂ V) (small large : ℕ)
    (less : small ≤ large) (killed : delta^[small] distribution = 0) : delta^[large]
      distribution = 0 := by
  have original : (deltaEnd ^ small) distribution = 0 := by
    rw [Module.End.pow_apply]
    exact killed
  have result := Module.End.pow_map_zero_of_le less original
  rw [Module.End.pow_apply] at result
  exact result
theorem localAdd (first second third : VertexOperator ℂ V)
    (firstLocal : Local first third) (secondLocal : Local second third) : Local (first +
      second) third := by
  obtain ⟨firstOrder, firstKilled⟩ := firstLocal
  obtain ⟨secondOrder, secondKilled⟩ := secondLocal
  let order := max firstOrder secondOrder
  have firstBound := monotone (FieldNormalProductLocality.commutator first third) firstOrder
    order (le_max_left _ _) firstKilled
  have secondBound := monotone (FieldNormalProductLocality.commutator second third)
    secondOrder order (le_max_right _ _) secondKilled
  refine ⟨order, ?_⟩
  have split : FieldNormalProductLocality.commutator (first + second) third =
    FieldNormalProductLocality.commutator first third + FieldNormalProductLocality.commutator
    second third := by
    funext left right
    simp only [FieldNormalProductLocality.commutator, map_add, Pi.add_apply]
    noncomm_ring
  rw [split]
  change (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ V))^[order] _ = 0
  rw [← Module.End.pow_apply, map_add]
  simp only [Module.End.pow_apply]
  change delta^[order] (FieldNormalProductLocality.commutator first third) +
    delta^[order] (FieldNormalProductLocality.commutator second third) = 0
  rw [firstBound, secondBound, add_zero]
theorem localSmul (scalar : ℂ) (first second : VertexOperator ℂ V)
    (locality : Local first second) : Local (scalar • first) second := by
  obtain ⟨order, killed⟩ := locality
  refine ⟨order, ?_⟩
  have split : FieldNormalProductLocality.commutator (scalar • first) second = scalar •
    FieldNormalProductLocality.commutator first second := by
    funext left right
    simp only [FieldNormalProductLocality.commutator, map_smul, Pi.smul_apply,
      Algebra.smul_mul_assoc,
      Algebra.mul_smul_comm, ← smul_sub]
  rw [split]
  change (deltaEnd : Module.End ℂ (ℤ → ℤ → Module.End ℂ V))^[order] _ = 0
  rw [← Module.End.pow_apply, map_smul]
  simp only [Module.End.pow_apply]
  change scalar • delta^[order] (FieldNormalProductLocality.commutator first second) = 0
  rw [killed, smul_zero]
theorem localSum {Index : Type} (indices : Finset Index) (fields : Index → VertexOperator ℂ V)
    (operator : VertexOperator ℂ V) (locality : ∀ index ∈ indices, Local (fields index)
      operator) :
    Local (∑ index ∈ indices, fields index) operator := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
    refine ⟨0, ?_⟩
    funext left right
    simp [FieldNormalProductLocality.commutator]
  | @insert index indices absent inductionHypothesis =>
    rw [Finset.sum_insert absent]
    exact localAdd _ _ _ (locality index (Finset.mem_insert_self _ _))
      (inductionHypothesis (fun other member => locality other (Finset.mem_insert_of_mem member)))
theorem localSymm (A B : VertexOperator ℂ V) (h : Local A B) : Local B A := by
  obtain ⟨n,hn⟩ := h
  exact ⟨n,symmetry A B n hn⟩
theorem localDerivative (A B : VertexOperator ℂ V) (n : ℕ) (h : Local A B) :
    Local (dividedDerivative n A) B := by
  obtain ⟨k,hk⟩ := h
  exact ⟨k+n, dividedDerivative_locality A B k n hk⟩
theorem localNormal (A B C : VertexOperator ℂ V)
    (hAC : Local A C) (hBC : Local B C) (hAB : Local A B) :
    Local (normalMinusOne A B).val C := by
  obtain ⟨a,ha⟩ := hAC
  obtain ⟨b,hb⟩ := hBC
  obtain ⟨c,hc⟩ := hAB
  exact ⟨a+b+c, normalMinusOne_locality A B C a b c ha hb hc⟩
end D5.S3.VertexAlgebra.FiniteFieldLocality

/- Actual all-state locality, by derivative/Dong locality and finite input supports.
   Generic finite locality calculus is adapted with provenance from the sealed
   PolynomialFockStateField proof. All generator inputs here are independently
   proved on the actual lattice carrier, without a transfer or locality premise.
   Matsuo--Nagatomo hep-th/9706118v1, Theorem 5.4.1. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeAllStateLocality
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeAllStateField
open LatticeActualChargedLocality LatticeActualMixedLocality LatticeActualCurrentLocality
open FieldNormalProduct FiniteFieldLocality

noncomputable section

theorem derived_charged_local (D : LatticeData) (x : Index D) (α : Charge D) :
    Local (dividedDerivative x.2 (neutralField D x.1)) (actualField D α) :=
  localDerivative _ _ x.2 ⟨1,actual_neutral_charged_locality D x.1 α⟩

theorem derived_pair_local (D : LatticeData) (x y : Index D) :
    Local (dividedDerivative x.2 (neutralField D x.1))
      (dividedDerivative y.2 (neutralField D y.1)) := by
  have h : Local (neutralField D x.1) (neutralField D y.1) :=
    ⟨2,actual_neutral_neutral_locality D x.1 y.1⟩
  exact localSymm _ _ (localDerivative _ _ y.2
    (localSymm _ _ (localDerivative _ _ x.2 h)))

theorem derived_word_local (D : LatticeData) (δ : Charge D) (w : List (Index D))
    (x : Index D) : Local (dividedDerivative x.2 (neutralField D x.1)) (wordField D δ w) := by
  induction w generalizing x with
  | nil => exact derived_charged_local D x δ
  | cons y tail ih =>
    exact localSymm _ _ (localNormal _ _ _ (derived_pair_local D y x)
      (localSymm _ _ (ih x)) (ih y))

theorem charged_word_local (D : LatticeData) (α δ : Charge D) (w : List (Index D)) :
    Local (actualField D α) (wordField D δ w) := by
  induction w with
  | nil => exact ⟨(-bilinear D α δ).toNat,actual_charged_charged_locality D α δ⟩
  | cons x tail ih =>
    exact localSymm _ _ (localNormal _ _ _ (derived_charged_local D x α)
      (localSymm _ _ ih) (derived_word_local D δ tail x))

/-- Every pair of actual nested word fields is uniformly local. -/
theorem word_locality (D : LatticeData) (α β : Charge D)
    (w z : List (Index D)) : Local (wordField D α w) (wordField D β z) := by
  induction w with
  | nil => exact charged_word_local D α β z
  | cons x tail ih =>
    exact localNormal _ _ _ (derived_word_local D β z x) ih
      (derived_word_local D α tail x)

theorem state_word_local (D : LatticeData) (v : Carrier D)
    (δ : Charge D) (w : List (Index D)) : Local (Y D v) (wordField D δ w) := by
  rw [stateField_expansion]
  apply localSum
  intro α hα
  apply localSum
  intro e he
  exact localSmul _ _ _ (word_locality D α δ (occurrences D e) w)

/-- Every two actual states are local, with a vector-independent finite exponent. -/
theorem stateField_locality (D : LatticeData) (v w : Carrier D) :
    ∃ N : ℕ, FieldNormalProductLocality.delta^[N]
      (FieldNormalProductLocality.commutator (Y D v) (Y D w)) = 0 := by
  change Local (Y D v) (Y D w)
  apply localSymm
  rw [stateField_expansion D w]
  apply localSum
  intro δ hδ
  apply localSum
  intro e he
  exact localSmul _ _ _ (localSymm _ _ (state_word_local D v δ (occurrences D e)))

end
end D5.S3.VertexAlgebra.LatticeAllStateLocality

/- Actual all-state residue closure and integer iterate identity.
Uses the unchanged immutable StateFieldResidueReconstruction supplier with
actual Y, actual vacuum, concrete translation, and proved actual locality.
No desired iterate or Jacobi hypothesis is supplied. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeAllStateReconstruction
open LatticeGeneratingFieldLocality LatticeAllStateField LatticeSugawaraConformal
open scoped VertexOperator
noncomputable section
def mu (D : LatticeData) (a : Carrier D) (n : ℤ) (b : Carrier D) : Carrier D := ((Y D a)[[n]]) b
abbrev residueField (D : LatticeData) (r : ℤ) (a b : Carrier D) :=
  StateFieldResidueReconstruction.residueField (Y := Y D) r a b

theorem residue_closure (D : LatticeData) (a b : Carrier D) (r : ℤ) :
    Y D (mu D a r b) = (residueField D r a b).operator :=
  StateFieldResidueReconstruction.residue_closure (Y := Y D) (vacuum D) (translation D)
    (translation_kills_vacuum D) (stateField_creation D) (stateField_creativity D)
    (stateField_covariance D) (LatticeAllStateLocality.stateField_locality D) a b r

theorem stateField_iterate (D : LatticeData) (a b c : Carrier D) (r n : ℤ) :
    let left : ℕ → Carrier D := fun i =>
      (((-1 : ℂ)^i) * ((Ring.choose r i : ℤ) : ℂ)) •
        (((Y D a)[[r-(i : ℤ)]]) (((Y D b)[[n+(i : ℤ)]]) c))
    let right : ℕ → Carrier D := fun i =>
      (((-1 : ℂ)^i) * ((Ring.choose r i : ℤ) : ℂ)) •
        (((Y D b)[[r+n-(i : ℤ)]]) (((Y D a)[[(i : ℤ)]]) c))
    Function.HasFiniteSupport left ∧ Function.HasFiniteSupport right ∧
      (((Y D (((Y D a)[[r]]) b))[[n]]) c) =
        (∑ᶠ i : ℕ, left i) - ((-1 : ℂ)^r) • (∑ᶠ i : ℕ, right i) :=
  StateFieldResidueReconstruction.stateField_iterate_of_creation_translation_locality
    (Y D) (vacuum D) (translation D) (translation_kills_vacuum D)
    (stateField_creation D) (stateField_creativity D) (stateField_covariance D)
    (LatticeAllStateLocality.stateField_locality D) a b c r n
end
end D5.S3.VertexAlgebra.LatticeAllStateReconstruction
