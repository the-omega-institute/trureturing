/-
SOURCE-ONLY candidate on the PRESENT full matter/ghost State and cohomology.
No elaboration, kernel check, native acceptance or official acceptance is claimed.

The current tensorNumber_Q supplier (LatticeMatterGhostDegree, SHA256
e63dfb0e88e1b5c286b57115fd0aff7e4d75ebb061a73f3c0efc18e601dfc7f0)
is consumed directly in Q_basis_eigen below. Its Q is definitionally the current
LatticeBRST.totalCharge; there is no comparison to a historical charge.
The b-mode degree is consumed from BcGhostCharge.ghost_number_relations.
Ghost number here is signed occupation charge, never an energy or intercept.

The ONLY basis is the supplied LatticeBRSTZeroEnergyReduction.fullBasis.
Its coefficientMap, fullBasis_apply, and energyWeight_basis are reused exactly.
The coefficient diagonalization argument follows that supplier. The quotient
and its boundary descent mechanism are the supplied CohomologyField ones.
HISTORICAL SOURCE-ONLY provenance: earlier Field and ZeroEnergyReduction
drafts were respectively pinned at SHA256
048d060860b115eebc685b77e6d9b4a1426e054bcf800954c7301c4151939ed1 and
353096271e7aea09945d1ad1f8ba47f66703d28b7b3c2906e71433e8fc63bf03.
Authoritative actual dependencies: inputs.json's native_five_supplier_custody_ref.
This consumer remains source-only; no live repair was read.

Supplier attribution is retained: lattice realization follows Bakalov--Kac;
the supplied Sugawara material retains Kalle Kytölä's Apache-2.0 attribution;
the supplied field/quotient material retains Scott Carnahan's attribution;
basis, coefficient and quotient machinery retains Mathlib's Apache-2.0
attribution and original authorship. The supplied zero-energy draft attributes
its energy-weight and boundary-primitive mechanisms to its earlier reassembly
and topological sources; those attributions are preserved, without claiming
independent inspection of those historical sources. No novelty is claimed.

All lattice charges, oscillators and ghost occupations remain. The quotient is
the exact current cycles/range quotient. Delta remains class b0(P0 x).
This establishes a candidate integer decomposition and Delta degree only.
Product degree zero, an integer-graded product, and full integer-graded BV
structure remain subsequent obligations. The parent research goal stays active.
-/

import D5.S3.VertexAlgebra.Lattice.LatticeBRSTZeroEnergyReduction
import D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostDegree
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct Classical

namespace D5.S3.VertexAlgebra.LatticeBRSTGhostNumberGrading

open LatticeGeneratingFieldLocality (LatticeData)
open LatticeSugawaraCurrents (gramComplex)
open LatticeMatterGhostCoupling (State ghostB)
open LatticeMatterGhostDegree (tensorNumber)
open LatticeBRST (totalCharge)
open LatticeBRSTCohomologyField (cycles boundaries Cohomology classOf)
open LatticeBRSTZeroEnergyReduction (FullLabel fullBasis P0 B0 Delta)
open D5.S3.Quantum.Fermionic
open private coefficientMap fullBasis_apply energyWeight_basis from
  D5.S3.VertexAlgebra.Lattice.LatticeBRSTZeroEnergyReduction
open private number_ket from D5.S3.Quantum.Fermionic.BcGhostCharge

noncomputable section

/-- The ghost occupation component of the existing full label determines charge. -/
def labelCharge (D : LatticeData) (label : FullLabel D) : ℤ :=
  BcGhostCharge.charge label.2

/-- Actual integer ghost-number projection on the existing unrestricted State. -/
def Pg (D : LatticeData) (k : ℤ) : Module.End ℂ (State D) :=
  (fullBasis D).constr ℂ (fun label =>
    (if labelCharge D label = k then (1 : ℂ) else 0) • fullBasis D label)

theorem Pg_basis (D : LatticeData) (k : ℤ) (label : FullLabel D) :
    Pg D k (fullBasis D label) =
      (if labelCharge D label = k then (1 : ℂ) else 0) • fullBasis D label :=
  (fullBasis D).constr_basis ℂ (fun input =>
    (if labelCharge D input = k then (1 : ℂ) else 0) • fullBasis D input) label

/-- This is the existing id tensor ghostNumber, with its actual occupation charge. -/
theorem tensorNumber_basis (D : LatticeData) (label : FullLabel D) :
    tensorNumber D (fullBasis D label) =
      (labelCharge D label : ℂ) • fullBasis D label := by
  simp only [fullBasis_apply, tensorNumber, BcGhostChargeTensor.number,
    BcGhostChargeTensor.liftGhost, TensorProduct.map_tmul, LinearMap.id_apply,
    number_ket, TensorProduct.tmul_smul, labelCharge]

/-- The supplied coefficient-map diagonal argument, on the SAME full basis. -/
theorem tensorNumber_coeff (D : LatticeData) (x : State D) (label : FullLabel D) :
    (fullBasis D).repr (tensorNumber D x) label =
      (labelCharge D label : ℂ) * (fullBasis D).repr x label := by
  classical
  have diagonal : (coefficientMap D label).comp (tensorNumber D) =
      (labelCharge D label : ℂ) • coefficientMap D label := by
    apply (fullBasis D).ext
    intro input
    change coefficientMap D label (tensorNumber D (fullBasis D input)) =
      (labelCharge D label : ℂ) • coefficientMap D label (fullBasis D input)
    rw [tensorNumber_basis, map_smul]
    change (labelCharge D input : ℂ) * (fullBasis D).repr (fullBasis D input) label =
      (labelCharge D label : ℂ) * (fullBasis D).repr (fullBasis D input) label
    rw [(fullBasis D).repr_self]
    by_cases equality : input = label
    · subst input; rfl
    · simp only [Finsupp.single_apply, if_neg equality, mul_zero]
  exact LinearMap.congr_fun diagonal x

theorem Pg_coeff (D : LatticeData) (k : ℤ) (x : State D) (label : FullLabel D) :
    (fullBasis D).repr (Pg D k x) label =
      (if labelCharge D label = k then (1 : ℂ) else 0) *
        (fullBasis D).repr x label := by
  classical
  have diagonal : (coefficientMap D label).comp (Pg D k) =
      (if labelCharge D label = k then (1 : ℂ) else 0) • coefficientMap D label := by
    apply (fullBasis D).ext
    intro input
    change coefficientMap D label (Pg D k (fullBasis D input)) =
      (if labelCharge D label = k then (1 : ℂ) else 0) •
        coefficientMap D label (fullBasis D input)
    rw [Pg_basis, map_smul]
    change (if labelCharge D input = k then (1 : ℂ) else 0) *
        (fullBasis D).repr (fullBasis D input) label =
      (if labelCharge D label = k then (1 : ℂ) else 0) *
        (fullBasis D).repr (fullBasis D input) label
    rw [(fullBasis D).repr_self]
    by_cases equality : input = label
    · subst input; rfl
    · simp only [Finsupp.single_apply, if_neg equality, mul_zero]
  exact LinearMap.congr_fun diagonal x

private theorem eigen_coeff_zero (D : LatticeData) (x : State D) (d : ℤ)
    (hx : tensorNumber D x = (d : ℂ) • x) (label : FullLabel D)
    (different : labelCharge D label ≠ d) : (fullBasis D).repr x label = 0 := by
  have coefficients := congrArg (fun y : State D => (fullBasis D).repr y label) hx
  rw [tensorNumber_coeff] at coefficients
  rw [(fullBasis D).repr.map_smul, Finsupp.smul_apply, smul_eq_mul] at coefficients
  have separated : ((labelCharge D label : ℂ) - (d : ℂ)) *
      (fullBasis D).repr x label = 0 := by
    rw [sub_mul, coefficients, sub_self]
  have scalarNonzero : (labelCharge D label : ℂ) - (d : ℂ) ≠ 0 := by
    intro equality
    exact different (Int.cast_injective (sub_eq_zero.mp equality))
  exact (mul_eq_zero.mp separated).resolve_left scalarNonzero

/-- The projector acts spectrally on actual eigenvectors, proved by coefficients. -/
theorem Pg_of_eigen (D : LatticeData) (x : State D) (d k : ℤ)
    (hx : tensorNumber D x = (d : ℂ) • x) :
    Pg D k x = (if d = k then (1 : ℂ) else 0) • x := by
  apply (fullBasis D).repr.injective
  ext label
  rw [Pg_coeff]
  rw [(fullBasis D).repr.map_smul,
    Finsupp.smul_apply, smul_eq_mul]
  by_cases equality : labelCharge D label = d
  · rw [equality]
  · rw [eigen_coeff_zero D x d hx label equality]
    simp only [mul_zero]

theorem tensorNumber_Pg (D : LatticeData) (k : ℤ) (x : State D) :
    tensorNumber D (Pg D k x) = (k : ℂ) • Pg D k x := by
  apply (fullBasis D).repr.injective
  ext label
  rw [tensorNumber_coeff, Pg_coeff]
  rw [(fullBasis D).repr.map_smul,
    Finsupp.smul_apply, smul_eq_mul, Pg_coeff]
  by_cases equality : labelCharge D label = k
  · simp only [equality, if_pos rfl, ite_true, one_mul]
  · simp only [if_neg equality, zero_mul, mul_zero]

theorem Pg_fixed_iff (D : LatticeData) (k : ℤ) (x : State D) :
    Pg D k x = x ↔ tensorNumber D x = (k : ℂ) • x := by
  constructor
  · intro fixed
    calc
      tensorNumber D x = tensorNumber D (Pg D k x) := congrArg (tensorNumber D) fixed.symm
      _ = (k : ℂ) • Pg D k x := tensorNumber_Pg D k x
      _ = (k : ℂ) • x := congrArg (fun y : State D => (k : ℂ) • y) fixed
  · intro eigen
    simpa only [if_pos rfl, ite_true, one_smul] using Pg_of_eigen D x k k eigen

theorem Pg_orthogonal (D : LatticeData) (k l : ℤ) (different : k ≠ l) :
    Pg D k * Pg D l = 0 := by
  apply LinearMap.ext
  intro x
  change Pg D k (Pg D l x) = 0
  rw [Pg_of_eigen D (Pg D l x) l k (tensorNumber_Pg D l x)]
  simp only [if_neg (Ne.symm different), zero_smul]

theorem Pg_idempotent (D : LatticeData) (k : ℤ) : Pg D k * Pg D k = Pg D k := by
  apply LinearMap.ext
  intro x
  change Pg D k (Pg D k x) = Pg D k x
  simpa only [if_pos rfl, ite_true, one_smul] using
    Pg_of_eigen D (Pg D k x) k k (tensorNumber_Pg D k x)

/-- A genuine finite set computed from the existing full-basis coefficients of x. -/
def ghostSupport (D : LatticeData) (x : State D) : Finset ℤ :=
  ((fullBasis D).repr x).support.image (labelCharge D)

theorem Pg_eq_zero_of_not_mem (D : LatticeData) (x : State D) (k : ℤ)
    (outside : k ∉ ghostSupport D x) : Pg D k x = 0 := by
  apply (fullBasis D).repr.injective
  ext label
  rw [Pg_coeff]
  simp only [(fullBasis D).repr.map_zero, Finsupp.zero_apply]
  by_cases equality : labelCharge D label = k
  · have zeroCoefficient : (fullBasis D).repr x label = 0 := by
      by_contra nonzero
      exact outside (Finset.mem_image.mpr
        ⟨label, Finsupp.mem_support_iff.mpr nonzero, equality⟩)
    rw [zeroCoefficient, mul_zero]
  · rw [if_neg equality, zero_mul]

private theorem Pg_support_subset (D : LatticeData) (x : State D) :
    Function.support (fun k : ℤ => Pg D k x) ⊆ (ghostSupport D x : Set ℤ) := by
  intro k nonzero
  by_contra outside
  exact nonzero (Pg_eq_zero_of_not_mem D x k outside)

theorem Pg_finite_support (D : LatticeData) (x : State D) :
    (fun k : ℤ => Pg D k x).HasFiniteSupport :=
  Set.Finite.subset (ghostSupport D x).finite_toSet (Pg_support_subset D x)

/-- Every full state is the finite sum of its actual integer charge projections. -/
theorem Pg_decomposition (D : LatticeData) (x : State D) :
    ∑ k ∈ ghostSupport D x, Pg D k x = x := by
  classical
  apply (fullBasis D).repr.injective
  ext label
  change coefficientMap D label (∑ k ∈ ghostSupport D x, Pg D k x) =
    coefficientMap D label x
  rw [map_sum]
  change (∑ k ∈ ghostSupport D x, (fullBasis D).repr (Pg D k x) label) =
    (fullBasis D).repr x label
  simp_rw [Pg_coeff]
  by_cases zeroCoefficient : (fullBasis D).repr x label = 0
  · simp only [zeroCoefficient, mul_zero, Finset.sum_const_zero]
  · have member : labelCharge D label ∈ ghostSupport D x :=
      Finset.mem_image.mpr ⟨label, Finsupp.mem_support_iff.mpr zeroCoefficient, rfl⟩
    rw [Finset.sum_eq_single (labelCharge D label)]
    · simp only [if_pos rfl, ite_true, one_mul]
    · intro k hk different
      simp only [if_neg (Ne.symm different), zero_mul]
    · intro outside
      exact (outside member).elim

theorem finsum_Pg (D : LatticeData) (x : State D) : ∑ᶠ k : ℤ, Pg D k x = x := by
  classical
  rw [finsum_eq_sum_of_support_subset _ (Pg_support_subset D x)]
  exact Pg_decomposition D x

/- The next proof is the DIRECT use of the existing current NQ theorem.
   No rank or Gram premise is needed, and no commutator is reproved. -/
private theorem Q_basis_eigen (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (label : FullLabel D) :
    tensorNumber D (totalCharge D H (fullBasis D label)) =
      ((labelCharge D label + 1 : ℤ) : ℂ) • totalCharge D H (fullBasis D label) := by
  have relation := LinearMap.congr_fun (LatticeMatterGhostDegree.tensorNumber_Q D H)
    (fullBasis D label)
  change tensorNumber D (totalCharge D H (fullBasis D label)) -
    totalCharge D H (tensorNumber D (fullBasis D label)) =
      totalCharge D H (fullBasis D label) at relation
  rw [tensorNumber_basis, map_smul] at relation
  calc
    _ = totalCharge D H (fullBasis D label) +
        (labelCharge D label : ℂ) • totalCharge D H (fullBasis D label) :=
      sub_eq_iff_eq_add.mp relation
    _ = _ := by
      simp only [Int.cast_add, Int.cast_one, add_smul, one_smul]
      exact add_comm _ _

/-- Exact charge shift for the CURRENT total Q, on every State and arbitrary D,H. -/
theorem Pg_Q (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (k : ℤ) :
    Pg D k * totalCharge D H = totalCharge D H * Pg D (k - 1) := by
  apply (fullBasis D).ext
  intro label
  change Pg D k (totalCharge D H (fullBasis D label)) =
    totalCharge D H (Pg D (k - 1) (fullBasis D label))
  rw [Pg_of_eigen D (totalCharge D H (fullBasis D label))
    (labelCharge D label + 1) k (Q_basis_eigen D H label), Pg_basis, map_smul]
  have indices : labelCharge D label + 1 = k ↔ labelCharge D label = k - 1 := by omega
  simp only [indices]

theorem Pg_cycle (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (k : ℤ) (x : State D) (hx : totalCharge D H x = 0) :
    totalCharge D H (Pg D k x) = 0 := by
  have equality := LinearMap.congr_fun (Pg_Q D H (k + 1)) x
  have index : k + 1 - 1 = k := by omega
  change Pg D (k + 1) (totalCharge D H x) = totalCharge D H (Pg D (k + 1 - 1) x)
    at equality
  rw [index, hx, map_zero] at equality
  exact equality.symm

/-- In particular a projected boundary has THIS actual primitive. -/
theorem Pg_boundary_primitive (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (k : ℤ) (z : State D) :
    totalCharge D H (Pg D (k - 1) z) = Pg D k (totalCharge D H z) :=
  (LinearMap.congr_fun (Pg_Q D H k) z).symm

def cyclePg (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (k : ℤ) :
    Module.End ℂ (cycles D H) :=
  ((Pg D k).comp (cycles D H).subtype).codRestrict (cycles D H)
    (fun x => Pg_cycle D H k x x.property)

@[simp] theorem cyclePg_val (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (k : ℤ) (x : cycles D H) :
    (cyclePg D H k x : State D) = Pg D k (x : State D) := rfl

private theorem cyclePg_decomposition (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (x : cycles D H) :
    ∑ k ∈ ghostSupport D (x : State D), cyclePg D H k x = x := by
  apply Subtype.ext
  change (cycles D H).subtype
      (∑ k ∈ ghostSupport D (x : State D), cyclePg D H k x) = (x : State D)
  rw [map_sum]
  exact Pg_decomposition D (x : State D)

/-- Descent uses the existing range characterization and Pg(k-1) of the primitive. -/
theorem cyclePg_boundary (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (k : ℤ) (x : cycles D H) (hx : x ∈ boundaries D H h26 hHG hGH) :
    cyclePg D H k x ∈ boundaries D H h26 hHG hGH := by
  obtain ⟨z, equation⟩ :=
    (LatticeBRSTCohomologyField.mem_boundaries D H h26 hHG hGH x).mp hx
  apply (LatticeBRSTCohomologyField.mem_boundaries D H h26 hHG hGH _).mpr
  refine ⟨Pg D (k - 1) z, ?_⟩
  change totalCharge D H (Pg D (k - 1) z) = Pg D k (x : State D)
  rw [Pg_boundary_primitive, equation]

/-- Integer projection on the SAME full cycles/range cohomology quotient. -/
def Pi (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (h26 : D.rank = 26) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (k : ℤ) : Module.End ℂ (Cohomology D H h26 hHG hGH) :=
  (boundaries D H h26 hHG hGH).mapQ (boundaries D H h26 hHG hGH)
    (cyclePg D H k) (cyclePg_boundary D H h26 hHG hGH k)

@[simp] theorem Pi_classOf (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (k : ℤ) (x : cycles D H) :
    Pi D H h26 hHG hGH k (classOf D H h26 hHG hGH x) =
      classOf D H h26 hHG hGH (cyclePg D H k x) := rfl

theorem Pi_idempotent (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (k : ℤ) (u : Cohomology D H h26 hHG hGH) :
    Pi D H h26 hHG hGH k (Pi D H h26 hHG hGH k u) = Pi D H h26 hHG hGH k u := by
  obtain ⟨x, rfl⟩ := LatticeBRSTCohomologyField.classOf_surjective D H h26 hHG hGH u
  simp only [Pi_classOf]
  apply congrArg (classOf D H h26 hHG hGH)
  apply Subtype.ext
  exact LinearMap.congr_fun (Pg_idempotent D k) (x : State D)

theorem Pi_orthogonal (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (k l : ℤ) (different : k ≠ l) (u : Cohomology D H h26 hHG hGH) :
    Pi D H h26 hHG hGH k (Pi D H h26 hHG hGH l u) = 0 := by
  obtain ⟨x, rfl⟩ := LatticeBRSTCohomologyField.classOf_surjective D H h26 hHG hGH u
  simp only [Pi_classOf]
  have vanished : cyclePg D H k (cyclePg D H l x) = 0 := by
    apply Subtype.ext
    exact LinearMap.congr_fun (Pg_orthogonal D k l different) (x : State D)
  rw [vanished, map_zero]

/-- Every full quotient class has a finite decomposition, with genuine support. -/
theorem Pi_decomposition (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (u : Cohomology D H h26 hHG hGH) :
    ∃ s : Finset ℤ, (∀ k : ℤ, k ∉ s → Pi D H h26 hHG hGH k u = 0) ∧
      ∑ k ∈ s, Pi D H h26 hHG hGH k u = u := by
  classical
  obtain ⟨x, rfl⟩ := LatticeBRSTCohomologyField.classOf_surjective D H h26 hHG hGH u
  refine ⟨ghostSupport D (x : State D), ?_, ?_⟩
  · intro k outside
    rw [Pi_classOf]
    have vanished : cyclePg D H k x = 0 := by
      apply Subtype.ext
      exact Pg_eq_zero_of_not_mem D (x : State D) k outside
    rw [vanished, map_zero]
  · simp only [Pi_classOf]
    rw [← map_sum, cyclePg_decomposition]

theorem Pi_finite_support (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (u : Cohomology D H h26 hHG hGH) :
    (fun k : ℤ => Pi D H h26 hHG hGH k u).HasFiniteSupport := by
  obtain ⟨s, outside, _⟩ := Pi_decomposition D H h26 hHG hGH u
  apply Set.Finite.subset s.finite_toSet
  intro k nonzero
  by_contra hk
  exact nonzero (outside k hk)

/-- A fixed CLASS has a genuine N-homogeneous CYCLE lift, even for a mixed lift. -/
theorem homogeneous_cycle_lift (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (k : ℤ) (u : Cohomology D H h26 hHG hGH)
    (fixed : Pi D H h26 hHG hGH k u = u) :
    ∃ x : cycles D H, classOf D H h26 hHG hGH x = u ∧
      tensorNumber D (x : State D) = (k : ℂ) • (x : State D) := by
  obtain ⟨x, hx⟩ := LatticeBRSTCohomologyField.classOf_surjective D H h26 hHG hGH u
  refine ⟨cyclePg D H k x, ?_, tensorNumber_Pg D k (x : State D)⟩
  rw [← Pi_classOf, hx, fixed]

/-- Literal diagonal P0 and Pg commute; there is no positivity/Gram/rank premise. -/
theorem P0_Pg (D : LatticeData) (k : ℤ) : P0 D * Pg D k = Pg D k * P0 D := by
  apply (fullBasis D).ext
  intro label
  simp only [Module.End.mul_apply, P0, Pg_basis, energyWeight_basis, map_smul, smul_smul]
  rw [mul_comm]

private theorem tensorNumber_B0 (D : LatticeData) :
    tensorNumber D * B0 D - B0 D * tensorNumber D = -B0 D := by
  apply TensorProduct.ext'
  intro v w
  have relation := LinearMap.congr_fun (BcGhostCharge.ghost_number_relations.2.1 0) w
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.neg_apply] at relation
  simp only [tensorNumber, BcGhostChargeTensor.number, BcGhostChargeTensor.liftGhost,
    B0, ghostB, LinearMap.sub_apply, Module.End.mul_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, LinearMap.neg_apply]
  rw [← TensorProduct.tmul_sub, relation, TensorProduct.tmul_neg]

private theorem B0_basis_eigen (D : LatticeData) (label : FullLabel D) :
    tensorNumber D (B0 D (fullBasis D label)) =
      ((labelCharge D label - 1 : ℤ) : ℂ) • B0 D (fullBasis D label) := by
  have relation := LinearMap.congr_fun (tensorNumber_B0 D) (fullBasis D label)
  change tensorNumber D (B0 D (fullBasis D label)) -
    B0 D (tensorNumber D (fullBasis D label)) = -B0 D (fullBasis D label) at relation
  rw [tensorNumber_basis, map_smul] at relation
  calc
    _ = -B0 D (fullBasis D label) + (labelCharge D label : ℂ) • B0 D (fullBasis D label) :=
      sub_eq_iff_eq_add.mp relation
    _ = _ := by
      simp only [Int.cast_sub, Int.cast_one, sub_smul, one_smul]
      abel

/-- b0 lowers actual charge by one, derived from the current b-mode commutator. -/
theorem B0_Pg (D : LatticeData) (k : ℤ) : B0 D * Pg D k = Pg D (k - 1) * B0 D := by
  apply (fullBasis D).ext
  intro label
  change B0 D (Pg D k (fullBasis D label)) = Pg D (k - 1) (B0 D (fullBasis D label))
  rw [Pg_basis, map_smul, Pg_of_eigen D (B0 D (fullBasis D label))
    (labelCharge D label - 1) (k - 1) (B0_basis_eigen D label)]
  have indices : labelCharge D label - 1 = k - 1 ↔ labelCharge D label = k := by omega
  simp only [indices]

/-- The actual reduced operator identity, BEFORE passing to any quotient. -/
theorem B0_P0_Pg (D : LatticeData) (k : ℤ) (x : State D) :
    B0 D (P0 D (Pg D k x)) = Pg D (k - 1) (B0 D (P0 D x)) := by
  calc
    _ = B0 D (Pg D k (P0 D x)) :=
      congrArg (B0 D) (LinearMap.congr_fun (P0_Pg D k) x)
    _ = _ := LinearMap.congr_fun (B0_Pg D k) (P0 D x)

/-- Delta is the supplied class b0(P0 x), on the identical full quotient.
Every displayed raw representative has the imported or Pg-derived cycle proof. -/
theorem Delta_Pi (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (k : ℤ) (u : Cohomology D H h26 hHG hGH) :
    Delta D H h26 hHG hGH (Pi D H h26 hHG hGH k u) =
      Pi D H h26 hHG hGH (k - 1) (Delta D H h26 hHG hGH u) := by
  obtain ⟨x, rfl⟩ := LatticeBRSTCohomologyField.classOf_surjective D H h26 hHG hGH u
  simp only [Pi_classOf, LatticeBRSTZeroEnergyReduction.Delta_classOf]
  apply congrArg (classOf D H h26 hHG hGH)
  apply Subtype.ext
  exact B0_P0_Pg D k (x : State D)

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 4000000 in
/-- Only the actual fixed submodules needed for the Delta degree endpoint. -/
def grade (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (h26 : D.rank = 26) (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (k : ℤ) : Submodule ℂ (Cohomology D H h26 hHG hGH) := by
  let p : Module.End ℂ (Cohomology D H h26 hHG hGH) := Pi D H h26 hHG hGH k
  let i : Module.End ℂ (Cohomology D H h26 hHG hGH) := LinearMap.id
  exact (p - i).ker

set_option backward.isDefEq.respectTransparency true in
theorem mem_grade (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (k : ℤ) (u : Cohomology D H h26 hHG hGH) :
    u ∈ grade D H h26 hHG hGH k ↔ Pi D H h26 hHG hGH k u = u := by
  change Pi D H h26 hHG hGH k u - u = 0 ↔ Pi D H h26 hHG hGH k u = u
  exact sub_eq_zero (a := Pi D H h26 hHG hGH k u) (b := u)

theorem Delta_lowers_ghost_number (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (k : ℤ) (u : Cohomology D H h26 hHG hGH) (hu : u ∈ grade D H h26 hHG hGH k) :
    Delta D H h26 hHG hGH u ∈ grade D H h26 hHG hGH (k - 1) := by
  apply (mem_grade D H h26 hHG hGH (k - 1) _).mpr
  have fixed := (mem_grade D H h26 hHG hGH k u).mp hu
  rw [← Delta_Pi D H h26 hHG hGH k u, fixed]

end
end D5.S3.VertexAlgebra.LatticeBRSTGhostNumberGrading
