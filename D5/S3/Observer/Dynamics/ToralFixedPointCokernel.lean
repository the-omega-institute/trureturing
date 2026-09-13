/- GID: D5/S3/Observer/Dynamics/ToralFixedPointCokernel
   generality: G
   mirror-B: D5/B/S3/Observer/Dynamics/ToralFixedPointCokernel
   mirror-E: none(waiver:actual-real-torus-and-lattice-quotients)
   anchors: []
   utility: none
   digest: The actual continuous integer action on the real torus has periodic-point groups isomorphic to the existing return cokernels. -/

import D5.S3.Observer.Dynamics.ToralReturnModuleStructure
import Mathlib.Topology.Algebra.Group.Quotient

/-!
The state space is the actual quotient R^2 / image(Z^2), with its quotient
topology. Integer matrices induce continuous linear maps of this torus.
Their iterates, not a separately named periodic model, define the periodic
group. An explicit inverse real matrix constructs a surjection from Z^2 to
that group, and its kernel is exactly (A^n-I)Z^2.

The determinant-nonzero condition is proved for the original C_k,D_k family
at every positive time and parameter. Thus the family corollaries do not
assume the missing periodic-point/cokernel identification.

Repository-first search read the three ToralReturn modules, the Solenoid
owners and MinimalSuspensionContinuum. Pinned mathlib db584cd6 supplies
Submodule.mapQ, Quotient.mk_eq_zero, quotKerEquivOfSurjective and the
quotient topology. The construction and the actual-source identification
below are new repository proof scripts for a classical torus fact.

This is an additive/linear group equivalence, not a claim of a constructed
mapping torus, singular homology computation, or three-manifold rigidity.
No new mathematical open problem is claimed solved.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix
open scoped Matrix

namespace D5.S3.Observer.Dynamics.ToralFixedPointCokernel

open D5.S3.Observer.Dynamics.ToralReturnModuleSpectrum
open D5.S3.Observer.Dynamics.ToralReturnModuleStructure
open private companion_return_det_neg
  from D5.S3.Observer.Dynamics.ToralReturnModuleSpectrum

abbrev RealPlane := Fin 2 → ℝ

/-- The original integer lattice included coordinatewise in the real plane. -/
def latticeEmbedding : Lattice →ₗ[ℤ] RealPlane :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun z i => (z i : ℝ)
      map_zero' := by ext i; simp
      map_add' := by intro z w; ext i; simp }

private theorem latticeEmbedding_injective : Function.Injective latticeEmbedding := by
  intro z w h
  funext i
  have hi : (z i : ℝ) = (w i : ℝ) := congrFun h i
  exact_mod_cast hi

/-- The literal embedded integer lattice, not an abstract isomorphic copy. -/
def integerLattice : Submodule ℤ RealPlane := LinearMap.range latticeEmbedding

/-- Real quotient torus. The topology is the quotient topology of the additive group. -/
abbrev Torus := RealPlane ⧸ integerLattice

/-- The real action of the original integer matrix. -/
def realAction (A : BinaryMatrix) : RealPlane →ₗ[ℤ] RealPlane :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun x => (A.map (Int.castRingHom ℝ)).mulVec x
      map_zero' := by simp
      map_add' := by intro x y; exact Matrix.mulVec_add _ _ _ }

private theorem realAction_embedding (A : BinaryMatrix) (z : Lattice) :
    realAction A (latticeEmbedding z) = latticeEmbedding (Matrix.toLin' A z) := by
  funext i
  change (A.map (Int.castRingHom ℝ)).mulVec (fun j => (z j : ℝ)) i =
    ((A.mulVec z i : ℤ) : ℝ)
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem realAction_mul (A B : BinaryMatrix) (x : RealPlane) :
    realAction (A * B) x = realAction A (realAction B x) := by
  funext i
  fin_cases i <;>
    simp [realAction, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem realAction_sub (A B : BinaryMatrix) (x : RealPlane) :
    realAction (A - B) x = realAction A x - realAction B x := by
  funext i
  simp [realAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

private theorem realAction_one (x : RealPlane) : realAction 1 x = x := by
  funext i
  fin_cases i <;> simp [realAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem preserves_integerLattice (A : BinaryMatrix) :
    integerLattice ≤ integerLattice.comap (realAction A) := by
  rintro x ⟨z, rfl⟩
  exact ⟨Matrix.toLin' A z, (realAction_embedding A z).symm⟩

/-- The induced action on the actual real torus. -/
def torusAction (A : BinaryMatrix) : Torus →ₗ[ℤ] Torus :=
  integerLattice.mapQ integerLattice (realAction A) (preserves_integerLattice A)

@[simp] theorem torusAction_mk (A : BinaryMatrix) (x : RealPlane) :
    torusAction A (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (realAction A x) := rfl

/-- The induced action is continuous for the real quotient topology. -/
theorem torusAction_continuous (A : BinaryMatrix) : Continuous (torusAction A) := by
  rw [← (QuotientAddGroup.isQuotientMap_mk integerLattice.toAddSubgroup).continuous_comp_iff]
  change Continuous (fun x : RealPlane => Submodule.Quotient.mk (realAction A x) : RealPlane → Torus)
  apply continuous_quot_mk.comp
  apply continuous_pi
  intro i
  change Continuous (fun x : RealPlane => (A.map (Int.castRingHom ℝ)).mulVec x i)
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  fun_prop

private theorem torusAction_mul_apply (A B : BinaryMatrix) (z : Torus) :
    torusAction (A * B) z = torusAction A (torusAction B z) := by
  obtain ⟨x, rfl⟩ := integerLattice.mkQ_surjective z
  simp only [Submodule.mkQ_apply, torusAction_mk, realAction_mul]

private theorem torusAction_sub_apply (A B : BinaryMatrix) (z : Torus) :
    torusAction (A - B) z = torusAction A z - torusAction B z := by
  obtain ⟨x, rfl⟩ := integerLattice.mkQ_surjective z
  simp only [Submodule.mkQ_apply, torusAction_mk, realAction_sub, Submodule.Quotient.mk_sub]

private theorem torusAction_one_apply (z : Torus) : torusAction 1 z = z := by
  obtain ⟨x, rfl⟩ := integerLattice.mkQ_surjective z
  simp only [Submodule.mkQ_apply, torusAction_mk, realAction_one]

/-- Matrix powers are the actual time iterates on the quotient state space. -/
theorem torusAction_pow_apply (A : BinaryMatrix) (n : ℕ) (z : Torus) :
    torusAction (A ^ n) z = (torusAction A)^[n] z := by
  induction n with
  | zero => simpa using torusAction_one_apply z
  | succ n ih =>
      rw [pow_succ', torusAction_mul_apply, Function.iterate_succ_apply', ih]

/-- A subgroup of the actual torus; the following theorem identifies its points
with precisely the points fixed by the nth time iterate. -/
def PeriodicGroup (A : BinaryMatrix) (n : ℕ) : Submodule ℤ Torus :=
  LinearMap.ker (torusAction (A ^ n - 1))

theorem mem_periodicGroup_iff (A : BinaryMatrix) (n : ℕ) (z : Torus) :
    z ∈ PeriodicGroup A n ↔ (torusAction A)^[n] z = z := by
  change torusAction (A ^ n - 1) z = 0 ↔ _
  rw [torusAction_sub_apply, torusAction_one_apply, torusAction_pow_apply, sub_eq_zero]

/-- Explicit real inverse of a binary matrix, used only with a nonzero determinant. -/
def realInverse (M : BinaryMatrix) : RealPlane →ₗ[ℤ] RealPlane :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun x =>
        ![((M 1 1 : ℝ) * x 0 - (M 0 1 : ℝ) * x 1) / (M.det : ℝ),
          ((M 0 0 : ℝ) * x 1 - (M 1 0 : ℝ) * x 0) / (M.det : ℝ)]
      map_zero' := by ext i; fin_cases i <;> simp
      map_add' := by intro x y; ext i; fin_cases i <;> simp <;> ring }

private theorem inverse_action (M : BinaryMatrix) (hd : M.det ≠ 0) (x : RealPlane) :
    realInverse M (realAction M x) = x := by
  have hd' : (M 0 0 : ℝ) * (M 1 1 : ℝ) - (M 0 1 : ℝ) * (M 1 0 : ℝ) ≠ 0 := by
    rw [Matrix.det_fin_two] at hd
    exact_mod_cast hd
  funext i
  fin_cases i <;>
    simp [realInverse, realAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two] <;>
    field_simp [hd'] <;> ring

private theorem action_inverse (M : BinaryMatrix) (hd : M.det ≠ 0) (x : RealPlane) :
    realAction M (realInverse M x) = x := by
  have hd' : (M 0 0 : ℝ) * (M 1 1 : ℝ) - (M 0 1 : ℝ) * (M 1 0 : ℝ) ≠ 0 := by
    rw [Matrix.det_fin_two] at hd
    exact_mod_cast hd
  funext i
  fin_cases i <;>
    simp [realInverse, realAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two] <;>
    field_simp [hd'] <;> ring

/-- Lift each integer vector by the actual inverse matrix, then pass to its
class in the real torus. Its image lies in the actual kernel of torusAction M. -/
def integerToTorusKernel (M : BinaryMatrix) (hd : M.det ≠ 0) :
    Lattice →ₗ[ℤ] LinearMap.ker (torusAction M) where
  toFun z := ⟨integerLattice.mkQ (realInverse M (latticeEmbedding z)), by
    change torusAction M (Submodule.Quotient.mk (realInverse M (latticeEmbedding z))) = 0
    rw [torusAction_mk, action_inverse M hd]
    exact (Submodule.Quotient.mk_eq_zero integerLattice).mpr ⟨z, rfl⟩⟩
  map_add' z w := by
    apply Subtype.ext
    change integerLattice.mkQ (realInverse M (latticeEmbedding (z + w))) =
      integerLattice.mkQ (realInverse M (latticeEmbedding z)) +
        integerLattice.mkQ (realInverse M (latticeEmbedding w))
    simp only [map_add]
  map_smul' a z := by
    apply Subtype.ext
    change integerLattice.mkQ (realInverse M (latticeEmbedding (a • z))) =
      a • integerLattice.mkQ (realInverse M (latticeEmbedding z))
    simp only [map_smul]

private theorem integerToTorusKernel_surjective (M : BinaryMatrix) (hd : M.det ≠ 0) :
    Function.Surjective (integerToTorusKernel M hd) := by
  intro q
  obtain ⟨x, hx⟩ := integerLattice.mkQ_surjective q.1
  have hm : realAction M x ∈ integerLattice := by
    apply (Submodule.Quotient.mk_eq_zero integerLattice).mp
    change torusAction M (integerLattice.mkQ x) = 0
    rw [hx]
    exact q.2
  obtain ⟨z, hz⟩ := hm
  refine ⟨z, Subtype.ext ?_⟩
  change integerLattice.mkQ (realInverse M (latticeEmbedding z)) = q.1
  rw [hz, inverse_action M hd]
  exact hx

/-- The kernel is proved equal to the image of the original integer matrix. -/
theorem integerToTorusKernel_ker (M : BinaryMatrix) (hd : M.det ≠ 0) :
    LinearMap.ker (integerToTorusKernel M hd) = LinearMap.range (Matrix.toLin' M) := by
  ext z
  constructor
  · intro hz
    change integerToTorusKernel M hd z = 0 at hz
    have hval := congrArg Subtype.val hz
    have hmem : realInverse M (latticeEmbedding z) ∈ integerLattice :=
      (Submodule.Quotient.mk_eq_zero integerLattice).mp hval
    obtain ⟨w, hw⟩ := hmem
    refine ⟨w, latticeEmbedding_injective ?_⟩
    calc
      latticeEmbedding (Matrix.toLin' M w) = realAction M (latticeEmbedding w) :=
        (realAction_embedding M w).symm
      _ = realAction M (realInverse M (latticeEmbedding z)) := by rw [hw]
      _ = latticeEmbedding z := action_inverse M hd _
  · rintro ⟨w, rfl⟩
    apply Subtype.ext
    change integerLattice.mkQ (realInverse M (latticeEmbedding (Matrix.toLin' M w))) = 0
    rw [← realAction_embedding, inverse_action M hd]
    exact (Submodule.Quotient.mk_eq_zero integerLattice).mpr ⟨w, rfl⟩

/-- The genuine return cokernel is isomorphic to the genuine periodic subgroup
of the real quotient torus. -/
def returnModuleEquivPeriodicGroup (A : BinaryMatrix) (n : ℕ)
    (hd : (A ^ n - 1).det ≠ 0) : ReturnModule A n ≃ₗ[ℤ] PeriodicGroup A n := by
  change (Lattice ⧸ LinearMap.range (Matrix.toLin' (A ^ n - 1))) ≃ₗ[ℤ]
    LinearMap.ker (torusAction (A ^ n - 1))
  rw [← integerToTorusKernel_ker (A ^ n - 1) hd]
  exact LinearMap.quotKerEquivOfSurjective _ (integerToTorusKernel_surjective _ hd)

/-- The preceding all-time scalar equality now concerns actual torus points.
All determinant hypotheses are discharged from the original family. -/
theorem equal_actual_periodic_cardinalities (k : ℕ) (hk : 0 < k)
    (n : ℕ) (hn : 0 < n) :
    Nat.card (PeriodicGroup (companion k) n) = Nat.card (PeriodicGroup (balanced k) n) ∧
    0 < Nat.card (PeriodicGroup (companion k) n) := by
  have hc : (companion k ^ n - 1).det ≠ 0 := ne_of_lt (companion_return_det_neg k n hk hn)
  have hd : (balanced k ^ n - 1).det ≠ 0 := by
    rw [← same_return_determinant k n]
    exact hc
  have ec := Nat.card_congr (returnModuleEquivPeriodicGroup (companion k) n hc).toEquiv
  have ed := Nat.card_congr (returnModuleEquivPeriodicGroup (balanced k) n hd).toEquiv
  rw [← ec, ← ed]
  exact equal_cardinality_return_modules k hk n hn

/-- One-step periodic groups on the actual torus remain structurally distinct,
despite agreement of the entire positive-time cardinality sequence. -/
theorem actual_fixed_groups_not_isomorphic (k : ℕ) (hk : 0 < k) :
    ¬ Nonempty (PeriodicGroup (companion k) 1 ≃+ PeriodicGroup (balanced k) 1) := by
  have hc : (companion k ^ 1 - 1).det ≠ 0 :=
    ne_of_lt (companion_return_det_neg k 1 hk (by omega))
  have hd : (balanced k ^ 1 - 1).det ≠ 0 := by
    rw [← same_return_determinant k 1]
    exact hc
  rintro ⟨e⟩
  apply one_step_return_modules_not_isomorphic k hk
  exact ⟨(returnModuleEquivPeriodicGroup (companion k) 1 hc).toAddEquiv.trans
    (e.trans (returnModuleEquivPeriodicGroup (balanced k) 1 hd).symm.toAddEquiv)⟩

#print axioms torusAction_continuous
#print axioms torusAction_pow_apply
#print axioms mem_periodicGroup_iff
#print axioms integerToTorusKernel_ker
#print axioms returnModuleEquivPeriodicGroup
#print axioms equal_actual_periodic_cardinalities
#print axioms actual_fixed_groups_not_isomorphic

end D5.S3.Observer.Dynamics.ToralFixedPointCokernel
