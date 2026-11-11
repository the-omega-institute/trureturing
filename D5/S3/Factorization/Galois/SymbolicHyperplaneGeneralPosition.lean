/- GID: D5/S3/Factorization/Galois/SymbolicHyperplaneGeneralPosition
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/SymbolicHyperplaneGeneralPosition
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: General position of one symbolic normal for constant subspace arrangements. -/

import D5.S3.Factorization.Galois.ActualWindowCommonKernel
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Etale.Kaehler

/-!
The symbolic normal uses the fraction field of the full multivariate polynomial
ring. The arrangement is defined over the coefficient field before adjoining
the variables. In particular, its members cannot depend on the normal.

The intersection argument uses derivations in an arbitrary rational direction:
if that direction annihilates the cut span, differentiation preserves each cut
and hence both extended uncut spans. Dual separation then proves precisely the
intersection clause of Raz--Wigderson, Definition 5.1, including empty families.
-/

noncomputable section

open scoped Classical TensorProduct

namespace D5.S3.Factorization.Galois.SymbolicHyperplaneGeneralPosition

open ActualWindowCommonKernel.HyperplaneRank

variable {F α ι : Type*} [Field F] [Fintype α]

/-- The rational function field with one independent variable per coordinate. -/
abbrev SymbolicField (F α : Type*) [Field F] := FractionRing (MvPolynomial α F)

/-- The actual independent coordinate variables, embedded in the fraction field. -/
def coordinate (j : α) : SymbolicField F α :=
  algebraMap (MvPolynomial α F) (SymbolicField F α) (MvPolynomial.X j)

/-- Coordinatewise scalar inclusion. -/
def constantVector (v : α → F) : α → SymbolicField F α :=
  fun j => algebraMap F (SymbolicField F α) (v j)

/-- Scalar extension of an F-subspace, as an actual span in the new ambient space. -/
def extend (V : Submodule F (α → F)) : Submodule (SymbolicField F α) (α → SymbolicField F α) :=
  Submodule.span _ (constantVector '' (V : Set (α → F)))

/-- One common normal, with all coordinates independently indeterminate. -/
def symbolicNormal : (α → SymbolicField F α) →ₗ[SymbolicField F α] SymbolicField F α where
  toFun v := ∑ j, coordinate j * v j
  map_add' v w := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.mul_sum, mul_left_comm, mul_assoc]

private def direction (y : α → SymbolicField F α) :
    Derivation F (SymbolicField F α) (SymbolicField F α) := by
  let P := MvPolynomial α F
  let K := SymbolicField F α
  letI : Algebra.FormallyEtale P K :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors P)
  let d := MvPolynomial.mkDerivation F y
  exact ((d.liftKaehlerDifferential.liftBaseChange K).comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale F P K).symm.toLinearMap).compDer
      (KaehlerDifferential.D F K)

private theorem direction_coordinate (y : α → SymbolicField F α) (j : α) :
    direction y (coordinate j) = y j := by
  dsimp [direction, coordinate, LinearMap.compDer]
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]
  simp

private def differentiate (d : Derivation F (SymbolicField F α) (SymbolicField F α))
    (v : α → SymbolicField F α) : α → SymbolicField F α := fun j => d (v j)

private theorem differentiate_add (d : Derivation F (SymbolicField F α) (SymbolicField F α))
    (v w : α → SymbolicField F α) : differentiate d (v + w) = differentiate d v + differentiate d w := by
  ext j
  exact map_add d _ _

private theorem differentiate_smul (d : Derivation F (SymbolicField F α) (SymbolicField F α))
    (c : SymbolicField F α) (v : α → SymbolicField F α) :
    differentiate d (c • v) = d c • v + c • differentiate d v := by
  ext j
  simpa [differentiate, smul_eq_mul, add_comm] using d.leibniz c (v j)

private theorem differentiate_extend (d : Derivation F (SymbolicField F α) (SymbolicField F α))
    (V : Submodule F (α → F)) {v : α → SymbolicField F α} (hv : v ∈ extend V) :
    differentiate d v ∈ extend V := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨a, ha, rfl⟩ := hv
      have hz : differentiate d (constantVector a) = 0 := by
        ext j
        exact d.map_algebraMap _
      rw [hz]
      exact (extend V).zero_mem
  | zero => simpa [differentiate] using (extend V).zero_mem
  | add v w hv hw ihv ihw =>
      rw [differentiate_add]
      exact (extend V).add_mem ihv ihw
  | smul c v hv ih =>
      rw [differentiate_smul]
      exact (extend V).add_mem ((extend V).smul_mem _ hv) ((extend V).smul_mem _ ih)

private theorem differentiate_normal (ψ : (α → SymbolicField F α) →ₗ[SymbolicField F α]
    SymbolicField F α) (v : α → SymbolicField F α) :
    direction (fun j => ψ (Pi.single j 1)) (symbolicNormal v) =
      symbolicNormal (differentiate (direction (fun j => ψ (Pi.single j 1))) v) + ψ v := by
  classical
  simp only [symbolicNormal, LinearMap.coe_mk, AddHom.coe_mk, map_sum,
    Derivation.leibniz, smul_eq_mul, direction_coordinate, Finset.sum_add_distrib]
  congr 1
  conv_rhs => rw [← Finset.univ_sum_single v, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [show Pi.single j (v j) = v j • Pi.single j (1 : SymbolicField F α) by
    ext k; simp [Pi.single_apply]]
  simp

private theorem normal_constant_ne_zero {v : α → F} (hv : v ≠ 0) :
    symbolicNormal (constantVector v) ≠ 0 := by
  classical
  intro hz
  apply hv
  ext j
  have h := congrArg (direction (Pi.single j (1 : SymbolicField F α))) hz
  simp only [symbolicNormal, LinearMap.coe_mk, AddHom.coe_mk, map_sum,
    Derivation.leibniz, direction_coordinate, constantVector, Derivation.map_algebraMap,
    smul_eq_mul, mul_zero, zero_add, map_zero, Pi.single_apply, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, one_mul] at h
  exact (algebraMap F (SymbolicField F α)).injective (by simpa using h)

private theorem stable_sup {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (D : E → E) (hadd : ∀ x y, D (x + y) = D x + D y)
    {U W : Submodule K E} (hU : ∀ x ∈ U, D x ∈ U) (hW : ∀ x ∈ W, D x ∈ W) :
    ∀ x ∈ U ⊔ W, D x ∈ U ⊔ W := by
  intro x hx
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
  rw [hadd]
  exact (U ⊔ W).add_mem (le_sup_left (hU u hu)) (le_sup_right (hW w hw))

private theorem stable_finset_sup {K E η : Type*} [Field K] [AddCommGroup E] [Module K E]
    (D : E → E) (hzero : D 0 = 0) (hadd : ∀ x y, D (x + y) = D x + D y)
    (V : η → Submodule K E) (A : Finset η) (hV : ∀ i ∈ A, ∀ x ∈ V i, D x ∈ V i) :
    ∀ x ∈ A.sup V, D x ∈ A.sup V := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using hzero
  | @insert i A hi ih =>
      rw [Finset.sup_insert]
      exact stable_sup D hadd (hV i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hV j (Finset.mem_insert_of_mem hj)))

/-- The exact two-clause general-position predicate for the scalar extensions
of nonzero constant subspaces. A, B and C may be empty, overlap, and contain
indices representing equal subspaces. No genericity antecedent is assumed. -/
theorem symbolic_general_position [CharZero F] (V : ι → Submodule F (α → F))
    (s : Finset ι) (hV : ∀ i ∈ s, V i ≠ ⊥) :
    InGeneralPosition (fun i => extend (V i)) symbolicNormal s := by
  classical
  constructor
  · intro i hi hker
    obtain ⟨v, hv, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hV i hi)
    exact normal_constant_ne_zero hne (LinearMap.mem_ker.mp
      (hker (Submodule.subset_span ⟨v, hv, rfl⟩)))
  · intro A hA B hB C hC hker
    let T := cutSpan (fun i => extend (V i)) symbolicNormal A
    let I := (T ⊔ familySpan (fun i => extend (V i)) B) ⊓
      (T ⊔ familySpan (fun i => extend (V i)) C)
    apply le_antisymm _ (le_inf le_sup_left le_sup_left)
    intro w hw
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff T w).mp
    intro ψ hψ
    have hψT : ∀ v ∈ T, ψ v = 0 := (Submodule.mem_dualAnnihilator ψ).mp hψ
    let d := direction (fun j => ψ (Pi.single j 1))
    have hstableT : ∀ v ∈ T, differentiate d v ∈ T := by
      apply stable_finset_sup (differentiate d) (by ext j; exact map_zero d)
        (differentiate_add d)
      intro i hi v hv
      refine ⟨differentiate_extend d (V i) hv.1, LinearMap.mem_ker.mpr ?_⟩
      have hψv : ψ v = 0 := hψT v (Finset.le_sup (f := fun i =>
        extend (V i) ⊓ LinearMap.ker symbolicNormal) hi hv)
      have hd := differentiate_normal ψ v
      rw [LinearMap.mem_ker.mp hv.2, map_zero, hψv, add_zero] at hd
      exact hd.symm
    have hstable (S : Finset ι) : ∀ v ∈ familySpan (fun i => extend (V i)) S,
        differentiate d v ∈ familySpan (fun i => extend (V i)) S :=
      stable_finset_sup (differentiate d) (by ext j; exact map_zero d)
        (differentiate_add d) _ S (fun i _ v hv => differentiate_extend d (V i) hv)
    have hdw : differentiate d w ∈ I :=
      ⟨stable_sup _ (differentiate_add d) hstableT (hstable B) w hw.1,
        stable_sup _ (differentiate_add d) hstableT (hstable C) w hw.2⟩
    have hd := differentiate_normal ψ w
    rw [LinearMap.mem_ker.mp (hker hw), map_zero,
      LinearMap.mem_ker.mp (hker hdw), zero_add] at hd
    exact hd.symm

#print axioms symbolic_general_position

end D5.S3.Factorization.Galois.SymbolicHyperplaneGeneralPosition
