/- GID: D5/S3/VertexAlgebra/Lattice/NormFourTensorVertexAlgebra
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/NormFourTensorVertexAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual range and literal tensor vertex algebras with the full coefficient embedding. -/

import D5.S3.VertexAlgebra.Lattice.NormFourTensorCommutantModes
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
The literal range of NormFourTensorEmbedding.tensorMap is closed under the
actual vacuum, every integer field coefficient and actual translation. The
range proof uses both complete finite-support families of the residue iterate,
NormFourTensorEmbedding.actual_tensor_embedding and
NormFourTensorCommutantModes.actual_commutant_mode_intertwining.
The coefficient inheritance adapts the literal subtype constructions in
NormFourVacuumVertexAlgebra and NormFourCommutant. LinearEquiv.ofInjective
transports the resulting LatticeActualVertexAlgebra.StateFieldVertexAlgebra
onto the literal tensor product, preserving all states and all integer modes.

The norm-four construction retains the Dong--Mason--Zhu and Shimakura
attribution. Actual lattice fields retain Bakalov--Kac attribution; residue,
normal-product and Jacobi constructions retain the Scott Carnahan and
Matsuo--Nagatomo attribution and imported Apache 2.0 notices.
Only an ungraded vertex algebra on the literal tensor product is constructed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.NormFourTensorVertexAlgebra

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticeSugawaraConformal LatticeActualStateFieldCalculus
open NormFourVacuumIrreducible NormFourTensorEmbedding
open NormFourTensorCommutantModes
open LatticeActualVertexAlgebra (StateFieldVertexAlgebra)
open scoped BigOperators VertexOperator TensorProduct

open private finite_sum_mem
  from D5.S3.VertexAlgebra.Lattice.NormFourVacuumVertexAlgebra

noncomputable section

-- One coefficient-level inheritance proof, consumed below for the actual
-- range inclusion and for its actual linear-equivalence pullback. The Hahn
-- operators are constructed separately; no vertex-algebra laws are assumed
-- on the source, and all three Borcherds supports are transported explicitly.
private def inheritCoefficients {V W : Type}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (A : StateFieldVertexAlgebra W) (f : V →ₗ[ℂ] W) (hf : Function.Injective f)
    (fields : V →ₗ[ℂ] VertexOperator ℂ V) (vac : V) (T : Module.End ℂ V)
    (hc : ∀ (u v : V) (n : ℤ),
      f (((fields u)[[n]]) v) = ((A.stateField (f u))[[n]]) (f v))
    (hv : f vac = A.vacuum)
    (ht : ∀ v : V, f (T v) = A.translation (f v)) : StateFieldVertexAlgebra V := by
  classical
  have finite_lift {ι : Type} (g : ι → V)
      (hg : Function.HasFiniteSupport (fun i => f (g i))) :
      Function.HasFiniteSupport g := by
    apply hg.subset
    intro i hi hz
    exact hi (hf (hz.trans (map_zero f).symm))
  have sum_map {ι : Type} (g : ι → V) :
      f (∑ᶠ i, g i) = ∑ᶠ i, f (g i) :=
    f.toAddMonoidHom.map_finsum_of_injective hf g
  have delta_map
      (P : ℤ → ℤ → Module.End ℂ V) (Q : ℤ → ℤ → Module.End ℂ W)
      (hPQ : ∀ p q (v : V), f (P p q v) = Q p q (f v))
      (N : ℕ) (p q : ℤ) (v : V) :
      f ((FieldNormalProductLocality.delta^[N] P) p q v) =
        (FieldNormalProductLocality.delta^[N] Q) p q (f v) := by
    induction N generalizing p q with
    | zero => exact hPQ p q v
    | succ N ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        change f ((FieldNormalProductLocality.delta^[N] P) (p+1) q v -
            (FieldNormalProductLocality.delta^[N] P) p (q+1) v) =
          (FieldNormalProductLocality.delta^[N] Q) (p+1) q (f v) -
            (FieldNormalProductLocality.delta^[N] Q) p (q+1) (f v)
        rw [map_sub, ih (p+1) q, ih p (q+1)]
  exact
    { stateField := fields
      vacuum := vac
      translation := T
      vacuum_field := by
        apply HVertexOperator.coeff_inj
        funext j
        apply LinearMap.ext
        intro v
        apply hf
        rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff,
          hc, hv, A.vacuum_field]
        simp only [FieldNormalProduct.identityField, VertexOperator.ncoeff_of_coeff]
        split_ifs <;> simp only [LinearMap.id_apply, LinearMap.zero_apply, map_zero]
      creation := by
        intro u
        apply hf
        rw [hc, hv, A.creation]
      creativity := by
        intro u n hn
        apply hf
        rw [hc, hv, A.creativity (f u) n hn, map_zero]
      translation_vacuum := by
        apply hf
        rw [ht, hv, A.translation_vacuum, map_zero]
      covariance := by
        intro u n
        apply LinearMap.ext
        intro v
        apply hf
        have h := LinearMap.congr_fun (A.covariance (f u) n) (f v)
        simpa only [LinearMap.sub_apply, Module.End.mul_apply,
          LinearMap.smul_apply, map_sub, map_smul, ht, hc] using h
      locality := by
        intro u v
        obtain ⟨N, hN⟩ := A.locality (f u) (f v)
        refine ⟨N, ?_⟩
        funext p q
        apply LinearMap.ext
        intro w
        apply hf
        have h := delta_map
          (FieldNormalProductLocality.commutator (fields u) (fields v))
          (FieldNormalProductLocality.commutator (A.stateField (f u))
            (A.stateField (f v)))
          (by
            intro i j x
            simp only [FieldNormalProductLocality.commutator, LinearMap.sub_apply,
              Module.End.mul_apply, map_sub, hc]) N p q w
        rw [hN] at h
        simpa only [Pi.zero_apply, LinearMap.zero_apply, map_zero] using h
      borcherds := by
        intro u v w p q r
        dsimp only
        have h := A.borcherds (f u) (f v) (f w) p q r
        dsimp only at h
        refine ⟨finite_lift _ ?_, finite_lift _ ?_, finite_lift _ ?_, ?_⟩
        · simpa only [map_smul, hc] using h.1
        · simpa only [map_smul, hc] using h.2.1
        · simpa only [map_smul, hc] using h.2.2.1
        · apply hf
          simpa only [sum_map, map_smul, map_sub, hc] using h.2.2.2 }

section ActualRange

variable (D : LatticeData) (a : Charge D)
variable (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)

local notation "S" => vacuumDescendants D a s
local notation "C" => NormFourCommutant.space D a s
local notation "TensorState" => S ⊗[ℂ] C
local notation "F" => tensorMap D a s
local notation "R" => LinearMap.range F

-- Both suppliers already act on arbitrary right tensor states.
include ha hs in
private theorem s_coefficient_mem (u : S) (n : ℤ) (z : TensorState) :
    mu D u.val n (F z) ∈ R := by
  exact ⟨TensorProduct.map
    (((NormFourVacuumVertexAlgebra.vertexAlgebra D a ha s hs).stateField u)[[n]])
      LinearMap.id z,
    (actual_tensor_embedding D a ha s hs).2.2.1 u n z⟩

private theorem c_coefficient_mem (b : C) (n : ℤ) (z : TensorState) :
    mu D b.val n (F z) ∈ R := by
  exact ⟨TensorProduct.map LinearMap.id
    (((NormFourCommutant.restrictedVertexAlgebra D a s).stateField b)[[n]]) z,
    actual_commutant_mode_intertwining D a s b n z⟩

-- The entire r=-1 iterate is retained. In particular its second family is
-- not discarded: it lies in the range by C-then-S intertwining.
include ha hs in
private theorem pure_field_mem (u : S) (b : C) (n : ℤ) (z : TensorState) :
    mu D (F (u ⊗ₜ[ℂ] b)) n (F z) ∈ R := by
  have it := stateField_iterate D b.val u.val (F z) (-1) n
  dsimp only at it
  change ((Y D (((Y D b.val)[[-1]]) u.val))[[n]]) (F z) ∈ R
  rw [it.2.2]
  apply (R).sub_mem
  · apply finite_sum_mem R _ it.1
    intro i
    apply (R).smul_mem
    change mu D b.val (-1-i) (mu D u.val (n+i) (F z)) ∈ R
    obtain ⟨z', hz'⟩ := s_coefficient_mem D a ha s hs u (n+i) z
    rw [← hz']
    exact c_coefficient_mem D a s b (-1-i) z'
  · apply (R).smul_mem
    apply finite_sum_mem R _ it.2.1
    intro i
    apply (R).smul_mem
    change mu D u.val (-1+n-i) (mu D b.val i (F z)) ∈ R
    obtain ⟨z', hz'⟩ := c_coefficient_mem D a s b i z
    rw [← hz']
    exact s_coefficient_mem D a ha s hs u (-1+n-i) z'

-- Induction only on the LEFT tensor: the right state remains arbitrary.
include ha hs in
private theorem tensor_field_mem (x z : TensorState) (n : ℤ) :
    mu D (F x) n (F z) ∈ R := by
  induction x using TensorProduct.inductionOn with
  | tmul u b => exact pure_field_mem D a ha s hs u b n z
  | add x y hx hy =>
      simpa only [mu, map_add, LinearMap.add_apply, Pi.add_apply] using (R).add_mem hx hy

include ha hs in
private theorem range_field_closed (u v : Carrier D) (hu : u ∈ R) (hv : v ∈ R)
    (n : ℤ) : mu D u n v ∈ R := by
  obtain ⟨x, rfl⟩ := hu
  obtain ⟨z, rfl⟩ := hv
  exact tensor_field_mem D a ha s hs x z n

private theorem tensor_vacuum_image :
    F ((NormFourVacuumVertexAlgebra.vertexAlgebra D a ha s hs).vacuum ⊗ₜ[ℂ]
      (NormFourCommutant.restrictedVertexAlgebra D a s).vacuum) = vacuum D :=
  (actual_tensor_embedding D a ha s hs).2.2.2
    (NormFourCommutant.restrictedVertexAlgebra D a s).vacuum

include ha hs in
private theorem range_vacuum_mem : vacuum D ∈ R :=
  ⟨(NormFourVacuumVertexAlgebra.vertexAlgebra D a ha s hs).vacuum ⊗ₜ[ℂ]
      (NormFourCommutant.restrictedVertexAlgebra D a s).vacuum,
    tensor_vacuum_image D a ha s hs⟩

-- No separate Leibniz statement is needed: T is the actual -2 vacuum mode.
include ha hs in
private theorem range_translation_closed (v : Carrier D) (hv : v ∈ R) :
    translation D v ∈ R := by
  rw [LatticeActualVertexAlgebra.translation_as_mode D v]
  exact range_field_closed D a ha s hs v (vacuum D) hv
    (range_vacuum_mem D a ha s hs) (-2)

private def rangeVacuum : R := ⟨vacuum D, range_vacuum_mem D a ha s hs⟩

private def rangeRawCoefficient (u : R) (j : ℤ) : Module.End ℂ R :=
  (HVertexOperator.coeff (Y D u.val) j).restrict (by
    intro v hv
    simpa only [VertexOperator.coeff_eq_ncoeff, mu] using
      range_field_closed D a ha s hs u.val v u.property hv (-j-1))

private theorem range_raw_support (u v : R) :
    (Function.support (fun j => rangeRawCoefficient D a ha s hs u j v)).IsPWO := by
  refine Set.IsPWO.mono
    (HVertexOperator.isPWO_support_coeff (Y D u.val) v.val) ?_
  intro j hj
  change rangeRawCoefficient D a ha s hs u j v ≠ 0 at hj
  change HVertexOperator.coeff (Y D u.val) j v.val ≠ 0
  intro hz
  exact hj (Subtype.ext hz)

private def rangeFieldFor (u : R) : VertexOperator ℂ R :=
  HVertexOperator.of_coeff (rangeRawCoefficient D a ha s hs u)
    (range_raw_support D a ha s hs u)

private def rangeY : R →ₗ[ℂ] VertexOperator ℂ R where
  toFun := rangeFieldFor D a ha s hs
  map_add' u v := by
    apply HVertexOperator.coeff_inj
    funext j
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change HVertexOperator.coeff (Y D (u.val + v.val)) j x.val =
      HVertexOperator.coeff (Y D u.val) j x.val +
        HVertexOperator.coeff (Y D v.val) j x.val
    simp only [map_add, LinearMap.add_apply, Pi.add_apply]
  map_smul' c u := by
    apply HVertexOperator.coeff_inj
    funext j
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change HVertexOperator.coeff (Y D (c • u.val)) j x.val =
      c • HVertexOperator.coeff (Y D u.val) j x.val
    simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply]

private theorem range_coefficient_val (u v : R) (n : ℤ) :
    (((rangeY D a ha s hs u)[[n]]) v : Carrier D) = mu D u.val n v.val := rfl

private def rangeTranslation : Module.End ℂ R :=
  (translation D).restrict (range_translation_closed D a ha s hs)

/-- Actual state-field vertex algebra on the literal range of the actual F.
Every locality and full p,q,r Borcherds law is inherited through inclusion. -/
def rangeVertexAlgebra : StateFieldVertexAlgebra R :=
  inheritCoefficients (LatticeActualVertexAlgebra.actualVertexAlgebra D)
    (R).subtype Subtype.val_injective (rangeY D a ha s hs)
    (rangeVacuum D a ha s hs) (rangeTranslation D a ha s hs)
    (range_coefficient_val D a ha s hs) rfl (fun _ => rfl)

-- The supplier's injection is the only injectivity fact used here.
private def tensorEquiv : TensorState ≃ₗ[ℂ] R :=
  LinearEquiv.ofInjective F (actual_tensor_embedding D a ha s hs).1

private def tensorRawCoefficient (u : TensorState) (j : ℤ) :
    Module.End ℂ TensorState :=
  (tensorEquiv D a ha s hs).symm.toLinearMap.comp
    ((HVertexOperator.coeff
      ((rangeVertexAlgebra D a ha s hs).stateField (tensorEquiv D a ha s hs u)) j).comp
        (tensorEquiv D a ha s hs).toLinearMap)

private theorem tensor_raw_support (u v : TensorState) :
    (Function.support (fun j => tensorRawCoefficient D a ha s hs u j v)).IsPWO := by
  refine Set.IsPWO.mono
    (HVertexOperator.isPWO_support_coeff
      ((rangeVertexAlgebra D a ha s hs).stateField (tensorEquiv D a ha s hs u))
        (tensorEquiv D a ha s hs v)) ?_
  intro j hj
  change tensorRawCoefficient D a ha s hs u j v ≠ 0 at hj
  change HVertexOperator.coeff
    ((rangeVertexAlgebra D a ha s hs).stateField (tensorEquiv D a ha s hs u)) j
      (tensorEquiv D a ha s hs v) ≠ 0
  intro hz
  apply hj
  change (tensorEquiv D a ha s hs).symm
    (HVertexOperator.coeff
      ((rangeVertexAlgebra D a ha s hs).stateField (tensorEquiv D a ha s hs u)) j
        (tensorEquiv D a ha s hs v)) = 0
  rw [hz, map_zero]

private def tensorFieldFor (u : TensorState) : VertexOperator ℂ TensorState :=
  HVertexOperator.of_coeff (tensorRawCoefficient D a ha s hs u)
    (tensor_raw_support D a ha s hs u)

private def tensorY : TensorState →ₗ[ℂ] VertexOperator ℂ TensorState where
  toFun := tensorFieldFor D a ha s hs
  map_add' u v := by
    apply HVertexOperator.coeff_inj
    funext j
    apply LinearMap.ext
    intro z
    change (tensorEquiv D a ha s hs).symm
      (HVertexOperator.coeff
        ((rangeVertexAlgebra D a ha s hs).stateField (tensorEquiv D a ha s hs (u+v))) j
          (tensorEquiv D a ha s hs z)) =
      (tensorEquiv D a ha s hs).symm
        (HVertexOperator.coeff
          ((rangeVertexAlgebra D a ha s hs).stateField (tensorEquiv D a ha s hs u)) j
            (tensorEquiv D a ha s hs z)) +
      (tensorEquiv D a ha s hs).symm
        (HVertexOperator.coeff
          ((rangeVertexAlgebra D a ha s hs).stateField (tensorEquiv D a ha s hs v)) j
            (tensorEquiv D a ha s hs z))
    simp only [map_add, LinearMap.add_apply, Pi.add_apply]
  map_smul' c u := by
    apply HVertexOperator.coeff_inj
    funext j
    apply LinearMap.ext
    intro z
    change (tensorEquiv D a ha s hs).symm
      (HVertexOperator.coeff
        ((rangeVertexAlgebra D a ha s hs).stateField (tensorEquiv D a ha s hs (c • u))) j
          (tensorEquiv D a ha s hs z)) =
      c • (tensorEquiv D a ha s hs).symm
        (HVertexOperator.coeff
          ((rangeVertexAlgebra D a ha s hs).stateField (tensorEquiv D a ha s hs u)) j
            (tensorEquiv D a ha s hs z))
    simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply]

private theorem tensor_coefficient_equiv (u v : TensorState) (n : ℤ) :
    tensorEquiv D a ha s hs (((tensorY D a ha s hs u)[[n]]) v) =
      (((rangeVertexAlgebra D a ha s hs).stateField (tensorEquiv D a ha s hs u))[[n]])
        (tensorEquiv D a ha s hs v) :=
  (tensorEquiv D a ha s hs).apply_symm_apply _

private def tensorTranslation : Module.End ℂ TensorState :=
  (tensorEquiv D a ha s hs).symm.toLinearMap.comp
    ((rangeVertexAlgebra D a ha s hs).translation.comp
      (tensorEquiv D a ha s hs).toLinearMap)

/-- Genuine ungraded vertex algebra on the literal S tensor C, transported
from the actual range by the already-proved injection of the actual F. -/
def tensorVertexAlgebra : StateFieldVertexAlgebra TensorState :=
  inheritCoefficients (rangeVertexAlgebra D a ha s hs)
    (tensorEquiv D a ha s hs).toLinearMap (tensorEquiv D a ha s hs).injective
    (tensorY D a ha s hs)
    ((tensorEquiv D a ha s hs).symm (rangeVertexAlgebra D a ha s hs).vacuum)
    (tensorTranslation D a ha s hs) (tensor_coefficient_equiv D a ha s hs)
    ((tensorEquiv D a ha s hs).apply_symm_apply _)
    (fun _ => (tensorEquiv D a ha s hs).apply_symm_apply _)

private theorem tensor_vacuum_preserved :
    F (tensorVertexAlgebra D a ha s hs).vacuum = vacuum D := by
  have h := (tensorEquiv D a ha s hs).apply_symm_apply
    (rangeVertexAlgebra D a ha s hs).vacuum
  exact congrArg (fun x : R => (x : Carrier D)) h

private theorem tensor_vacuum_eq :
    (tensorVertexAlgebra D a ha s hs).vacuum =
      (NormFourVacuumVertexAlgebra.vertexAlgebra D a ha s hs).vacuum ⊗ₜ[ℂ]
        (NormFourCommutant.restrictedVertexAlgebra D a s).vacuum := by
  apply (actual_tensor_embedding D a ha s hs).1
  exact (tensor_vacuum_preserved D a ha s hs).trans
    (tensor_vacuum_image D a ha s hs).symm

private theorem tensor_coefficient_preserved (u v : TensorState) (n : ℤ) :
    F ((((tensorVertexAlgebra D a ha s hs).stateField u)[[n]]) v) =
      mu D (F u) n (F v) := by
  have h := congrArg (fun x : R => (x : Carrier D))
    (tensor_coefficient_equiv D a ha s hs u v n)
  exact h.trans (range_coefficient_val D a ha s hs
    (tensorEquiv D a ha s hs u) (tensorEquiv D a ha s hs v) n)

private theorem tensor_translation_preserved (v : TensorState) :
    F ((tensorVertexAlgebra D a ha s hs).translation v) = translation D (F v) := by
  have h := (tensorEquiv D a ha s hs).apply_symm_apply
    ((rangeVertexAlgebra D a ha s hs).translation (tensorEquiv D a ha s hs v))
  exact congrArg (fun x : R => (x : Carrier D)) h

/-- Actual range closure and the exact tensor embedding: literal vacuum,
all states/all integer coefficients, and actual translation. Both constructed
StateFieldVertexAlgebra values contain statewise Hahn truncation, locality and
the complete p,q,r Borcherds identity with all three finite-support clauses.
No positivity, rootlessness, finiteness, factorization, extra commutation or
injectivity premise occurs. -/
theorem actual_tensor_vertex_algebra_embedding :
    let V_R := rangeVertexAlgebra D a ha s hs
    let V_T := tensorVertexAlgebra D a ha s hs
    Function.Injective F ∧
    vacuum D ∈ R ∧
    (∀ (u v : Carrier D), u ∈ R → v ∈ R → ∀ n : ℤ, mu D u n v ∈ R) ∧
    (∀ v : Carrier D, v ∈ R → translation D v ∈ R) ∧
    (V_R.vacuum : Carrier D) = vacuum D ∧
    (∀ (u v : R) (n : ℤ), (((V_R.stateField u)[[n]]) v : Carrier D) =
      mu D u.val n v.val) ∧
    (∀ v : R, (V_R.translation v : Carrier D) = translation D v.val) ∧
    V_T.vacuum = (NormFourVacuumVertexAlgebra.vertexAlgebra D a ha s hs).vacuum ⊗ₜ[ℂ]
      (NormFourCommutant.restrictedVertexAlgebra D a s).vacuum ∧
    F V_T.vacuum = vacuum D ∧
    (∀ (u v : TensorState) (n : ℤ), F (((V_T.stateField u)[[n]]) v) =
      mu D (F u) n (F v)) ∧
    (∀ v : TensorState, F (V_T.translation v) = translation D (F v)) := by
  dsimp only
  exact ⟨(actual_tensor_embedding D a ha s hs).1,
    range_vacuum_mem D a ha s hs, range_field_closed D a ha s hs,
    range_translation_closed D a ha s hs, rfl, range_coefficient_val D a ha s hs,
    (fun _ => rfl), tensor_vacuum_eq D a ha s hs,
    tensor_vacuum_preserved D a ha s hs, tensor_coefficient_preserved D a ha s hs,
    tensor_translation_preserved D a ha s hs⟩

end ActualRange
end
end D5.S3.VertexAlgebra.Lattice.NormFourTensorVertexAlgebra
