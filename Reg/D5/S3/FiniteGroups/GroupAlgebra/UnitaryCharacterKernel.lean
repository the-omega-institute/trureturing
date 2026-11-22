import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.GroupAlgebra.UnitaryCharacterKernel
import Reg.Support.DependentFamily
import Reg.Support.RealScalarLift
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! # Source registrations for unitary representations and character kernels

For semisimplicity the readout is the representation in the conclusion; a representation that
is not semisimple, the unipotent action of the integers on the plane, refutes the varied law.
For the positivity criterion and for positivity under nonnegative weights the readout is the
character kernel as a function of the weights; the empty family and the constant matrix `-1`
refute the varied laws. -/

namespace Reg.D5.S3.FiniteGroups.GroupAlgebra.UnitaryCharacterKernel
open _root_.D5.S3.FiniteGroups.GroupAlgebra.UnitaryCharacterKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.RealScalarLift
open LeanInformationAudit
open scoped ComplexOrder InnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

universe u1 u2 u3
noncomputable section

/-! ## A representation that is not semisimple -/

/-- A representation of a commutative group in which some element acts as `1 + N` with
`N ∘ N = 0` and `N ≠ 0` is not semisimple: the kernel of `N` has no invariant complement. -/
theorem not_isSemisimple {𝕜 G E : Type*} [Field 𝕜] [CommGroup G] [AddCommGroup E] [Module 𝕜 E]
    (ρ : Representation 𝕜 G E) (g₀ : G) (hN : (ρ g₀ - 1) * (ρ g₀ - 1) = 0)
    (hN0 : ρ g₀ - 1 ≠ 0) : ¬ ρ.IsSemisimpleRepresentation := by
  intro hss
  set N := ρ g₀ - 1 with hNdef
  have hcomm : ∀ g, N * ρ g = ρ g * N := by
    intro g
    simp only [N, sub_mul, mul_sub, one_mul, mul_one, ← map_mul, mul_comm g₀ g]
  let σ : Subrepresentation ρ :=
    { toSubmodule := LinearMap.ker N
      apply_mem_toSubmodule := fun g v hv => by
        rw [LinearMap.mem_ker] at hv ⊢
        rw [← Module.End.mul_apply, hcomm, Module.End.mul_apply, hv, map_zero] }
  obtain ⟨τ, hτ⟩ := hss.exists_isCompl σ
  obtain ⟨u, hu⟩ : ∃ u, N u ≠ 0 := by
    by_contra h
    push Not at h
    exact hN0 (LinearMap.ext h)
  have hmem : u ∈ σ.toSubmodule ⊔ τ.toSubmodule := by
    have h2 : (σ ⊔ τ).toSubmodule = ⊤ := by
      rw [codisjoint_iff.1 hτ.codisjoint]
      rfl
    rw [← Subrepresentation.toSubmodule_sup, h2]
    exact Submodule.mem_top
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.1 hmem
  have hNs : N s = 0 := hs
  have hNt : N t ∈ τ.toSubmodule := by
    have : N t = ρ g₀ t - t := by simp [N]
    rw [this]
    exact τ.toSubmodule.sub_mem (τ.apply_mem_toSubmodule g₀ ht) ht
  have hNt' : N t ∈ σ.toSubmodule := by
    show N (N t) = 0
    rw [← Module.End.mul_apply, hN, LinearMap.zero_apply]
  have hbot : N t ∈ (σ ⊓ τ).toSubmodule := by
    rw [Subrepresentation.toSubmodule_inf]
    exact ⟨hNt', hNt⟩
  rw [disjoint_iff.1 hτ.disjoint] at hbot
  have h0 : N t = 0 := hbot
  apply hu
  rw [map_add, hNs, h0, add_zero]

/-- The real numbers as an `RCLike` field in universe `u1`. -/
abbrev K := ULift.{u1} ℝ
/-- The real line in universe `u3`, an inner product space over `K`. -/
abbrev A := ULift.{u3} ℝ
/-- The Euclidean plane `A × A` with the `L²` norm. -/
abbrev Plane := WithLp 2 (A.{u3} × A.{u3})
/-- The additive group of the integers, written multiplicatively, in universe `u2`. -/
abbrev Ints := ULift.{u2} (Multiplicative ℤ)

/-- The real line of universe `u3` is a line over `K`. -/
def lineEquiv : A.{u3} ≃ₗ[K.{u1}] K.{u1} :=
  { lineIsometry.{u1, u3, u1}.toLinearMap with
    invFun := lineIsometry.{u1, u1, u3}
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem plane_finite : FiniteDimensional K.{u1} Plane.{u3} := by
  have : Module.Finite K.{u1} A.{u3} := Module.Finite.equiv lineEquiv.symm
  infer_instance

/-- The coordinates of the plane. -/
def coord : Plane.{u3} ≃ₗ[K.{u1}] A.{u3} × A.{u3} := WithLp.linearEquiv 2 K.{u1} (A.{u3} × A.{u3})

/-- The nilpotent map `(a, b) ↦ (b, 0)`. -/
def nil : Module.End K.{u1} Plane.{u3} :=
  coord.symm.toLinearMap ∘ₗ (LinearMap.inl K.{u1} A.{u3} A.{u3} ∘ₗ
    LinearMap.snd K.{u1} A.{u3} A.{u3}) ∘ₗ coord.toLinearMap

theorem nil_sq : nil.{u1, u3} * nil.{u1, u3} = 0 := by
  ext v
  simp [nil, coord]

theorem nil_ne : nil.{u1, u3} ≠ 0 := by
  intro h
  have := congrArg (fun f : Module.End K.{u1} Plane.{u3} =>
    coord.{u1, u3} (f (coord.{u1, u3}.symm (0, 1)))) h
  simp [nil, coord] at this

/-- The shear `(a, b) ↦ (a + b, b)` as a unit. -/
def shear : (Module.End K.{u1} Plane.{u3})ˣ where
  val := 1 + nil
  inv := 1 - nil
  val_inv := by rw [add_mul, mul_sub, mul_sub, nil_sq]; simp
  inv_val := by rw [sub_mul, mul_add, mul_add, nil_sq]; simp

/-- The integers acting on the plane by powers of the shear. -/
def unipotent : Representation K.{u1} Ints.{u2} Plane.{u3} :=
  (Units.coeHom _).comp ((zpowersHom _ shear.{u1, u3}).comp MulEquiv.ulift.toMonoidHom)

/-- The generator of the integers. -/
abbrev gen : Ints.{u2} := ULift.up (Multiplicative.ofAdd 1)

theorem unipotent_gen : unipotent.{u1, u2, u3} gen = 1 + nil := by
  change ((shear.{u1, u3} ^ (1 : ℤ) : (Module.End K.{u1} Plane.{u3})ˣ) :
    Module.End K.{u1} Plane.{u3}) = _
  rw [zpow_one]
  rfl

theorem unipotent_not_isSemisimple : ¬ unipotent.{u1, u2, u3}.IsSemisimpleRepresentation := by
  refine not_isSemisimple unipotent gen ?_ ?_
  · rw [unipotent_gen, add_sub_cancel_left, nil_sq]
  · rw [unipotent_gen, add_sub_cancel_left]
    exact nil_ne

/-! ## `isSemisimpleRepresentation_of_norm_map`: the representation in the conclusion -/
namespace Semisimple

set_option linter.checkUnivs false in
/-- Scalar field, monoid, space and their dictionaries. -/
abbrev Params := Σ 𝕜 : Type u1, Σ G : Type u2, Σ E : Type u3, Σ _ : RCLike 𝕜, Σ _ : Monoid G,
  Σ _ : NormedAddCommGroup E, InnerProductSpace 𝕜 E

set_option linter.checkUnivs false in
abbrev signature : Signature where
  Params := Params.{u1, u2, u3}
  State p := letI := p.2.2.2.1; letI := p.2.2.2.2.1; letI := p.2.2.2.2.2.1;
    letI := p.2.2.2.2.2.2; Representation p.1 p.2.1 p.2.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := letI := p.2.2.2.1; letI := p.2.2.2.2.1; letI := p.2.2.2.2.2.1;
    letI := p.2.2.2.2.2.2; Representation p.1 p.2.1 p.2.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u1, u2, u3} :=
  realize signature (fun _ _ s => s) (fun e => nomatch e)

/-- A representation on the same space that is not semisimple, when one exists. -/
def rejected : Realization signature.{u1, u2, u3} :=
  realize signature (fun _ p s => letI := p.2.2.2.1; letI := p.2.2.2.2.1; letI := p.2.2.2.2.2.1;
    letI := p.2.2.2.2.2.2
    @Classical.epsilon (Representation p.1 p.2.1 p.2.2.1) ⟨s⟩
      fun σ => ¬ σ.IsSemisimpleRepresentation) (fun e => nomatch e)

set_option linter.checkUnivs false in
/-- The complete original telescope is retained; only the representation in the conclusion
varies. -/
abbrev arena : Arena where
  signature := signature.{u1, u2, u3}
  Law R := ∀ {𝕜 : Type u1} {G : Type u2} {E : Type u3} [i𝕜 : RCLike 𝕜] [iG : Monoid G]
    [iE : NormedAddCommGroup E] [iI : InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (ρ : Representation 𝕜 G E) (_hρ : ∀ g v, ‖ρ g v‖ = ‖v‖),
    (R.readout () ⟨𝕜, G, E, i𝕜, iG, iE, iI⟩ ρ).IsSemisimpleRepresentation

/-- The model: the integers, as a monoid, acting on the Euclidean plane over the real numbers. -/
abbrev testParams : Params.{u1, u2, u3} :=
  ⟨K, Ints, Plane, inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- The trivial representation acts by isometries, but the representation chosen by the rejected
readout on the plane is not semisimple. -/
theorem rejected_law : ¬ arena.{u1, u2, u3}.Law rejected := by
  intro h
  have hh := @h K.{u1} Ints.{u2} Plane.{u3} _ _ _ _ plane_finite
    (Representation.trivial K.{u1} Ints.{u2} Plane.{u3}) (fun _ _ => rfl)
  change (@Classical.epsilon (Representation K.{u1} Ints.{u2} Plane.{u3}) ⟨1⟩
    fun σ => ¬ σ.IsSemisimpleRepresentation).IsSemisimpleRepresentation at hh
  exact Classical.epsilon_spec (p := fun σ : Representation K.{u1} Ints.{u2} Plane.{u3} =>
    ¬ σ.IsSemisimpleRepresentation) ⟨unipotent, unipotent_not_isSemisimple⟩ hh

theorem dependence : ObservationalDependence signature.{u1, u2, u3} actual := by
  intro i
  refine ⟨testParams, unipotent, 1, fun h => nil_ne.{u1, u3} ?_⟩
  have h' : unipotent.{u1, u2, u3} = 1 := h
  have := congrArg (fun r : Representation K.{u1} Ints.{u2} Plane.{u3} => r gen) h'
  simp only [unipotent_gen, MonoidHom.one_apply] at this
  exact add_eq_left.1 this

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @isSemisimpleRepresentation_of_norm_map.{u1, u2, u3}

def source : Registration arena.{u1, u2, u3} sourceStatement.{u1, u2, u3} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@isSemisimpleRepresentation_of_norm_map.{u1, u2, u3}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := dependence

end Semisimple

def isSemisimpleRepresentation_of_norm_map_registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@isSemisimpleRepresentation_of_norm_map.{u1, u2, u3})
      (Realization Semisimple.signature.{u1, u2, u3}) Unit Unit := {
  unitName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.UnitaryCharacterKernel.isSemisimpleRepresentation_of_norm_map_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.UnitaryCharacterKernel.Semisimple.source
  realizationSource := none
  generated := false
  arena := .source ⟨Semisimple.arena⟩
  objectArena := .source ⟨Semisimple.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Semisimple.arena ⟨Semisimple.source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Semisimple.signature (fun _ _ s => s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.UnitaryCharacterKernel
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

/-! ## `posSemidef_sum_character_kernel_iff`: the kernel as a function of the weights -/
namespace Kernel

set_option linter.checkUnivs false in
/-- Group, index type, spaces, their dictionaries and the representations. -/
abbrev Params := Σ G : Type u1, Σ _ : Group G, Σ ι : Type u2, Σ _ : Fintype ι,
  Σ W : ι → Type u3, Σ _ : (∀ i, NormedAddCommGroup (W i)),
  Σ _ : (∀ i, InnerProductSpace ℂ (W i)), ∀ i, Representation ℂ G (W i)

set_option linter.checkUnivs false in
abbrev signature : Signature where
  Params := Params.{u1, u2, u3}
  State p := p.2.2.1 → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix p.1 p.1 ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- The character kernel `(x, y) ↦ ∑ i, c i * χ_i (x * y⁻¹)` of the weights `c`. -/
def observe (p : Params.{u1, u2, u3}) (c : p.2.2.1 → ℂ) : Matrix p.1 p.1 ℂ := by
  obtain ⟨G, gG, ι, fι, W, nW, iW, ρ⟩ := p
  exact Matrix.of fun x y : G => ∑ i, c i * (ρ i).character (x * y⁻¹)

def actual : Realization signature.{u1, u2, u3} :=
  realize signature (fun _ => observe) (fun e => nomatch e)

def rejected : Realization signature.{u1, u2, u3} :=
  realize signature (fun _ _ _ => Matrix.of fun _ _ => (-1 : ℂ)) (fun e => nomatch e)

set_option linter.checkUnivs false in
/-- The complete original telescope is retained; only the kernel in the conclusion varies. -/
abbrev arena : Arena where
  signature := signature.{u1, u2, u3}
  Law R := ∀ {G : Type u1} [gG : Group G] {ι : Type u2} [fι : Fintype ι] {W : ι → Type u3}
    [nW : ∀ i, NormedAddCommGroup (W i)] [iW : ∀ i, InnerProductSpace ℂ (W i)]
    [∀ i, FiniteDimensional ℂ (W i)] (ρ : ∀ i, Representation ℂ G (W i))
    [∀ i, (ρ i).IsIrreducible] (_hne : ∀ i j, i ≠ j → IsEmpty ((ρ i).Equiv (ρ j)))
    (_hunit : ∀ i g v, ‖ρ i g v‖ = ‖v‖) (c : ι → ℂ),
    (R.readout () ⟨G, gG, ι, fι, W, nW, iW, ρ⟩ c).PosSemidef ↔ ∀ i, 0 ≤ c i

/-- The constant matrix `-1` on a nonempty index type is not positive semidefinite. -/
theorem const_not_posSemidef {G : Type*} (x : G) :
    ¬ (Matrix.of fun _ _ : G => (-1 : ℂ)).PosSemidef := by
  intro h
  have := h.2 (Finsupp.single x 1)
  simp at this
  norm_num at this

/-- On the empty family every weight condition holds, but `-1` is not positive semidefinite. -/
theorem rejected_law : ¬ arena.{u1, u2, u3}.Law rejected := by
  intro h
  have hh := @h PUnit.{u1 + 1} _ PEmpty.{u2 + 1} _ (fun i => i.elim) (fun i => i.elim)
    (fun i => i.elim) (fun i => i.elim) (fun i => i.elim) (fun i => i.elim) (fun i => i.elim)
    (fun i => i.elim) (fun _ => 0)
  exact const_not_posSemidef PUnit.unit (hh.2 fun i => i.elim)

/-- The complex line in universe `u3` as a complex inner product space. -/
@[instance_reducible]
def lineSpace : InnerProductSpace ℂ (ULift.{u3} ℂ) where
  inner x y := inner ℂ x.down y.down
  norm_sq_eq_re_inner x := norm_sq_eq_re_inner (𝕜 := ℂ) x.down
  conj_inner_symm x y := inner_conj_symm x.down y.down
  add_left x y z := inner_add_left x.down y.down z.down
  smul_left x y r := inner_smul_left x.down y.down r

/-- One summand: the trivial group acting trivially on the complex line. -/
abbrev testParams : Params.{u1, u2, u3} :=
  ⟨PUnit, inferInstance, PUnit, inferInstance, fun _ => ULift.{u3} ℂ, fun _ => inferInstance,
    fun _ => lineSpace, fun _ => Representation.trivial ℂ PUnit (ULift.{u3} ℂ)⟩

theorem observe_ne :
    observe testParams.{u1, u2, u3} (fun _ => 0) ≠ observe testParams.{u1, u2, u3} (fun _ => 1) := by
  intro h
  have h1 := congrFun (congrFun h PUnit.unit) PUnit.unit
  simp only [observe, Matrix.of_apply, Representation.character] at h1
  simp only [one_mul, zero_mul, Finset.sum_const_zero, Fintype.sum_unique] at h1
  change (0 : ℂ) = LinearMap.trace ℂ (ULift.{u3} ℂ) 1 at h1
  rw [LinearMap.trace_one, finrank_ulift, Module.finrank_self] at h1
  norm_num at h1

theorem dependence : ObservationalDependence signature.{u1, u2, u3} actual := by
  intro i
  exact ⟨testParams, fun _ => 0, fun _ => 1, observe_ne⟩

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @posSemidef_sum_character_kernel_iff.{u1, u2, u3}

def source : Registration arena.{u1, u2, u3} sourceStatement.{u1, u2, u3} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@posSemidef_sum_character_kernel_iff.{u1, u2, u3}, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := dependence

end Kernel

def posSemidef_sum_character_kernel_iff_registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@posSemidef_sum_character_kernel_iff.{u1, u2, u3})
      (Realization Kernel.signature.{u1, u2, u3}) Unit Unit := {
  unitName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.UnitaryCharacterKernel.posSemidef_sum_character_kernel_iff_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.UnitaryCharacterKernel.Kernel.source
  realizationSource := none
  generated := false
  arena := .source ⟨Kernel.arena⟩
  objectArena := .source ⟨Kernel.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Kernel.arena ⟨Kernel.source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Kernel.signature (fun _ => Kernel.observe) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.UnitaryCharacterKernel
    definition := none
    coordinates := #[0, 2, 4, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 12
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

/-! ## `posSemidef_sum_character_kernel_of_nonneg`: the kernel as a function of the weights -/
namespace Nonneg

set_option linter.checkUnivs false in
/-- The complete original telescope is retained; only the kernel in the conclusion varies.
The signature, the actual readout and the observation are those of the equivalence. -/
abbrev arena : Arena where
  signature := Kernel.signature.{u1, u2, u3}
  Law R := ∀ {G : Type u1} [gG : Group G] {ι : Type u2} [fι : Fintype ι] {W : ι → Type u3}
    [nW : ∀ i, NormedAddCommGroup (W i)] [iW : ∀ i, InnerProductSpace ℂ (W i)]
    [∀ i, FiniteDimensional ℂ (W i)] (ρ : ∀ i, Representation ℂ G (W i))
    (_hunit : ∀ i g v, ‖ρ i g v‖ = ‖v‖) (c : ι → ℂ) (_hc : ∀ i, 0 ≤ c i),
    (R.readout () ⟨G, gG, ι, fι, W, nW, iW, ρ⟩ c).PosSemidef

/-- On the empty family the weight condition holds, but `-1` is not positive semidefinite. -/
theorem rejected_law : ¬ arena.{u1, u2, u3}.Law Kernel.rejected := by
  intro h
  have hh := @h PUnit.{u1 + 1} _ PEmpty.{u2 + 1} _ (fun i => i.elim) (fun i => i.elim)
    (fun i => i.elim) (fun i => i.elim) (fun i => i.elim) (fun i => i.elim) (fun _ => 0)
    (fun i => i.elim)
  exact Kernel.const_not_posSemidef PUnit.unit hh

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @posSemidef_sum_character_kernel_of_nonneg.{u1, u2, u3}

def source : Registration arena.{u1, u2, u3} sourceStatement.{u1, u2, u3} where
  actual := Kernel.actual
  bridge := Iff.rfl
  variation := ⟨@posSemidef_sum_character_kernel_of_nonneg.{u1, u2, u3}, Kernel.rejected,
    rejected_law⟩
  sensitivity := ⟨fun i => ⟨Kernel.rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := Kernel.dependence

end Nonneg

def posSemidef_sum_character_kernel_of_nonneg_registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@posSemidef_sum_character_kernel_of_nonneg.{u1, u2, u3})
      (Realization Kernel.signature.{u1, u2, u3}) Unit Unit := {
  unitName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.UnitaryCharacterKernel.posSemidef_sum_character_kernel_of_nonneg_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GroupAlgebra.UnitaryCharacterKernel.Nonneg.source
  realizationSource := none
  generated := false
  arena := .source ⟨Nonneg.arena⟩
  objectArena := .source ⟨Nonneg.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Nonneg.arena ⟨Nonneg.source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Kernel.signature (fun _ => Kernel.observe) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GroupAlgebra.UnitaryCharacterKernel
    definition := none
    coordinates := #[0, 2, 4, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.FiniteGroups.GroupAlgebra.UnitaryCharacterKernel
