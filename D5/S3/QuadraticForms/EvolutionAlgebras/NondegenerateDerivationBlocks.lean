/- GID: D5/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/EvolutionAlgebras/NondegenerateDerivationBlocks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual natural-basis blocks, reduced orthogonal actions and solvable kernels. -/

/-
admission_basis: escape-witness
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22095
Historical dependent-equivalence audit: https://github.com/the-omega-institute/trureturing/issues/19944
The arbitrary full-Der family still lacks complete variation, sensitivity and
observational-dependence registration. No blanket issue exception is asserted.
utility none: structural existence and actual Lie maps/equivalences.
The canonical natural-basis equation bodies are factored into their imported
NaturalBasisDerivationEquations owner with their original qualified names.
The old full block equivalence still requires semisimple derivations.
The general reduced surjection retains every small/isotropic/degenerate block.
Classical structure is credited as prior mathematics; the scientific application
retains Haobo Ma, then Wenlin Zhang. No priority claim.
-/

import D5.S3.QuadraticForms.EvolutionAlgebras.NaturalBasisDerivationEquations
import D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers

attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Pi
instance piLieRing {α : Type*} {H : α → Type*} [∀ a, LieRing (H a)] : LieRing (∀ a,H a) :=
  { (inferInstance : AddCommGroup (∀ a,H a)) with
    bracket := fun f g a => ⁅f a,g a⁆
    add_lie := fun f g h => funext (fun a => add_lie (f a) (g a) (h a))
    lie_add := fun f g h => funext (fun a => lie_add (f a) (g a) (h a))
    lie_self := fun f => funext (fun a => lie_self (f a))
    leibniz_lie := fun f g h => funext (fun a => leibniz_lie (f a) (g a) (h a)) }
instance piLieAlgebra {k α : Type*} [CommRing k] {H : α → Type*}
    [∀ a, LieRing (H a)] [∀ a, LieAlgebra k (H a)] : LieAlgebra k (∀ a,H a) :=
  { (inferInstance : Module k (∀ a,H a)) with
    lie_smul := fun c f g => funext (fun a => lie_smul c (f a) (g a)) }

private def piHom {k L α : Type*} [CommRing k] [LieRing L] [LieAlgebra k L]
    (H : α → Type*) [∀ a, LieRing (H a)] [∀ a, LieAlgebra k (H a)]
    (f : ∀ a, L →ₗ⁅k⁆ H a) : L →ₗ⁅k⁆ ∀ a, H a :=
  { LinearMap.pi (fun a => (f a).toLinearMap) with
    map_lie' := by
      intro x y
      funext a
      exact (f a).map_lie x y }

private def codRestrictHom {k L M : Type*} [CommRing k]
    [LieRing L] [LieAlgebra k L] [LieRing M] [LieAlgebra k M]
    (f : L →ₗ⁅k⁆ M) (S : LieSubalgebra k M) (hf : ∀ x, f x ∈ S) :
    L →ₗ⁅k⁆ S :=
  { f.toLinearMap.codRestrict S.toSubmodule hf with
    map_lie' := fun {x y} => Subtype.ext (f.map_lie x y) }
end D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Pi

namespace D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.BlockLinear
open DirectSum
open scoped Classical
attribute [local instance 100] LieRing.ofAssociativeRing
variable {k V ι α : Type*} [Field k] [AddCommGroup V] [Module k V]
variable [Fintype ι] (b : Module.Basis ι k V) (label : ι → α)
private noncomputable def splitEquiv : V ≃ₗ[k] ∀ a, ({i : ι // label i = a} → k) :=
  b.equivFun.trans ((LinearEquiv.piCongrLeft' k (fun _ : ι => k)
    (Equiv.sigmaFiberEquiv label).symm).trans
    (LinearEquiv.piCurry k (fun a (_ : {i : ι // label i = a}) => k)))
private theorem splitEquiv_apply (x : V) (a : α) (i : {i // label i = a}) :
    splitEquiv b label x a i = b.repr x i.val := by
  rfl
private theorem splitEquiv_symm_apply (y : ∀ a, ({i : ι // label i = a} → k)) (i : ι) :
    b.repr ((splitEquiv b label).symm y) i = y (label i) ⟨i,rfl⟩ := by
  change b.equivFun (b.equivFun.symm (fun j => y (label j) ⟨j,rfl⟩)) i = _
  exact congrFun (b.equivFun.apply_symm_apply _) i

variable {β : Type*} (E : β → Type*) [∀ a, AddCommGroup (E a)] [∀ a, Module k (E a)]
private def piEndHom : (∀ a, Module.End k (E a)) →ₗ⁅k⁆ Module.End k (∀ a, E a) where
  toFun f := LinearMap.piMap f
  map_add' := by intro f g; ext x a; rfl
  map_smul' := by intro c f; ext x a; rfl
  map_lie' := by intro f g; ext x a; rfl
private theorem piEndHom_injective : Function.Injective (piEndHom (k := k) E) := by
  classical
  intro f g h
  funext a
  ext x
  simpa [piEndHom] using congrArg (fun F : Module.End k (∀ a, E a) => F (Pi.single a x) a) h

private noncomputable def assemble : (∀ a, Module.End k (({i : ι // label i = a} → k))) →ₗ⁅k⁆ Module.End k V :=
  (splitEquiv b label).symm.lieConj.toLieHom.comp (piEndHom ((fun a => {i : ι // label i = a} → k)))
private theorem assemble_coordinate (f : ∀ a, Module.End k (({i : ι // label i = a} → k))) (x : V) (i : ι) :
    b.repr (assemble b label f x) i = f (label i) (splitEquiv b label x (label i)) ⟨i,rfl⟩ := by
  change b.repr ((splitEquiv b label).symm
    (fun a => f a (splitEquiv b label x a))) i = _
  exact splitEquiv_symm_apply b label _ i
private theorem assemble_injective : Function.Injective (assemble b label) := by
  exact (splitEquiv b label).symm.lieConj.injective.comp (piEndHom_injective _)

noncomputable def piDirectSumEquiv [Fintype β] (H : β → Type*)
    [∀ a, LieRing (H a)] [∀ a, LieAlgebra k (H a)] :
    (∀ a, H a) ≃ₗ⁅k⁆ ⨁ a, H a :=
  { (DirectSum.linearEquivFunOnFintype k β H).symm with
    map_lie' := by intro f g; ext a; rfl }

private noncomputable def blockProject (a : α) : V →ₗ[k] ({i : ι // label i = a} → k) :=
  (LinearMap.proj a).comp (splitEquiv b label).toLinearMap

private noncomputable def blockInclude (a : α) : ({i : ι // label i = a} → k) →ₗ[k] V := by
  classical
  exact (splitEquiv b label).symm.toLinearMap.comp
    (LinearMap.single k ((fun a => {i : ι // label i = a} → k)) a)
private theorem project_include_same (a : α) (x : ({i : ι // label i = a} → k)) :
    blockProject b label a (blockInclude b label a x) = x := by
  classical
  change (splitEquiv b label ((splitEquiv b label).symm (Pi.single a x))) a = x
  rw [LinearEquiv.apply_symm_apply, Pi.single_eq_same]
private theorem include_basis (a : α) (i : {i // label i = a}) :
    blockInclude b label a (Pi.single i 1) = b i.val := by
  classical
  apply (splitEquiv b label).injective
  change splitEquiv b label ((splitEquiv b label).symm
    (Pi.single a (Pi.single i (1 : k)))) = splitEquiv b label (b i.val)
  rw [LinearEquiv.apply_symm_apply]
  ext c j
  rw [splitEquiv_apply, b.repr_self, Finsupp.single_apply]
  by_cases hac : a = c
  · subst c
    simp only [Pi.single_eq_same, Pi.single_apply]
    simp only [Subtype.ext_iff,eq_comm]
  · have hji : i.val ≠ j.val := by
      intro h
      exact hac (i.property.symm.trans ((congrArg label h).trans j.property))
    rw [Pi.single_eq_of_ne (Ne.symm hac), Pi.zero_apply, if_neg hji]

private noncomputable def restrictBlock (D : Module.End k V) (a : α) :
    Module.End k (({i : ι // label i = a} → k)) :=
  (blockProject b label a).comp (D.comp (blockInclude b label a))
private theorem restrictBlock_coefficient (D : Module.End k V) (a : α)
    (i j : {i // label i = a}) :
    restrictBlock b label D a (Pi.single i 1) j = b.repr (D (b i.val)) j.val := by
  simp only [restrictBlock, LinearMap.comp_apply, include_basis]
  rfl
private theorem project_assemble (f : ∀ a, Module.End k (({i : ι // label i = a} → k))) (x : V) (a : α) :
    blockProject b label a (assemble b label f x) = f a (blockProject b label a x) := by
  change (splitEquiv b label ((splitEquiv b label).symm
    (fun c => f c (splitEquiv b label x c)))) a = _
  rw [LinearEquiv.apply_symm_apply]
  rfl
private theorem assemble_cross_zero (f : ∀ a, Module.End k (({i : ι // label i = a} → k)))
    (i j : ι) (hc : label i ≠ label j) : b.repr (assemble b label f (b i)) j = 0 := by
  classical
  rw [assemble_coordinate]
  have hproj : splitEquiv b label (b i) (label j) = 0 := by
    ext u
    rw [splitEquiv_apply, b.repr_self, Finsupp.single_apply]
    have hne : i ≠ u.val := by
      intro h
      exact hc ((congrArg label h).trans u.property)
    simp only [hne, if_false, Pi.zero_apply]
  rw [hproj, map_zero, Pi.zero_apply]
private theorem assemble_restrict_of_cross_zero (D : Module.End k V)
    (hcross : ∀ i j, label i ≠ label j → b.repr (D (b i)) j = 0) :
    assemble b label (restrictBlock b label D) = D := by
  classical
  apply b.ext
  intro i
  apply b.repr.injective
  ext j
  rw [assemble_coordinate]
  by_cases hc : label i = label j
  · have hproj : splitEquiv b label (b i) (label j) =
        Pi.single (⟨i,hc⟩ : {i // label i = label j}) 1 := by
      ext u
      rw [splitEquiv_apply, b.repr_self, Finsupp.single_apply, Pi.single_apply]
      simp only [Subtype.ext_iff,eq_comm]
    rw [hproj, restrictBlock_coefficient]
  · have hproj : splitEquiv b label (b i) (label j) = 0 := by
      ext u
      rw [splitEquiv_apply, b.repr_self, Finsupp.single_apply]
      have hne : i ≠ u.val := by
        intro h
        exact hc ((congrArg label h).trans u.property)
      simp only [hne, if_false, Pi.zero_apply]
    rw [hproj, map_zero, Pi.zero_apply, hcross i j hc]
private theorem restrict_assemble (f : ∀ a, Module.End k (({i : ι // label i = a} → k))) :
    restrictBlock b label (assemble b label f) = f := by
  classical
  funext a
  apply LinearMap.ext
  intro x
  change blockProject b label a (assemble b label f (blockInclude b label a x)) = f a x
  rw [project_assemble,project_include_same]

end D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.BlockLinear

namespace D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Decomposition

private theorem map_triple_bracket_zero {R L M : Type*} [CommRing R]
    [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]
    (f : L →ₗ⁅R⁆ M) (h : ∀ u v w : M, ⁅u, ⁅v,w⁆⁆ = 0) (x y z : L) :
    f ⁅x, ⁅y,z⁆⁆ = 0 :=
  (f.map_lie x ⁅y,z⁆).trans
    ((congrArg (fun t : M => ⁅f x,t⁆) (f.map_lie y z)).trans (h (f x) (f y) (f z)))

open DirectSum
open D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.BlockLinear D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Normalized
attribute [local instance 100] LieRing.ofAssociativeRing
variable {k V ι α : Type*} [Field k] [AddCommGroup V] [Module k V]
variable [Fintype ι] [Fintype α] [DecidableEq α]
variable (μ : V →ₗ[k] V →ₗ[k] V) (b : Module.Basis ι k V)
variable (label : ι → α) (w : α → V)

noncomputable def blockW (a : α) : Submodule k (({i : ι // label i = a} → k)) :=
  Submodule.span k (Set.range (fun c (i : {i : ι // label i = a}) => b.repr (w c) i.val))

variable (hn : ∀ i j, i ≠ j → μ (b i) (b j) = 0)
variable (hsq : ∀ i, μ (b i) (b i) = w (label i))
variable (hw : ∀ a, w a ≠ 0)
variable (hsep : ∀ a c, a ≠ c → ∀ s t : k, s • w a + t • w c = 0 → s = 0 ∧ t = 0)

private theorem assemble_properties
    (f : ∀ a, (D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.Stabilizer.stabilizer (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix _ _ k)) (D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Decomposition.blockW b label w a))) :
    (∀ i j, label i ≠ label j →
      b.repr (assemble b label (fun a => (f a).val) (b i)) j = 0) ∧
    (∀ i j, b.repr (assemble b label (fun a => (f a).val) (b i)) j =
      -b.repr (assemble b label (fun a => (f a).val) (b j)) i) ∧
    (∀ c ∈ Set.range label, assemble b label (fun a => (f a).val) (w c) = 0) := by
  classical
  let F := fun a => (f a).val
  refine ⟨assemble_cross_zero b label F, ?_, ?_⟩
  · intro i j
    by_cases hc : label i = label j
    · have hf : (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix _ _ k)).IsSkewAdjoint (F (label i)) :=
        (LinearMap.mem_skewAdjointSubmodule _).mp (f (label i)).property.1
      have hh := (D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.BlockForm.skew_iff_coefficients (F (label i))).mp hf
        ⟨i,rfl⟩ ⟨j,hc.symm⟩
      have heq := congrFun (restrict_assemble b label F) (label i)
      rw [← heq, restrictBlock_coefficient, restrictBlock_coefficient] at hh
      exact hh
    · rw [assemble_cross_zero b label F i j hc,
        assemble_cross_zero b label F j i (Ne.symm hc), neg_zero]
  · intro c hc
    apply (splitEquiv b label).injective
    rw [map_zero]
    funext a
    change blockProject b label a (assemble b label F (w c)) = 0
    rw [project_assemble]
    exact (f a).property.2 _ (Submodule.subset_span ⟨c,rfl⟩)

include hn hsq hw hsep in
private theorem assemble_mem_derivations_general
    (f : ∀ a, (D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.Stabilizer.stabilizer (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix _ _ k)) (D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Decomposition.blockW b label w a))) :
    assemble b label (fun a => (f a).val) ∈ derivations μ := by
  obtain ⟨hc,hs,hk⟩ := assemble_properties b label w f
  exact derivation_of_skew_killing μ b label w hn hsq _ hc hs hk

include hn hsq hw hsep in
private noncomputable def productToDerivationsGeneral :
    (∀ a, (D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.Stabilizer.stabilizer (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix _ _ k)) (D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Decomposition.blockW b label w a))) →ₗ⁅k⁆ derivations μ where
  toFun f := ⟨assemble b label (fun a => (f a).val), assemble_mem_derivations_general μ b label w hn hsq hw hsep f⟩
  map_add' := by
    intro f g
    apply Subtype.ext
    exact (assemble b label).map_add _ _
  map_smul' := by
    intro c f
    apply Subtype.ext
    exact (assemble b label).map_smul c _
  map_lie' := by
    intro f g
    apply Subtype.ext
    exact (assemble b label).map_lie _ _

include hn hsq hsep in
private theorem project_derivation (D : derivations μ) (a : α) (x : V) :
    blockProject b label a (D.val x) =
      restrictBlock b label D.val a (blockProject b label a x) := by
  have he := assemble_restrict_of_cross_zero b label D.val
    (derivation_cross_zero μ b label w hn hsq hsep D)
  rw [← he, project_assemble]
  rw [restrict_assemble]

include hn hsq hsep in
private noncomputable def restrictDerivation (a : α) :
    derivations μ →ₗ⁅k⁆ Module.End k ({i : ι // label i = a} → k) where
  toFun D := restrictBlock b label D.val a
  map_add' := by
    intro D E
    apply LinearMap.ext
    intro x
    funext i
    simp [restrictBlock, map_add]
  map_smul' := by
    intro c D
    apply LinearMap.ext
    intro x
    funext i
    simp [restrictBlock, map_smul]
  map_lie' := by
    intro D E
    apply LinearMap.ext
    intro x
    funext i
    change blockProject b label a
      (D.val (E.val (blockInclude b label a x)) -
        E.val (D.val (blockInclude b label a x))) i = _
    rw [map_sub, project_derivation μ b label w hn hsq hsep D,
      project_derivation μ b label w hn hsq hsep E,
      project_derivation μ b label w hn hsq hsep E,
      project_derivation μ b label w hn hsq hsep D,
      project_include_same]
    rfl

include hn hsq hw hsep in
private noncomputable def classDiagonal (hl : Function.Surjective label) (a : α) :
    derivations μ →ₗ⁅k⁆ k where
  toFun D := b.repr (D.val (b (Classical.choose (hl a)))) (Classical.choose (hl a))
  map_add' := by intro D E; simp
  map_smul' := by intro c D; simp
  map_lie' := by
    intro D E
    change b.repr ((⁅D,E⁆ : derivations μ).val (b (Classical.choose (hl a))))
      (Classical.choose (hl a)) = _
    rw [derivation_bracket_diagonal_zero μ b label w hn hsq hw hsep D E]
    simp [Ring.lie_def, mul_comm]

include hn hsq hw hsep in
private theorem classDiagonal_coefficient [CharZero k]
    (hl : Function.Surjective label) (a : α) (D : derivations μ)
    (i : {i // label i = a}) :
    classDiagonal μ b label w hn hsq hw hsep hl a D = b.repr (D.val (b i.val)) i.val :=
  derivation_diagonal_eq_on_class μ b label w hn hsq hw D _ _
    ((Classical.choose_spec (hl a)).trans i.property.symm)

include hn hsq hw hsep in
private theorem classDiagonal_square (hl : Function.Surjective label)
    (a : α) (D : derivations μ) :
    D.val (w a) = (2 * classDiagonal μ b label w hn hsq hw hsep hl a D) • w a := by
  have hh := D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Equations.square_equation μ b hn D (Classical.choose (hl a))
  rw [hsq, Classical.choose_spec (hl a)] at hh
  exact hh

include hn hsq hw hsep in
private noncomputable def correctedRestrict (hl : Function.Surjective label) (a : α) :
    derivations μ →ₗ⁅k⁆ Module.End k ({i : ι // label i = a} → k) where
  toFun D := restrictDerivation μ b label w hn hsq hsep a D -
    classDiagonal μ b label w hn hsq hw hsep hl a D • (1 : Module.End k _)
  map_add' := by
    intro D E
    simp only [map_add, add_smul]
    abel
  map_smul' := by
    intro c D
    simp only [map_smul, smul_sub, smul_smul, smul_eq_mul, RingHom.id_apply]
  map_lie' := by
    intro D E
    rw [(restrictDerivation μ b label w hn hsq hsep a).map_lie,
      (classDiagonal μ b label w hn hsq hw hsep hl a).map_lie]
    have hc (u v : k) : ⁅u,v⁆ = 0 := by simp [Ring.lie_def, mul_comm]
    simp only [hc, zero_smul, sub_zero, lie_sub, sub_lie, lie_smul, smul_lie]
    simp only [Ring.lie_def, mul_one, one_mul, sub_self, smul_zero, sub_zero,
      zero_sub, neg_zero]

include hn hsq hw hsep in
private theorem correctedRestrict_mem_preserver [CharZero k]
    (hl : Function.Surjective label) (a : α) (D : derivations μ) :
    correctedRestrict μ b label w hn hsq hw hsep hl a D ∈
      D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.Stabilizer.preserver
        (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix _ _ k))
        (blockW b label w a) := by
  classical
  constructor
  · apply (LinearMap.mem_skewAdjointSubmodule _).mpr
    apply (D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.BlockForm.skew_iff_coefficients _).mpr
    intro i j
    change restrictBlock b label D.val a (Pi.single i (1 : k)) j -
        classDiagonal μ b label w hn hsq hw hsep hl a D * ((Pi.single i (1 : k) : {i : ι // label i = a} → k) j) =
      -(restrictBlock b label D.val a (Pi.single j (1 : k)) i -
        classDiagonal μ b label w hn hsq hw hsep hl a D * ((Pi.single j (1 : k) : {i : ι // label i = a} → k) i))
    rw [restrictBlock_coefficient, restrictBlock_coefficient]
    by_cases hij : i = j
    · subst j
      rw [← classDiagonal_coefficient μ b label w hn hsq hw hsep hl a D i]
      simp
    · have hv : i.val ≠ j.val := fun h => hij (Subtype.ext h)
      rw [derivation_off_diagonal_skew μ b label w hn hsq hw hsep D i.val j.val hv]
      simp [Pi.single_apply, hij, Ne.symm hij]
  · intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨c,rfl⟩ := hx
        change restrictBlock b label D.val a (blockProject b label a (w c)) -
          classDiagonal μ b label w hn hsq hw hsep hl a D •
            (blockProject b label a (w c)) ∈ blockW b label w a
        rw [← project_derivation μ b label w hn hsq hsep D a (w c),
          classDiagonal_square μ b label w hn hsq hw hsep hl c D, map_smul]
        exact (blockW b label w a).sub_mem
          ((blockW b label w a).smul_mem _ (Submodule.subset_span ⟨c,rfl⟩))
          ((blockW b label w a).smul_mem _ (Submodule.subset_span ⟨c,rfl⟩))
    | zero => simp
    | add x y hx hy ihx ihy =>
        simpa only [map_add] using (blockW b label w a).add_mem ihx ihy
    | smul c x hx ih =>
        simpa only [map_smul] using (blockW b label w a).smul_mem c ih

include hn hsq hw hsep in
private noncomputable def correctedPreserverHom [CharZero k]
    (hl : Function.Surjective label) (a : α) : derivations μ →ₗ⁅k⁆
      D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.Stabilizer.preserver
        (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix _ _ k))
        (blockW b label w a) :=
  { (correctedRestrict μ b label w hn hsq hw hsep hl a).toLinearMap.codRestrict _
      (fun D => correctedRestrict_mem_preserver μ b label w hn hsq hw hsep hl a D) with
    map_lie' := fun {D E} => Subtype.ext
      ((correctedRestrict μ b label w hn hsq hw hsep hl a).map_lie D E) }

include hn hsq hw hsep in
private theorem productToDerivationsGeneral_injective :
    Function.Injective (productToDerivationsGeneral μ b label w hn hsq hw hsep) := by
  intro f g h
  have hh := assemble_injective b label (congrArg Subtype.val h)
  funext a
  exact Subtype.ext (congrFun hh a)

include hn hsq hw hsep in
private theorem assemble_mem_derivations [LieAlgebra.IsSemisimple k (derivations μ)]
    (f : ∀ a, D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.Stabilizer.stabilizer
      (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix _ _ k))
      (blockW b label w a)) :
    assemble b label (fun a => (f a).val) ∈ derivations μ :=
  assemble_mem_derivations_general μ b label w hn hsq hw hsep f

include hn hsq hw hsep in
private noncomputable def productToDerivations [LieAlgebra.IsSemisimple k (derivations μ)] :
    (∀ a, D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.Stabilizer.stabilizer
      (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix _ _ k))
      (blockW b label w a)) →ₗ⁅k⁆ derivations μ :=
  productToDerivationsGeneral μ b label w hn hsq hw hsep

include hn hsq hw hsep in
private theorem productToDerivations_injective [LieAlgebra.IsSemisimple k (derivations μ)] :
    Function.Injective (productToDerivations μ b label w hn hsq hw hsep) :=
  productToDerivationsGeneral_injective μ b label w hn hsq hw hsep

include hn hsq hw hsep in
private theorem restrictBlock_mem_stabilizer_of_diagonal_zero
    (hl : Function.Surjective label) (D : derivations μ)
    (hdiag : ∀ i, b.repr (D.val (b i)) i = 0) (a : α) :
    restrictBlock b label D.val a ∈ (D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.Stabilizer.stabilizer (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix _ _ k)) (D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Decomposition.blockW b label w a)) := by
  classical
  have hD := properties_of_diagonal_zero μ b label w hn hsq hw hsep D hdiag
  have heq := assemble_restrict_of_cross_zero b label D.val hD.1
  refine ⟨(LinearMap.mem_skewAdjointSubmodule _).mpr ?_, ?_⟩
  · apply (D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.BlockForm.skew_iff_coefficients _).mpr
    intro i j
    rw [restrictBlock_coefficient, restrictBlock_coefficient]
    exact hD.2.1 i.val j.val
  · intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨c,rfl⟩ := hx
        calc
          restrictBlock b label D.val a (blockProject b label a (w c)) =
              blockProject b label a (assemble b label (restrictBlock b label D.val) (w c)) :=
            (project_assemble b label _ _ _).symm
          _ = blockProject b label a (D.val (w c)) := by rw [heq]
          _ = 0 := by rw [hD.2.2 c (hl c), map_zero]
    | zero => exact map_zero _
    | add x y hx hy ihx ihy => simp [ihx,ihy]
    | smul c x hx ih => simp [ih]

include hn hsq hw hsep in
private theorem restrictBlock_mem_stabilizer [LieAlgebra.IsSemisimple k (derivations μ)]
    (hl : Function.Surjective label) (D : derivations μ) (a : α) :
    restrictBlock b label D.val a ∈
      D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.Stabilizer.stabilizer
        (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix _ _ k))
        (blockW b label w a) :=
  restrictBlock_mem_stabilizer_of_diagonal_zero μ b label w hn hsq hw hsep hl D
    (semisimple_diagonal_zero μ b label w hn hsq hw hsep D) a

include hn hsq hw hsep in
private noncomputable def productToDiagonalKernel [CharZero k] :
    (∀ a, D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.Stabilizer.stabilizer
      (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix _ _ k))
      (blockW b label w a)) →ₗ⁅k⁆ (diagonalHom μ b label w hn hsq hw hsep).ker where
  toFun f := ⟨productToDerivationsGeneral μ b label w hn hsq hw hsep f, by
    rw [LieHom.mem_ker]
    funext i
    change b.repr (assemble b label (fun a => (f a).val) (b i)) i = 0
    have h := (assemble_properties b label w f).2.1 i i
    have htwo : (2 : k) * b.repr (assemble b label (fun a => (f a).val) (b i)) i = 0 := by
      simpa only [two_mul] using eq_neg_iff_add_eq_zero.mp h
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)⟩
  map_add' := by
    intro f g
    apply Subtype.ext
    exact (productToDerivationsGeneral μ b label w hn hsq hw hsep).map_add f g
  map_smul' := by
    intro c f
    apply Subtype.ext
    exact (productToDerivationsGeneral μ b label w hn hsq hw hsep).map_smul c f
  map_lie' := by
    intro f g
    apply Subtype.ext
    exact (productToDerivationsGeneral μ b label w hn hsq hw hsep).map_lie f g

include hn hsq hw hsep in
/-- The actual kernel of the diagonal Lie map is the direct sum of orthogonal
pointwise stabilizers, without a semisimplicity assumption on derivations. -/
private theorem diagonalKernel_equiv_stabilizers [CharZero k] (hl : Function.Surjective label) :
    Nonempty ((diagonalHom μ b label w hn hsq hw hsep).ker ≃ₗ⁅k⁆
      ⨁ a, D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.Stabilizer.stabilizer
        (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix _ _ k))
        (blockW b label w a)) := by
  classical
  refine ⟨(LieEquiv.ofBijective (productToDiagonalKernel μ b label w hn hsq hw hsep)
    ⟨?_, ?_⟩).symm.trans (piDirectSumEquiv (k := k) _)⟩
  · intro f g h
    exact productToDerivationsGeneral_injective μ b label w hn hsq hw hsep (congrArg Subtype.val h)
  · intro D
    have hd (i : ι) : b.repr (D.val.val (b i)) i = 0 :=
      congrFun (LieHom.mem_ker.mp D.property) i
    let f : ∀ a, D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.Stabilizer.stabilizer
        (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix _ _ k))
        (blockW b label w a) := fun a =>
      ⟨restrictBlock b label D.val.val a,
        restrictBlock_mem_stabilizer_of_diagonal_zero μ b label w hn hsq hw hsep hl D.val hd a⟩
    refine ⟨f, Subtype.ext (Subtype.ext ?_)⟩
    exact assemble_restrict_of_cross_zero b label D.val.val
      (properties_of_diagonal_zero μ b label w hn hsq hw hsep D.val hd).1

include hn hsq hw hsep in
/-- The quotient of actual derivations by their diagonal kernel is abelian. -/
private theorem diagonalKernel_quotient_abelian :
    IsLieAbelian (derivations μ ⧸ (diagonalHom μ b label w hn hsq hw hsep).ker) := by
  let f := diagonalHom μ b label w hn hsq hw hsep
  have hf : IsLieAbelian (ι → k) :=
    ⟨fun x y => by ext i; simp [Ring.lie_def, mul_comm]⟩
  have hr : IsLieAbelian f.range :=
    Function.Injective.isLieAbelian (f := f.range.incl) Subtype.val_injective hf
  exact f.quotKerEquivRange.injective.isLieAbelian hr

/-- The nondegenerate quotient of the orthogonal complement of a block's
pointwise fixed subspace. Naming the actual quotient also keeps its module
structure shared in dependent families of reduced orthogonal blocks. -/
def reducedBlockSpace (a : α) : Type _ :=
  let B : LinearMap.BilinForm k ({i : ι // label i = a} → k) :=
    Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix _ _ k)
  let U := B.orthogonal (blockW b label w a)
  U ⧸ LinearMap.ker (B.restrict U)

noncomputable instance reducedBlockSpaceAddCommGroup (a : α) :
    AddCommGroup (reducedBlockSpace b label w a) := by
  unfold reducedBlockSpace
  infer_instance

noncomputable instance reducedBlockSpaceModule (a : α) :
    Module k (reducedBlockSpace b label w a) := by
  unfold reducedBlockSpace
  infer_instance

noncomputable instance reducedBlockSpaceFiniteDimensional (a : α) :
    FiniteDimensional k (reducedBlockSpace b label w a) := by
  unfold reducedBlockSpace
  infer_instance

noncomputable def reducedBlockForm (a : α) :
    LinearMap.BilinForm k (reducedBlockSpace b label w a) :=
  let B : LinearMap.BilinForm k ({i : ι // label i = a} → k) :=
    Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix _ _ k)
  let W := blockW b label w a
  LinearMap.IsRefl.liftQ₂ (B.restrict (B.orthogonal W))
    (LinearMap.ker (B.restrict (B.orthogonal W)))
    (fun x y =>
      (D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.NormalForm.standardForm_symm _).isRefl
        x.val y.val) le_rfl

/-- The actual skew-adjoint Lie algebra on the reduced block. Its named Lie
instances keep this dependent carrier shared in the full derivation action. -/
def reducedBlockLie (a : α) : Type _ :=
  skewAdjointLieSubalgebra (reducedBlockForm b label w a)

noncomputable instance reducedBlockLieRing (a : α) :
    LieRing (reducedBlockLie b label w a) := by
  unfold reducedBlockLie
  infer_instance

noncomputable instance reducedBlockLieAlgebra (a : α) :
    LieAlgebra k (reducedBlockLie b label w a) := by
  unfold reducedBlockLie
  infer_instance

private noncomputable def reducedStabilizerQuotientHom (a : α) :
    D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.Stabilizer.stabilizer
      (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k)
        (1 : Matrix {i : ι // label i = a} {i : ι // label i = a} k))
      (blockW b label w a) →ₗ⁅k⁆ reducedBlockLie b label w a :=
  D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.Stabilizer.quotientLieHom
    _ _ (D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.NormalForm.standardForm_symm _)

private noncomputable def reducedPreserverQuotientHom (a : α) :
    D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.Stabilizer.preserver
      (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k)
        (1 : Matrix {i : ι // label i = a} {i : ι // label i = a} k))
      (blockW b label w a) →ₗ⁅k⁆ reducedBlockLie b label w a :=
  D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.Stabilizer.preserverQuotientLieHom
    _ _ (D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.NormalForm.standardForm_symm _)

include hn hsq hw hsep in
private noncomputable def normalizedReducedBlockHom [CharZero k]
    (hl : Function.Surjective label) (a : α) :
    derivations μ →ₗ⁅k⁆ reducedBlockLie b label w a :=
  (reducedPreserverQuotientHom b label w a).comp
    (correctedPreserverHom μ b label w hn hsq hw hsep hl a)

include hn hsq hw hsep in
private noncomputable def normalizedReducedHom [CharZero k]
    (hl : Function.Surjective label) : derivations μ →ₗ⁅k⁆
      ∀ a, reducedBlockLie b label w a :=
  Pi.piHom (fun a => reducedBlockLie b label w a)
    (fun a => normalizedReducedBlockHom μ b label w hn hsq hw hsep hl a)

include hn hsq hw hsep in
private theorem correctedRestrict_eq_of_diagonal_zero [CharZero k]
    (hl : Function.Surjective label) (D : derivations μ)
    (hd : ∀ i, b.repr (D.val (b i)) i = 0) (a : α) :
    correctedRestrict μ b label w hn hsq hw hsep hl a D = restrictBlock b label D.val a := by
  have hc : classDiagonal μ b label w hn hsq hw hsep hl a D = 0 :=
    hd (Classical.choose (hl a))
  change restrictBlock b label D.val a -
    classDiagonal μ b label w hn hsq hw hsep hl a D • 1 = _
  rw [hc, zero_smul, sub_zero]

include hn hsq hw hsep in
private theorem normalizedReducedHom_of_diagonal_zero [CharZero k]
    (hl : Function.Surjective label) (D : derivations μ)
    (hd : ∀ i, b.repr (D.val (b i)) i = 0) (a : α) :
    normalizedReducedHom μ b label w hn hsq hw hsep hl D a =
      reducedStabilizerQuotientHom b label w a
        ⟨restrictBlock b label D.val a,
          restrictBlock_mem_stabilizer_of_diagonal_zero μ b label w hn hsq hw hsep hl D hd a⟩ := by
  let B : LinearMap.BilinForm k ({i : ι // label i = a} → k) :=
    Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix _ _ k)
  let W := blockW b label w a
  let x : D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.Stabilizer.stabilizer B W :=
    ⟨restrictBlock b label D.val a,
      restrictBlock_mem_stabilizer_of_diagonal_zero μ b label w hn hsq hw hsep hl D hd a⟩
  let y : D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.Stabilizer.preserver B W :=
    ⟨x.val, x.property.1, fun u hu => by rw [x.property.2 u hu]; exact W.zero_mem⟩
  have he : correctedPreserverHom μ b label w hn hsq hw hsep hl a D = y :=
    Subtype.ext (correctedRestrict_eq_of_diagonal_zero μ b label w hn hsq hw hsep hl D hd a)
  exact congrArg (D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.Stabilizer.preserverQuotientLieHom
    B W (D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.NormalForm.standardForm_symm _)) he

include hn hsq hw hsep in
private theorem normalizedReducedHom_surjective [CharZero k]
    (hl : Function.Surjective label) :
    Function.Surjective (normalizedReducedHom μ b label w hn hsq hw hsep hl) := by
  classical
  intro F
  let B (a : α) : LinearMap.BilinForm k ({i : ι // label i = a} → k) :=
    Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix _ _ k)
  let W (a : α) := blockW b label w a
  let f (a : α) := Classical.choose
    (D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.Stabilizer.quotientLieHom_surjective
      (B a) (W a)
      (D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.NormalForm.standardForm_symm _) (F a))
  let D := productToDiagonalKernel μ b label w hn hsq hw hsep f
  have hd (i : ι) : b.repr (D.val.val (b i)) i = 0 :=
    congrFun (LieHom.mem_ker.mp D.property) i
  refine ⟨D.val, ?_⟩
  funext a
  have hnorm := normalizedReducedHom_of_diagonal_zero μ b label w hn hsq hw hsep hl D.val hd a
  have hrest : restrictBlock b label D.val.val a = (f a).val :=
    congrFun (restrict_assemble b label (fun c => (f c).val)) a
  have he : (⟨restrictBlock b label D.val.val a,
      restrictBlock_mem_stabilizer_of_diagonal_zero μ b label w hn hsq hw hsep hl D.val hd a⟩ :
      D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.Stabilizer.stabilizer (B a) (W a)) = f a :=
    Subtype.ext hrest
  exact hnorm.trans ((congrArg
    (D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.Stabilizer.quotientLieHom
      (B a) (W a)
      (D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.NormalForm.standardForm_symm _)) he).trans
    (Classical.choose_spec
      (D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.Stabilizer.quotientLieHom_surjective
        (B a) (W a)
        (D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.NormalForm.standardForm_symm _) (F a))))

include hn hsq hw hsep in
private def diagonalReducedKernel [CharZero k]
    (hl : Function.Surjective label) : Type _ :=
  ((diagonalHom μ b label w hn hsq hw hsep).comp
    (normalizedReducedHom μ b label w hn hsq hw hsep hl).ker.incl).ker

include hn hsq hw hsep in
private noncomputable instance diagonalReducedKernelLieRing [CharZero k]
    (hl : Function.Surjective label) :
    LieRing (diagonalReducedKernel μ b label w hn hsq hw hsep hl) := by
  unfold diagonalReducedKernel
  infer_instance

include hn hsq hw hsep in
private noncomputable instance diagonalReducedKernelLieAlgebra [CharZero k]
    (hl : Function.Surjective label) :
    LieAlgebra k (diagonalReducedKernel μ b label w hn hsq hw hsep hl) := by
  unfold diagonalReducedKernel
  infer_instance

private def reducedBlockKernel (a : α) : Type _ :=
  (reducedStabilizerQuotientHom b label w a).ker

private noncomputable instance reducedBlockKernelLieRing (a : α) :
    LieRing (reducedBlockKernel b label w a) := by
  unfold reducedBlockKernel
  infer_instance

private noncomputable instance reducedBlockKernelLieAlgebra (a : α) :
    LieAlgebra k (reducedBlockKernel b label w a) := by
  unfold reducedBlockKernel
  infer_instance

include hn hsq hw hsep in
private noncomputable def diagonalReducedKernelBlockHom [CharZero k]
    (hl : Function.Surjective label) (a : α) :
    diagonalReducedKernel μ b label w hn hsq hw hsep hl →ₗ⁅k⁆
      reducedBlockKernel b label w a := by
  let N := ((diagonalHom μ b label w hn hsq hw hsep).comp
    (normalizedReducedHom μ b label w hn hsq hw hsep hl).ker.incl).ker
  have hd (x : N) (i : ι) : b.repr (x.val.val.val (b i)) i = 0 :=
    congrFun (LieHom.mem_ker.mp x.property) i
  let f : N →ₗ⁅k⁆ D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.Stabilizer.stabilizer
      (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix _ _ k))
      (blockW b label w a) :=
    Pi.codRestrictHom ((restrictDerivation μ b label w hn hsq hsep a).comp
      ((normalizedReducedHom μ b label w hn hsq hw hsep hl).ker.incl.comp N.incl)) _
      (fun x => restrictBlock_mem_stabilizer_of_diagonal_zero
        μ b label w hn hsq hw hsep hl x.val.val (hd x) a)
  refine Pi.codRestrictHom f
    (reducedStabilizerQuotientHom b label w a).ker.toLieSubalgebra (fun x => ?_)
  apply LieHom.mem_ker.mpr
  have hz := congrFun (LieHom.mem_ker.mp x.val.property) a
  have hnorm := normalizedReducedHom_of_diagonal_zero μ b label w hn hsq hw hsep hl x.val.val (hd x) a
  exact hnorm.symm.trans hz

include hn hsq hw hsep in
private theorem normalizedReducedHom_kernel_solvable [CharZero k]
    (hl : Function.Surjective label) :
    LieAlgebra.IsSolvable (normalizedReducedHom μ b label w hn hsq hw hsep hl).ker := by
  let f := normalizedReducedHom μ b label w hn hsq hw hsep hl
  let g := (diagonalHom μ b label w hn hsq hw hsep).comp f.ker.incl
  have hi : ∀ x : g.ker,
      (∀ a, diagonalReducedKernelBlockHom μ b label w hn hsq hw hsep hl a x = 0) → x = 0 := by
    intro x hx
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    have he := assemble_restrict_of_cross_zero b label x.val.val.val
      (derivation_cross_zero μ b label w hn hsq hsep x.val.val)
    apply he.symm.trans
    have hh : restrictBlock b label x.val.val.val = 0 :=
      funext (fun a => congrArg Subtype.val (congrArg Subtype.val (hx a)))
    exact (congrArg (assemble b label) hh).trans (map_zero (assemble b label))
  haveI : LieRing.IsNilpotent g.ker :=
    D5.S3.QuadraticForms.LieRadicalTransfer.nilpotent_of_triple_bracket_zero (k := k) (by
      intro x y z
      refine hi ⁅x, ⁅y, z⁆⁆ (fun a => ?_)
      let q := diagonalReducedKernelBlockHom μ b label w hn hsq hw hsep hl a
      let B : LinearMap.BilinForm k ({i : ι // label i = a} → k) :=
        Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix _ _ k)
      let W := blockW b label w a
      have hND : B.Nondegenerate :=
        LinearMap.nondegenerate_toLinearMap₂'_of_det_ne_zero' (by simp)
      exact map_triple_bracket_zero q
        (D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.Stabilizer.quotientLieHom_kernel_triple_zero
          B W (D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.NormalForm.standardForm_symm _) hND)
        x y z)
  haveI : IsLieAbelian (ι → k) :=
    ⟨fun x y => by ext i; simp [Ring.lie_def, mul_comm]⟩
  exact D5.S3.QuadraticForms.LieRadicalTransfer.solvable_of_solvable_kernel g

include hn hsq hw hsep in
private theorem productToDerivations_surjective [LieAlgebra.IsSemisimple k (derivations μ)]
    (hl : Function.Surjective label) :
    Function.Surjective (productToDerivations μ b label w hn hsq hw hsep) := by
  intro D
  let f : ∀ a, (D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.Stabilizer.stabilizer (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix _ _ k)) (D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Decomposition.blockW b label w a)) := fun a =>
    ⟨restrictBlock b label D.val a, restrictBlock_mem_stabilizer μ b label w hn hsq hw hsep hl D a⟩
  refine ⟨f, ?_⟩
  apply Subtype.ext
  exact assemble_restrict_of_cross_zero b label D.val
    ((semisimple_normalized_derivation_iff μ b label w hn hsq hw hsep D.val).mp D.property).1

include hn hsq hw hsep in
private theorem normalized_block_decomposition [LieAlgebra.IsSemisimple k (derivations μ)]
    (hl : Function.Surjective label) :
    Nonempty (derivations μ ≃ₗ⁅k⁆ ⨁ a, (D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.Stabilizer.stabilizer (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix _ _ k)) (D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Decomposition.blockW b label w a))) := by
  exact ⟨(LieEquiv.ofBijective (productToDerivations μ b label w hn hsq hw hsep)
    ⟨productToDerivations_injective μ b label w hn hsq hw hsep,
      productToDerivations_surjective μ b label w hn hsq hw hsep hl⟩).symm.trans
    (piDirectSumEquiv (k := k) _)⟩

end D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Decomposition

namespace D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Rescaling
variable {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V]
variable (μ : V →ₗ[k] V →ₗ[k] V) (b : Module.Basis ι k V)
noncomputable def squareRepresentative (a : (Set.range (fun i => k ∙ μ (b i) (b i)))) : V :=
  μ (b ((Classical.choose a.property))) (b ((Classical.choose a.property)))
private theorem representative_line (a : (Set.range (fun i => k ∙ μ (b i) (b i)))) : k ∙ squareRepresentative μ b a = a.val := by
  exact   Classical.choose_spec a.property
private theorem square_proportional_representative (i : ι) :
    ∃ t : k, t ≠ 0 ∧ μ (b i) (b i) = t • squareRepresentative μ b ((Set.rangeFactorization (fun i => k ∙ μ (b i) (b i))) i) := by
  have hh : k ∙ squareRepresentative μ b ((Set.rangeFactorization (fun i => k ∙ μ (b i) (b i))) i) = k ∙ μ (b i) (b i) :=
    representative_line μ b ((Set.rangeFactorization (fun i => k ∙ μ (b i) (b i))) i)
  obtain ⟨u, hu⟩ := Submodule.span_singleton_eq_span_singleton.mp hh
  exact ⟨u, Units.ne_zero u, hu.symm⟩
private theorem representatives_distinct_lines (a c : (Set.range (fun i => k ∙ μ (b i) (b i)))) (hac : a ≠ c) :
    k ∙ squareRepresentative μ b a ≠ k ∙ squareRepresentative μ b c := by
  rw [representative_line, representative_line]
  exact fun h => hac (Subtype.ext h)
private theorem representatives_nonzero (hs : ∀ i, μ (b i) (b i) ≠ 0) (a : (Set.range (fun i => k ∙ μ (b i) (b i)))) :
    squareRepresentative μ b a ≠ 0 := by
  exact hs _
private theorem exists_rescaled_basis [IsAlgClosed k] {α : Type*} (label : ι → α) (w : α → V)
    (hn : ∀ i j, i ≠ j → μ (b i) (b j) = 0)
    (hw : ∀ i, ∃ t : k, t ≠ 0 ∧ μ (b i) (b i) = t • w (label i)) :
    ∃ b' : Module.Basis ι k V,
      (∀ i j, i ≠ j → μ (b' i) (b' j) = 0) ∧ (∀ i, μ (b' i) (b' i) = w (label i)) := by
  classical
  choose t ht htw using hw
  choose c hc using fun i => IsAlgClosed.isSquare ((t i)⁻¹)
  have hc0 (i : ι) : c i ≠ 0 := by
    intro hz
    have hh := hc i
    rw [hz, zero_mul] at hh
    exact inv_ne_zero (ht i) hh
  let u : ι → kˣ := fun i => Units.mk0 (c i) (hc0 i)
  let b' := b.unitsSMul u
  refine ⟨b', ?_, ?_⟩
  · intro i j hij
    simp only [b', Module.Basis.unitsSMul_apply, Units.smul_def, LinearMap.map_smul₂,
      map_smul, LinearMap.smul_apply, hn i j hij, smul_zero]
  · intro i
    simp only [b', Module.Basis.unitsSMul_apply, Units.smul_def, LinearMap.map_smul₂,
      map_smul, LinearMap.smul_apply, htw i, smul_smul, u, Units.val_mk0]
    rw [← mul_assoc, ← hc i, inv_mul_cancel₀ (ht i), one_smul]
private theorem exists_class_normalization [IsAlgClosed k]
    (hn : ∀ i j, i ≠ j → μ (b i) (b j) = 0) :
    ∃ b' : Module.Basis ι k V,
      (∀ i j, i ≠ j → μ (b' i) (b' j) = 0) ∧
      (∀ i, μ (b' i) (b' i) = squareRepresentative μ b ((Set.rangeFactorization (fun i => k ∙ μ (b i) (b i))) i)) := by
  exact exists_rescaled_basis μ b (Set.rangeFactorization (fun i => k ∙ μ (b i) (b i))) (squareRepresentative μ b) hn
    (square_proportional_representative μ b)

end D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Rescaling

namespace D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Blocks
open DirectSum
open D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Rescaling D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Decomposition D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Normalized
attribute [local instance 100] LieRing.ofAssociativeRing
variable {k V ι : Type*} [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
variable [Fintype ι] (μ : V →ₗ[k] V →ₗ[k] V) (b : Module.Basis ι k V)

/-- For arbitrary nonzero natural squares, the kernel of the actual diagonal
map is a sum of pointwise orthogonal stabilizers and the remaining quotient is
abelian. This does not assert that this kernel is the solvable radical. -/
theorem nonzero_square_diagonal_kernel_decomposition [CharZero k]
    (hn : ∀ i j, i ≠ j → μ (b i) (b j) = 0)
    (hs : ∀ i, μ (b i) (b i) ≠ 0) :
    ∃ b' : Module.Basis ι k V,
      (∀ i j, i ≠ j → μ (b' i) (b' j) = 0) ∧
      (∀ i, μ (b' i) (b' i) = squareRepresentative μ b
        ((Set.rangeFactorization (fun i => k ∙ μ (b i) (b i))) i)) ∧
      ∃ K : LieIdeal k (derivations μ), IsLieAbelian (derivations μ ⧸ K) ∧
        Nonempty (K ≃ₗ⁅k⁆ ⨁ a : (Set.range (fun i => k ∙ μ (b i) (b i))),
          D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.Stabilizer.stabilizer
            (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix _ _ k))
            (blockW b' (Set.rangeFactorization (fun i => k ∙ μ (b i) (b i)))
              (squareRepresentative μ b) a)) := by
  classical
  let label := Set.rangeFactorization (fun i => k ∙ μ (b i) (b i))
  let w := squareRepresentative μ b
  letI : Fintype (Set.range (fun i => k ∙ μ (b i) (b i))) :=
    Fintype.ofSurjective label (Set.rangeFactorization_surjective (f := fun i => k ∙ μ (b i) (b i)))
  obtain ⟨b', hn', hsq'⟩ := exists_class_normalization μ b hn
  have hw : ∀ a, w a ≠ 0 := representatives_nonzero μ b hs
  have hsep : ∀ a c, a ≠ c → ∀ s t : k, s • w a + t • w c = 0 → s = 0 ∧ t = 0 := by
    intro a c hac s t h
    exact separate_of_distinct_lines (w a) (w c) (hw a) (hw c)
      (representatives_distinct_lines μ b a c hac) s t h
  refine ⟨b', hn', hsq', (diagonalHom μ b' label w hn' hsq' hw hsep).ker,
    diagonalKernel_quotient_abelian μ b' label w hn' hsq' hw hsep, ?_⟩
  exact diagonalKernel_equiv_stabilizers μ b' label w hn' hsq' hw hsep
    (Set.rangeFactorization_surjective (f := fun i => k ∙ μ (b i) (b i)))

/-- A full-derivation surjection onto the product of the nondegenerate reduced
orthogonal blocks. Its kernel is solvable, including all isotropic boundaries.
Small orthogonal blocks have deliberately not yet been discarded. -/
theorem nonzero_square_reduced_orthogonal_surjection [CharZero k]
    (hn : ∀ i j, i ≠ j → μ (b i) (b j) = 0)
    (hs : ∀ i, μ (b i) (b i) ≠ 0) :
    let α := Set.range (fun i => k ∙ μ (b i) (b i))
    let label : ι → α := Set.rangeFactorization (fun i => k ∙ μ (b i) (b i))
    let w : α → V := squareRepresentative μ b
    ∃ b' : Module.Basis ι k V,
      (∀ i j, i ≠ j → μ (b' i) (b' j) = 0) ∧
      let H : α → Type _ := fun a =>
        reducedBlockLie b' label w a
      letI : ∀ a, LieRing (H a) := fun a => inferInstance
      letI : ∀ a, LieAlgebra k (H a) := fun a => inferInstance
      ∃ f : derivations μ →ₗ⁅k⁆ ∀ a : α, H a,
        Function.Surjective f ∧ LieAlgebra.IsSolvable f.ker := by
  classical
  let label := Set.rangeFactorization (fun i => k ∙ μ (b i) (b i))
  let w := squareRepresentative μ b
  letI : Fintype (Set.range (fun i => k ∙ μ (b i) (b i))) :=
    Fintype.ofSurjective label (Set.rangeFactorization_surjective (f := fun i => k ∙ μ (b i) (b i)))
  let normalization := exists_class_normalization μ b hn
  let b' : Module.Basis ι k V := normalization.choose
  have hn' : ∀ i j, i ≠ j → μ (b' i) (b' j) = 0 := normalization.choose_spec.1
  have hsq' : ∀ i, μ (b' i) (b' i) = w (label i) := normalization.choose_spec.2
  have hw : ∀ a, w a ≠ 0 := representatives_nonzero μ b hs
  have hsep : ∀ a c, a ≠ c → ∀ s t : k, s • w a + t • w c = 0 → s = 0 ∧ t = 0 := by
    intro a c hac s t h
    exact separate_of_distinct_lines (w a) (w c) (hw a) (hw c)
      (representatives_distinct_lines μ b a c hac) s t h
  exact ⟨b', hn', normalizedReducedHom μ b' label w hn' hsq' hw hsep
    (Set.rangeFactorization_surjective (f := fun i => k ∙ μ (b i) (b i))),
    normalizedReducedHom_surjective μ b' label w hn' hsq' hw hsep
      (Set.rangeFactorization_surjective (f := fun i => k ∙ μ (b i) (b i))),
    normalizedReducedHom_kernel_solvable μ b' label w hn' hsq' hw hsep
      (Set.rangeFactorization_surjective (f := fun i => k ∙ μ (b i) (b i)))⟩

theorem nonzero_square_block_decomposition
    [LieAlgebra.IsSemisimple k (derivations μ)]
    (hn : ∀ i j, i ≠ j → μ (b i) (b j) = 0)
    (hs : ∀ i, μ (b i) (b i) ≠ 0) :
    ∃ b' : Module.Basis ι k V,
      (∀ i j, i ≠ j → μ (b' i) (b' j) = 0) ∧
      (∀ i, μ (b' i) (b' i) = squareRepresentative μ b ((Set.rangeFactorization (fun i => k ∙ μ (b i) (b i))) i)) ∧
      Nonempty (derivations μ ≃ₗ⁅k⁆ ⨁ a : (Set.range (fun i => k ∙ μ (b i) (b i))),
        D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.Stabilizer.stabilizer (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix _ _ k)) (D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Decomposition.blockW b' (Set.rangeFactorization (fun i => k ∙ μ (b i) (b i))) (squareRepresentative μ b) a)) := by
  classical
  letI : Fintype ((Set.range (fun i => k ∙ μ (b i) (b i)))) := Fintype.ofSurjective (Set.rangeFactorization (fun i => k ∙ μ (b i) (b i))) ((Set.rangeFactorization_surjective (f := fun i => k ∙ μ (b i) (b i))))
  obtain ⟨b', hn', hsq'⟩ := exists_class_normalization μ b hn
  refine ⟨b',hn',hsq',?_⟩
  apply normalized_block_decomposition μ b' (Set.rangeFactorization (fun i => k ∙ μ (b i) (b i))) (squareRepresentative μ b)
    hn' hsq' (representatives_nonzero μ b hs)
  · intro a c hac s t h
    exact separate_of_distinct_lines (squareRepresentative μ b a) (squareRepresentative μ b c)
      (representatives_nonzero μ b hs a) (representatives_nonzero μ b hs c)
      (representatives_distinct_lines μ b a c hac) s t h
  · exact (Set.rangeFactorization_surjective (f := fun i => k ∙ μ (b i) (b i)))

end D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Blocks
