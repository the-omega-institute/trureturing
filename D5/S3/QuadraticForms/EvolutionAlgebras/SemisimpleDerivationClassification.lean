/- GID: D5/S3/QuadraticForms/EvolutionAlgebras/SemisimpleDerivationClassification
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/EvolutionAlgebras/SemisimpleDerivationClassification
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Semisimple evolution derivations are sums of orthogonal Lie algebras. -/

/-
admission_basis: open-problem-resolution (#18575; Proved)
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19944
utility none: structural existence and Lie equivalences; no finite certificate or algorithm.
  RadicalTransfer.trivialRadical_of_equiv: proof_shape: bind-only; escape_witness: none;
    consumers: result, trim_orthogonal_product
  RadicalTransfer.coordinateIdeal: proof_shape: bind-only; escape_witness: none;
    consumers: RadicalTransfer.coordinateIdeal_abelian, RadicalTransfer.factor_trivialRadical
  RadicalTransfer.coordinateIdeal_abelian: proof_shape: bind-only; escape_witness: none;
    consumers: RadicalTransfer.factor_trivialRadical
  RadicalTransfer.factor_trivialRadical: proof_shape: bind-only; escape_witness: none;
    consumers: result, trim_orthogonal_product
  SmallOrthogonal.diagonal_zero: proof_shape: bind-only; escape_witness: none;
    consumers: SmallOrthogonal.so_two_abelian, SmallOrthogonal.subsingleton_of_dimension_le_one
  SmallOrthogonal.coefficient_skew: proof_shape: bind-only; escape_witness: none;
    consumers: SmallOrthogonal.so_two_abelian
  SmallOrthogonal.subsingleton_of_dimension_le_one: proof_shape: bind-only; escape_witness: none;
    consumers: trim_orthogonal_product
  SmallOrthogonal.so_two_abelian: proof_shape: bind-only; escape_witness: none;
    consumers: trim_orthogonal_product
  SmallOrthogonal.so_two_nontrivial: proof_shape: bind-only; escape_witness: none;
    consumers: trim_orthogonal_product
  PiAssembly.piCongr: proof_shape: bind-only; escape_witness: none;
    consumers: result
  PiAssembly.reindex: proof_shape: bind-only; escape_witness: none;
    consumers: trim_orthogonal_product
  PiAssembly.omitSubsingleton: proof_shape: bind-only; escape_witness: none;
    consumers: trim_orthogonal_product
  claim: proof_shape: bind-only; escape_witness: none;
    consumers: result
  trim_orthogonal_product: proof_shape: bind-only; escape_witness: none;
    consumers: result
  result: proof_shape: content; escape_witness: none;
    consumers: external settling endpoint
-/

import D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction
import D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers
import D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks


attribute [local instance] Classical.propDecidable

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification.RadicalTransfer
variable {k L N : Type*} [Field k] [LieRing L] [LieAlgebra k L]
variable [LieRing N] [LieAlgebra k N]
private theorem trivialRadical_of_equiv [LieAlgebra.HasTrivialRadical k L]
    (e : L ≃ₗ⁅k⁆ N) : LieAlgebra.HasTrivialRadical k N := by
  apply (LieAlgebra.hasTrivialRadical_iff_no_abelian_ideals k N).mpr
  intro I hI
  letI : IsLieAbelian I := hI
  let J : LieIdeal k L := I.comap e.toLieHom
  haveI : IsLieAbelian J := by
    constructor
    intro x y
    apply Subtype.ext
    apply e.injective
    change e ⁅x.val,y.val⁆ = e 0
    rw [map_zero, e.map_lie]
    have hh := trivial_lie_zero I I
      (⟨e x.val,x.property⟩ : I) (⟨e y.val,y.property⟩ : I)
    exact congrArg Subtype.val hh
  have hJ : J = ⊥ := LieAlgebra.HasTrivialRadical.eq_bot_of_isSolvable _
  apply le_antisymm ?_ bot_le
  intro x hx
  have hy : e.symm x ∈ J := by
    change e (e.symm x) ∈ I
    simpa only [e.apply_symm_apply] using hx
  have hy0 : e.symm x = 0 := by simpa only [hJ, LieSubmodule.mem_bot] using hy
  change x = 0
  simpa only [e.apply_symm_apply,map_zero] using congrArg e hy0

variable {α : Type*} (H : α → Type*) [∀ a, LieRing (H a)] [∀ a, LieAlgebra k (H a)]
private def coordinateIdeal (a : α) (I : LieIdeal k (H a)) : LieIdeal k (∀ a, H a) where
  carrier := {f | f a ∈ I ∧ ∀ c, c ≠ a → f c = 0}
  zero_mem' := ⟨I.zero_mem,by simp⟩
  add_mem' := by
    rintro f g ⟨hf,hf0⟩ ⟨hg,hg0⟩
    exact ⟨I.add_mem hf hg, fun c hc => by simp only [Pi.add_apply,hf0 c hc,hg0 c hc,add_zero]⟩
  smul_mem' := by
    rintro t f ⟨hf,hf0⟩
    exact ⟨I.smul_mem t hf, fun c hc => by simp only [Pi.smul_apply,hf0 c hc,smul_zero]⟩
  lie_mem := by
    intro f g hg
    refine ⟨I.lie_mem hg.1,?_⟩
    intro c hc
    change ⁅f c,g c⁆ = 0
    rw [hg.2 c hc,lie_zero]
private theorem coordinateIdeal_abelian (a : α) (I : LieIdeal k (H a)) [IsLieAbelian I] :
    IsLieAbelian (coordinateIdeal H a I) := by
  constructor
  intro f g
  apply Subtype.ext
  funext c
  change ⁅f.val c,g.val c⁆ = 0
  by_cases hc : c = a
  · subst c
    have hh := trivial_lie_zero I I
      (⟨f.val a,f.property.1⟩ : I) (⟨g.val a,g.property.1⟩ : I)
    exact congrArg Subtype.val hh
  · rw [f.property.2 c hc,zero_lie]
private theorem factor_trivialRadical [LieAlgebra.HasTrivialRadical k (∀ a, H a)] (a : α) :
    LieAlgebra.HasTrivialRadical k (H a) := by
  classical
  apply (LieAlgebra.hasTrivialRadical_iff_no_abelian_ideals k (H a)).mpr
  intro I hI
  haveI := hI
  haveI : IsLieAbelian (coordinateIdeal H a I) := coordinateIdeal_abelian H a I
  have hJ : coordinateIdeal H a I = ⊥ := LieAlgebra.HasTrivialRadical.eq_bot_of_isSolvable _
  apply le_antisymm ?_ bot_le
  intro x hx
  let F : ∀ a, H a := Pi.single a x
  have hF : F ∈ coordinateIdeal H a I := by
    refine ⟨?_,?_⟩
    · simpa only [F,Pi.single_eq_same] using hx
    · intro c hc
      exact Pi.single_eq_of_ne hc x
  have hz : F = 0 := by simpa only [hJ,LieSubmodule.mem_bot] using hF
  change x = 0
  simpa only [F,Pi.single_eq_same,Pi.zero_apply] using congrFun hz a

end D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification.RadicalTransfer

namespace D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification.SmallOrthogonal
attribute [local instance 100] LieRing.ofAssociativeRing
variable {k : Type*} [Field k] [CharZero k]
private theorem diagonal_zero {n : Type*} [Fintype n] [DecidableEq n]
    (A : LieAlgebra.Orthogonal.so n k) (i : n) : A.val i i = 0 := by
  have h := congrArg (fun M : Matrix n n k => M i i)
    ((LieAlgebra.Orthogonal.mem_so n k A.val).mp A.property)
  change A.val i i = -A.val i i at h
  have ht : 2 * A.val i i = 0 := by
    rw [two_mul]
    exact eq_neg_iff_add_eq_zero.mp h
  exact (mul_eq_zero.mp ht).resolve_left two_ne_zero
private theorem coefficient_skew {n : Type*} [Fintype n] [DecidableEq n]
    (A : LieAlgebra.Orthogonal.so n k) (i j : n) : A.val j i = -A.val i j := by
  exact congrArg (fun M : Matrix n n k => M i j)
    ((LieAlgebra.Orthogonal.mem_so n k A.val).mp A.property)
private theorem subsingleton_of_dimension_le_one (m : ℕ) (hm : m ≤ 1) :
    Subsingleton (LieAlgebra.Orthogonal.so (Fin m) k) := by
  have hz (A : LieAlgebra.Orthogonal.so (Fin m) k) : A.val = 0 := by
    ext i j
    have hij : i = j := Fin.ext (by omega)
    subst j
    exact diagonal_zero A i
  constructor
  intro A B
  exact Subtype.ext ((hz A).trans (hz B).symm)
private theorem so_two_abelian : IsLieAbelian (LieAlgebra.Orthogonal.so (Fin 2) k) := by
  have hnormal (C : LieAlgebra.Orthogonal.so (Fin 2) k) :
      C.val = !![0,C.val 0 1;-C.val 0 1,0] := by
    ext i j
    fin_cases i <;> fin_cases j
    · change C.val 0 0 = 0
      exact diagonal_zero C 0
    · rfl
    · change C.val 1 0 = -C.val 0 1
      exact coefficient_skew C 0 1
    · change C.val 1 1 = 0
      exact diagonal_zero C 1
  constructor
  intro A B
  apply Subtype.ext
  change (A.val * B.val - B.val * A.val : Matrix (Fin 2) (Fin 2) k) = 0
  rw [hnormal A,hnormal B]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two] <;> ring
private theorem so_two_nontrivial : Nontrivial (LieAlgebra.Orthogonal.so (Fin 2) k) := by
  let A : LieAlgebra.Orthogonal.so (Fin 2) k := ⟨!![0,1;-1,0],by
    rw [LieAlgebra.Orthogonal.mem_so]
    ext i j
    fin_cases i <;> fin_cases j <;> simp⟩
  refine ⟨⟨A,0,?_⟩⟩
  intro h
  have hh := congrArg (fun F : LieAlgebra.Orthogonal.so (Fin 2) k => F.val 0 1) h
  exact one_ne_zero hh

end D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification.SmallOrthogonal

namespace D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification.PiAssembly
open DirectSum
variable {k α β : Type*} [Field k]
variable (H : α → Type*) [∀ a,LieRing (H a)] [∀ a,LieAlgebra k (H a)]

private noncomputable def piCongr {J : α → Type*} [∀ a,LieRing (J a)] [∀ a,LieAlgebra k (J a)]
    (e : ∀ a,H a ≃ₗ⁅k⁆ J a) : (∀ a,H a) ≃ₗ⁅k⁆ ∀ a,J a :=
  { LinearEquiv.piCongrRight (fun a => (e a).toLinearEquiv) with
    map_lie' := by intro f g; funext a; exact (e a).map_lie (f a) (g a) }

private noncomputable def reindex (e : α ≃ β) :
    (∀ a,H a) ≃ₗ⁅k⁆ ∀ b,H (e.symm b) :=
  { LinearEquiv.piCongrLeft' k H e with
    map_lie' := by intro f g; funext b; rfl }

private noncomputable def omitSubsingleton (p : α → Prop) [DecidablePred p]
    (hs : ∀ a,¬p a → Subsingleton (H a)) :
    (∀ a,H a) ≃ₗ⁅k⁆ ∀ a : {a // p a},H a.val := by
  let r : (∀ a, H a) →ₗ[k] ∀ a : {a // p a}, H a.val :=
    LinearMap.pi (fun a => LinearMap.proj a.val)
  have hr : Function.Bijective r := by
    constructor
    · intro f g h
      funext a
      by_cases ha : p a
      · exact congrFun h ⟨a, ha⟩
      · letI := hs a ha
        exact Subsingleton.elim _ _
    · intro g
      refine ⟨fun a => if h : p a then g ⟨a, h⟩ else 0, ?_⟩
      funext a
      exact dif_pos a.property
  exact { LinearEquiv.ofBijective r hr with map_lie' := by intro f g; rfl }

end D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification.PiAssembly

namespace D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification
open DirectSum D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction
attribute [local instance 100] LieRing.ofAssociativeRing
variable {k : Type*} [Field k] [CharZero k]

/-- Conjecture 5 (Semisimple derivation algebras): over an algebraically closed field of
characteristic `0`, if `Der(A)` is semisimple for a finite-dimensional evolution algebra `A`, then
`Der(A) ≅ ⊕ᵢ 𝔰𝔬_{mᵢ}` with every `mᵢ ≥ 3`. -/
def claim : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (V : Type) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (μ : V →ₗ[k] V →ₗ[k] V),
    IsEvolutionAlgebra μ → LieAlgebra.IsSemisimple k (derivations μ) →
      ∃ (r : ℕ) (m : Fin r → ℕ), (∀ i, 3 ≤ m i) ∧
        Nonempty (derivations μ ≃ₗ⁅k⁆ ⨁ i : Fin r, LieAlgebra.Orthogonal.so (Fin (m i)) k)
private theorem trim_orthogonal_product {α L : Type*} [Fintype α] [LieRing L] [LieAlgebra k L]
    [LieAlgebra.HasTrivialRadical k L] (m : α → ℕ)
    (e : L ≃ₗ⁅k⁆ ∀ a,LieAlgebra.Orthogonal.so (Fin (m a)) k) :
    ∃ (r : ℕ) (m' : Fin r → ℕ), (∀ i,3 ≤ m' i) ∧
      Nonempty (L ≃ₗ⁅k⁆ ⨁ i : Fin r,LieAlgebra.Orthogonal.so (Fin (m' i)) k) := by
  classical
  let H : α → Type _ := fun a => LieAlgebra.Orthogonal.so (Fin (m a)) k
  letI : LieAlgebra.HasTrivialRadical k (∀ a,H a) := D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification.RadicalTransfer.trivialRadical_of_equiv e
  have hm2 (a : α) : m a ≠ 2 := by
    intro heq
    have hR := D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification.RadicalTransfer.factor_trivialRadical (k := k) H a
    change LieAlgebra.HasTrivialRadical k (LieAlgebra.Orthogonal.so (Fin (m a)) k) at hR
    rw [heq] at hR
    letI := hR
    letI := D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification.SmallOrthogonal.so_two_abelian (k := k)
    letI := LieAlgebra.subsingleton_of_hasTrivialRadical_lie_abelian k
      (LieAlgebra.Orthogonal.so (Fin 2) k)
    letI := D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification.SmallOrthogonal.so_two_nontrivial (k := k)
    obtain ⟨x,y,hxy⟩ := exists_pair_ne (LieAlgebra.Orthogonal.so (Fin 2) k)
    exact hxy (Subsingleton.elim x y)
  have hsmall (a : α) (ha : ¬3 ≤ m a) : Subsingleton (H a) := by
    apply D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification.SmallOrthogonal.subsingleton_of_dimension_le_one (k := k) (m a)
    have := hm2 a
    omega
  let β := {a : α // 3 ≤ m a}
  let e1 := D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification.PiAssembly.omitSubsingleton (k := k) H (fun a => 3 ≤ m a) hsmall
  let ef : β ≃ Fin (Fintype.card β) := Fintype.equivFin β
  let e2 := D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification.PiAssembly.reindex (k := k) (fun a : β => H a.val) ef
  refine ⟨Fintype.card β,fun i => m (ef.symm i).val,fun i => (ef.symm i).property,?_⟩
  exact ⟨((e.trans e1).trans e2).trans (D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.BlockLinear.piDirectSumEquiv (k := k)
    (fun i : Fin (Fintype.card β) => LieAlgebra.Orthogonal.so (Fin (m (ef.symm i).val)) k))⟩
theorem result : claim := by
  intro k _ _ _ V _ _ _ μ hE hL
  classical
  letI : LieAlgebra.IsSemisimple k (derivations μ) := hL
  obtain ⟨hc,ι,b,hn⟩ := hE
  letI : Fintype ι := FiniteDimensional.fintypeBasisIndex b
  have hs : ∀ i,μ (b i) (b i) ≠ 0 :=
    D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction.Annihilator.semisimple_natural_squares_ne_zero μ hc b hn
  obtain ⟨b',hn',hsq',⟨e⟩⟩ := D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Blocks.nonzero_square_block_decomposition μ b hn hs
  let α := (Set.range (fun i => k ∙ μ (b i) (b i)))
  let label : ι → α := (Set.rangeFactorization (fun i => k ∙ μ (b i) (b i)))
  let w : α → V := D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Rescaling.squareRepresentative μ b
  letI : Fintype α := Fintype.ofSurjective label ((Set.rangeFactorization_surjective (f := fun i => k ∙ μ (b i) (b i))))
  let H : α → Type _ := fun a => (D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.Stabilizer.stabilizer (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix _ _ k)) (D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Decomposition.blockW b' label w a))
  let ePi : derivations μ ≃ₗ⁅k⁆ ∀ a,H a :=
    e.trans (D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.BlockLinear.piDirectSumEquiv (k := k) H).symm
  letI : LieAlgebra.HasTrivialRadical k (∀ a,H a) := D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification.RadicalTransfer.trivialRadical_of_equiv ePi
  let B (a : α) : LinearMap.BilinForm k (({i : ι // label i = a} → k)) := (Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) (1 : Matrix _ _ k))
  let W (a : α) := D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks.Decomposition.blockW b' label w a
  let Q (a : α) := ((B a).orthogonal (W a)) ⧸ (LinearMap.ker ((B a).restrict ((B a).orthogonal (W a))))
  let m (a : α) := Module.finrank k (Q a)
  have hstd (a : α) : Nonempty (H a ≃ₗ⁅k⁆ LieAlgebra.Orthogonal.so (Fin (m a)) k) := by
    letI : LieAlgebra.HasTrivialRadical k (H a) := D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification.RadicalTransfer.factor_trivialRadical (k := k) H a
    have hB : (B a).IsSymm := D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.NormalForm.standardForm_symm _
    have hND : (B a).Nondegenerate := LinearMap.nondegenerate_toLinearMap₂'_of_det_ne_zero' (by simp)
    letI : LieAlgebra.HasTrivialRadical k (D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.Stabilizer.stabilizer (B a) (W a)) := by
      change LieAlgebra.HasTrivialRadical k (H a)
      infer_instance
    obtain ⟨e1⟩ := D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.Stabilizer.stabilizer_equiv_of_trivialRadical (B a) (W a) hB hND
    obtain ⟨e2⟩ := D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.NormalForm.skewAdjoint_equiv_so
      ((LinearMap.IsRefl.liftQ₂ ((B a).restrict ((B a).orthogonal (W a))) (LinearMap.ker ((B a).restrict ((B a).orthogonal (W a)))) (fun x y => hB.isRefl x.val y.val) le_rfl))
      (D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.Stabilizer.quotientForm_symm (B a) (W a) hB)
      (D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers.Stabilizer.quotientForm_nondegenerate (B a) (W a) hB)
    exact ⟨e1.trans e2⟩
  let eStd (a : α) := Classical.choice (hstd a)
  let eFull := ePi.trans (D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification.PiAssembly.piCongr H eStd)
  exact trim_orthogonal_product m eFull

end D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification
