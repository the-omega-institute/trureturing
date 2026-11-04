/- GID: D5/S3/QuadraticForms/EvolutionAlgebras/DerivationRadicalQuotient
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/EvolutionAlgebras/DerivationRadicalQuotient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual radical quotient of arbitrary zero-annihilator evolution derivations. -/

/-
admission_basis: escape-witness
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19944
utility none: structural Lie equivalence, not a finite certificate or algorithm.
The full dependent algebra/basis/radical-quotient telescope has no completed
registration or variation/sensitivity certificate. This uses the existing linked
escape-audit exception and makes no claim of a successful registration.
-/

import D5.S3.QuadraticForms.OrthogonalLieStructure
import D5.S3.QuadraticForms.SerreG2MatrixImage
import D5.S3.QuadraticForms.EvolutionAlgebras.AlgebraicGroupRealizationRefutation

/-!
The radical-quotient part of Corollary 8 in the supplied scientific note by
Haobo Ma, then Wenlin Zhang. The canonical general derivation equations,
normalization and stabilizer quotient maps are reused directly. Classical
orthogonal structure and solvable-extension arguments are prior mathematics.
No semisimplicity assumption on the actual derivation algebra is made.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace D5.S3.QuadraticForms.EvolutionAlgebras.DerivationRadicalQuotient

open LieAlgebra
open D5.S3.QuadraticForms.EvolutionAlgebras.DerivationAnnihilatorObstruction
open D5.S3.QuadraticForms.EvolutionAlgebras.NondegenerateDerivationBlocks
open D5.S3.QuadraticForms.EvolutionAlgebras.SemisimpleDerivationClassification
open D5.S3.QuadraticForms.OrthogonalPointwiseStabilizers

attribute [local instance 100] LieRing.ofAssociativeRing

variable {k V ι : Type*} [Field k] [IsAlgClosed k] [CharZero k]
variable [AddCommGroup V] [Module k V] [Fintype ι]

/-- The full actual derivation algebra surjects onto its nondegenerate reduced
orthogonal blocks with solvable kernel; sizes zero through two remain here. -/
theorem orthogonal_surjection
    (μ : V →ₗ[k] V →ₗ[k] V) (b : Module.Basis ι k V)
    (hn : ∀ i j, i ≠ j → μ (b i) (b j) = 0)
    (hs : ∀ i, μ (b i) (b i) ≠ 0) :
    ∃ r : ℕ, ∃ m : Fin r → ℕ,
      ∃ f : derivations μ →ₗ⁅k⁆ ∀ a, Orthogonal.so (Fin (m a)) k,
        Function.Surjective f ∧ IsSolvable f.ker := by
  classical
  obtain ⟨b', hn', f, hf, hker⟩ :=
    Blocks.nonzero_square_reduced_orthogonal_surjection μ b hn hs
  let α := Set.range (fun i => k ∙ μ (b i) (b i))
  let label := Set.rangeFactorization (fun i => k ∙ μ (b i) (b i))
  let w := Rescaling.squareRepresentative μ b
  letI : Fintype α := Fintype.ofSurjective label (Set.rangeFactorization_surjective _)
  let B (a : α) : LinearMap.BilinForm k ({i : ι // label i = a} → k) :=
    Matrix.toLinearMap₂' k (S₁ := k) (S₂ := k) 1
  let W (a : α) := Decomposition.blockW b' label w a
  have he (a : α) : ∃ m : ℕ,
      Nonempty (skewAdjointLieSubalgebra (Decomposition.reducedBlockForm b' label w a) ≃ₗ⁅k⁆
        Orthogonal.so (Fin m) k) := by
    exact ⟨_, NormalForm.skewAdjoint_equiv_so _
      (Stabilizer.quotientForm_symm (B a) (W a) (NormalForm.standardForm_symm _))
      (Stabilizer.quotientForm_nondegenerate (B a) (W a) (NormalForm.standardForm_symm _))⟩
  choose m he using he
  let e := PiAssembly.piCongr _ (fun a => (he a).some)
  let q := PiAssembly.reindex (fun a => Orthogonal.so (Fin (m a)) k) (Fintype.equivFin α)
  let E := e.trans q
  refine ⟨Fintype.card α, fun a => m ((Fintype.equivFin α).symm a),
    E.toLieHom.comp f, E.surjective.comp hf, ?_⟩
  have hh : (E.toLieHom.comp f).ker = f.ker := by
    ext x
    simp only [LieHom.mem_ker, LieHom.comp_apply, LieEquiv.coe_toLieHom,
      map_eq_zero_iff E E.injective]
  rw [hh]
  exact hker

variable {α : Type*} [Fintype α] (m : α → ℕ)

private def keepLarge : (∀ a, Orthogonal.so (Fin (m a)) k) →ₗ⁅k⁆
    ∀ a : {a // 3 ≤ m a}, Orthogonal.so (Fin (m a.val)) k :=
  { LinearMap.pi (fun a => LinearMap.proj a.val) with map_lie' := fun {x y} => rfl }

private theorem keepLarge_surjective : Function.Surjective (keepLarge (k := k) m) := by
  classical
  intro x
  refine ⟨fun a => if h : 3 ≤ m a then x ⟨a,h⟩ else 0, ?_⟩
  funext a
  exact dif_pos a.property

/-- The discarded standard orthogonal factors are abelian: dimensions zero and
one vanish, and the dimension-two factor is one-dimensional and abelian. -/
private theorem keepLarge_kernel_abelian : IsLieAbelian (keepLarge (k := k) m).ker := by
  constructor
  intro x y
  apply Subtype.ext
  funext a
  change ⁅x.val a, y.val a⁆ = 0
  by_cases ha : 3 ≤ m a
  · have hx : x.val a = 0 := congrFun (LieHom.mem_ker.mp x.property) ⟨a,ha⟩
    rw [hx, zero_lie]
  · have hm : m a ≤ 2 := by omega
    by_cases htwo : m a = 2
    · haveI : IsLieAbelian (Orthogonal.so (Fin (m a)) k) := by
        rw [htwo]
        exact SmallOrthogonal.so_two_abelian
      exact trivial_lie_zero _ _ _ _
    · haveI : Subsingleton (Orthogonal.so (Fin (m a)) k) :=
        SmallOrthogonal.subsingleton_of_dimension_le_one _ (by omega)
      exact Subsingleton.elim _ _

/-- The complete radical-quotient statement for a finite natural basis with
nonzero squares. The finite sum may be empty. -/
theorem quotient_of_nonzero_squares [FiniteDimensional k V]
    (μ : V →ₗ[k] V →ₗ[k] V) (b : Module.Basis ι k V)
    (hn : ∀ i j, i ≠ j → μ (b i) (b j) = 0)
    (hs : ∀ i, μ (b i) (b i) ≠ 0) :
    ∃ r : ℕ, ∃ m : Fin r → ℕ, (∀ a, 3 ≤ m a) ∧
      Nonempty ((derivations μ ⧸ radical k (derivations μ)) ≃ₗ⁅k⁆
        ⨁ a, Orthogonal.so (Fin (m a)) k) := by
  classical
  obtain ⟨r,m,f,hf,hker⟩ := orthogonal_surjection μ b hn hs
  let p := keepLarge (k := k) m
  haveI : IsSolvable f.ker := hker
  haveI : IsLieAbelian p.ker := keepLarge_kernel_abelian m
  let g := p.comp f
  haveI : IsSolvable g.ker :=
    D5.S3.QuadraticForms.LieRadicalTransfer.solvable_comap f p.ker
  let H (a : {a : Fin r // 3 ≤ m a}) := Orthogonal.so (Fin (m a.val)) k
  haveI (a : {a : Fin r // 3 ≤ m a}) : HasTrivialRadical k (H a) :=
    D5.S3.QuadraticForms.OrthogonalLieStructure.hasTrivialRadical _ a.property
  let ev (a : {a : Fin r // 3 ≤ m a}) : (∀ a, H a) →ₗ⁅k⁆ H a :=
    { LinearMap.proj a with map_lie' := fun {x y} => rfl }
  have hev (a : {a : Fin r // 3 ≤ m a}) : Function.Surjective (ev a) := by
    intro x
    exact ⟨Pi.single a x, Pi.single_eq_same a x⟩
  haveI : HasTrivialRadical k (∀ a, H a) :=
    D5.S3.QuadraticForms.LieRadicalTransfer.hasTrivialRadical_of_separating_surjections
      H ev hev (fun x hx => funext hx)
  let E := D5.S3.QuadraticForms.LieRadicalTransfer.quotientEquiv_of_solvable_kernel g
    ((keepLarge_surjective m).comp hf)
  let q := Fintype.equivFin {a : Fin r // 3 ≤ m a}
  let R := PiAssembly.reindex H q
  refine ⟨Fintype.card {a : Fin r // 3 ≤ m a}, fun a => m (q.symm a).val,
    fun a => (q.symm a).property, ?_⟩
  exact ⟨(E.trans R).trans (BlockLinear.piDirectSumEquiv (k := k) _)⟩

/-- Every finite-dimensional actual evolution algebra with zero annihilator,
over every algebraically closed characteristic-zero field, has an actual
orthogonal solvable-radical quotient. No condition on its square or on the
semisimplicity of its derivations is imposed. -/
theorem result [FiniteDimensional k V]
    (μ : V →ₗ[k] V →ₗ[k] V) (hE : IsEvolutionAlgebra μ)
    (hAnn : LinearMap.ker μ = ⊥) :
    ∃ r : ℕ, ∃ m : Fin r → ℕ, (∀ a, 3 ≤ m a) ∧
      Nonempty ((derivations μ ⧸ radical k (derivations μ)) ≃ₗ⁅k⁆
        ⨁ a, Orthogonal.so (Fin (m a)) k) := by
  classical
  obtain ⟨hc,ι,b,hn⟩ := hE
  letI : Fintype ι := FiniteDimensional.fintypeBasisIndex b
  have hs (i : ι) : μ (b i) (b i) ≠ 0 := by
    intro hi
    have hz := Annihilator.zero_square_mem_ann μ b hn i hi
    rw [hAnn, Submodule.mem_bot] at hz
    exact b.ne_zero i hz
  exact quotient_of_nonzero_squares μ b hn hs

/-- Every actual nonabelian simple ideal of actual derivations is an orthogonal
simple type. The dimension-four factor is split into its two actual factors. -/
theorem simple_ideal_type [FiniteDimensional k V]
    (μ : V →ₗ[k] V →ₗ[k] V) (hE : IsEvolutionAlgebra μ)
    (hAnn : LinearMap.ker μ = ⊥) (I : LieIdeal k (derivations μ)) [IsSimple k I] :
    ∃ m : ℕ, (m = 3 ∨ 5 ≤ m) ∧ Nonempty (I ≃ₗ⁅k⁆ Orthogonal.so (Fin m) k) := by
  classical
  obtain ⟨hc,ι,b,hn⟩ := hE
  letI : Fintype ι := FiniteDimensional.fintypeBasisIndex b
  have hs (i : ι) : μ (b i) (b i) ≠ 0 := by
    intro hi
    have hz := Annihilator.zero_square_mem_ann μ b hn i hi
    rw [hAnn, Submodule.mem_bot] at hz
    exact b.ne_zero i hz
  obtain ⟨r,m,f,hf,hker⟩ := orthogonal_surjection μ b hn hs
  let p := keepLarge (k := k) m
  let g := p.comp f
  haveI : IsSolvable f.ker := hker
  haveI : IsLieAbelian p.ker := keepLarge_kernel_abelian m
  haveI : IsSolvable g.ker :=
    D5.S3.QuadraticForms.LieRadicalTransfer.solvable_comap f p.ker
  have hinj := D5.S3.QuadraticForms.LieRadicalTransfer.injective_on_simple_ideal g I
  haveI : Nontrivial I := IsSimple.nontrivial k
  obtain ⟨x,hx⟩ := exists_ne (0 : I)
  have hgx : g x.val ≠ 0 := by
    intro hh
    apply hx
    apply hinj
    simpa using hh
  obtain ⟨a,ha⟩ : ∃ a : {a : Fin r // 3 ≤ m a}, g x.val a ≠ 0 := by
    by_contra! h
    apply hgx
    funext a
    exact h a
  let ev : (∀ a : {a : Fin r // 3 ≤ m a}, Orthogonal.so (Fin (m a.val)) k) →ₗ⁅k⁆
      Orthogonal.so (Fin (m a.val)) k :=
    { LinearMap.proj a with map_lie' := fun {x y} => rfl }
  have hev : Function.Surjective ev := fun y => ⟨Pi.single a y, Pi.single_eq_same a y⟩
  let F := ev.comp g
  have hF : Function.Surjective F := hev.comp ((keepLarge_surjective m).comp hf)
  by_cases hfour : m a.val = 4
  · let e4 : Orthogonal.so (Fin (m a.val)) k ≃ₗ⁅k⁆ Orthogonal.so (Fin 4) k := by
      rw [hfour]
      exact LieEquiv.refl k _
    let e := e4.trans (D5.S3.QuadraticForms.OrthogonalLieStructure.soFourEquiv (k := k))
    let F4 := e.toLieHom.comp F
    have hF4 : Function.Surjective F4 := e.surjective.comp hF
    have h4x : F4 x.val ≠ 0 := by
      intro h
      apply ha
      exact e.injective (by simpa using h)
    haveI : IsSimple k (Orthogonal.so (Fin 3) k) :=
      D5.S3.QuadraticForms.OrthogonalLieStructure.isSimple_of_card_ne_four (by simp) (by simp)
    refine ⟨3, Or.inl rfl, ?_⟩
    by_cases hfst : (F4 x.val).1 = 0
    · have hsnd : (F4 x.val).2 ≠ 0 := by
        intro h
        apply h4x
        exact Prod.ext hfst h
      exact ⟨D5.S3.QuadraticForms.LieRadicalTransfer.simpleIdealEquiv_of_surjection
        ((LieHom.snd k _ _).comp F4) (LieHom.snd_surjective.comp hF4) I ⟨x,hsnd⟩⟩
    · exact ⟨D5.S3.QuadraticForms.LieRadicalTransfer.simpleIdealEquiv_of_surjection
        ((LieHom.fst k _ _).comp F4) (LieHom.fst_surjective.comp hF4) I ⟨x,hfst⟩⟩
  · haveI : IsSimple k (Orthogonal.so (Fin (m a.val)) k) :=
      D5.S3.QuadraticForms.OrthogonalLieStructure.isSimple_of_card_ne_four
        (by simpa using a.property) (by simpa using hfour)
    exact ⟨m a.val, by omega,
      ⟨D5.S3.QuadraticForms.LieRadicalTransfer.simpleIdealEquiv_of_surjection F hF I ⟨x,ha⟩⟩⟩

private theorem orthogonal_dimension_exclusions (m : ℕ) :
    m.choose 2 ≠ 8 ∧ m.choose 2 ≠ 14 := by
  by_cases hm : m ≤ 5
  · interval_cases m <;> norm_num
  · have hb : 15 ≤ m.choose 2 := by
      simpa using (Nat.choose_le_choose 2 (show 6 ≤ m by omega))
    constructor <;> omega

/-- The exclusion concerns actual simple ideals, rather than arbitrary
subalgebras or faithful actions. -/
theorem simple_ideal_not_sl3 [FiniteDimensional k V]
    (μ : V →ₗ[k] V →ₗ[k] V) (hE : IsEvolutionAlgebra μ)
    (hAnn : LinearMap.ker μ = ⊥) (I : LieIdeal k (derivations μ)) [IsSimple k I] :
    ¬ Nonempty (I ≃ₗ⁅k⁆ SpecialLinear.sl (Fin 3) k) := by
  rintro ⟨e⟩
  obtain ⟨m,hm,⟨es⟩⟩ := simple_ideal_type μ hE hAnn I
  have hdim := (e.symm.trans es).toLinearEquiv.finrank_eq
  rw [AlgebraicGroupRealizationRefutation.Dimensions.sl3_finrank,
    AlgebraicGroupRealizationRefutation.Dimensions.so_finrank] at hdim
  exact (orthogonal_dimension_exclusions m).1 hdim.symm

/-- This excludes mathlib's actual standard Serre G2 object. Under a
hypothetical isomorphism, simplicity of the actual ideal makes the proved
Serre-to-matrix surjection a Lie equivalence. Its fourteen-dimensional image
then contradicts every possible orthogonal simple-factor dimension. -/
theorem simple_ideal_not_g2 [FiniteDimensional k V]
    (μ : V →ₗ[k] V →ₗ[k] V) (hE : IsEvolutionAlgebra μ)
    (hAnn : LinearMap.ker μ = ⊥) (I : LieIdeal k (derivations μ)) [IsSimple k I] :
    ¬ Nonempty (I ≃ₗ⁅k⁆ LieAlgebra.g₂ k) := by
  rintro ⟨e⟩
  haveI : IsSimple k (LieAlgebra.g₂ k) :=
    D5.S3.QuadraticForms.LieRadicalTransfer.isSimple_of_equiv e
  let E := e.trans (D5.S3.QuadraticForms.SerreG2MatrixImage.correspondence_of_isSimple (k := k))
  obtain ⟨m,hm,⟨es⟩⟩ := simple_ideal_type μ hE hAnn I
  have hdim := (E.symm.trans es).toLinearEquiv.finrank_eq
  rw [D5.S3.QuadraticForms.SerreG2MatrixImage.matrixImage_finrank,
    AlgebraicGroupRealizationRefutation.Dimensions.so_finrank] at hdim
  exact (orthogonal_dimension_exclusions m).2 hdim.symm

/-- Complete K2 over its original domain: an actual radical quotient and all
actual nonabelian simple-ideal types and exclusions. Empty and degenerate
orthogonal reductions are included by construction. -/
theorem complete [FiniteDimensional k V]
    (μ : V →ₗ[k] V →ₗ[k] V) (hE : IsEvolutionAlgebra μ)
    (hAnn : LinearMap.ker μ = ⊥) :
    (∃ r : ℕ, ∃ m : Fin r → ℕ, (∀ a, 3 ≤ m a) ∧
      Nonempty ((derivations μ ⧸ radical k (derivations μ)) ≃ₗ⁅k⁆
        ⨁ a, Orthogonal.so (Fin (m a)) k)) ∧
    (∀ I : LieIdeal k (derivations μ), IsSimple k I →
      (∃ m : ℕ, (m = 3 ∨ 5 ≤ m) ∧ Nonempty (I ≃ₗ⁅k⁆ Orthogonal.so (Fin m) k)) ∧
      ¬ Nonempty (I ≃ₗ⁅k⁆ SpecialLinear.sl (Fin 3) k) ∧
      ¬ Nonempty (I ≃ₗ⁅k⁆ LieAlgebra.g₂ k)) := by
  refine ⟨result μ hE hAnn, ?_⟩
  intro I hI
  letI : IsSimple k I := hI
  exact ⟨simple_ideal_type μ hE hAnn I, simple_ideal_not_sl3 μ hE hAnn I,
    simple_ideal_not_g2 μ hE hAnn I⟩

end D5.S3.QuadraticForms.EvolutionAlgebras.DerivationRadicalQuotient
