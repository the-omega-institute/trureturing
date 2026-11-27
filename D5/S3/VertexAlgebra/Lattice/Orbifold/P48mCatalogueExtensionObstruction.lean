/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48mCatalogueExtensionObstruction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48mCatalogueExtensionObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The P48m catalogue block forces two actual extension weight-two states. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48mCatalogueZeroBlock
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48mConformalActionObstruction

/-!
The external lattice identification supplies the rootless positive Gram data,
its full isometry group, and the rational coordinate basis in which the six
catalogue matrices act by right multiplication. In that basis the kernel-checked
zero block and the generation hypothesis yield a proper invariant Cartan block.
The actual untwisted modes then give two independent fixed weight-two states.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48mCatalogueExtensionObstruction

open LatticeGeneratingFieldLocality (LatticeData Charge Carrier bilinear)
open LatticeActualConformalState (omega)
open LatticePositiveEnergy (grade actualL0_eigen_iff_grade)
open LatticeSugawaraCurrents (gramComplex sugawaraMode)
open Lattice.Automorphisms.ConformalGroundTransport (conformal_ground_projection)
open DiagonalCharacterConjugacy (PreservesModes)
open P48mCatalogueZeroBlock (catalogueGenerator exists_invariant_block)
open P48qInvariantQuadratics (RationalCartan rationalGram rationalCurrent blockQuadratic
  invariant_block_quadratics)
open scoped Matrix

open private rationalAction rationalExtension_preserves_gram rationalCurrent_lift from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qSplitActionObstruction
open private fixedL0 from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48mConformalActionObstruction

private theorem catalogue_cartan_block (D : LatticeData) {G : Type*} [Group G]
    (ρ : Representation ℚ G (RationalCartan D))
    (b : Module.Basis (Fin 48) ℚ (RationalCartan D))
    (g : Fin 6 → G) (hGenerate : Subgroup.closure (Set.range g) = ⊤)
    (hCatalogue : ∀ j,
      (LinearMap.toMatrix b b (ρ (g j)))ᵀ =
        (Int.castRingHom ℚ).mapMatrix (catalogueGenerator j)) :
    ∃ W : Submodule ℚ (RationalCartan D), W ≠ ⊥ ∧ W ≠ ⊤ ∧
      ∀ h, W ≤ W.comap (ρ h) := by
  -- Transposition reverses multiplication, as does inversion in G.
  let M : G →* Matrix (Fin 48) (Fin 48) ℚ :=
    { toFun := fun h => (LinearMap.toMatrix b b (ρ h⁻¹))ᵀ
      map_one' := by rw [inv_one, map_one, LinearMap.toMatrix_one, Matrix.transpose_one]
      map_mul' := fun x y => by
        rw [mul_inv_rev, map_mul, LinearMap.toMatrix_mul, Matrix.transpose_mul] }
  let generators : Fin 6 → G := fun j => (g j)⁻¹
  have hInverseGenerate : Subgroup.closure (Set.range generators) = ⊤ := by
    apply top_unique
    rw [← hGenerate, Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    have hj : (g j)⁻¹ ∈ Subgroup.closure (Set.range generators) :=
      Subgroup.subset_closure ⟨j, rfl⟩
    change g j ∈ Subgroup.closure (Set.range generators)
    simpa only [inv_inv] using Subgroup.inv_mem _ hj
  have hMatrix : ∀ j, M (generators j) =
      (Int.castRingHom ℚ).mapMatrix (catalogueGenerator j) := by
    intro j
    change (LinearMap.toMatrix b b (ρ ((g j)⁻¹)⁻¹))ᵀ = _
    rw [inv_inv, hCatalogue]
  obtain ⟨B, hBot, hTop, hInvariant⟩ := exists_invariant_block M generators hMatrix
  let W := B.comap b.equivFun.toLinearMap
  have hMap : W.map b.equivFun.toLinearMap = B :=
    Submodule.map_comap_eq_of_surjective b.equivFun.surjective B
  refine ⟨W, ?_, ?_, ?_⟩
  · intro h
    rw [h, Submodule.map_bot] at hMap
    exact hBot hMap.symm
  · intro h
    rw [h, Submodule.map_top, LinearMap.range_eq_top.mpr b.equivFun.surjective] at hMap
    exact hTop hMap.symm
  · intro h x hx
    have hh : h⁻¹ ∈ Subgroup.closure (Set.range generators) := by
      rw [hInverseGenerate]
      exact Subgroup.mem_top _
    have hImage := hInvariant h⁻¹ hh (b.equivFun x) hx
    change b.equivFun (ρ h x) ∈ B
    have hTransport : b.equivFun x ᵥ* M h⁻¹ = b.equivFun (ρ h x) := by
      change b.equivFun x ᵥ* (LinearMap.toMatrix b b (ρ (h⁻¹)⁻¹))ᵀ = _
      rw [inv_inv, Matrix.vecMul_transpose]
      exact LinearMap.toMatrix_mulVec_repr b b (ρ h) x
    rwa [hTransport] at hImage

/-- For the P48m isometry group presented by the six catalogue generators,
any actual conformal action and injective conformal inclusion of its fixed
carrier force the weight-two dimension of the target to be at least two. -/
theorem p48m_catalogue_extension_obstruction (D : LatticeData)
    (hPos : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hRoot : ∀ a : Charge D, bilinear D a a ≠ 2)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hHG : H * gramComplex D = 1)
    {G E : Type*} [Group G] [Group E]
    (realization : Additive G →+ AddAut (Charge D))
    (hFaithful : Function.Injective realization)
    (hIsometry : ∀ g : Additive G, ∀ a b,
      bilinear D (realization g a) (realization g b) = bilinear D a b)
    (hExhaustive : ∀ t : AddAut (Charge D),
      (∀ a b, bilinear D (t a) (t b) = bilinear D a b) → ∃ g, realization g = t)
    (b : Module.Basis (Fin 48) ℚ (RationalCartan D))
    (g : Fin 6 → G) (hGenerate : Subgroup.closure (Set.range g) = ⊤)
    (hCatalogue : ∀ j,
      (LinearMap.toMatrix b b (((rationalAction D).comp realization.toMultiplicativeRight)
        (g j)))ᵀ = (Int.castRingHom ℚ).mapMatrix (catalogueGenerator j))
    (U : E →* (Carrier D ≃ₗ[ℂ] Carrier D))
    (hMode : ∀ e, PreservesModes D (U e))
    (hOmega : ∀ e, U e (omega D H) = omega D H)
    {V : Type*} [AddCommGroup V] [Module ℂ V] (L : Module.End ℂ V)
    [FiniteDimensional ℂ (L.eigenspace (2 : ℂ))] :
    let A : Representation ℂ E (Carrier D) :=
      LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp U
    ∀ (inclusion : A.invariants →ₗ[ℂ] V), Function.Injective inclusion →
      (∀ x, L (inclusion x) = inclusion (fixedL0 D H U hMode hOmega x)) →
      2 ≤ Module.finrank ℂ (L.eigenspace (2 : ℂ)) := by
  intro A inclusion hInjective hIntertwine
  let ρ : Representation ℚ G (RationalCartan D) :=
    (rationalAction D).comp realization.toMultiplicativeRight
  obtain ⟨W, hBot, hTop, hW⟩ := catalogue_cartan_block D ρ b g hGenerate hCatalogue
  obtain ⟨π, phase, hGround⟩ := conformal_ground_projection D hPos hRoot H hHG
    realization hFaithful hExhaustive U (fun e a n v => hMode e a v n) hOmega
  let q : Fin 2 → Carrier D :=
    ![blockQuadratic D hPos W, blockQuadratic D hPos ((rationalGram D).orthogonal W)]
  have hQuadratics := invariant_block_quadratics D hPos (ρ.comp π) A
    (fun e => rationalExtension_preserves_gram D _ (hIsometry (Additive.ofMul (π e))))
    (fun e => rationalCurrent_lift D _ (hIsometry (Additive.ofMul (π e)))
      (U e) (phase e) (hMode e) (hGround e))
    (fun e a n v => hMode e a v n) W hBot hTop (fun e => hW (π e))
  obtain ⟨hGrade, hFixed, hIndependent⟩ :
      (∀ i, q i ∈ grade D 2) ∧ (∀ e i, A e (q i) = q i) ∧ LinearIndependent ℂ q :=
    hQuadratics
  have hWeight (x : A.invariants) (hx : (x : Carrier D) ∈ grade D 2) :
      inclusion x ∈ L.eigenspace (2 : ℂ) := by
    have hEigen : fixedL0 D H U hMode hOmega x = (2 : ℂ) • x := by
      apply Subtype.ext
      change sugawaraMode D H 0 (x : Carrier D) = (2 : ℂ) • (x : Carrier D)
      simpa only [Int.cast_ofNat] using
        (actualL0_eigen_iff_grade D H hHG (mul_eq_one_comm.mp hHG) 2 (x : Carrier D)).mpr hx
    apply Module.End.mem_eigenspace_iff.mpr
    rw [hIntertwine x, hEigen, map_smul]
  let qFixed (i : Fin 2) : A.invariants := ⟨q i, fun e => hFixed e i⟩
  have hFixedIndependent : LinearIndependent ℂ qFixed :=
    LinearIndependent.of_comp A.invariants.subtype hIndependent
  let qImage (i : Fin 2) : L.eigenspace (2 : ℂ) :=
    ⟨inclusion (qFixed i), hWeight (qFixed i) (hGrade i)⟩
  have hImageIndependent : LinearIndependent ℂ qImage := by
    apply LinearIndependent.of_comp (L.eigenspace (2 : ℂ)).subtype
    exact hFixedIndependent.map' inclusion (LinearMap.ker_eq_bot.mpr hInjective)
  simpa only [Fintype.card_fin] using hImageIndependent.fintype_card_le_finrank

run_cmd do
  let name := ``p48m_catalogue_extension_obstruction
  let axioms ← Lean.collectAxioms name
  unless axioms.all (fun ax => [``propext, ``Classical.choice, ``Quot.sound].contains ax) do
    throwError "Unexpected axiom closure for {name}: {axioms}"
  Lean.logInfo m!"{name} depends on axioms: {axioms}"

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48mCatalogueExtensionObstruction
