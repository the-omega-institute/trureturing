/- GID: D5/S3/Quantum/Completion/OneStepQuotientSplit
   generality: G
   mirror-B: D5/B/S3/Quantum/Completion/OneStepQuotientSplit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: One orthogonal shell canonically splits successive Hilbert quotients. -/

import D5.S3.Quantum.Algebra.QuotientOrthogonalComplement
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.LinearAlgebra.Isomorphisms

/- Library-search audit trail (2026-08-25):
   * The repository exact supporting hit
     `quotient_orthogonal_complement_isometry` supplies the canonical Hilbert
     quotient model and is applied below.
   * Pinned Mathlib exact hits `Submodule.factor`, `Submodule.factor_mk`,
     `Submodule.ker_mapQ`, `LinearMap.quotientInfEquivSupQuotient`,
     `Submodule.quotientQuotientLIEQuotient`, and
     `Submodule.orthogonalDecomposition` construct the canonical maps and
     equivalences and are applied directly.
   * Repository and pinned-Mathlib searches found no declaration combining the
     shell formula, short exactness, both kernel identifications, and the
     Hilbert product splitting. -/

noncomputable section

open scoped InnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Completion.OneStepQuotientSplit

open D5.S3.Quantum.Algebra.QuotientOrthogonalComplement

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H]

/-- The next visible space, constructed by adjoining the orthogonal shell. -/
def nextSpace (S E : Submodule 𝕜 H) : Submodule 𝕜 H := E ⊔ S

/-- The canonical quotient map from the old residual quotient to the next one. -/
def stepMap (S E : Submodule 𝕜 H) :
    (H ⧸ S) →ₗ[𝕜] H ⧸ nextSpace S E :=
  Submodule.factor (show S ≤ nextSpace S E by exact le_sup_right)

/-- The shell inclusion followed by the old quotient map. -/
def shellEmbedding (S E : Submodule 𝕜 H) : E →ₗ[𝕜] H ⧸ S :=
  S.mkQ.comp E.subtype

/-- The copy of the old space inside the next visible space. -/
def oldInsideNext (S E : Submodule 𝕜 H) :
    Submodule 𝕜 (nextSpace S E) :=
  S.comap (nextSpace S E).subtype

/-- The literal successive quotient `(E + S) / S`. -/
abbrev SuccessiveQuotient (S E : Submodule 𝕜 H) :=
  (nextSpace S E) ⧸ oldInsideNext S E

private theorem shell_disjoint_old
    (S E : Submodule 𝕜 H) (hOrth : S ⟂ E) :
    E.comap E.subtype ⊓ S.comap E.subtype = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxSE : (x : H) ∈ S ⊓ E := ⟨hx.2, hx.1⟩
  have : (x : H) ∈ (⊥ : Submodule 𝕜 H) :=
    hOrth.disjoint.le_bot hxSE
  simpa using this

/-- The canonical second-isomorphism-law identification
`(E + S) / S ≃ E`. -/
def successiveQuotientShellEquiv (S E : Submodule 𝕜 H)
    (hOrth : S ⟂ E) : SuccessiveQuotient S E ≃ₗ[𝕜] E :=
  (LinearMap.quotientInfEquivSupQuotient E S).symm.trans
    ((E.comap E.subtype ⊓ S.comap E.subtype).quotEquivOfEqBot
      (shell_disjoint_old S E hOrth))

private theorem shell_range_eq_kernel
    (S E : Submodule 𝕜 H) :
    LinearMap.range (shellEmbedding S E) = LinearMap.ker (stepMap S E) := by
  rw [stepMap, Submodule.ker_mapQ]
  change LinearMap.range (S.mkQ.comp E.subtype) =
    (nextSpace S E).map S.mkQ
  rw [nextSpace, Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq]
  rw [LinearMap.range_comp, Submodule.range_subtype]

/-- The shell embeds isometrically in the old quotient because it is
orthogonal to the old visible space. -/
def shellIsometry (S E : Submodule 𝕜 H) [S.HasOrthogonalProjection]
    (hOrth : S ⟂ E) : E →ₗᵢ[𝕜] H ⧸ S where
  toLinearMap := shellEmbedding S E
  norm_map' e := by
    have hCanonical := quotient_orthogonal_complement_isometry S
    have hMem : (e : H) ∈ Sᗮ := hOrth.symm e.property
    calc
      ‖shellEmbedding S E e‖ =
          ‖S.quotientEquivOrthogonal (shellEmbedding S E e)‖ :=
        (hCanonical.1.norm_map_of_map_zero
          (map_zero S.quotientEquivOrthogonal) _).symm
      _ = ‖(⟨e, hMem⟩ : Sᗮ)‖ := by
        change ‖S.quotientEquivOrthogonal
          (Submodule.Quotient.mk (e : H))‖ = _
        rw [Submodule.quotientEquivOrthogonal_mk]
      _ = ‖e‖ := rfl

/-- The canonical isometric equivalence between the new shell and the kernel
of the one-step quotient map. -/
def shellKernelEquiv (S E : Submodule 𝕜 H) [S.HasOrthogonalProjection]
    (hOrth : S ⟂ E) : E ≃ₗᵢ[𝕜] LinearMap.ker (stepMap S E) := by
  let inclusion : E →ₗᵢ[𝕜] LinearMap.ker (stepMap S E) :=
    { toLinearMap :=
        (shellEmbedding S E).codRestrict (LinearMap.ker (stepMap S E))
          (fun e => by
            rw [← shell_range_eq_kernel S E]
            exact ⟨e, rfl⟩)
      norm_map' := (shellIsometry S E hOrth).norm_map }
  refine LinearIsometryEquiv.ofSurjective inclusion ?_
  intro x
  have hx : (x : H ⧸ S) ∈ LinearMap.range (shellEmbedding S E) := by
    rw [shell_range_eq_kernel S E]
    exact x.property
  rcases hx with ⟨e, he⟩
  refine ⟨e, Subtype.ext ?_⟩
  exact he

/-- The shell viewed as a subspace of the old orthogonal residual. -/
def shellInResidual (S E : Submodule 𝕜 H) (_hOrth : S ⟂ E) :
    Submodule 𝕜 Sᗮ :=
  E.comap Sᗮ.subtype

/-- Forgetting the residual-subtype layer canonically identifies the embedded
shell with the original shell. -/
def shellResidualEquiv (S E : Submodule 𝕜 H) (hOrth : S ⟂ E) :
    shellInResidual S E hOrth ≃ₗᵢ[𝕜] E where
  toFun x := ⟨x, x.property⟩
  invFun e := ⟨⟨e, hOrth.symm e.property⟩, e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

/-- Inside the old residual, the vectors orthogonal to the shell are exactly
the orthogonal residual of the enlarged visible space. -/
def residualComplementEquiv (S E : Submodule 𝕜 H) (hOrth : S ⟂ E) :
    (shellInResidual S E hOrth)ᗮ ≃ₗᵢ[𝕜] (nextSpace S E)ᗮ where
  toFun x := by
    refine ⟨x, ?_⟩
    rw [Submodule.mem_orthogonal]
    intro y hy
    rcases Submodule.mem_sup.mp hy with ⟨e, he, s, hs, rfl⟩
    have hE : ⟪(e : H), (x : H)⟫_𝕜 = 0 := by
      have heResidual : (e : H) ∈ Sᗮ := hOrth.symm he
      exact (Submodule.mem_orthogonal (shellInResidual S E hOrth) x).mp
        x.property ⟨e, heResidual⟩ he
    have hS : ⟪(s : H), (x : H)⟫_𝕜 = 0 :=
      Submodule.inner_right_of_mem_orthogonal hs x.val.property
    rw [inner_add_left, hE, hS, add_zero]
  invFun x := by
    have hS : (x : H) ∈ Sᗮ := by
      apply (Submodule.mem_orthogonal S x).mpr
      intro s hs
      exact Submodule.inner_right_of_mem_orthogonal
        (show (s : H) ∈ nextSpace S E by
          change (s : H) ∈ E ⊔ S
          exact Submodule.mem_sup_right hs)
        x.property
    refine ⟨⟨x, hS⟩, ?_⟩
    apply (Submodule.mem_orthogonal (shellInResidual S E hOrth) _).mpr
    intro e he
    simpa using (Submodule.mem_orthogonal (nextSpace S E) x).mp x.property
      (e : H) (show (e : H) ∈ nextSpace S E by
        change (e : H) ∈ E ⊔ S
        exact Submodule.mem_sup_left he)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

/-- The canonical Hilbert splitting of the old quotient into the extracted
shell and the next residual quotient. -/
def quotientShellSplit (S E : Submodule 𝕜 H)
    [S.HasOrthogonalProjection] [(nextSpace S E).HasOrthogonalProjection]
    [CompleteSpace E] (hOrth : S ⟂ E) :
    (H ⧸ S) ≃ₗᵢ[𝕜] WithLp 2 (E × (H ⧸ nextSpace S E)) := by
  let K : Submodule 𝕜 Sᗮ := shellInResidual S E hOrth
  let eK : K ≃ₗᵢ[𝕜] E := shellResidualEquiv S E hOrth
  letI : CompleteSpace K := eK.toIsometryEquiv.completeSpace
  letI : K.HasOrthogonalProjection := inferInstance
  exact S.quotientEquivOrthogonal |>.trans
    K.orthogonalDecomposition |>.trans
    (LinearIsometryEquiv.withLpProdCongr 2 eK
      ((residualComplementEquiv S E hOrth).trans
        (nextSpace S E).quotientEquivOrthogonal.symm))

/-- One orthogonal shell yields the canonical split short exact sequence.
The public clauses expose both quotient identifications and the computation
rule of the Hilbert product splitting. -/
theorem one_step_quotient_split_exact
    (S E : Submodule 𝕜 H)
    [S.HasOrthogonalProjection] [(nextSpace S E).HasOrthogonalProjection]
    [CompleteSpace E] (hOrth : S ⟂ E) :
    Function.Injective (shellEmbedding S E) ∧
      Function.Surjective (stepMap S E) ∧
      LinearMap.range (shellEmbedding S E) = LinearMap.ker (stepMap S E) ∧
      (∀ e : E, shellEmbedding S E e = S.mkQ e) ∧
      (∀ e : E,
        shellKernelEquiv S E hOrth e =
          ⟨shellEmbedding S E e, by
            rw [← shell_range_eq_kernel S E]
            exact ⟨e, rfl⟩⟩) ∧
      (∀ e : E,
        successiveQuotientShellEquiv S E hOrth
            (Submodule.Quotient.mk
              (⟨e, by
                change (e : H) ∈ E ⊔ S
                exact Submodule.mem_sup_left e.property⟩ :
                nextSpace S E)) = e) ∧
      (∀ e : E,
        (quotientShellSplit S E hOrth (shellEmbedding S E e)).fst = e) := by
  refine ⟨?_, Submodule.factor_surjective le_sup_right,
    shell_range_eq_kernel S E, ?_, ?_, ?_, ?_⟩
  · exact (shellIsometry S E hOrth).injective
  · intro e
    rfl
  · intro e
    rfl
  · intro e
    change ((LinearMap.quotientInfEquivSupQuotient E S).symm.trans
      ((E.comap E.subtype ⊓ S.comap E.subtype).quotEquivOfEqBot
        (shell_disjoint_old S E hOrth)))
      (Submodule.Quotient.mk
        (⟨(e : H), show (e : H) ∈ E ⊔ S from
          Submodule.mem_sup_left e.property⟩ : ↥(E ⊔ S))) = e
    rw [LinearEquiv.trans_apply,
      LinearMap.quotientInfEquivSupQuotient_symm_apply_left,
      Submodule.quotEquivOfEqBot_apply_mk]
  · intro e
    let K : Submodule 𝕜 Sᗮ := shellInResidual S E hOrth
    let eK : K ≃ₗᵢ[𝕜] E := shellResidualEquiv S E hOrth
    letI : CompleteSpace K := eK.toIsometryEquiv.completeSpace
    letI : K.HasOrthogonalProjection := inferInstance
    let r : Sᗮ := ⟨e, hOrth.symm e.property⟩
    have hr : r ∈ shellInResidual S E hOrth := e.property
    have hQuotient :
        S.quotientEquivOrthogonal (shellEmbedding S E e) = r := by
      change S.quotientEquivOrthogonal
        (Submodule.Quotient.mk (e : H)) = r
      exact S.quotientEquivOrthogonal_mk (e : H) (hOrth.symm e.property)
    simp only [quotientShellSplit, LinearIsometryEquiv.trans_apply,
      LinearIsometryEquiv.withLpProdCongr_apply,
      Submodule.orthogonalDecomposition_apply]
    rw [hQuotient]
    have hProjection :
        (shellInResidual S E hOrth).orthogonalProjectionOnto r =
          ⟨r, hr⟩ :=
      (shellInResidual S E hOrth).orthogonalProjectionOnto_mem_subspace_eq_self
        ⟨r, hr⟩
    rw [hProjection]
    rfl

#print axioms nextSpace
#print axioms stepMap
#print axioms shellEmbedding
#print axioms successiveQuotientShellEquiv
#print axioms shellKernelEquiv
#print axioms shellResidualEquiv
#print axioms residualComplementEquiv
#print axioms quotientShellSplit
#print axioms one_step_quotient_split_exact

end D5.S3.Quantum.Completion.OneStepQuotientSplit
