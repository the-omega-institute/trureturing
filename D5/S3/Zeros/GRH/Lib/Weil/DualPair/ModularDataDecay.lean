/- GID: D5/S3/Zeros/GRH/Lib/Weil/DualPair/ModularDataDecay
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/DualPair/ModularDataDecay
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.DualPair.ModularDataDecay. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/DualPair/ModularDataDecay.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.DualPair.KernelDecay
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Theta kernels of unitary dual pairs: functoriality, seesaw, growth, rapid decay (known
result; see Lib.Weil.DualPair.KernelDecay).

This file: Operator norm of block diagonal matrices; block embeddings are proper maps. Rapid decay
of theta kernels for data mod m supported on full-rank matrices. -/

open Matrix Norms.L2Operator Function IsLocalRing Space
variable {n m : Type _} [Fintype n] [Fintype m] {ε : n → _} {ε' : m → _}

@[simp] lemma norm_fromBlocks x b : ‖@fromBlocks n m n m ℂ x 0 0 b‖ = ‖x‖ ⊔ ‖b‖ := by
  apply NonUnitalStarAlgHom.norm_map ({toFun := (fromBlocks · 0 0).uncurry, ..} :
    _ →⋆ₙₐ[ℂ] _) _ (x, b) <;> aesop_cat

@[fun_prop] lemma isProperMap_inl : IsProperMap (U.inl ε ε') := isProperMap_of_comp_of_t2 (g :=
  (·.1.1.onFun .inl)) (by simp [continuous_U_iff_matrix]; fun_prop) (by fun_prop)
  isClosedEmbedding_U.isProperMap

section

variable {E n n' : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {𝔪 : Modulus E}

/-- For a place w dividing 𝔪, the reduction map from O_E/𝔪 to the residue field at w. -/
noncomputable def modulusResidue (𝔪 : Modulus E) {w} (h : w ∈ 𝔪.places) :
    𝔪.ResRing →+* ResField w := Ideal.Quotient.lift _ _ (algebraMap_ResField_eq_zero.2 ∘ @h ·)

@[simp] lemma modulusResidue_reduction (𝔪 : Modulus E) {w} h x :
  modulusResidue 𝔪 h (𝔪.reduction x) = reduceAt w x := 𝔪.apply_reduction_eq_of_algebraMap x

end

variable {E n n' : Type} [Field E] [CMType E] {𝔪 : Modulus E} [Fintype n] [Fintype n'] {s : n → ℤˣ}
  {s' : n' → ℤˣ} (S : Space E n s) (T : Space E n' s')

/-- Suppose Ψ(y) ≠ 0 forces the matrix of entries of y arranged by e to have a left inverse
modulo 𝔪. Then wherever the adelic lift of Ψ is nonzero, the matrix so arranged is primitive
over O_w at each w dividing 𝔪. -/
lemma isPrimitiveMatrix_of_liftFn_ne_zero {ι Ψ} (e : Matrix n' n ι) (l : ∀ y, Ψ y ≠ 0 →
  HasLeftInv (e.map y)) ⦃w x⦄ (o : w ∈ 𝔪.places) (h : 𝔪.liftFn Ψ x ≠ 0) :
  IsPrimitiveMatrix (LocInt w).1 ((e.map x).map (evalAt w)) := ((dite_ne_right_iff.1 h).imp
  fun _ ↦ l _).elim fun i ⟨L, l⟩ ↦ ⟨by solve_by_elim [idem_mul_mem_Ô.1], _, .symm
  ⟨by simpa [o] using! Matrix.map_mul.symm.trans congr(Matrix.map $((Matrix.mul_assoc ..).trans
        (isUnit_of_mapMatrix (residue _) (M :=
  L.map (surjInv residue_surjective ∘ modulusResidue _ o) * e.map
  fun j ↦ ⟨_, mem_Ô.1 (i j) w⟩) (by simpa [comp_def, surjInv_eq] using! congr(IsUnit (Matrix.map $l
  (modulusResidue _ o))))).val_inv_mul) (LocInt w).subtype), by simp [IsIntMatrix]⟩⟩

lemma Space.height_sum_le g h : (S.sum T).height (.sum (g, h)) ≤ S.height g * T.height h := by
  simp [height, field, firstMinimum_pos, inf_le_firstMinimum_sum.trans']

lemma modDatum_eq_sum [WeilData E] Ψ v : modDatum S T 𝔪 Ψ v = ∑ x,
  Ψ x • modDatum S T 𝔪 (Pi.single x 1) v := by nth_rw 1 [pi_eq_sum_univ' Ψ]; simp [-Pi.single_apply,
  modDatum, comp_def, ← Finset.sum_fn, ← Pi.smul_def, -smul_eq_mul]

/-- Let 𝔪 ≠ (1), Ψ be supported on left invertible matrices mod 𝔪, and θ the kernel of v ⊗ Ψ.
For each M there are B, N, C with |θ(g,h)| ht(g)^M ≤ C mom_N(v) ht(h)^B for all g, h and all
v with finite N-th moment. -/
lemma pairTheta_modDatum_decay [WeilData E] a b {Ψ} (o : Nonempty 𝔪.places) (h :
  support Ψ ⊆ {y | HasLeftInv y}) M : ∃ B N C, ∀ v h g, weightedNorm N v ≠ ⊤ → ‖pairTheta S T a b
  (modDatum S T 𝔪 Ψ v) (g, h)‖ * S.height g ^ M ≤ C * (weightedNorm N v).toReal * T.height h ^
  B := let ⟨_, _, H⟩ := (pairThetaKer ..).swap.moderate_growth; ⟨_, _, (exists_norm_name_le a b
    𝔪.disjoint_places_star vacElem_mem_finitePart ..).imp fun _ D v k g ↦ (D v g k (θ _) _
    _ · (one_le_height k) (height_pos g) (H k g) fun l ↦ (T.exists_short_basis_matrix.choose_spec
    k).rec fun Y u ↦ ⟨_, (S.exists_short_isotropic l).imp fun x ⟨h0, i, e⟩ ↦ ⟨_, _, u, e, le_rfl,
    .inr i, by simp [← vecAtPoint_hom], .inl fun y c ↦ (S.mul_coordMatrix_ne_zero h0 (_ * (_ * Y.map
    _)) ((isPrimitiveMatrix_of_liftFn_ne_zero _ (by tauto) o.some.2 c).2.imp (by tauto)) :)⟩⟩)⟩
