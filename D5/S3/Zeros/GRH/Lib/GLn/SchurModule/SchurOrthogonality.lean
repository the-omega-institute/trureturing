/- GID: D5/S3/Zeros/GRH/Lib/GLn/SchurModule/SchurOrthogonality
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/GLn/SchurModule/SchurOrthogonality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.GLn.SchurModule.SchurOrthogonality. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/GLn/SchurModule/SchurOrthogonality.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.GLn.SchurModule.WeightRepBasic
import D5.S3.Zeros.GRH.Lib.GLn.SchurModule.SchurContinuous
import D5.S3.Zeros.GRH.Lib.Weil.Construction.DataProduct
import D5.S3.Zeros.GRH.Lib.DiscreteSeries.Theta.LocalThetaCorrespondence
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Lemmas on Weyl representations, their Gram form and the highest vector, used to turn algebraic
forms into functions on G.

Part of: Contravariant form on Weyl's lattice, Fischer product, irreducibility under U(n) (known
result; see Lib.Adelic.CuspForms.DeltaForms).

Part of: Cusp forms: rapid decay, finite dimension, Poincaré series; algebraic modular forms (known
result; see Lib.Adelic.CuspForms.Petersson).

This file: Maps between algebraic forms and scalar functions on the adelic group. Schur
orthogonality on products of U(n); highest coefficient as product of principal minors. -/

variable {E n} [Field E] [CMType E] [Fintype n] (l) {κ e}

/-- For a linear functional L on vectors of weight κ, the linear map sending an algebraic form φ
to the function g ↦ L(ḡ_∞⁻¹ φ(g_f)) on G, acting through `conjWeylRep`. -/
@[simps! -isSimp apply] noncomputable def algFormCoeff (s : n → _) (L :
  (WeylIndex n κ → ℂ) →ₗ[ℂ] ℂ) : AlgForm (E :=
  E) n κ e →ₗ[ℂ] G E s → ℂ := .pi fun g ↦ L ∘ₗ conjWeylRep κ e g.1⁻¹ ∘ₗ .domRestrict (.proj g.2) _

/-- The linear map φ ↦ F_φ from algebraic forms of weight (κ, e) to functions on G, F_φ(g) =
⟨v⁺, ρ(g_∞⁻¹) φ(g_f)⟩, with v⁺ = `highestVector` for l. -/
noncomputable abbrev ofAlgForm s :=
  algFormCoeff (E := E) (e := e) s (gramForm (n := n) (highestVector κ l))

lemma Space.IsStd.eq_stdSpace V [IsStd V] : V = stdSpace E n := ext point_eq_one

@[elab_as_elim, induction_eliminator] lemma Space.IsStd.std_induction {p : ∀ _ V, V.IsStd →
    Prop} (h : p 1 (stdSpace E n) ⟨rfl, rfl⟩) {s V} i : p s V i := by cases i.1; simpa [eq_stdSpace]

open MeasureTheory Matrix ComplexConjugate Finset Fintype Fin Norms.Operator PolyRep
variable {Φ n : Type} [Fintype Φ] [Fintype n] {κ : Φ → _} {e : _} {l : _ → n → _} {s : n → _}

instance : Nonempty (WeylIndex n
  κ) := by by_contra!; simpa [weylNormSq] using weylNormSq_weylEval_permArray (κ := κ) (rowPos n)

/-- The vector v⁺ = `highestVector` κ l equals its complex conjugate. -/
lemma star_highestVector : star (highestVector κ l) = highestVector κ l :=
  (star_weylEval _).trans (by rcongr; simp [permArray])

attribute [local simp] gramForm_apply Function.comp_def filter_lt_eq_Ioi conjWeylRep weylRep
  val_eq_val

lemma conj_gramForm (ξ η : WeylIndex n κ → ℂ) : conj (gramForm ξ η) = gramForm η ξ :=
  star_form weylGram_posDef.1 ..

lemma exists_equiv_decrPosition {l} (h : l.Injective) : ∃ e : n ≃ Fin (card n), ∀ a,
  decrPosition l a = e a ∧ decrPosition (-l) a = (e a).rev :=
  (exists_equiv_fin_lt_iff (neg_injective.comp h)).imp' .symm fun e _ ↦ (reindex_equiv e).1.2
  (by simp_all [decrPosition, card_filter, reindex_equiv e, filter_gt_eq_Iio]; lia)

@[fun_prop] lemma continuous_conjWeylRep ξ :
  Continuous (conjWeylRep (s := s) κ e · ξ) := by simp; fun_prop

/-- For matrix representations S, R of a compact group with Haar measure ν and M with g ↦
S(g)MR(g⁻¹) continuous, some B has BR(y) = S(y)B for all y and ∫ L(S(g)MR(g⁻¹)) dν = L(B)
for every complex linear functional L. -/
lemma exists_intertwining_mean {G} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G] ν [Measure.IsHaarMeasure ν] (S : G →* Matrix Φ
  Φ ℂ) (R : G →* Matrix n n ℂ) (M : Matrix Φ n ℂ) (h : Continuous fun g ↦ S g * M * R g⁻¹ := by
  fun_prop) : ∃ B, (∀ y, B * R y = S y * B) ∧ ∀ L : _ →ₗ[ℂ] ℂ, ∫ g, L (S g * M * R g⁻¹) ∂ν = L B :=
  ⟨_, (iff_and_self.2 fun H y ↦ sub_eq_zero.1 <| (Module.forall_dual_apply_eq_zero_iff ℂ _).1
  fun L ↦ (map_sub L ..).trans <| sub_eq_zero.2 <|
  ((integral_mul_left_eq_self _ y).trans (H (L ∘ₗ mulRightLinearMap ..))).symm.trans (by
    simpa [Matrix.mul_assoc, ← R.map_mul y⁻¹] using! H (_ ∘ₗ mulLinearMap ℂ _))).1
    (·.toContinuousLinearMap.integral_comp_comm integrable_of_compactSpace)⟩

attribute [-simp] Fintype.card_pi

/-- Let v be the evaluation vector of weight κ at the permutation matrices of orderings p_τ. For
g in ∏_τ GL(n_τ, ℂ), the coefficient ⟨v, ρ(g)v⟩ of weight (κ, e) is ∏_τ m(g_τ), m = `weightMinors`
for the weight e_τ + λ(τ, p_τ(i)). -/
lemma weylRep_coeff_eq_prod_weightMinors {n} [∀ τ, Fintype (n τ)] (p : ∀ τ, n τ ≃ Fin (rankAt n τ))
  g : let v := weylEval n κ (permArray p); v ⬝ᵥ weylGramOver *ᵥ weylRep κ e g *ᵥ v = ∏ τ,
    weightMinors (e τ + diagramWeight (rankAt n) κ ⟨τ, p τ ·⟩) (g τ) := by
  simp [-mulVec_smul, weylKernel, eval_rowSubst, minor, highestPoly, tableauPoly, diagramWeight,
    RingHom.map_det,
    Units.smul_def, ← prod_mul_distrib, Finsupp.single_apply, ite_and, sum_range (n := rankAt ..)]
  congr!; induction @univ (Fin _) _ using cons_induction <;> simp [*,
    mul_left_comm (_ ^ e _), add_comm (ite ..), ← add_assoc]
  rename_i h _ _ _
  rw [weightMinors_add_ite, mul_comm, ← det_reindex_self (.trans (castLEquiv h.is_le')
    ((p _).subtypeEquiv fun _ ↦ .rfl).symm), ← det_transpose] <;>
    rcongr <;> simp_intro .. [permArray]; gcongr; lia

/-- Schur orthogonality for the representation ρ = `conjWeylRep` of weight (κ, e) of the compact
group ∏ U(n): for a linear functional f and vectors a, b, c, ∫ f(ρ(x)c) ⟨a, ρ(x⁻¹)b⟩ dx =
(dim ρ)⁻¹ ⟨a, c⟩ f(b). -/
lemma schur_orthogonality e (f : _ →ₗ[ℂ] ℂ) a b c : ∫ x, f (conjWeylRep κ e x c) * gramForm (n :=
  n) a (conjWeylRep κ e (s := 1) x⁻¹ b) = (card (WeylIndex n κ) : ℂ)⁻¹ * gramForm a c * f b := by
  have ⟨B, hB, hL⟩ := exists_intertwining_mean volume (conjWeylMatrix (s := 1) κ e) (conjWeylMatrix
    κ e) ((gramForm a).smulRight c).toMatrix' (by simp [-Pi.inv_apply]; fun_prop)
  obtain ⟨_, _, z, ⟨⟩⟩ := hL (traceLinearMap ..), hL (f ∘ₗ toLin'.1.flip b), scalar_of_commute_schur
    fun g h ↦ by simpa [smul_left_cancel_iff] using! hB fun τ ↦ U.of (by simp) (.map _ conj) (by
    simpa using! congr($(h τ)ᵀᴴ))
  simp_all [trace_mul_cycle (weylRep κ e _), ← map_mul, ← trace_toLin'_eq,
    ↓trace_diagonal, -weylRep, mul_comm]

/-- If each l_w is injective, the vector v⁺ = `highestVector` κ l is a unit vector for the Gram form
of weight κ: ⟨v⁺, v⁺⟩ = 1. -/
lemma gramForm_highestVector_self (h : ∀ w, (l w).Injective) : gramForm (highestVector κ l)
  (highestVector κ l) = 1 := by choose _ _ using (exists_equiv_decrPosition <| h ·); simp_all
  [← coe_weylNormSq, highestVector, weylNormSq_weylEval_permArray]
