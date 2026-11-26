import OmegaMath.NumberTheory.GRH.Lib.Shimura.ThetaNormality.NormalGeneration
import OmegaMath.NumberTheory.GRH.Lib.Shimura.ThetaGroup.ThetaStructure
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of algebraic geometry (textbook or folklore).

This file: Serre: sections of high powers of a very ample bundle are forms. -/


open MvPolynomial AlgebraicGeometry Scheme CategoryTheory MorphismProperty Filter Set Submodule
  LineBundle Spec Limits.pullback
attribute [-simp] pull_opens pull_transition
variable {k F ι} [CommRing k] [IsNoetherianRing k] [Finite ι]

/-- Saturation: let x be a finite family in a commutative k-algebra F, k noetherian, with x_r = 1.
For all large D, if for each i some f·x_i^N is a form of degree D + N in x, then f is a form
of degree D. -/
lemma eventually_mem_formSpan_of_mul_pow [CommRing F] [Algebra k F] (x : ι → F) {r} (hr : x r = 1) :
  ∀ᶠ D in atTop, ∀ f, (∀ i, ∃ N, f * x i ^ N ∈ formSpan k x (D + N)) →
  f ∈ formSpan k x D := let T := formSpan k x
  have M j {m f} : f ∈ T m → _ ∈ T m.succ := (mul_mem_mul · (subset_span ⟨j, rfl⟩))
  let φ := aeval (R := k) ((Polynomial.X * ·) ∘ .C ∘ x)
  let I c : Ideal _ := ⟨⟨⟨{p | ∀ n, (∀ i, (φ p).coeff n * x i ∈ T n) ∧ (c < n → (φ p).coeff
    n ∈ T n.pred)}, by simp_all [add_mul, add_mem]⟩, by simp⟩, fun q p h ↦ by
    apply q.induction_on <;> (try rintro _ _ _ ⟨⟩) <;>
    simp_all [φ, mul_right_comm _ _ p, ← mul_assoc, add_mul, add_mem, smul_mem, C_mul']⟩
  mem_atTop_sets.2 ((WellFoundedGT.monotone_chain_condition ⟨I, fun _ _ _ _ ↦
    forall_imp (by lia)⟩).imp fun c hc D e f ↦ by
  choose N h
  induction' N using WellFoundedLT.fix with N ih generalizing D f
  have H j : f * x j ∈ T D.succ := by
    cases z : N j; simpa [z] using M j (h j)
    exact ih _ (update_lt_self_iff.2 z.ge) _ e.step _ (by grind [M j <| h ·])
  have ⟨p, g, E⟩ := (map_homogeneousSubmodule_eq_formSpan ..).ge (H r)
  have : φ p = _ :=
    (eval₂_mul_of_isHomogeneous g ..).trans congr(_ * $(E ▸ aeval_algebraMap_apply ..))
  simpa [*] using (hc _ e.step).ge (by aesop : p ∈ _) D.succ)

/-- Serre's theorem: let N be a projective embedding of an integral scheme A over a field, p :
A' → A a base change to a noetherian ring k. For large m, the degree m monomials in the
coordinates span H⁰((p^*N)^m) over k. -/
lemma eventually_span_coordSection [Field F] {A : Over (Spec ⟨F⟩)} [IsIntegral A.1] {N :
  LineBundle _ ι}
  (A' : Over (Spec ⟨k⟩)) (hN : N.IsProjEmbedding A.hom) {p b} (Q : IsPullback p A'.hom A.hom b) :
  ∀ᶠ m in atTop, ∀ h : ((N.pull p).pow m).IsLinearSystem, span k (range (coordSection h)) = ⊤ := by
  let ζ := A.1.fromSpecResidueField (genericPoint _)
  obtain ⟨_, ⟨_, _, ξ, E⟩, _ : Flat p, i, I⟩ := (isSchemeTheoreticallyDominant_iff_isDominant ζ).2
    ⟨fun _ ↦ by simp [ζ, range_fromSpecResidueField]⟩, @exists_isPullback_SpecMap _ _ p
    (of_isPullback Q.flip inferInstance) _ ζ, of_isPullback Q.flip inferInstance, N.exists_landsIn ζ
  algebraize [(Spec.preimage (ξ ≫ A'.hom)).1]
  let v : PointFn _ →ₐ[k] _ := by use! (· _ ξ) <;> tauto
  have Y j : v ((N.pull p).transition i j) = _ := E.w ▸ (hN.1.1 ..).1 _ _ I
  obtain ⟨hN, hi : LandsIn ξ ((N.pull p).opens i)⟩ := hN.of_isPullback Q, (E.w ▸ I.comp _ :)
  refine (eventually_mem_formSpan_of_mul_pow (v ∘ _) (transition_self _ _ _ _ hi)).mono fun m H h ↦
    top_unique fun ⟨t, ⟨u, w⟩, _⟩ _ ↦ (apply_mem_span_image_iff_mem_span (f :=
    v.toLinearMap ∘ₗ .domRestrict (.proj fun _ ↦ i) _) (.of_ker _ fun ⟨s, ⟨a, d⟩, _⟩ e ↦
    H0_ext fun {l} ↦ (·.ext_of_dominant (E.isoPullback.1 ≫ fst ..) · .one (by simp +contextual [hi,
    map_surjective.forall, a _ _, d l fun _ ↦ i, landsIn_iInf, hi.comp, pow,
    (id e : s .. = 0)])))).1 (span_mono (by simp [subset_def, mem_pow_iff_prod,
    @Classical.skolem (Fin m), ← funext_iff, ← map_prod]; tauto) ((span_pow ..).le
    (H (t ..) fun j ↦ if z : IsUnit (N.transition i j _ ζ) then ?_ else ⟨1, by aesop⟩)))
  obtain ⟨hj, -, _, s, -, V⟩ := (hN.1.2 hi _).1.2 (Y j ▸ z.map _), hN.exists_affine_chart j
  choose P e using s.exists.1 ((u _).mono le_iInf_const).exists_ofSection
  rw [w _ fun _ ↦ j] <;> simp [landsIn_iInf, hi, hj, ← e, pow, V]
  exact ⟨_, (map_homogeneousSubmodule_eq_formSpan ..).le
    ((exists_homogenization (isHomogeneous_X _ j) P le_add_self).imp
    fun Q ⟨q, E⟩ ↦ ⟨q, congr(Q.eval₂ _ $(funext (hN.1.isSection · |>.2 _ _ _ _ hi hj))).trans (by
    simp [eval₂_mul_of_isHomogeneous q, ← aeval_def, E, transition_self, hj]; ring!)⟩)⟩
