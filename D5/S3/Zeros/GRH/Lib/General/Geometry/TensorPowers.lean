/- GID: D5/S3/Zeros/GRH/Lib/General/Geometry/TensorPowers
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/General/Geometry/TensorPowers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.General.Geometry.TensorPowers. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/General/Geometry/TensorPowers.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.Geometry.ProjectiveSpace
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! General lemmas of algebraic geometry (textbook or folklore).

This file: Projective embeddings by linear systems: properness, closed immersions, Segre, affine
charts. Tensor products and powers of line bundles; Segre and Veronese embeddings. -/

open AlgebraicGeometry CategoryTheory CommRingCat Finset PointFn Function MvPolynomial ProjSpace
  TopologicalSpace Over

variable {X Y S ι κ} {L : LineBundle X ι} {s : X ⟶ S} {Λ : Type} [Fintype Λ] {ν : Λ → _}
  (N : ∀ l, LineBundle X (ν l))

instance [h : HasProjEmbedding s] : IsProper s := h.rec (·.2.1)

lemma LineBundle.IsProjEmbedding.ext (h : L.IsProjEmbedding s) {a b : Y ⟶ X} (e : L.pull a =
  L.pull b) (o : a ≫ s = b ≫ s) : a = b := hom_ext_of_cover (L.pull a) fun i A t x ↦
  h.2.2 ⟨x, (e ▸ x :), (congr(($e).transition i · A t))⟩ (t ≫= o)

/-- If the linear system L embeds X projectively over S along s: X → S
(`LineBundle.IsProjEmbedding`) and p: Y → X is a closed immersion, then p*L embeds Y projectively
over S along s∘p. -/
lemma LineBundle.IsProjEmbedding.comp : L.IsProjEmbedding s → ∀ p [@IsClosedImmersion Y X p],
  (L.pull p).IsProjEmbedding (p ≫ s)
  | ⟨l, _, H⟩, p, _ => ⟨l.pull p, {}, ((cancel_mono p).1 <| H · ·)⟩

/-- Segre embedding of a tower: if L embeds X over S along s, and N embeds S over S' along b (any
index sets), then L ⊗ s*N embeds X over S' along the composite. -/
lemma LineBundle.IsProjEmbedding.mul {N b} : L.IsProjEmbedding s → @IsProjEmbedding S Y κ N b →
  (L.mul (N.pull s)).IsProjEmbedding (s ≫ b)
  | ⟨l, _, H⟩, ⟨k, _, G⟩ => ⟨l.mul (k.pull _), {}, by simp_all; grind [→ transition_self]⟩

/-- If L, with finitely many coordinates ι, is a projective embedding for s: X → S, then L is
the pull-back of O(1), cover and transition functions included, along a closed immersion of
X into ℙ^ι × S over S. -/
lemma LineBundle.IsProjEmbedding.exists_isClosedImmersion [Finite ι] (h : L.IsProjEmbedding s) :
    ∃ j, IsClosedImmersion j ∧ j ≫ Limits.prod.snd = s ∧
  ((hyperplaneBundle ι).pull Limits.prod.fst).pull j = L := (h.1.exists_hom_projSpace s).imp fun j
  a ↦ ⟨(IsClosedImmersion.iff_isProper_and_mono _).2 ⟨@.of_comp _ _ _ _ _ (a.1 ▸ h.2.1)
  isProjEmbedding_projSpace.2.1.1, ⟨by intros; apply h.ext <;> grind [=_ pull_comp]⟩⟩, a⟩

/-- If L embeds X in projective space over Spec R, then each U_i is affine and the chart map
R[X_j] → Γ(X, U_i), X_j ↦ g_ij (the transition function), is surjective. -/
lemma LineBundle.IsProjEmbedding.exists_affine_chart [Finite ι] {R s} (h :
  @IsProjEmbedding X (Spec R) ι L s) i : ∃ u : IsAffineOpen _, ∃ φ : MvPolynomial ι R →+* Γ(X,
  L.opens i), Surjective φ ∧ specMap (φ.comp C) = u.fromSpec ≫ s ∧ ∀ {A t}, LandsIn t (L.opens i) →
  ∀ P, ofSection (φ P) A t = eval₂Hom (Spec.preimage (t ≫ s)).hom (L.transition i · A t) P := by
  obtain ⟨⟨f, _, _, e⟩, W⟩ := h.exists_isClosedImmersion, @(isAffineOpen_chart i).preimage _ _ _ _
    (MorphismProperty.of_isPullback (.flip (.of_hasBinaryProduct' _ (Spec R))) inferInstance)
  refine have u := e ▸ W.preimage f; have I := by simpa using landsIn_fromSpec u (𝟙 _)
      ⟨u, eval₂Hom (Spec.preimage (u.fromSpec ≫ s)).hom (L.transition i · _ u.fromSpec), ?_, by
        simp [specMap], (map_evalSection_fromSpec u · ▸ by simp [(h.1.1 ..).1 _, I, hom_eval₂])⟩
  obtain ⟨⟨⟩, t, _, k⟩ := e,
    @exists_isHomogCoords (Spec R) _ ⟨_⟩ i (update .X i 1) (specMap C) (by simp)
  use have T := (k i).1.2 (by simp); (f.app_surjective _ W).forall.2 fun s ↦ ⟨_,
      (isRegularOn_ofSection s (ofHom (eval₂Hom ..)) t T).symm.trans
      ((congrArg _ (?_ : _ = _ ≫ f)).trans (ofSection_map_fromSpec u _ (𝟙 _)))⟩
  refine isProjEmbedding_projSpace.2.2 ⟨T.comp _,
    I, ?_⟩ ?_ <;> simp_all [↓((isLinearSystem_hyperplaneBundle.pull _).1 ..).1 _, ↓k i,
    ← Spec.map_comp, ← ofHom_comp, update, apply_ite, transition_self]

attribute [local simp] IsRegularOn LineBundle.transition_self landsIn_iInf

/-- The tensor product of the N_a over a in s (by default all a), on the common refinement of
all covers; for linear systems, the Segre product. -/
@[simps -fullyApplied] noncomputable def LineBundle.pi (s : _ := @univ Λ _) := mk
    (fun i : ∀ l, _ ↦ ⨅ a, (N a).opens (i a)) fun i j ↦ ∏ a ∈ s, (N a).transition (i a) (j a)

/-- The m-th tensor power of L, indexed by m-tuples of indices; for a linear system, the
Veronese system of all monomials of degree m. -/
noncomputable def LineBundle.pow (L : LineBundle X ι) m := pi fun _ : Fin m ↦ L

variable {S : _} {Λ : Type} [Fintype Λ] {ν : Λ → _} {N : ∀ l, LineBundle X (ν l)} {ι : Type} {L :
  LineBundle X ι} {Y : Scheme} (p : Y ⟶ X) (m)

@[simp] lemma LineBundle.picClass_pi s : (pi N s).picClass = ∑ l ∈ s, (N l).picClass :=
  .symm (by induction s using
  cons_induction <;> simp [*] <;> (apply picClass_eq_of_le (by tauto)) <;> simp [iInf_le, *])

lemma LineBundle.IsLinearSystem.pi (h : ∀ a, (N a).IsLinearSystem) :
  (LineBundle.pi N).IsLinearSystem := by
  simp_all [IsLinearSystem, IsHomogCoords, forall_and, Ring.eq_mul_inverse_iff_mul_eq,
    ← prod_mul_distrib]
  use fun _ _ _ _ a _ ↦ prod_eq_zero (mem_univ a) (by grind), by grind

lemma LineBundle.pull_pi : (pi N).pull p = pi (N · |>.pull p) := by ext <;> simp [Opens.coe_iInf]

/-- Segre: let W be proper over S, with finitely many S-maps π_l: W → Z_l that jointly separate
morphisms into W over S. If each N_l satisfies `LineBundle.IsProjEmbedding` on Z_l, so does the
Segre product of the π_l^*N_l on W. -/
lemma LineBundle.isProjEmbedding_pi {W : Over S} [IsProper W.hom] {Z : Λ → _} (π : ∀ l, W ⟶ Z l)
  {N : ∀ l, LineBundle _ (ν l)} (h : ∀ l, (N l).IsProjEmbedding (Z l).hom) (H : ∀ {T} {x y : T ⟶ W},
  (∀ l, x ≫ π l = y ≫ π l) → x = y) : (pi fun l ↦ (N l).pull (π l).left).IsProjEmbedding W.hom :=
  ⟨.pi (h · |>.1.pull _), {}, fun {c A a b} g
  o ↦ congr($(@H (.mk _) (homMk a o) (homMk b) fun l ↦ by ext; exact (@(h l).2.2 (c l) A (a ≫ _)
  (b ≫ _) (have := (g.2.2 <| update c l ·); by simp_all [prod_eq_single l]) (by simpa))).1)⟩

@[simp] lemma LineBundle.picClass_pow : (L.pow m).picClass = m • L.picClass := by simp [pow]

lemma LineBundle.IsProjEmbedding.pow {s} (h : @IsProjEmbedding X S _ L s) {m} (hm : m ≠ 0) :
  (L.pow m).IsProjEmbedding s := @isProjEmbedding_pi _ _
  _ _ (.mk s) h.2.1 _ (fun _ ↦ 𝟙 _) _ (by tauto) (· ⟨_, hm.pos⟩)
