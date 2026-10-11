/- GID: D5/S3/HomologicalAlgebra/Solid/FiniteApproximationDifferences
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/FiniteApproximationDifferences
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.FiniteApproximationCodeBounds
import D5.S3.HomologicalAlgebra.Solid.FiniteApproximationFamily

/-!
The actual compact light-profinite parameter space for the representative
differences used in the generator retract. Every finite fiber is the stated
pair of representatives, and every infinity fiber is diagonal. Projection
onto the convergent sequence is surjective. No ordinary/derived free
descent or realization is asserted in this topology module.
New proofs, Apache-2.0; Rodriguez Camargo, Notes on Solid Geometry,
Lemma 3.3.2. The closure/fiber proof follows the accepted immutable
CWComparison.BinaryEdgeSpace pattern; no frozen source is modified.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits LightProfinite OnePoint

namespace CWSolid

def finiteApproximationDifferencePair (S : LightProfinite)
    (j : finiteApproximationIndex S) : S × S :=
  let a := (compatibleFiniteSection S j.1).val j.2
  (a, finiteApproximation S (j.1 - 1) a)

theorem finiteApproximationDifferencePair_proj (S : LightProfinite)
    (j : finiteApproximationIndex S) (m : ℕ) (hm : m ≤ j.1 - 1) :
    S.proj m (finiteApproximationDifferencePair S j).1 =
      S.proj m (finiteApproximationDifferencePair S j).2 := by
  exact (ConcreteCategory.congr_hom (finiteApproximation_projLE S hm)
    ((compatibleFiniteSection S j.1).val j.2)).symm

def finiteApproximationDifferencePairAt (S : LightProfinite) (s₀ : S)
    (k : ℕ) : S × S :=
  match @Encodable.decode₂ (finiteApproximationIndex S)
      (finiteApproximationIndexEncoding S) k with
  | none => (s₀, s₀)
  | Option.some j => finiteApproximationDifferencePair S j

theorem finiteApproximationDifferencePairAt_code (S : LightProfinite)
    (s₀ : S) (j : finiteApproximationIndex S) :
    finiteApproximationDifferencePairAt S s₀ (finiteApproximationIndexCode S j) =
      finiteApproximationDifferencePair S j := by
  letI := finiteApproximationIndexEncoding S
  simp only [finiteApproximationDifferencePairAt, finiteApproximationIndexCode,
    Encodable.decode₂_encode]

theorem finiteApproximationDifferencePairAt_proj (S : LightProfinite)
    (s₀ : S) (m k : ℕ) (hk : k ∉ finiteApproximationStageCodes S (m + 1)) :
    S.proj m (finiteApproximationDifferencePairAt S s₀ k).1 =
      S.proj m (finiteApproximationDifferencePairAt S s₀ k).2 := by
  letI := finiteApproximationIndexEncoding S
  cases hd : Encodable.decode₂ (finiteApproximationIndex S) k with
  | none => simp only [finiteApproximationDifferencePairAt, hd]
  | some j =>
    have hj : finiteApproximationIndexCode S j = k :=
      Encodable.decode₂_eq_some.mp hd
    have hn : m + 1 ≤ j.1 := by
      by_contra h
      exact hk (hj ▸ (finiteApproximationStageCodes_mem S (m + 1) j).mpr (by omega))
    simp only [finiteApproximationDifferencePairAt, hd]
    exact finiteApproximationDifferencePair_proj S j m (by omega)

def finiteApproximationDifferenceSpace (S : LightProfinite) (s₀ : S) :
    LightProfinite := by
  let C := closure (Set.range (fun k : ℕ =>
    ((k : OnePoint ℕ), finiteApproximationDifferencePairAt S s₀ k)))
  letI : CompactSpace C := isCompact_iff_compactSpace.mp isClosed_closure.isCompact
  exact LightProfinite.of C

def finiteApproximationDifferenceProjection (S : LightProfinite) (s₀ : S) :
    finiteApproximationDifferenceSpace S s₀ ⟶ LightProfinite.of (OnePoint ℕ) :=
  ConcreteCategory.ofHom ⟨fun p => p.val.1,
    continuous_fst.comp continuous_subtype_val⟩

def finiteApproximationDifferenceFirst (S : LightProfinite) (s₀ : S) :
    finiteApproximationDifferenceSpace S s₀ ⟶ S :=
  ConcreteCategory.ofHom ⟨fun p => p.val.2.1,
    continuous_fst.comp (continuous_snd.comp continuous_subtype_val)⟩

def finiteApproximationDifferenceSecond (S : LightProfinite) (s₀ : S) :
    finiteApproximationDifferenceSpace S s₀ ⟶ S :=
  ConcreteCategory.ofHom ⟨fun p => p.val.2.2,
    continuous_snd.comp (continuous_snd.comp continuous_subtype_val)⟩

def finiteApproximationDifferencePoint (S : LightProfinite) (s₀ : S) (k : ℕ) :
    finiteApproximationDifferenceSpace S s₀ :=
  ⟨((k : OnePoint ℕ), finiteApproximationDifferencePairAt S s₀ k),
    subset_closure ⟨k, rfl⟩⟩

theorem finiteApproximationDifference_finite_fiber (S : LightProfinite) (s₀ : S)
    (p : finiteApproximationDifferenceSpace S s₀) (k : ℕ)
    (hk : finiteApproximationDifferenceProjection S s₀ p = (k : OnePoint ℕ)) :
    p = finiteApproximationDifferencePoint S s₀ k := by
  have ho : IsOpen ({(k : OnePoint ℕ)} : Set (OnePoint ℕ)) := by
    exact (OnePoint.isOpen_iff_of_notMem (by simp)).2 (isOpen_discrete _)
  have hc : IsClosed {q : OnePoint ℕ × S × S |
      q.1 ≠ (k : OnePoint ℕ) ∨ q.2 = finiteApproximationDifferencePairAt S s₀ k} := by
    change IsClosed ((Prod.fst ⁻¹' ({(k : OnePoint ℕ)} : Set (OnePoint ℕ))ᶜ) ∪
      (Prod.snd ⁻¹' {finiteApproximationDifferencePairAt S s₀ k}))
    exact (ho.isClosed_compl.preimage continuous_fst).union
      (isClosed_singleton.preimage continuous_snd)
  have hs : Set.range (fun n : ℕ =>
      ((n : OnePoint ℕ), finiteApproximationDifferencePairAt S s₀ n)) ⊆
        {q : OnePoint ℕ × S × S |
          q.1 ≠ (k : OnePoint ℕ) ∨ q.2 = finiteApproximationDifferencePairAt S s₀ k} := by
    rintro _ ⟨n, rfl⟩
    by_cases h : n = k
    · subst n
      exact Or.inr rfl
    · exact Or.inl (fun hnk => h (OnePoint.coe_injective hnk))
  have h := closure_minimal hs hc p.property
  have he : p.val.2 = finiteApproximationDifferencePairAt S s₀ k :=
    h.resolve_left (not_not.mpr hk)
  exact Subtype.ext (Prod.ext hk he)

theorem finiteApproximationDifference_infty_proj (S : LightProfinite) (s₀ : S)
    (p : finiteApproximationDifferenceSpace S s₀)
    (hp : finiteApproximationDifferenceProjection S s₀ p = ∞) (m : ℕ) :
    S.proj m (finiteApproximationDifferenceFirst S s₀ p) =
      S.proj m (finiteApproximationDifferenceSecond S s₀ p) := by
  let B : Set (OnePoint ℕ) := OnePoint.some ''
    (↑(finiteApproximationStageCodes S (m + 1)) : Set ℕ)
  have hB : IsClosed B :=
    ((finiteApproximationStageCodes S (m + 1)).finite_toSet.image _).isClosed
  have hc : IsClosed {q : OnePoint ℕ × S × S |
      q.1 ∈ B ∨ S.proj m q.2.1 = S.proj m q.2.2} := by
    exact (hB.preimage continuous_fst).union
      (isClosed_eq ((S.proj m).hom.hom.continuous.comp
        (continuous_fst.comp continuous_snd))
        ((S.proj m).hom.hom.continuous.comp (continuous_snd.comp continuous_snd)))
  have hs : Set.range (fun k : ℕ =>
      ((k : OnePoint ℕ), finiteApproximationDifferencePairAt S s₀ k)) ⊆
        {q : OnePoint ℕ × S × S |
          q.1 ∈ B ∨ S.proj m q.2.1 = S.proj m q.2.2} := by
    rintro _ ⟨k, rfl⟩
    by_cases hk : k ∈ finiteApproximationStageCodes S (m + 1)
    · exact Or.inl ⟨k, hk, rfl⟩
    · exact Or.inr (finiteApproximationDifferencePairAt_proj S s₀ m k hk)
  have h := closure_minimal hs hc p.property
  apply h.resolve_left
  rw [show p.val.1 = ∞ from hp]
  simp [B]

theorem finiteApproximationDifference_infty_fiber (S : LightProfinite) (s₀ : S)
    (p : finiteApproximationDifferenceSpace S s₀)
    (hp : finiteApproximationDifferenceProjection S s₀ p = ∞) :
    finiteApproximationDifferenceFirst S s₀ p =
      finiteApproximationDifferenceSecond S s₀ p := by
  let a : LightProfinite.of PUnit.{1} ⟶ S :=
    ConcreteCategory.ofHom ⟨fun _ => finiteApproximationDifferenceFirst S s₀ p,
      continuous_const⟩
  let b : LightProfinite.of PUnit.{1} ⟶ S :=
    ConcreteCategory.ofHom ⟨fun _ => finiteApproximationDifferenceSecond S s₀ p,
      continuous_const⟩
  have hab : a = b := by
    apply S.asLimit.hom_ext
    rintro ⟨m⟩
    ext u
    exact finiteApproximationDifference_infty_proj S s₀ p hp m
  exact ConcreteCategory.congr_hom hab PUnit.unit

theorem finiteApproximationDifferenceProjection_surjective (S : LightProfinite) (s₀ : S) :
    Function.Surjective (finiteApproximationDifferenceProjection S s₀) := by
  have hc : IsClosed (Set.range (finiteApproximationDifferenceProjection S s₀)) :=
    isCompact_range (finiteApproximationDifferenceProjection S s₀).hom.hom.continuous |>.isClosed
  have hs : Set.range (OnePoint.some : ℕ → OnePoint ℕ) ⊆
      Set.range (finiteApproximationDifferenceProjection S s₀) := by
    rintro _ ⟨k, rfl⟩
    exact ⟨finiteApproximationDifferencePoint S s₀ k, rfl⟩
  intro r
  exact closure_minimal hs hc (OnePoint.denseRange_coe r)

end CWSolid
