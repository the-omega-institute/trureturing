/- GID: D5/S3/Quantum/TensorNetworks/NonFactorizableDoubledTriangle
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/NonFactorizableDoubledTriangle
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/TensorNetworks/NonFactorizableDoubledTriangle.claim; result=D5/S3/Quantum/TensorNetworks/NonFactorizableDoubledTriangle.result; claim=D5/S3/Quantum/TensorNetworks/NonFactorizableDoubledTriangle.claim
   digest: The doubled triangle obstructs factorizability by a parity product identity. -/

import D5.S1.Recurrence.Residue.ExponentialSquareWeightCatalanParity
import Mathlib.Basic.Real.Basic

namespace D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle

/-- The divisibility condition and the source's standing singleton assumption. -/
def WeightedSimplicialComplex {n : ℕ} (ω : Finset (Fin (n + 1)) → ℕ) : Prop :=
  (∀ S T, S ⊆ T → ω S ∣ ω T) ∧ ∀ i, ω {i} ≠ 0

/-- Each facet has exactly its weight many distinct copies. -/
def Multifacet {n : ℕ} (ω : Finset (Fin (n + 1)) → ℕ) :=
  Σ F : {S // Maximal (fun T => ω T ≠ 0) S}, Fin (ω F.val)

/-- The collapse map forgets the copy index. -/
def collapse {n : ℕ} {ω : Finset (Fin (n + 1)) → ℕ}
    (x : Multifacet ω) : Finset (Fin (n + 1)) := x.1.val

/-- The local multifacets at a vertex. -/
def Incident {n : ℕ} (ω : Finset (Fin (n + 1)) → ℕ) (i : Fin (n + 1)) :=
  {x : Multifacet ω // i ∈ collapse x}

/-- Both invariance of weights and linearity of collapse are required. -/
def Compatible {n : ℕ} (ω : Finset (Fin (n + 1)) → ℕ) (G : Type) [Group G]
    (A : MulAction G (Fin (n + 1))) (B : MulAction G (Multifacet ω)) : Prop :=
  letI := A
  letI := B
  (∀ (g : G) (S : Finset (Fin (n + 1))), ω (S.image (g • ·)) = ω S) ∧
    ∀ (g : G) (x : Multifacet ω), collapse (g • x) = (collapse x).image (g • ·)

/-- Collapse linearity makes inverse pullback well defined on local labelings. -/
def transport {n : ℕ} {ω : Finset (Fin (n + 1)) → ℕ} {G : Type} [Group G]
    {A : MulAction G (Fin (n + 1))} {B : MulAction G (Multifacet ω)}
    (h : Compatible ω G A B) {ι : Type} (g : G) (i : Fin (n + 1))
    (β : Incident ω i → ι) : Incident ω (A.smul g i) → ι :=
  letI := A
  letI := B
  fun x => β ⟨g⁻¹ • x.val, by
    rw [h.2]
    exact Finset.mem_image.mpr ⟨g • i, x.property, inv_smul_smul g i⟩⟩

/-- The source's cardinality, with an independently chosen stabilizer at each vertex. -/
noncomputable def K {n : ℕ} {ω : Finset (Fin (n + 1)) → ℕ} (G : Type) [Group G]
    (A : MulAction G (Fin (n + 1))) (B : MulAction G (Multifacet ω))
    {ι : Type} (α : Multifacet ω → ι) : ℕ :=
  Nat.card {γ : Multifacet ω → ι //
    ∀ i, ∃ g : G, A.smul g i = i ∧
      Subtype.restrict (fun x => i ∈ collapse x) ((@arrowAction _ _ _ _ B).smul g γ) =
      Subtype.restrict (fun x => i ∈ collapse x) α}

/-- Finite index sets are represented by `Fin m`, including the empty index set. -/
def Factorizable {n : ℕ} (ω : Finset (Fin (n + 1)) → ℕ) (G : Type) [Group G]
    [Fintype G] (A : MulAction G (Fin (n + 1))) (B : MulAction G (Multifacet ω))
    (h : Compatible ω G A B) : Prop :=
  ∀ m : ℕ, ∃ C : (i : Fin (n + 1)) → (Incident ω i → Fin m) → ℝ,
    (∀ i β, 0 < C i β) ∧
    (∀ g i β, C (A.smul g i) (transport h g i β) = C i β) ∧
    ∀ α, ∏ i, C i (Subtype.restrict (fun x => i ∈ collapse x) α) = (K G A B α : ℝ)⁻¹

/-- The universal assertion whose negation answers the source's question. -/
def claim : Prop :=
  ∀ (n : ℕ) (ω : Finset (Fin (n + 1)) → ℕ), WeightedSimplicialComplex ω →
    ∀ (G : Type) [Group G] [Fintype G]
      (A : MulAction G (Fin (n + 1))) (B : MulAction G (Multifacet ω))
      (h : Compatible ω G A B), Factorizable ω G A B h

private def triangle (S : Finset (Fin 3)) : ℕ :=
  if S.card ≤ 1 then 1 else if S.card = 2 then 2 else 0

private theorem triangle_valid : WeightedSimplicialComplex triangle := by
  unfold WeightedSimplicialComplex triangle
  decide

private theorem triangle_facets (S : Finset (Fin 3)) :
    Maximal (fun T => triangle T ≠ 0) S ↔ ∃ e : Fin 3, S = Finset.univ.erase e := by
  revert S
  unfold Maximal triangle
  decide

private theorem edge_weight (e : Fin 3) : triangle (Finset.univ.erase e) = 2 := by
  fin_cases e <;> decide

private def copy (x : Fin 3 × Fin 2) : Multifacet triangle :=
  ⟨⟨Finset.univ.erase x.1, (triangle_facets _).mpr ⟨x.1, rfl⟩⟩,
    Fin.cast (edge_weight x.1).symm x.2⟩

private theorem copy_bijective : Function.Bijective copy := by
  refine ⟨?_, ?_⟩
  · letI : DecidableEq (Multifacet triangle) := by unfold Multifacet; infer_instance
    decide
  rintro ⟨⟨S, hS⟩, k⟩
  obtain ⟨e, rfl⟩ := (triangle_facets S).mp hS
  refine ⟨(e, Fin.cast (edge_weight e) k), ?_⟩
  dsimp only [copy]
  congr 1

private noncomputable def copyEquiv : (Fin 3 × Fin 2) ≃ Multifacet triangle :=
  Equiv.ofBijective copy copy_bijective

private theorem copy_incident (i : Fin 3) (x : Fin 3 × Fin 2) :
    i ∈ collapse (copy x) ↔ i ≠ x.1 := by
  rw [collapse, copy]
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]

private def facetAction : MulAction (Multiplicative (ZMod 2)) (Multifacet triangle) where
  smul g x := ⟨x.1, if g = 1 then x.2 else x.2.rev⟩
  one_smul := by
    intro x
    change (⟨x.1, if (1 : Multiplicative (ZMod 2)) = 1 then x.2 else x.2.rev⟩ :
      Multifacet triangle) = x
    simp only [ite_true]
    cases x
    rfl
  mul_smul := by
    intro g h x
    change (⟨x.1, if g * h = 1 then x.2 else x.2.rev⟩ : Multifacet triangle) =
      ⟨x.1, if g = 1 then (if h = 1 then x.2 else x.2.rev)
        else (if h = 1 then x.2 else x.2.rev).rev⟩
    rcases (show g = 1 ∨ g = Multiplicative.ofAdd 1 from
      D5.S1.Recurrence.Residue.ExponentialSquareWeightCatalanParity.binary g.toAdd) with
      rfl | rfl <;>
      rcases (show h = 1 ∨ h = Multiplicative.ofAdd 1 from
        D5.S1.Recurrence.Residue.ExponentialSquareWeightCatalanParity.binary h.toAdd) with
        rfl | rfl <;>
      simp [show (Multiplicative.ofAdd (1 : ZMod 2)) ^ 2 = 1 from ZMod.natCast_self 2,
        show Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 from
          (one_ne_zero : (1 : ZMod 2) ≠ 0), ← pow_two]

private theorem copy_smul (g : Multiplicative (ZMod 2)) (x : Fin 3 × Fin 2) :
    facetAction.smul g (copy x) = copy (x.1, if g = 1 then x.2 else x.2.rev) := by
  by_cases hg : g = 1
  · subst g
    change copy x = copy (x.1, if (1 : Multiplicative (ZMod 2)) = 1 then x.2 else _)
    simp only [ite_true]
  · change (⟨(copy x).1, if g = 1 then (copy x).2 else (copy x).2.rev⟩ :
      Multifacet triangle) = _
    simp only [copy, hg, ↓reduceIte]
    congr 1
    exact (Fin.cast_rev _ _).symm

private theorem triangle_compatible :
    Compatible triangle (Multiplicative (ZMod 2))
      (MulAction.ofEndHom (1 : Multiplicative (ZMod 2) →* Function.End (Fin 3))) facetAction := by
  unfold Compatible
  constructor
  · intro g S
    change triangle (S.image id) = triangle S
    rw [Finset.image_id]
  · intro g x
    change x.1.val = x.1.val.image id
    rw [Finset.image_id]

private def rawLabel (a b c : Fin 2) (x : Fin 3 × Fin 2) : Fin 2 :=
  if x.2 = 0 then 0 else ![a, b, c] x.1

private noncomputable def alpha (a b c : Fin 2) : Multifacet triangle → Fin 2 :=
  rawLabel a b c ∘ copyEquiv.symm

private theorem alpha_copy (a b c : Fin 2) (x : Fin 3 × Fin 2) :
    alpha a b c (copy x) = rawLabel a b c x := by
  change rawLabel a b c (copyEquiv.symm (copyEquiv x)) = _
  rw [copyEquiv.symm_apply_apply]

private theorem local_pullback (g : Multiplicative (ZMod 2))
    (γ : Multifacet triangle → Fin 2) (a b c : Fin 2) (i : Fin 3) :
    Subtype.restrict (fun x => i ∈ collapse x) ((@arrowAction _ _ _ _ facetAction).smul g γ) =
      Subtype.restrict (fun x => i ∈ collapse x) (alpha a b c) ↔
      ∀ x : Fin 3 × Fin 2, i ≠ x.1 →
        γ (copy (x.1, if g = 1 then x.2 else x.2.rev)) = rawLabel a b c x := by
  constructor
  · intro h x hx
    have he := congrFun h ⟨copy x, (copy_incident i x).mpr hx⟩
    change γ (facetAction.smul g⁻¹ (copy x)) = alpha a b c (copy x) at he
    rw [copy_smul, alpha_copy] at he
    simpa only [inv_eq_one] using he
  · intro h
    funext ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := copy_bijective.surjective y
    change γ (facetAction.smul g⁻¹ (copy x)) = alpha a b c (copy x)
    rw [copy_smul, alpha_copy]
    simpa only [inv_eq_one] using h x ((copy_incident i x).mp hy)

private def Qualifies (a b c : Fin 2) (γ : (Fin 3 × Fin 2) → Fin 2) : Prop :=
  ∀ i : Fin 3,
    (∀ x, i ≠ x.1 → γ x = rawLabel a b c x) ∨
    (∀ x, i ≠ x.1 → γ (x.1, x.2.rev) = rawLabel a b c x)

private theorem count_transfer (a b c : Fin 2) :
    K (Multiplicative (ZMod 2))
      (MulAction.ofEndHom (1 : Multiplicative (ZMod 2) →* Function.End (Fin 3))) facetAction (alpha a b c) =
      Nat.card {γ : (Fin 3 × Fin 2) → Fin 2 // Qualifies a b c γ} := by
  unfold K
  apply Nat.card_congr
  refine (Equiv.arrowCongr copyEquiv.symm (Equiv.refl (Fin 2))).subtypeEquiv ?_
  intro γ
  change (∀ i, ∃ g : Multiplicative (ZMod 2),
    (MulAction.ofEndHom (1 : Multiplicative (ZMod 2) →* Function.End (Fin 3))).smul g i = i ∧
      Subtype.restrict (fun x => i ∈ collapse x) ((@arrowAction _ _ _ _ facetAction).smul g γ) =
      Subtype.restrict (fun x => i ∈ collapse x) (alpha a b c)) ↔
        Qualifies a b c (γ ∘ copy)
  unfold Qualifies
  apply forall_congr'
  intro i
  constructor
  · rintro ⟨g, _, hg⟩
    have ht := (local_pullback g γ a b c i).mp hg
    rcases (show g = 1 ∨ g = Multiplicative.ofAdd 1 from
      D5.S1.Recurrence.Residue.ExponentialSquareWeightCatalanParity.binary g.toAdd) with
        rfl | rfl
    · exact Or.inl (by simpa only [ite_true, Function.comp_apply] using ht)
    · exact Or.inr (by simpa only [(show Multiplicative.ofAdd (1 : ZMod 2) ≠ 1
        from (one_ne_zero : (1 : ZMod 2) ≠ 0)), ↓reduceIte, Function.comp_apply] using ht)
  · rintro (hi | hi)
    · refine ⟨1, rfl, (local_pullback 1 γ a b c i).mpr ?_⟩
      simpa only [ite_true, Function.comp_apply] using hi
    · refine ⟨Multiplicative.ofAdd 1, rfl,
        (local_pullback (Multiplicative.ofAdd 1) γ a b c i).mpr ?_⟩
      simpa only [(show Multiplicative.ofAdd (1 : ZMod 2) ≠ 1
        from (one_ne_zero : (1 : ZMod 2) ≠ 0)), ↓reduceIte, Function.comp_apply] using hi

private theorem raw_counts (a b c : Fin 2) :
    Nat.card {γ : (Fin 3 × Fin 2) → Fin 2 // Qualifies a b c γ} =
      if a = 0 ∧ b = 0 ∧ c = 0 then 1 else 2 := by
  unfold Qualifies
  rw [Nat.card_eq_fintype_card]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide

private theorem counts (a b c : Fin 2) :
    K (Multiplicative (ZMod 2))
      (MulAction.ofEndHom (1 : Multiplicative (ZMod 2) →* Function.End (Fin 3))) facetAction (alpha a b c) =
      if a = 0 ∧ b = 0 ∧ c = 0 then 1 else 2 := by
  rw [count_transfer, raw_counts]

private noncomputable def product (C : (i : Fin 3) → (Incident triangle i → Fin 2) → ℝ)
    (a b c : Fin 2) : ℝ := ∏ i, C i (Subtype.restrict (fun x => i ∈ collapse x) (alpha a b c))

private theorem restrict_alpha (a b c a' b' c' : Fin 2) (i : Fin 3)
    (h : ∀ e : Fin 3, e ≠ i → ![a, b, c] e = ![a', b', c'] e) :
    Subtype.restrict (fun x => i ∈ collapse x) (alpha a b c) =
      Subtype.restrict (fun x => i ∈ collapse x) (alpha a' b' c') := by
  funext ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := copy_bijective.surjective y
  change alpha a b c (copy x) = alpha a' b' c' (copy x)
  rw [alpha_copy, alpha_copy]
  unfold rawLabel
  split_ifs
  · rfl
  · exact h x.1 (Ne.symm ((copy_incident i x).mp hy))

private theorem parity_identity
    (C : (i : Fin 3) → (Incident triangle i → Fin 2) → ℝ) :
    product C 0 0 0 * product C 0 1 1 * product C 1 0 1 * product C 1 1 0 =
      product C 0 0 1 * product C 0 1 0 * product C 1 0 0 * product C 1 1 1 := by
  have h0 (a b c : Fin 2) : Subtype.restrict (fun x => 0 ∈ collapse x) (alpha a b c) =
      Subtype.restrict (fun x => 0 ∈ collapse x) (alpha 0 b c) := by
    apply restrict_alpha
    intro e he
    fin_cases e <;> simp_all
  have h1 (a b c : Fin 2) : Subtype.restrict (fun x => 1 ∈ collapse x) (alpha a b c) =
      Subtype.restrict (fun x => 1 ∈ collapse x) (alpha a 0 c) := by
    apply restrict_alpha
    intro e he
    fin_cases e <;> simp_all
  have h2 (a b c : Fin 2) : Subtype.restrict (fun x => 2 ∈ collapse x) (alpha a b c) =
      Subtype.restrict (fun x => 2 ∈ collapse x) (alpha a b 0) := by
    apply restrict_alpha
    intro e he
    fin_cases e <;> simp_all
  unfold product
  simp only [Fin.prod_univ_three, h0, h1, h2]
  ring

private theorem triangle_not_factorizable :
    ¬ Factorizable triangle (Multiplicative (ZMod 2))
      (MulAction.ofEndHom (1 : Multiplicative (ZMod 2) →* Function.End (Fin 3))) facetAction
      triangle_compatible := by
  intro h
  obtain ⟨C, _, _, hC⟩ := h 2
  have eqn (a b c : Fin 2) : product C a b c =
      ((if a = 0 ∧ b = 0 ∧ c = 0 then 1 else 2 : ℕ) : ℝ)⁻¹ := by
    exact (hC (alpha a b c)).trans (by rw [counts])
  have hp := parity_identity C
  rw [eqn, eqn, eqn, eqn, eqn, eqn, eqn, eqn] at hp
  norm_num at hp

theorem result : ¬ claim := by
  intro h
  exact triangle_not_factorizable
    (h 2 triangle triangle_valid (Multiplicative (ZMod 2))
      (MulAction.ofEndHom (1 : Multiplicative (ZMod 2) →* Function.End (Fin 3))) facetAction
      triangle_compatible)

end D5.S3.Quantum.TensorNetworks.NonFactorizableDoubledTriangle
