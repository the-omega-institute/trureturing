/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SaturatedContactCompanions
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SaturatedContactCompanions
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Weighted saturation forces a companion for each two-axis contact. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.Q9TranslationAperiodicity

/-! Coordinate restrictions on contacts between weighted-saturated cube components. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SaturatedContactCompanions

open scoped BigOperators Matrix
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open Q9BoundaryGram (Exterior)
open Q9IsotropicHuang (parity weightedLinear)
open Q9SignedContactCells (weighted_cross)
open Q9WeightedBoundaryGram (gram_split signed signed_mulVec signed_transpose switched)
open Q9WeightedSaturation (Rows biadjacency defect signedBiadjacency
  exists_positive_gram_of_signed_defect_singular)
open private balanced_switch from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedBoundaryGram
open private cubeParity from D5.S3.Combinatorics.Graph.HypercubeSubQuorum

open Classical in
/-- A positive interior Gram vector gives an ambient parity vector whose
weighted image has no exterior entries. -/
private theorem exists_parity_supported_of_singular
    (C : Finset (Q 9)) (b : Bool)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hc : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hb : IsBalanced C) (w : Fin 9 → ℝ) (hw : ∀ i, 0 < w i)
    (hdet : (defect w (signedBiadjacency w C b)).det = 0) :
    ∃ f : Q 9 → ℝ, (∀ x, f x ≠ 0 ↔ x ∈ C ∧ parity x = b) ∧
      (∀ x ∉ C, weightedLinear w f x = 0) := by
  classical
  obtain ⟨u, hu, heig⟩ := exists_positive_gram_of_signed_defect_singular
    C b hr hc hb w hw hdet
  obtain ⟨s, hs, hswitch⟩ := balanced_switch (R := ℝ) C hb
  let r : Rows C b ↪ Q 9 := ⟨fun x => x.val.val, fun _ _ h => Subtype.ext (Subtype.ext h)⟩
  have hmem (x : Rows C b) : r x ∈ C ∧ parity (r x) = b :=
    ⟨x.val.property, (Finset.mem_filter.mp x.property).2⟩
  have hexact (x : Q 9) : (∃ y, r y = x) ↔ x ∈ C ∧ parity x = b := by
    constructor
    · rintro ⟨y, rfl⟩
      exact hmem y
    · rintro ⟨hx, hp⟩
      exact ⟨⟨⟨x, hx⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩⟩, rfl⟩
  have hsne (x : Q 9) : (s x : ℝ) ≠ 0 := by
    have h : (s x : ℝ) * (s x : ℝ) = 1 := by exact_mod_cast hs x
    exact fun hz => by simp [hz] at h
  let v : Rows C b → ℝ := fun x => (s (r x) : ℝ) * u x
  let f : Q 9 → ℝ := Function.extend r v 0
  have hfr (x : Rows C b) : f (r x) = v x := r.injective.extend_apply _ _ x
  have hf0 (x : Q 9) (hx : ¬ (x ∈ C ∧ parity x = b)) : f x = 0 :=
    Function.extend_apply' _ _ _ (fun h => hx ((hexact x).mp h))
  let K := (switched w s).submatrix r (fun y : Exterior C b => y.val.val)
  have hblock : K * Kᵀ = defect w (biadjacency w C b) := by
    have hB : (switched w s).submatrix r (fun y : Q9BoundaryGram.Interior C b => y.val.val) =
        biadjacency w C b := by
      ext x y
      exact hswitch w (r x) x.val.property y.val.val y.property
    have h := gram_split w s hs C b r (fun x => (hmem x).2)
    dsimp only at h
    rwa [hB] at h
  have hkernel : (K * Kᵀ) *ᵥ u = 0 := by
    rw [hblock, defect, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact sub_eq_zero.mpr heig.symm
  have hcross : Kᵀ *ᵥ u = 0 := by
    have h := congrArg (dotProduct u) hkernel
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      dotProduct_zero, dotProduct_self_eq_zero] at h
    exact h
  refine ⟨f, fun x => ?_, fun y hy => ?_⟩
  · constructor
    · intro h
      by_contra hn
      exact h (hf0 x hn)
    · intro hx
      obtain ⟨z, rfl⟩ := (hexact x).mpr hx
      rw [hfr]
      exact mul_ne_zero (hsne _) (hu z).ne'
  · by_cases hp : parity y = b
    · have hn : parity y ≠ !b := by simp [hp]
      exact weighted_cross w (fun x hx => hf0 x (fun h => hx h.2)) y hn
    · let j : Exterior C b := ⟨⟨y, hp⟩, hy⟩
      have hzero : (Kᵀ *ᵥ u) j = 0 := congrFun hcross j
      suffices hcompare : (Kᵀ *ᵥ u) j = (s y : ℝ) * weightedLinear w f y by
        rw [hcompare] at hzero
        exact (mul_eq_zero.mp hzero).resolve_left (hsne y)
      rw [← signed_mulVec]
      change (∑ x : Rows C b, switched w s (r x) y * u x) =
        (s y : ℝ) * ∑ x : Q 9, signed w y x * f x
      rw [Finset.mul_sum]
      refine Fintype.sum_of_injective r r.injective _ _ ?_ ?_
      · intro x hx
        rw [hf0 x (fun hm => hx ((hexact x).mpr hm)), mul_zero, mul_zero]
      · intro x
        rw [hfr, switched, show signed w (r x) y = signed w y (r x) from
          congrFun (congrFun (signed_transpose w) y) (r x)]
        dsimp only [v]
        ring

open scoped BigOperators Matrix
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_apply_same flip_flip flip_adj gamma gamma_apply)
open BalancedCubeGirth (gamma_anticommute)
open TwentyPointEightWord (gamma_square)
open Q9IsotropicHuang (parity weightedLinear)
open private huangMatrix cubeParity_ne_of_adj from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private weighted_sum weighted_selfAdjoint gamma_separated dot_disjoint opposite_eq from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedContactCells

/-- The C-side endpoint of a contact across flips in the prescribed axes. -/
def TwoFlipContact (C D : Finset (Q 9)) (b : Bool) (j k : Fin 9) (x : Q 9) : Prop :=
  k ≠ j ∧ x ∈ C ∧ parity x = b ∧ flip (flip x j) k ∈ D

/-- Axes that participate in a two-flip contact with the fixed axis on parity `b`. -/
def ActiveAxis (C D : Finset (Q 9)) (b : Bool) (j k : Fin 9) : Prop :=
  ∃ x, TwoFlipContact C D b j k x

/-- A necessary contact restriction for Hong–Wu–Xia, arXiv:2610.09483, Problem 2.
Each contact in axes `j,i` has a companion agreeing outside the other active axes. -/
theorem two_flip_contact_has_companion
    {C D : Finset (Q 9)} {b : Bool} {i j : Fin 9} {x : Q 9}
    (hdisj : Disjoint C D)
    (hsep : ∀ u ∈ C, ∀ v ∈ D, ¬ (hypercube 9).Adj u v)
    (f g : Q 9 → ℝ)
    (hf : ∀ z, f z ≠ 0 ↔ z ∈ C ∧ parity z = b)
    (hg : ∀ z, g z ≠ 0 ↔ z ∈ D ∧ parity z = b)
    (hAf : ∀ z ∉ C, weightedLinear (fun k => if k = i then 2 else 1) f z = 0)
    (hAg : ∀ z ∉ D, weightedLinear (fun _ => 1) g z = 0)
    (hx : TwoFlipContact C D b j i x) :
    ∃ y, y ≠ x ∧ TwoFlipContact C D b j i y ∧
      ∀ k, ¬ (ActiveAxis C D b j k ∧ k ≠ i) → y k = x k := by
  classical
  obtain ⟨hij, hxC, hxb, hxD⟩ := hx
  let w : Fin 9 → ℝ := fun k => if k = i then 2 else 1
  let Frozen (k : Fin 9) : Prop := ¬ (ActiveAxis C D b j k ∧ k ≠ i)
  let Matches (p z : Q 9) : Prop := ∀ k, Frozen k → z k = p k
  let proj (p : Q 9) (u : Q 9 → ℝ) : Q 9 → ℝ :=
    fun z => if Matches p z then u z else 0
  let B (p : Q 9) (k : Fin 9) : ℝ := proj p f ⬝ᵥ gamma j (gamma k g)
  have f_zero {z : Q 9} (hz : ¬ (z ∈ C ∧ parity z = b)) : f z = 0 := by
    by_contra hn
    exact hz ((hf z).mp hn)
  have f_support : ∀ z ∉ C, f z = 0 := fun z hz => f_zero (fun h => hz h.1)
  have g_support : ∀ z ∉ D, g z = 0 := by
    intro z hz
    by_contra hn
    exact hz ((hg z).mp hn).1
  have proj_support (p : Q 9) (u : Q 9 → ℝ) (hu : ∀ z ∉ C, u z = 0) :
      ∀ z ∉ C, proj p u z = 0 := by
    intro z hz
    simp [proj, hu z hz]
  have proj_dot (p : Q 9) (u v : Q 9 → ℝ) : u ⬝ᵥ proj p v = proj p u ⬝ᵥ v := by
    unfold dotProduct
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : Matches p z <;> simp [proj, hz]
  have flip_matches (p z : Q 9) (k : Fin 9) :
      Matches (flip p k) z ↔ Matches p (flip z k) := by
    have bit (l : Fin 9) : z l = flip p k l ↔ flip z k l = p l := by
      by_cases hlk : l = k
      · subst l
        cases hp : p k <;> cases hz : z k <;> simp [flip_apply_same, hp, hz]
      · simp [BalancedCriticalSpectrum.flip, hlk]
    exact ⟨fun h l hl => (bit l).mp (h l hl), fun h l hl => (bit l).mpr (h l hl)⟩
  have flip_proj (p : Q 9) (k : Fin 9) (u : Q 9 → ℝ) :
      gamma k (proj p u) = proj (flip p k) (gamma k u) := by
    funext z
    by_cases hz : Matches (flip p k) z
    · simp only [gamma_apply, proj, ite_eq_left hz, ite_eq_left ((flip_matches p z k).mp hz)]
    · have hn : ¬ Matches p (flip z k) := fun h => hz ((flip_matches p z k).mpr h)
      simp only [gamma_apply, proj, ite_eq_right hz, ite_eq_right hn, mul_zero]
  have same_proj (p : Q 9) {k : Fin 9} (hk : ActiveAxis C D b j k ∧ k ≠ i) :
      proj (flip p k) = proj p := by
    funext u z
    have bit (l : Fin 9) (hl : Frozen l) : flip p k l = p l := by
      have hlk : l ≠ k := fun he => hl (he.symm ▸ hk)
      simp [BalancedCriticalSpectrum.flip, hlk]
    have hm : Matches (flip p k) z ↔ Matches p z :=
      ⟨fun h l hl => (h l hl).trans (bit l hl), fun h l hl => (h l hl).trans (bit l hl).symm⟩
    simp [proj, hm]
  have contact_sum (p : Q 9) (k : Fin 9) :
      B p k = ∑ z, if Matches p z then f z * gamma j (gamma k g) z else 0 := by
    unfold B dotProduct
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : Matches p z <;> simp [proj, hz]
  have contact_zero {k : Fin 9} (hkj : k ≠ j) (z : Q 9)
      (hn : ¬ TwoFlipContact C D b j k z) :
      f z * gamma j (gamma k g) z = 0 := by
    by_cases hz : z ∈ C ∧ parity z = b
    · have hd : flip (flip z j) k ∉ D := fun h => hn ⟨hkj, hz.1, hz.2, h⟩
      simp only [gamma_apply, g_support _ hd, mul_zero]
    · rw [f_zero hz, zero_mul]
  have inactive (p : Q 9) (k : Fin 9) (hk : ¬ ActiveAxis C D b j k) : B p k = 0 := by
    by_cases hkj : k = j
    · subst k
      simpa only [B, gamma_square] using dot_disjoint hdisj (proj_support p f f_support) g_support
    · rw [contact_sum]
      apply Finset.sum_eq_zero
      intro z _
      simp only [contact_zero hkj z (fun h => hk ⟨z, h⟩), ite_self]
  have unit_sum (p : Q 9) : (∑ k, B p k) = 0 := by
    have h := gamma_separated hsep j (proj_support p f f_support) hAg
    simpa only [weighted_sum, one_smul, map_sum, dotProduct_sum, B] using h
  have move_flip (p : Q 9) (k : Fin 9) :
      f ⬝ᵥ gamma k (proj p (gamma j g)) = -B (flip p k) k := by
    rw [flip_proj, proj_dot]
    by_cases hkj : k = j
    · subst k
      simp only [B, gamma_square, dot_disjoint hdisj (proj_support (flip p j) f f_support)
        g_support, neg_zero]
    · simp only [B, gamma_anticommute hkj, dotProduct_neg]
  have weighted_sum_zero (p : Q 9) : (∑ k, w k * B (flip p k) k) = 0 := by
    have h := gamma_separated hsep j (proj_support p (weightedLinear w f) hAf) g_support
    rw [← proj_dot p, weighted_selfAdjoint] at h
    simpa only [weighted_sum, dotProduct_sum, dotProduct_smul, smul_eq_mul, move_flip, mul_neg,
      Finset.sum_neg_distrib, neg_eq_zero] using h
  have relation (p : Q 9) : B p i = 2 * B (flip p i) i := by
    have h₁ := unit_sum p
    have h₂ := weighted_sum_zero p
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at h₁ h₂
    have hrest : (∑ k ∈ Finset.univ.erase i, w k * B (flip p k) k) =
        ∑ k ∈ Finset.univ.erase i, B p k := by
      apply Finset.sum_congr rfl
      intro k hk
      have hki := Finset.ne_of_mem_erase hk
      have heq : B (flip p k) k = B p k := by
        by_cases ha : ActiveAxis C D b j k
        · simp only [B, same_proj p ⟨ha, hki⟩]
        · rw [inactive (flip p k) k ha, inactive p k ha]
      simp [w, hki, heq]
    rw [hrest, show w i = 2 by simp [w]] at h₂
    exact add_left_cancel (h₁.trans h₂.symm)
  have cell_zero : B x i = 0 := by
    have h₁ := relation x
    have h₂ := relation (flip x i)
    rw [BalancedCriticalSpectrum.flip_flip] at h₂
    linarith only [h₁, h₂]
  by_contra hn
  have single_contact : B x i = f x * gamma j (gamma i g) x := by
    rw [contact_sum, Finset.sum_eq_single x]
    · simp [Matches]
    · intro y _ hy
      by_cases hm : Matches x y
      · have hc : ¬ TwoFlipContact C D b j i y := fun h => hn ⟨y, hy, h, hm⟩
        simp only [ite_eq_left hm, contact_zero hij y hc]
      · exact ite_eq_right hm
    · simp
  have parity_flip (z : Q 9) (k : Fin 9) : parity (flip z k) = !parity z :=
    opposite_eq (cubeParity_ne_of_adj (flip_adj z k)).symm
  have endpoint_parity : parity (flip (flip x j) i) = b := by
    rw [parity_flip (flip x j) i, parity_flip x j, Bool.not_not, hxb]
  have edge_ne (z : Q 9) (k : Fin 9) : huangMatrix 9 z (flip z k) ≠ 0 := by
    intro hz
    have hs := SupportedEigenSaturation.matrix_sq_of_adj (flip_adj z k)
    rw [hz] at hs
    norm_num at hs
  have gamma_ne : gamma j (gamma i g) x ≠ 0 := by
    rw [gamma_apply, gamma_apply]
    exact mul_ne_zero (edge_ne x j) (mul_ne_zero (edge_ne (flip x j) i)
      ((hg _).mpr ⟨hxD, endpoint_parity⟩))
  exact (mul_ne_zero ((hf x).mpr ⟨hxC, hxb⟩) gamma_ne) (single_contact.symm.trans cell_zero)


/-- The displacement graph of two saturated components has at least three
possible partners for every axis incident to a contact. -/
private theorem contact_axis_has_two_other_partners
    {C D : Finset (Q 9)} {b : Bool} {j i : Fin 9} {x y : Q 9}
    (hx : TwoFlipContact C D b j i x) (hy : TwoFlipContact C D b j i y)
    (hne : y ≠ x)
    (hagree : ∀ k, ¬ (ActiveAxis C D b j k ∧ k ≠ i) → y k = x k) :
    ∃ k l, k ≠ l ∧ k ≠ i ∧ l ≠ i ∧ ActiveAxis C D b j k ∧ ActiveAxis C D b j l := by
  classical
  have hn0 : hammingDist y x ≠ 0 := fun h => hne (hammingDist_eq_zero.mp h)
  have hn1 : hammingDist y x ≠ 1 := fun h =>
    cubeParity_ne_of_adj (show (hypercube 9).Adj y x from h) (hy.2.2.1.trans hx.2.2.1.symm)
  have hcard : 1 < (Finset.univ.filter fun k : Fin 9 => y k ≠ x k).card := by
    change 1 < hammingDist y x
    omega
  obtain ⟨k, hk, l, hl, hkl⟩ := Finset.one_lt_card.mp hcard
  have hactive (a : Fin 9) (ha : y a ≠ x a) : ActiveAxis C D b j a ∧ a ≠ i := by
    by_contra hn
    exact ha (hagree a hn)
  obtain ⟨hka, hki⟩ := hactive k (Finset.mem_filter.mp hk).2
  obtain ⟨hla, hli⟩ := hactive l (Finset.mem_filter.mp hl).2
  exact ⟨k, l, hkl, hki, hli, hka, hla⟩

open scoped Matrix
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q)
open TwoBalancedComponents (componentFinset componentFinset_subset)
open Q9IsotropicHuang (parity)
open Translation.Q9ActualAperiodicity
  (exists_two_aperiodic_components signed_defect_det_eq_component)
open private component_connected from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.Q9TranslationAperiodicity
open private componentFinset_disjoint componentFinset_neighbor_closed from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwoBalancedComponents

open Classical in
/-- Two actual components of a subcubic 258-set satisfy the companion condition
in both orders. Each axis of a contact has at least two other partners. -/
theorem exists_two_components_with_two_flip_companions
    (U : Finset (Q 9)) (hU : U.card = 258)
    (hdeg : ∀ x : (U : Set (Q 9)), ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3) :
    ∃ C D : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent,
      C ≠ D ∧ ∀ A B, (A = C ∧ B = D) ∨ (A = D ∧ B = C) →
        ∀ (i j : Fin 9) (x : Q 9),
          TwoFlipContact (componentFinset U A) (componentFinset U B) false j i x →
          (∃ y, y ≠ x ∧ TwoFlipContact (componentFinset U A) (componentFinset U B) false j i y ∧
            ∀ k, ¬ (ActiveAxis (componentFinset U A) (componentFinset U B) false j k ∧ k ≠ i) →
              y k = x k) ∧
          ∃ k l, k ≠ l ∧ k ≠ i ∧ l ≠ i ∧
            ActiveAxis (componentFinset U A) (componentFinset U B) false j k ∧
            ActiveAxis (componentFinset U A) (componentFinset U B) false j l := by
  obtain ⟨C, D, hne, hcomponents⟩ := exists_two_aperiodic_components U hU hdeg
  refine ⟨C, D, hne, fun A B hab i j x hx => ?_⟩
  have hA : A = C ∨ A = D := hab.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hB : B = C ∨ B = D := hab.elim (fun h => Or.inr h.2) (fun h => Or.inl h.2)
  have hAB : A ≠ B := by rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exacts [hne, hne.symm]
  let S := componentFinset U A
  let T := componentFinset U B
  have hdisj : Disjoint S T := componentFinset_disjoint U A B hAB
  have hsep : ∀ u ∈ S, ∀ v ∈ T, ¬ (hypercube 9).Adj u v := by
    intro u hu v hv hadj
    have hvS := componentFinset_neighbor_closed U A u hu v (componentFinset_subset U B hv) hadj
    exact Finset.disjoint_left.mp hdisj hvS hv
  obtain ⟨hra, hba, hdeta, _⟩ := hcomponents A hA
  obtain ⟨hrb, hbb, hdetb, _⟩ := hcomponents B hB
  let w : Fin 9 → ℝ := fun k => if k = i then 2 else 1
  have hw (k : Fin 9) : 0 < w k := by
    dsimp only [w]
    split <;> norm_num
  obtain ⟨f, hf, hAf⟩ := exists_parity_supported_of_singular S false hra (component_connected U A)
    hba w hw ((signed_defect_det_eq_component w U false A).trans (hdeta w))
  obtain ⟨g, hg, hAg⟩ := exists_parity_supported_of_singular T false hrb (component_connected U B)
    hbb (fun _ => 1) (fun _ => zero_lt_one)
    ((signed_defect_det_eq_component (fun _ => 1) U false B).trans (hdetb fun _ => 1))
  obtain ⟨y, hne, hcontact, hagree⟩ :=
    two_flip_contact_has_companion hdisj hsep f g hf hg hAf hAg hx
  exact ⟨⟨y, hne, hcontact, hagree⟩, contact_axis_has_two_other_partners hx hcontact hne hagree⟩

#print axioms exists_two_components_with_two_flip_companions

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SaturatedContactCompanions
