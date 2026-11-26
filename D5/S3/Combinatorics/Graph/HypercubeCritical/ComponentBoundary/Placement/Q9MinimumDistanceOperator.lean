/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9MinimumDistanceOperator
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9MinimumDistanceOperator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Weighted signed coordinate flips cancel minimum-distance contacts in each coordinate cell. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointEightWord
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedContactCells
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.MinimumContactDisplacementCount

/-! Minimum-distance contact restrictions for Hong–Wu–Xia, arXiv:2610.09483, Problem 2. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator

open scoped BigOperators Matrix
open BalancedCriticalSpectrum (Q flip flip_adj flip_apply_same flip_flip gamma gamma_apply)
open BalancedCubeGirth (gamma_anticommute)
open TwentyPointEightWord (gamma_square wordGamma)
open Q9IsotropicHuang (parity weightedLinear)
open private huangMatrix cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private weighted_sum weighted_selfAdjoint opposite_eq from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedContactCells

private theorem wordGamma_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (word : List (Fin n)) (v : ι → Q n → ℝ) :
    wordGamma word (∑ j, v j) = ∑ j, wordGamma word (v j) := by
  induction word with
  | nil => rfl
  | cons a word ih =>
      change gamma a (wordGamma word (∑ j, v j)) = ∑ j, gamma a (wordGamma word (v j))
      rw [ih, map_sum]

private theorem gamma_wordGamma_of_not_mem {n : ℕ} (k : Fin n) (word : List (Fin n))
    (hk : k ∉ word) (u : Q n → ℝ) :
    gamma k (wordGamma word u) =
      (-1 : ℝ) ^ word.length • wordGamma word (gamma k u) := by
  induction word with
  | nil => simp [wordGamma]
  | cons a word ih =>
      have hka : k ≠ a := fun h => hk (List.mem_cons.mpr (Or.inl h))
      have hkw : k ∉ word := fun h => hk (List.mem_cons.mpr (Or.inr h))
      change gamma k (gamma a (wordGamma word u)) =
        (-1 : ℝ) ^ (word.length + 1) • gamma a (wordGamma word (gamma k u))
      rw [gamma_anticommute hka, ih hkw, map_smul]
      simp only [pow_succ', mul_smul, neg_one_smul]

/-- A flip in either position cancels its occurrence in a nodup word, up to sign. -/
private theorem wordGamma_cancel_axis {n : ℕ} (k : Fin n) (word : List (Fin n))
    (hnd : word.Nodup) (hk : k ∈ word) (u : Q n → ℝ) :
    ∃ short : List (Fin n), short.length + 1 = word.length ∧ ∃ l r : ℝ,
      gamma k (wordGamma word u) = l • wordGamma short u ∧
      wordGamma word (gamma k u) = r • wordGamma short u := by
  induction word with
  | nil => simp at hk
  | cons a word ih =>
      obtain ⟨ha, hw⟩ := List.nodup_cons.mp hnd
      rcases List.mem_cons.mp hk with hka | hkw
      · subst a
        refine ⟨word, rfl, 1, (-1 : ℝ) ^ word.length, ?_, ?_⟩
        · change gamma k (gamma k (wordGamma word u)) = 1 • wordGamma word u
          rw [gamma_square, one_smul]
        · change gamma k (wordGamma word (gamma k u)) =
            (-1 : ℝ) ^ word.length • wordGamma word u
          rw [gamma_wordGamma_of_not_mem k word ha, gamma_square]
      · have hka : k ≠ a := fun h => ha (h ▸ hkw)
        obtain ⟨short, hlen, l, r, hleft, hright⟩ := ih hw hkw
        refine ⟨a :: short, ?_, -l, r, ?_, ?_⟩
        · simp only [List.length_cons]
          omega
        · change gamma k (gamma a (wordGamma word u)) = (-l) • gamma a (wordGamma short u)
          rw [gamma_anticommute hka, hleft, map_smul, neg_smul]
        · change gamma a (wordGamma word (gamma k u)) = r • gamma a (wordGamma short u)
          rw [hright, map_smul]

/-- Every word of signed flips evaluates at its ordinary endpoint with a nonzero sign. -/
private theorem wordGamma_apply_ne_zero {n : ℕ} (word : List (Fin n))
    (u : Q n → ℝ) (z : Q n) :
    wordGamma word u z ≠ 0 ↔ u (word.foldl flip z) ≠ 0 := by
  induction word generalizing z with
  | nil => rfl
  | cons a word ih =>
      change gamma a (wordGamma word u) z ≠ 0 ↔ u (word.foldl flip (flip z a)) ≠ 0
      have hs : huangMatrix n z (flip z a) ≠ 0 := by
        intro hz
        have h := SupportedEigenSaturation.matrix_sq_of_adj (flip_adj z a)
        rw [hz] at h
        norm_num at h
      rw [gamma_apply, mul_ne_zero_iff_left hs]
      exact ih (flip z a)

private theorem hammingDist_foldl_flip_le {n : ℕ} (word : List (Fin n)) (z : Q n) :
    hammingDist z (word.foldl flip z) ≤ word.length := by
  induction word generalizing z with
  | nil => simp
  | cons a word ih =>
      change hammingDist z (word.foldl flip (flip z a)) ≤ word.length + 1
      have hstep : hammingDist z (flip z a) = 1 := flip_adj z a
      have htri := hammingDist_triangle z (flip z a) (word.foldl flip (flip z a))
      rw [hstep] at htri
      have htail := ih (flip z a)
      omega

private theorem wordGamma_pairing_eq_zero {n : ℕ} (word : List (Fin n))
    {C D : Finset (Q n)} {f g : Q n → ℝ}
    (hf : ∀ z ∉ C, f z = 0) (hg : ∀ z ∉ D, g z = 0)
    (hsep : ∀ u ∈ C, ∀ v ∈ D, word.length < hammingDist u v) :
    f ⬝ᵥ wordGamma word g = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro z _
  by_cases hz : z ∈ C
  · have hend : word.foldl flip z ∉ D := fun hv =>
      (not_lt_of_ge (hammingDist_foldl_flip_le word z)) (hsep z hz _ hv)
    have hzero : wordGamma word g z = 0 := by
      by_contra hn
      exact ((wordGamma_apply_ne_zero word g z).mp hn) (hg _ hend)
    rw [hzero, mul_zero]
  · rw [hf z hz, zero_mul]

/-- The endpoint parity after toggling the coordinates of a word. -/
def wordParity (word : List (Fin 9)) (b : Bool) : Bool :=
  word.foldl (fun p _ => !p) b

private theorem parity_flip (z : Q 9) (k : Fin 9) : parity (flip z k) = !parity z :=
  opposite_eq (cubeParity_ne_of_adj (flip_adj z k)).symm

private theorem parity_foldl_flip (word : List (Fin 9)) (z : Q 9) :
    parity (word.foldl flip z) = wordParity word (parity z) := by
  induction word generalizing z with
  | nil => rfl
  | cons a word ih =>
      change parity (word.foldl flip (flip z a)) = wordParity word (!parity z)
      rw [ih, parity_flip]

/-- The initial endpoint of a contact reached by extending the ridge with one new axis. -/
def RidgeContact (C D : Finset (Q 9)) (b : Bool) (ridge : List (Fin 9))
    (k : Fin 9) (z : Q 9) : Prop :=
  k ∉ ridge ∧ z ∈ C ∧ parity z = b ∧ flip (ridge.foldl flip z) k ∈ D

private theorem RidgeContact.hammingDist_eq {C D : Finset (Q 9)} {b : Bool}
    {ridge : List (Fin 9)} {k : Fin 9} {z : Q 9}
    (hsep : ∀ u ∈ C, ∀ v ∈ D, ridge.length + 1 ≤ hammingDist u v)
    (hz : RidgeContact C D b ridge k z) :
    hammingDist z (flip (ridge.foldl flip z) k) = ridge.length + 1 := by
  apply le_antisymm ?_ (hsep z hz.2.1 _ hz.2.2.2)
  simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_append,
    List.length_singleton] using hammingDist_foldl_flip_le (ridge ++ [k]) z

/-- An extension axis is active if it occurs in a contact on the chosen parity. -/
def RidgeActiveAxis (C D : Finset (Q 9)) (b : Bool) (ridge : List (Fin 9))
    (k : Fin 9) : Prop :=
  ∃ z, RidgeContact C D b ridge k z

/-- Contact cells fix the chosen extension axis and every inactive coordinate. -/
def SameContactCell (C D : Finset (Q 9)) (b : Bool) (ridge : List (Fin 9))
    (i : Fin 9) (p z : Q 9) : Prop :=
  ∀ k, ¬ (RidgeActiveAxis C D b ridge k ∧ k ≠ i) → z k = p k

private theorem contact_product_ne_zero {C D : Finset (Q 9)} {b : Bool}
    {ridge : List (Fin 9)} (f g : Q 9 → ℝ)
    (hf : ∀ z, f z ≠ 0 ↔ z ∈ C ∧ parity z = b)
    (hg : ∀ z, g z ≠ 0 ↔ z ∈ D ∧ parity z = !(wordParity ridge b))
    {k : Fin 9} (hk : k ∉ ridge) (z : Q 9) :
    f z * wordGamma ridge (gamma k g) z ≠ 0 ↔ RidgeContact C D b ridge k z := by
  have hright : wordGamma ridge (gamma k g) z ≠ 0 ↔
      g (flip (ridge.foldl flip z) k) ≠ 0 :=
    (wordGamma_apply_ne_zero ridge (gamma k g) z).trans
      (wordGamma_apply_ne_zero [k] g (ridge.foldl flip z))
  rw [mul_ne_zero_iff, hf z, hright, hg]
  constructor
  · rintro ⟨⟨hzC, hzb⟩, hzD, _⟩
    exact ⟨hk, hzC, hzb, hzD⟩
  · rintro ⟨_, hzC, hzb, hzD⟩
    exact ⟨⟨hzC, hzb⟩, hzD, by rw [parity_flip, parity_foldl_flip, hzb]⟩

open Classical in
/-- The signed contact contributions for an arbitrary ridge cancel on each contact cell. -/
theorem minimum_distance_contact_cell_cancels
    {C D : Finset (Q 9)} {b : Bool} {ridge : List (Fin 9)} {i : Fin 9}
    (hnd : ridge.Nodup)
    (hsep : ∀ u ∈ C, ∀ v ∈ D, ridge.length + 1 ≤ hammingDist u v)
    (f g : Q 9 → ℝ)
    (hf : ∀ z, f z ≠ 0 ↔ z ∈ C ∧ parity z = b)
    (hg : ∀ z, g z ≠ 0 ↔ z ∈ D ∧ parity z = !(wordParity ridge b))
    (hAf : ∀ z ∉ C, weightedLinear (fun k => if k = i then 2 else 1) f z = 0)
    (hAg : ∀ z ∉ D, weightedLinear (fun _ => 1) g z = 0)
    (p : Q 9) :
    (∑ z, if SameContactCell C D b ridge i p z then
      f z * wordGamma ridge (gamma i g) z else 0) = 0 := by
  classical
  let w : Fin 9 → ℝ := fun k => if k = i then 2 else 1
  let Frozen (k : Fin 9) : Prop := ¬ (RidgeActiveAxis C D b ridge k ∧ k ≠ i)
  let Matches (p z : Q 9) : Prop := SameContactCell C D b ridge i p z
  let proj (p : Q 9) (u : Q 9 → ℝ) : Q 9 → ℝ :=
    fun z => if Matches p z then u z else 0
  let B (p : Q 9) (k : Fin 9) : ℝ := proj p f ⬝ᵥ wordGamma ridge (gamma k g)
  have f_support : ∀ z ∉ C, f z = 0 := by
    intro z hz
    by_contra hn
    exact hz ((hf z).mp hn).1
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
    change (∀ l, Frozen l → z l = flip p k l) ↔
      (∀ l, Frozen l → flip z k l = p l)
    exact ⟨fun h l hl => (bit l).mp (h l hl), fun h l hl => (bit l).mpr (h l hl)⟩
  have flip_proj (p : Q 9) (k : Fin 9) (u : Q 9 → ℝ) :
      gamma k (proj p u) = proj (flip p k) (gamma k u) := by
    funext z
    by_cases hz : Matches (flip p k) z
    · simp only [gamma_apply, proj, ite_eq_left hz, ite_eq_left ((flip_matches p z k).mp hz)]
    · have hn : ¬ Matches p (flip z k) := fun h => hz ((flip_matches p z k).mpr h)
      simp only [gamma_apply, proj, ite_eq_right hz, ite_eq_right hn, mul_zero]
  have same_proj (p : Q 9) {k : Fin 9} (hk : RidgeActiveAxis C D b ridge k ∧ k ≠ i) :
      proj (flip p k) = proj p := by
    funext u z
    have bit (l : Fin 9) (hl : Frozen l) : flip p k l = p l := by
      have hlk : l ≠ k := fun he => hl (he.symm ▸ hk)
      simp [BalancedCriticalSpectrum.flip, hlk]
    have hm : Matches (flip p k) z ↔ Matches p z := by
      change (∀ l, Frozen l → z l = flip p k l) ↔ (∀ l, Frozen l → z l = p l)
      exact ⟨fun h l hl => (h l hl).trans (bit l hl),
        fun h l hl => (h l hl).trans (bit l hl).symm⟩
    simp [proj, hm]
  have contact_sum (p : Q 9) (k : Fin 9) :
      B p k = ∑ z, if Matches p z then f z * wordGamma ridge (gamma k g) z else 0 := by
    unfold B dotProduct
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : Matches p z <;> simp [proj, hz]
  have ridge_short : ∀ u ∈ C, ∀ v ∈ D, ridge.length < hammingDist u v :=
    fun u hu v hv => Nat.lt_of_succ_le (hsep u hu v hv)
  have repeated (p : Q 9) (k : Fin 9) (hk : k ∈ ridge) :
      B p k = 0 ∧ proj p f ⬝ᵥ gamma k (wordGamma ridge g) = 0 := by
    obtain ⟨short, hlen, l, r, hleft, hright⟩ := wordGamma_cancel_axis k ridge hnd hk g
    have hs : ∀ u ∈ C, ∀ v ∈ D, short.length < hammingDist u v := by
      intro u hu v hv
      have h := ridge_short u hu v hv
      omega
    have h := wordGamma_pairing_eq_zero short (proj_support p f f_support) g_support hs
    constructor
    · change proj p f ⬝ᵥ wordGamma ridge (gamma k g) = 0
      rw [hright, dotProduct_smul, h, smul_zero]
    · rw [hleft, dotProduct_smul, h, smul_zero]
  have inactive (p : Q 9) (k : Fin 9) (hk : ¬ RidgeActiveAxis C D b ridge k) :
      B p k = 0 := by
    by_cases hkr : k ∈ ridge
    · exact (repeated p k hkr).1
    · rw [contact_sum]
      apply Finset.sum_eq_zero
      intro z _
      have hz : f z * wordGamma ridge (gamma k g) z = 0 := by
        by_contra hn
        exact hk ⟨z, (contact_product_ne_zero f g hf hg hkr z).mp hn⟩
      simp only [hz, ite_self]
  have unit_sum (p : Q 9) : (∑ k, B p k) = 0 := by
    have h := wordGamma_pairing_eq_zero ridge (proj_support p f f_support) hAg ridge_short
    simpa only [weighted_sum, one_smul, wordGamma_sum, dotProduct_sum, B] using h
  have move_flip (p : Q 9) (k : Fin 9) :
      f ⬝ᵥ gamma k (proj p (wordGamma ridge g)) =
        (-1 : ℝ) ^ ridge.length * B (flip p k) k := by
    rw [flip_proj, proj_dot]
    by_cases hk : k ∈ ridge
    · obtain ⟨hr, hl⟩ := repeated (flip p k) k hk
      rw [hl, hr, mul_zero]
    · simp only [gamma_wordGamma_of_not_mem k ridge hk, dotProduct_smul, smul_eq_mul, B]
  have weighted_sum_zero (p : Q 9) : (∑ k, w k * B (flip p k) k) = 0 := by
    have h := wordGamma_pairing_eq_zero ridge (proj_support p (weightedLinear w f) hAf)
      g_support ridge_short
    rw [← proj_dot p, weighted_selfAdjoint] at h
    simp only [weighted_sum, dotProduct_sum, dotProduct_smul, smul_eq_mul, move_flip] at h
    have hfactor :
        (∑ k, w k * ((-1 : ℝ) ^ ridge.length * B (flip p k) k)) =
          (-1 : ℝ) ^ ridge.length * ∑ k, w k * B (flip p k) k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hfactor] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ (by norm_num))
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
        by_cases ha : RidgeActiveAxis C D b ridge k
        · simp only [B, same_proj p ⟨ha, hki⟩]
        · rw [inactive (flip p k) k ha, inactive p k ha]
      simp [w, hki, heq]
    rw [hrest, show w i = 2 by simp [w]] at h₂
    exact add_left_cancel (h₁.trans h₂.symm)
  have hB : B p i = 0 := by
    have h₁ := relation p
    have h₂ := relation (flip p i)
    rw [BalancedCriticalSpectrum.flip_flip] at h₂
    linarith only [h₁, h₂]
  exact (contact_sum p i).symm.trans hB

/-- Each minimum-distance contact has a distinct companion agreeing at every
coordinate except possibly the other active extension axes. -/
theorem minimum_distance_contact_has_companion
    {C D : Finset (Q 9)} {b : Bool} {ridge : List (Fin 9)} {i : Fin 9} {x : Q 9}
    (hnd : ridge.Nodup)
    (hsep : ∀ u ∈ C, ∀ v ∈ D, ridge.length + 1 ≤ hammingDist u v)
    (f g : Q 9 → ℝ)
    (hf : ∀ z, f z ≠ 0 ↔ z ∈ C ∧ parity z = b)
    (hg : ∀ z, g z ≠ 0 ↔ z ∈ D ∧ parity z = !(wordParity ridge b))
    (hAf : ∀ z ∉ C, weightedLinear (fun k => if k = i then 2 else 1) f z = 0)
    (hAg : ∀ z ∉ D, weightedLinear (fun _ => 1) g z = 0)
    (hx : RidgeContact C D b ridge i x) :
    ∃ y, y ≠ x ∧ RidgeContact C D b ridge i y ∧
      ∀ k, ¬ (RidgeActiveAxis C D b ridge k ∧ k ≠ i) → y k = x k := by
  classical
  have hsum := minimum_distance_contact_cell_cancels hnd hsep f g hf hg hAf hAg x
  have hprod (z : Q 9) := contact_product_ne_zero f g hf hg hx.1 z
  by_contra hn
  rw [Finset.sum_eq_single x] at hsum
  · have hxx : SameContactCell C D b ridge i x x := fun _ _ => rfl
    rw [ite_eq_left hxx] at hsum
    exact ((hprod x).mpr hx) hsum
  · intro y _ hy
    by_cases hm : SameContactCell C D b ridge i x y
    · rw [ite_eq_left hm]
      by_contra hne
      exact hn ⟨y, hy, (hprod y).mp hne, hm⟩
    · exact ite_eq_right hm
  · simp

private def differingAxes (x y : Q 9) : Finset (Fin 9) :=
  Finset.univ.filter fun j => x j ≠ y j

private theorem foldl_flip_apply (word : List (Fin 9)) (hnd : word.Nodup)
    (z : Q 9) (j : Fin 9) :
    word.foldl flip z j = if j ∈ word then !z j else z j := by
  induction word generalizing z with
  | nil => simp
  | cons a word ih =>
    obtain ⟨ha, hword⟩ := List.nodup_cons.mp hnd
    rw [List.foldl_cons, ih hword]
    by_cases hj : j = a
    · subst j
      simp [ha, flip_apply_same]
    · simp [hj, BalancedCriticalSpectrum.flip]

private theorem differingAxes_foldl_flip (word : List (Fin 9)) (hnd : word.Nodup)
    (z : Q 9) :
    differingAxes z (word.foldl flip z) = word.toFinset := by
  ext j
  simp only [differingAxes, Finset.mem_filter, Finset.mem_univ, true_and, foldl_flip_apply word hnd,
    List.mem_toFinset]
  by_cases hj : j ∈ word
  · cases hz : z j <;> simp [hj, hz]
  · simp [hj]

private theorem first_is_flip_word (T : Finset (Fin 9))
    {x y : Q 9} (hT : differingAxes x y = T) {i : Fin 9} (hi : i ∈ T) :
    flip ((T.erase i).toList.foldl flip x) i = y := by
  have hnd : ((T.erase i).toList ++ [i]).Nodup := by
    rw [List.nodup_append]
    refine ⟨Finset.nodup_toList _, by simp, ?_⟩
    intro a ha z hz
    rw [List.mem_singleton.mp hz]
    exact Finset.ne_of_mem_erase (Finset.mem_toList.mp ha)
  suffices hh : ((T.erase i).toList ++ [i]).foldl flip x = y by
    simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using hh
  funext j
  rw [foldl_flip_apply _ hnd]
  have he : j ∈ (T.erase i).toList ++ [i] ↔ x j ≠ y j := by
    have hmem : j ∈ T ↔ x j ≠ y j := by simp [← hT, differingAxes]
    rw [← hmem]
    by_cases hji : j = i
    · subst j
      simp [hi]
    · simp [hji]
  simp only [he]
  cases hx : x j <;> cases hy : y j <;> simp [hx, hy]

/-- The axis sets of all Hamming-distance-`d` contacts on one initial parity. -/
def minimumDisplacements (C D : Finset (Q 9)) (b : Bool) (d : ℕ) :
    Finset (Finset (Fin 9)) :=
  ((C.product D).filter fun p => parity p.1 = b ∧ hammingDist p.1 p.2 = d).image
    fun p => differingAxes p.1 p.2

private theorem mem_minimumDisplacements
    {C D : Finset (Q 9)} {b : Bool} {d : ℕ} {T : Finset (Fin 9)} :
    T ∈ minimumDisplacements C D b d ↔
      ∃ x ∈ C, ∃ y ∈ D, parity x = b ∧ hammingDist x y = d ∧ differingAxes x y = T := by
  constructor
  · intro h
    obtain ⟨⟨x, y⟩, hp, he⟩ := Finset.mem_image.mp h
    obtain ⟨hp, hpar, hdist⟩ := Finset.mem_filter.mp hp
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
    exact ⟨x, hx, y, hy, hpar, hdist, he⟩
  · rintro ⟨x, hx, y, hy, hpar, hdist, he⟩
    exact Finset.mem_image.mpr ⟨(x, y), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hpar, hdist⟩, he⟩

open Classical in
/-- At a nonempty minimum contact parity, weighted support forces at least
`(d + 2).choose 2` distinct displacements. At equality they are the complete
family of `d`-subsets of one set of `d + 2` coordinate axes. -/
theorem minimum_displacements_card_and_equality
    (C D : Finset (Q 9)) (b : Bool) (d : ℕ) (hd : 0 < d)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, d ≤ hammingDist x y)
    (hne : (minimumDisplacements C D b d).Nonempty)
    (hC : ∀ i, ∃ f : Q 9 → ℝ,
      (∀ z, f z ≠ 0 ↔ z ∈ C ∧ parity z = b) ∧
      (∀ z ∉ C, weightedLinear (fun k => if k = i then 2 else 1) f z = 0))
    (hD : ∀ c, ∃ g : Q 9 → ℝ,
      (∀ z, g z ≠ 0 ↔ z ∈ D ∧ parity z = c) ∧
      (∀ z ∉ D, weightedLinear (fun _ => 1) g z = 0)) :
    (d + 2).choose 2 ≤ (minimumDisplacements C D b d).card ∧
      ((minimumDisplacements C D b d).card = (d + 2).choose 2 →
        ∃ A : Finset (Fin 9), A.card = d + 2 ∧ minimumDisplacements C D b d = A.powersetCard d) := by
  apply MinimumContactDisplacementCount.card_and_eq_powerset_of_three_extensions d hd _ hne
  · intro T hT
    obtain ⟨x, _, y, _, _, hdist, rfl⟩ := mem_minimumDisplacements.mp hT
    exact hdist
  · intro T hT i hi
    obtain ⟨x, hx, y, hy, hxb, hdist, he⟩ := mem_minimumDisplacements.mp hT
    let ridge := (T.erase i).toList
    have hlen : ridge.length + 1 = d := by
      dsimp [ridge]
      rw [Finset.length_toList, Finset.card_erase_add_one hi, ← he]
      exact hdist
    have hnd : ridge.Nodup := Finset.nodup_toList _
    have hs : ∀ u ∈ C, ∀ v ∈ D, ridge.length + 1 ≤ hammingDist u v := by
      rw [hlen]
      exact hsep
    have hxi : RidgeContact C D b ridge i x :=
      ⟨by simp [ridge], hx, hxb, (first_is_flip_word T he hi).symm ▸ hy⟩
    obtain ⟨f, hf, hAf⟩ := hC i
    obtain ⟨g, hg, hAg⟩ := hD (!(wordParity ridge b))
    obtain ⟨z, hzx, hz, hzcell⟩ :=
      minimum_distance_contact_has_companion hnd hs f g hf hg hAf hAg hxi
    have hdiff : 1 < (differingAxes z x).card := by
      change 1 < hammingDist z x
      have h0 : hammingDist z x ≠ 0 := fun h => hzx (hammingDist_eq_zero.mp h)
      have h1 : hammingDist z x ≠ 1 := fun h =>
        cubeParity_ne_of_adj (show (D5.S3.Combinatorics.Graph.Hypercube.hypercube 9).Adj z x
          from h) (hz.2.2.1.trans hxb.symm)
      omega
    obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.mp hdiff
    have ha (l : Fin 9) (hl : l ∈ differingAxes z x) :
        RidgeActiveAxis C D b ridge l ∧ l ≠ i := by
      by_contra h
      exact (Finset.mem_filter.mp hl).2 (hzcell l h)
    obtain ⟨hja, hji⟩ := ha j hj
    obtain ⟨hka, hki⟩ := ha k hk
    refine ⟨i, j, k, hji.symm, hki.symm, hjk, ?_⟩
    intro l hl
    have hactive : RidgeActiveAxis C D b ridge l := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl | rfl
      · exact ⟨x, hxi⟩
      · exact hja
      · exact hka
    obtain ⟨u, hlu, hu, hub, hv⟩ := hactive
    let v := flip (ridge.foldl flip u) l
    have hdv : hammingDist u v = d := (RidgeContact.hammingDist_eq hs
      (show RidgeContact C D b ridge l u from ⟨hlu, hu, hub, hv⟩)).trans hlen
    have hlridge : l ∉ T.erase i := by simpa only [ridge, Finset.mem_toList] using hlu
    have hword : (ridge ++ [l]).Nodup := by
      rw [List.nodup_append]
      refine ⟨hnd, by simp, ?_⟩
      intro a ha z hz heq
      exact hlu ((heq.trans (List.mem_singleton.mp hz)) ▸ ha)
    have hdiffv : differingAxes u v = insert l (T.erase i) := by
      have heq := differingAxes_foldl_flip (ridge ++ [l]) hword u
      simpa [v, ridge, Finset.union_comm] using heq
    exact ⟨hlridge, mem_minimumDisplacements.mpr ⟨u, hu, v, hv, hub, hdv, hdiffv⟩⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
