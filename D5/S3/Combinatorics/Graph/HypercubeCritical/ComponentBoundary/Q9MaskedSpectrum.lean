/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedSpectrum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Singular Huang masks force a positive eigenfunction on a masked component. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MaskedGram

/-! Spectral saturation under a nonempty coordinate mask in the nine-cube. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MaskedSpectrum

open scoped BigOperators Matrix
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_adj IsBalanced IsSwitching switching_sq)
open BalancedCubeComponentBoundary (flip_injective)
open TwoBalancedComponents (componentFinset)
open Q9ComponentSaturation (componentDefect componentDefect_det_eq componentParityFinset)
open Q9MaskedGram (maskWeight)
open Q9IsotropicHuang (weightedLinear)
open Q9WeightedBoundaryGram (signed signed_mulVec signed_transpose)
open Q9SignedContactCells (unit_weight weighted_square)
open Q9WeightedSaturation (defect)

private abbrev Comp (U : Finset (Q 9)) :=
  ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent

/-- The spanning cube graph retaining just the edges in the specified directions. -/
def maskedGraph (I : Finset (Fin 9)) : SimpleGraph (Q 9) where
  Adj x y := ∃ a ∈ I, flip x a = y
  symm := ⟨by
    rintro x y ⟨a, ha, rfl⟩
    exact ⟨a, ha, BalancedCriticalSpectrum.flip_flip x a⟩⟩
  loopless := ⟨fun x ⟨a, _, h⟩ => (flip_adj x a).ne h.symm⟩

private theorem mask_weight_sq (I : Finset (Fin 9)) :
    ∑ a : Fin 9, maskWeight I a ^ 2 = (I.card : ℝ) := by
  classical
  simp only [maskWeight, apply_ite (fun x : ℝ => x ^ 2), one_pow, zero_pow (by decide : 2 ≠ 0)]
  simp

private theorem mask_sq_norm (I : Finset (Fin 9)) (f : Q 9 → ℝ) :
    ∑ x, (weightedLinear (maskWeight I) f x) ^ 2 = (I.card : ℝ) * ∑ x, (f x) ^ 2 := by
  let A := signed (maskWeight I)
  have h := Matrix.dotProduct_transpose_mulVec A (A *ᵥ f) f
  simp only [A, signed_transpose, signed_mulVec, weighted_square, mask_weight_sq,
    dotProduct_smul, smul_eq_mul] at h
  simpa only [dotProduct, pow_two] using h

set_option maxHeartbeats 450000 in
open Classical in
private theorem signed_eigen_of_singular (U : Finset (Q 9)) (b : Bool) (C : Comp U)
    (I : Finset (Fin 9)) (hI : I.Nonempty)
    (hdet : (componentDefect (maskWeight I) U b C).det = 0) :
    ∃ z : Q 9 → ℝ, z ≠ 0 ∧ (∀ x ∉ componentFinset U C, z x = 0) ∧
      weightedLinear (maskWeight I) z = Real.sqrt (I.card : ℝ) • z := by
  classical
  let S := componentParityFinset U b C
  let T := componentParityFinset U (!b) C
  let H := weightedLinear (maskWeight I)
  let M := (signed (maskWeight I)).submatrix (fun x : ↥S => x.val) (fun y : ↥T => y.val)
  rw [componentDefect_det_eq] at hdet
  change (defect (maskWeight I) M).det = 0 at hdet
  obtain ⟨u, hne, hu⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := defect (maskWeight I) M)).mpr hdet
  rw [defect, mask_weight_sq, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    sub_eq_zero, ← Matrix.mulVec_mulVec] at hu
  let f := Function.extend (Subtype.val : ↥S → Q 9) u 0
  have hf (x : ↥S) : f x.val = u x := Subtype.val_injective.extend_apply _ _ x
  have hfzero (x : Q 9) (hx : x ∉ S) : f x = 0 :=
    Function.extend_apply' _ _ _ (by rintro ⟨x, rfl⟩; exact hx x.property)
  have hfsq : ∑ x, f x ^ 2 = ∑ x : ↥S, u x ^ 2 := by
    symm
    exact Fintype.sum_of_injective Subtype.val Subtype.val_injective _ _
      (fun x hx => by rw [hfzero x (fun hm => hx ⟨⟨x, hm⟩, rfl⟩), zero_pow (by decide)])
      (fun x => by rw [hf])
  have hMv (y : ↥T) : (Mᵀ *ᵥ u) y = H f y.val := by
    rw [← signed_mulVec]
    change (∑ x : ↥S, signed (maskWeight I) x.val y.val * u x) =
      ∑ x, signed (maskWeight I) y.val x * f x
    refine Fintype.sum_of_injective Subtype.val Subtype.val_injective _ _ ?_ ?_
    · intro x hx
      rw [hfzero x (fun hm => hx ⟨⟨x, hm⟩, rfl⟩), mul_zero]
    · intro x
      rw [hf]
      have he := congrFun (congrFun (signed_transpose (maskWeight I)) y.val) x.val
      exact congrArg (fun t : ℝ => t * u x) he
  have hTsq : ∑ y ∈ T, (H f y) ^ 2 = ∑ y, (H f y) ^ 2 := by
    have h := Matrix.dotProduct_transpose_mulVec Mᵀ u (Mᵀ *ᵥ u)
    rw [Matrix.transpose_transpose, ← hu, dotProduct_smul, smul_eq_mul] at h
    calc
      _ = ∑ y : ↥T, (H f y.val) ^ 2 :=
        Finset.sum_subtype T (fun _ => Iff.rfl) (fun y => (H f y) ^ 2)
      _ = (I.card : ℝ) * ∑ x : ↥S, u x ^ 2 := by
        simp only [← hMv, pow_two]
        exact h.symm
      _ = _ := by rw [mask_sq_norm, hfsq]
  have hHzero (x : Q 9) (hx : x ∉ T) : H f x = 0 := by
    have hd : ∑ y ∈ Finset.univ \ T, (H f y) ^ 2 = 0 := by
      have h := Finset.sum_sdiff (f := fun y => (H f y) ^ 2) (Finset.subset_univ T)
      rw [hTsq] at h
      linarith
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => sq_nonneg (H f y))).mp hd x
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩)
    exact eq_zero_of_pow_eq_zero hz
  let lam := Real.sqrt (I.card : ℝ)
  have hlam : 0 < lam := Real.sqrt_pos.2 (by exact_mod_cast hI.card_pos)
  have hlamsq : lam * lam = (I.card : ℝ) := Real.mul_self_sqrt (by positivity)
  have hSS : S ⊆ componentFinset U C := Finset.filter_subset _ _
  have hTS : T ⊆ componentFinset U C := Finset.filter_subset _ _
  let z := f + lam⁻¹ • H f
  have hz (x : ↥S) : z x.val = u x := by
    have hx : x.val ∉ T := by
      intro ht
      have he := (Finset.mem_filter.mp x.property).2.symm.trans (Finset.mem_filter.mp ht).2
      cases b <;> simp at he
    change f x.val + lam⁻¹ * H f x.val = u x
    rw [hf, hHzero _ hx, mul_zero, add_zero]
  refine ⟨z, fun h => hne (funext fun x => (hz x).symm.trans (congrFun h x.val)), ?_, ?_⟩
  · intro x hx
    change f x + lam⁻¹ * H f x = 0
    rw [hfzero x (fun hm => hx (hSS hm)), hHzero x (fun hm => hx (hTS hm)), mul_zero, add_zero]
  · change H z = lam • z
    dsimp only [z]
    rw [map_add, map_smul, show H (H f) = (I.card : ℝ) • f by
      rw [weighted_square, mask_weight_sq], smul_add, smul_smul, smul_smul, ← hlamsq,
      inv_mul_cancel_left₀ hlam.ne', mul_inv_cancel₀ hlam.ne', one_smul, add_comm]

open Classical in
private theorem mask_row (I : Finset (Fin 9)) (S : Finset (Q 9)) {s : Q 9 → ℝ}
    (hs : IsSwitching S s) {f : Q 9 → ℝ} (hf : ∀ x ∉ S, f x = 0)
    {x : Q 9} (hx : x ∈ S) :
    s x * weightedLinear (maskWeight I) f x =
      ∑ y ∈ S.filter ((maskedGraph I).Adj x), s y * f y := by
  classical
  rw [← signed_mulVec]
  rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
  calc
    _ = ∑ y ∈ S.filter ((maskedGraph I).Adj x), s x * (signed (maskWeight I) x y * f y) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro y _ hy
      by_cases hys : y ∈ S
      · have hz : signed (maskWeight I) x y = 0 := by
          apply Finset.sum_eq_zero
          intro a _
          by_cases ha : a ∈ I
          · have he : flip x a ≠ y := fun he => hy (Finset.mem_filter.mpr ⟨hys, a, ha, he⟩)
            simp [he]
          · simp [maskWeight, ha]
        rw [hz, zero_mul, mul_zero]
      · rw [hf y hys, mul_zero, mul_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y hy
      obtain ⟨hys, a, ha, rfl⟩ := Finset.mem_filter.mp hy
      have hv : signed (maskWeight I) x (flip x a) = signed (fun _ => (1 : ℝ)) x (flip x a) := by
        unfold signed
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : flip x j = flip x a
        · obtain rfl := flip_injective x h
          simp [maskWeight, ha]
        · simp [h]
      have hunit := unit_weight (Pi.single (flip x a) (1 : ℝ))
      rw [← signed_mulVec, Matrix.toLin'_apply, Matrix.mulVec_single_one,
        Matrix.mulVec_single_one] at hunit
      have hentry := congrFun hunit x
      simp only [Matrix.col_apply] at hentry
      rw [hv, hentry, hs.2 x hx _ hys (flip_adj x a)]
      calc
        _ = s x ^ 2 * (s (flip x a) * f (flip x a)) := by ring
        _ = _ := by rw [switching_sq hs hx, one_mul]

open Classical in
private theorem abs_eigen (I : Finset (Fin 9)) (S : Finset (Q 9))
    (hbal : IsBalanced S) {z : Q 9 → ℝ} (hz : ∀ x ∉ S, z x = 0)
    (he : weightedLinear (maskWeight I) z = Real.sqrt (I.card : ℝ) • z) :
    ∀ x ∈ S, (∑ y ∈ S.filter ((maskedGraph I).Adj x), |z y|) =
      Real.sqrt (I.card : ℝ) * |z x| := by
  classical
  obtain ⟨s, hs⟩ := hbal
  let lam := Real.sqrt (I.card : ℝ)
  let g : Q 9 → ℝ := fun x => s x * |z x|
  have hsign (x : Q 9) (hx : x ∈ S) : |s x| = 1 := by
    rcases hs.1 x hx with h | h <;> simp [h]
  have hrow (x : Q 9) (hx : x ∈ S) :
      s x * weightedLinear (maskWeight I) g x =
        ∑ y ∈ S.filter ((maskedGraph I).Adj x), |z y| := by
    rw [mask_row I S hs (fun y hy => by simp [g, hz y hy]) hx]
    apply Finset.sum_congr rfl
    intro y hy
    unfold g
    rw [← mul_assoc, ← pow_two, switching_sq hs (Finset.mem_filter.mp hy).1, one_mul]
  have habs (x : Q 9) (hx : x ∈ S) :
      |weightedLinear (maskWeight I) g x| =
        ∑ y ∈ S.filter ((maskedGraph I).Adj x), |z y| := by
    have h := congrArg abs (hrow x hx)
    have hn : 0 ≤ ∑ y ∈ S.filter ((maskedGraph I).Adj x), |z y| :=
      Finset.sum_nonneg fun y _ => abs_nonneg _
    rwa [abs_mul, hsign x hx, one_mul, abs_of_nonneg hn] at h
  have hle (x : Q 9) : lam * |z x| ≤ |weightedLinear (maskWeight I) g x| := by
    by_cases hx : x ∈ S
    · rw [habs x hx]
      have h := congrArg abs (mask_row I S hs hz hx)
      rw [congrFun he x, Pi.smul_apply, smul_eq_mul, abs_mul, hsign x hx, one_mul,
        abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] at h
      rw [h]
      refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
      apply Finset.sum_congr rfl
      intro y hy
      rw [abs_mul, hsign y (Finset.mem_filter.mp hy).1, one_mul]
    · simp [hz x hx]
  have hg (x : Q 9) : g x ^ 2 = z x ^ 2 := by
    by_cases hx : x ∈ S
    · simp [g, mul_pow, switching_sq hs hx]
    · simp [g, hz x hx]
  have hsum : ∑ x, (lam * |z x|) ^ 2 = ∑ x, |weightedLinear (maskWeight I) g x| ^ 2 := by
    simp only [mul_pow, sq_abs, ← Finset.mul_sum, mask_sq_norm, hg]
    rw [Real.sq_sqrt (by positivity : 0 ≤ (I.card : ℝ))]
  intro x hx
  rw [← habs x hx]
  apply le_antisymm _ (hle x)
  by_contra! h
  have hlt : (lam * |z x|) ^ 2 < |weightedLinear (maskWeight I) g x| ^ 2 :=
    pow_lt_pow_left₀ h (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) (by decide)
  exact (ne_of_lt (Finset.sum_lt_sum
    (fun y _ => pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) (hle y) 2)
    ⟨x, Finset.mem_univ _, hlt⟩)) hsum

open Classical in
/-- A nonempty singular Huang mask in a balanced actual component has a masked
connected component carrying a strictly positive unsigned eigenfunction at
the square root of the number of active axes. -/
theorem exists_positive_masked_component (U : Finset (Q 9)) (b : Bool) (C : Comp U)
    (I : Finset (Fin 9)) (hI : I.Nonempty) (hb : IsBalanced (componentFinset U C))
    (hdet : (componentDefect (maskWeight I) U b C).det = 0) :
    let S := componentFinset U C
    ∃ K : ((maskedGraph I).induce (S : Set (Q 9))).ConnectedComponent,
      ∃ f : Q 9 → ℝ, ∀ x : (S : Set (Q 9)), x ∈ K.supp →
        0 < f x.val ∧
          (∑ y ∈ S.filter ((maskedGraph I).Adj x.val), f y) = Real.sqrt (I.card : ℝ) * f x.val := by
  classical
  let S := componentFinset U C
  let G := (maskedGraph I).induce (S : Set (Q 9))
  obtain ⟨z, hne, hz, he⟩ := signed_eigen_of_singular U b C I hI hdet
  let f : Q 9 → ℝ := fun x => |z x|
  have hrow := abs_eigen I S hb hz he
  obtain ⟨x, hx⟩ : ∃ x, z x ≠ 0 := by
    by_contra! h
    exact hne (funext h)
  let r : (S : Set (Q 9)) := ⟨x, by by_contra h; exact hx (hz x h)⟩
  have step {v w : (S : Set (Q 9))} (hvw : G.Adj v w) (hv : 0 < f v.val) : 0 < f w.val := by
    have hmem : v.val ∈ S.filter ((maskedGraph I).Adj w.val) :=
      Finset.mem_filter.mpr ⟨v.property, hvw.symm⟩
    have hle := Finset.single_le_sum (f := f) (fun y _ => abs_nonneg (z y)) hmem
    have hw := hrow w.val w.property
    change ∑ y ∈ S.filter ((maskedGraph I).Adj w.val), f y = _ at hw
    rw [hw] at hle
    by_contra! hn
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) hn)) (hv.trans_le hle)
  refine ⟨G.connectedComponentMk r, f, fun v hv => ⟨?_, hrow v.val v.property⟩⟩
  have hreach : G.Reachable r v := SimpleGraph.ConnectedComponent.exact hv.symm
  have walk_pos {w : (S : Set (Q 9))} (hw : Relation.ReflTransGen G.Adj r w) :
      0 < f w.val := by
    induction hw with
    | refl => exact abs_pos.mpr hx
    | tail _ hadj ih => exact step hadj ih
  exact walk_pos ((SimpleGraph.reachable_iff_reflTransGen r v).mp hreach)

/--
info: 'D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MaskedSpectrum.exists_positive_masked_component' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms exists_positive_masked_component

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MaskedSpectrum
