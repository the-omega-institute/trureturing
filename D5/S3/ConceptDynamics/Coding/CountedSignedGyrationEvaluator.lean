/- GID: D5/S3/ConceptDynamics/Coding/CountedSignedGyrationEvaluator
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/CountedSignedGyrationEvaluator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Order-faithful key comparison and rectangular signed gyration evaluation. -/

/-
This is a comparison/evaluation adapter for the original ranked-edge sum;
it does not supply a new ranking of product-edge fibres.
-/
import D5.S3.ConceptDynamics.Coding.CountedSignedGyrationSupport
import Mathlib.Data.Fin.Tuple.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration

open scoped BigOperators
open CountedMatrixOverlap

namespace SignedSupport

abbrev Key := ℕ × ℕ × ℕ × ℕ × ℕ

/-- Source, target, middle vertex, first half-edge rank, second rank. -/
def KeyLT (a b : Key) : Prop :=
  a.1 < b.1 ∨ a.1 = b.1 ∧
    (a.2.1 < b.2.1 ∨ a.2.1 = b.2.1 ∧
      (a.2.2.1 < b.2.2.1 ∨ a.2.2.1 = b.2.2.1 ∧
        (a.2.2.2.1 < b.2.2.2.1 ∨ a.2.2.2.1 = b.2.2.2.1 ∧
          a.2.2.2.2 < b.2.2.2.2)))

instance (a b : Key) : Decidable (KeyLT a b) := by
  unfold KeyLT
  infer_instance

noncomputable def edgeKey {n m : ℕ} (R : CountMat n m) (S : CountMat m n)
    (a : Edge (R*S)) : Key :=
  let p := fiberEquiv R S a.source a.target a.number
  (a.source.val, a.target.val, p.1.val, p.2.1.val, p.2.2.val)

private theorem edgeKey_injective {n m : ℕ} (R : CountMat n m) (S : CountMat m n) :
    Function.Injective (edgeKey R S) := by
  rintro ⟨i,k,a⟩ ⟨i',k',b⟩ h
  have hi : i = i' := Fin.ext (congrArg Prod.fst h)
  have hk : k = k' := Fin.ext (congrArg (fun v : Key => v.2.1) h)
  subst i'
  subst k'
  have ht :
      ((fiberEquiv R S i k a).1.val,
        (fiberEquiv R S i k a).2.1.val, (fiberEquiv R S i k a).2.2.val) =
      ((fiberEquiv R S i k b).1.val,
        (fiberEquiv R S i k b).2.1.val, (fiberEquiv R S i k b).2.2.val) :=
    congrArg (fun v : Key => v.2.2) h
  have hp : fiberEquiv R S i k a = fiberEquiv R S i k b := by
    generalize fiberEquiv R S i k a = p at ht ⊢
    generalize fiberEquiv R S i k b = q at ht ⊢
    rcases p with ⟨j,r,s⟩
    rcases q with ⟨j',r',s'⟩
    have hj : j = j' := Fin.ext (congrArg Prod.fst ht)
    subst j'
    have hr : r = r' := Fin.ext (congrArg (fun v : ℕ × ℕ × ℕ => v.2.1) ht)
    have hs : s = s' := Fin.ext (congrArg (fun v : ℕ × ℕ × ℕ => v.2.2) ht)
    subst r'
    subst s'
    rfl
  have hab : a = b := (fiberEquiv R S i k).injective hp
  subst b
  rfl

private theorem fiberKey_lt_naturals {n m : ℕ}
    (R : CountMat n m) (S : CountMat m n) (i k : Fin n)
    (p q : Fiber R S i k) :
    fiberKey p < fiberKey q ↔
      p.1.val < q.1.val ∨ p.1.val = q.1.val ∧
        (p.2.1.val < q.2.1.val ∨ p.2.1.val = q.2.1.val ∧ p.2.2.val < q.2.2.val) := by
  rcases p with ⟨j,r,s⟩
  rcases q with ⟨j',r',s'⟩
  change Sigma.Lex (fun a b : Fin m => a < b)
    (fun j (a b : Lex (Fin (R i j) × Fin (S j k))) => a < b)
    ⟨j, toLex (r,s)⟩ ⟨j', toLex (r',s')⟩ ↔ _
  rw [Sigma.lex_iff]
  dsimp only
  by_cases hj : j = j'
  · subst j'
    simp [Prod.Lex.toLex_lt_toLex,
      Fin.lt_def, Fin.val_eq_val, -Fin.val_fin_lt]
  · have hv : j.val ≠ j'.val := fun h => hj (Fin.ext h)
    simp [hj, hv, Fin.lt_def, -Fin.val_fin_lt]

/-- All comparisons of the last three coordinates are supplied by the
existing fiber_number_lt_iff. The outside endpoint order is unchanged. -/
private theorem edgeKey_lt_iff {n m : ℕ} (R : CountMat n m) (S : CountMat m n)
    (a b : Edge (R*S)) : EdgeLT a b ↔ KeyLT (edgeKey R S a) (edgeKey R S b) := by
  rcases a with ⟨i,k,a⟩
  rcases b with ⟨i',k',b⟩
  by_cases hi : i = i'
  · subst i'
    by_cases hk : k = k'
    · subst k'
      have h := fiber_number_lt_iff R S i k
        (fiberEquiv R S i k a) (fiberEquiv R S i k b)
      rw [fiberKey_lt_naturals] at h
      simpa [EdgeLT, KeyLT, edgeKey, Fin.lt_def, -Fin.val_fin_lt] using h
    · have hv : k.val ≠ k'.val := fun h => hk (Fin.ext h)
      simp [EdgeLT, KeyLT, edgeKey, hk, hv, Fin.lt_def, -Fin.val_fin_lt]
  · have hv : i.val ≠ i'.val := fun h => hi (Fin.ext h)
    simp [EdgeLT, KeyLT, edgeKey, hi, hv, Fin.lt_def, -Fin.val_fin_lt]

private theorem edgeKey_join {n m : ℕ} (R : CountMat n m) (S : CountMat m n)
    (i k : Fin n) (j : Fin m) (r : Fin (R i j)) (s : Fin (S j k)) :
    edgeKey R S (join R S ⟨i,j,r⟩ ⟨j,k,s⟩ rfl) =
      (i.val,k.val,j.val,r.val,s.val) := by
  exact congrArg
    (fun p : Fiber R S i k => (i.val, k.val, p.1.val, p.2.1.val, p.2.2.val))
    ((fiberEquiv R S i k).apply_symm_apply ⟨j, (r,s)⟩)

def KeyWordLT {d : ℕ} (a b : Fin d → Key) : Prop :=
  ∃ t : Fin d, (∀ u : Fin d, u < t → a u = b u) ∧ KeyLT (a t) (b t)

instance {d : ℕ} (a b : Fin d → Key) : Decidable (KeyWordLT a b) :=
  inferInstanceAs (Decidable (∃ t : Fin d,
    (∀ u : Fin d, u < t → a u = b u) ∧ KeyLT (a t) (b t)))

def KeyLeast {d : ℕ} [NeZero d] (a : Fin d → Key) : Prop :=
  ∀ k : Fin d, k ≠ 0 → KeyWordLT a (rotate k a)

instance {d : ℕ} [NeZero d] (a : Fin d → Key) : Decidable (KeyLeast a) :=
  inferInstanceAs (Decidable (∀ k : Fin d, k ≠ 0 → KeyWordLT a (rotate k a)))

/-- This keeps the whole defining sum, including k=0 and nonprimitive
words. There is no unproved uniqueness-of-least-rotation optimization. -/
def keyWeight {d : ℕ} [NeZero d] (a b : Fin d → Key) : ℤ :=
  if KeyLeast a then
    ∑ k : Fin d, if KeyLeast (rotate k b) then -(k.val : ℤ) else 0
  else 0

private theorem wordLT_keys {n m d : ℕ} (R : CountMat n m) (S : CountMat m n)
    (a b : Fin d → Edge (R*S)) :
    WordLT a b ↔ KeyWordLT (fun t => edgeKey R S (a t))
      (fun t => edgeKey R S (b t)) := by
  simp only [WordLT, KeyWordLT, (edgeKey_injective R S).eq_iff,
    ← edgeKey_lt_iff R S]

private theorem strictLeast_keys {n m d : ℕ} [NeZero d]
    (R : CountMat n m) (S : CountMat m n) (a : Fin d → Edge (R*S)) :
    StrictLeast a ↔ KeyLeast (fun t => edgeKey R S (a t)) := by
  unfold StrictLeast KeyLeast
  apply forall_congr'
  intro k
  exact imp_congr_right (fun _ => wordLT_keys R S a (rotate k a))

theorem wordWeight_keys {n m d : ℕ} [NeZero d]
    (R : CountMat n m) (S : CountMat m n)
    (a : Fin d → Edge (R*S)) (b : Fin d → Edge (S*R)) :
    wordWeight a b = keyWeight (fun t => edgeKey R S (a t))
      (fun t => edgeKey S R (b t)) := by
  classical
  unfold wordWeight keyWeight
  rw [strictLeast_keys R S]
  by_cases ha : KeyLeast (fun t => edgeKey R S (a t))
  · simp only [if_pos ha]
    apply Finset.sum_congr rfl
    intro k _
    rw [strictLeast_keys S R]
    congr 1
  · simp only [if_neg ha]

def sourceKeys {n m d : ℕ} [NeZero d] (w : VertexWord n m d)
    (l : Fin d → ℕ) : Fin d → Key := fun t =>
  ((w.1 t).val, (w.1 (t+1)).val, (w.2 t).val, 0, l t)

def targetKeys {n m d : ℕ} [NeZero d] (w : VertexWord n m d)
    (l : Fin d → ℕ) : Fin d → Key := fun t =>
  ((w.2 t).val, (w.2 (t+1)).val, (w.1 (t+1)).val, l t, 0)

def vectorTerm {n m d : ℕ} [NeZero d]
    (S : Matrix (Fin m) (Fin n) ℤ) (w : VertexWord n m d)
    (l : Fin d → ℕ) : ℤ :=
  keyWeight (sourceKeys w l) (targetKeys w l) * coefficient S w l

private theorem keyLT_irrefl (a : Key) : ¬ KeyLT a a := by
  simp [KeyLT]

private theorem keyLT_asymm (a b : Key) (h : KeyLT a b) : ¬ KeyLT b a := by
  simp only [KeyLT] at *
  omega

private theorem keyWordLT_not_reverse_zero {d : ℕ} [NeZero d]
    (a b : Fin d → Key) (h : KeyWordLT a b) : ¬ KeyLT (b 0) (a 0) := by
  obtain ⟨t, hp, ht⟩ := h
  by_cases hz : t = 0
  · subst t
    exact keyLT_asymm _ _ ht
  · have hpos : (0 : Fin d) < t := by
      change 0 < t.val
      exact Nat.pos_of_ne_zero (fun h => hz (Fin.ext h))
    rw [← hp 0 hpos]
    exact keyLT_irrefl _

def skeleton {n m d : ℕ} [NeZero d] (w : VertexWord n m d) (t : Fin d) : Key :=
  ((w.1 t).val, (w.1 (t+1)).val, (w.2 t).val, 0, 0)

def SkeletonMinimal {n m d : ℕ} [NeZero d] (w : VertexWord n m d) : Prop :=
  ∀ t : Fin d, ¬ KeyLT (skeleton w t) (skeleton w 0)

instance {n m d : ℕ} [NeZero d] (w : VertexWord n m d) :
    Decidable (SkeletonMinimal w) :=
  inferInstanceAs (Decidable (∀ t : Fin d, ¬ KeyLT (skeleton w t) (skeleton w 0)))

private theorem least_source_skeleton {n m d : ℕ} [NeZero d]
    (w : VertexWord n m d) (l : Fin d → ℕ) (h : KeyLeast (sourceKeys w l)) :
    SkeletonMinimal w := by
  intro t ht
  have hkey : KeyLT (sourceKeys w l t) (sourceKeys w l 0) := by
    simp only [KeyLT, skeleton, sourceKeys] at *
    omega
  have ht0 : t ≠ 0 := by
    intro he
    subst t
    exact keyLT_irrefl _ hkey
  have hword := h t ht0
  have hreverse := keyWordLT_not_reverse_zero _ _ hword
  apply hreverse
  simpa only [rotate, zero_add] using hkey

theorem vectorTerm_zero_of_nonminimal {n m d : ℕ} [NeZero d]
    (S : Matrix (Fin m) (Fin n) ℤ) (w : VertexWord n m d)
    (l : Fin d → ℕ) (hw : ¬ SkeletonMinimal w) : vectorTerm S w l = 0 := by
  have hn : ¬ KeyLeast (sourceKeys w l) := fun h => hw (least_source_skeleton w l h)
  simp only [vectorTerm, keyWeight, if_neg hn, zero_mul]

theorem rankedTerm_eq_vectorTerm {n m d : ℕ} [NeZero d]
    (S : Matrix (Fin m) (Fin n) ℤ) (w : VertexWord n m d)
    (l : Fin d → ℕ) (hl : l ∈ rankVectors S w) :
    rankedTerm S w l = vectorTerm S w l := by
  classical
  rw [rankedTerm, dif_pos hl]
  let T := typeOfRanks S w l hl
  have hsource : (fun t => edgeKey (rMatrix (widths T)) (sMatrix (widths T))
      (sourceEdge w (widths T) (rankLabels T) t)) = sourceKeys w l := by
    funext t
    exact edgeKey_join (rMatrix (widths T)) (sMatrix (widths T))
      (w.1 t) (w.1 (t+1)) (w.2 t)
      (rankLabels T (Sum.inl (w.1 t, w.2 t)) ⟨t, rfl⟩)
      (rankLabels T (Sum.inr (w.2 t, w.1 (t+1))) ⟨t, rfl⟩)
  have htarget : (fun t => edgeKey (sMatrix (widths T)) (rMatrix (widths T))
      (targetEdge w (widths T) (rankLabels T) t)) = targetKeys w l := by
    funext t
    exact edgeKey_join (sMatrix (widths T)) (rMatrix (widths T))
      (w.2 t) (w.2 (t+1)) (w.1 (t+1))
      (rankLabels T (Sum.inr (w.2 t, w.1 (t+1))) ⟨t, rfl⟩)
      (rankLabels T (Sum.inl (w.1 (t+1), w.2 (t+1))) ⟨t+1, rfl⟩)
  rw [wordWeight_keys (rMatrix (widths T)) (sMatrix (widths T)), hsource, htarget]
  rfl

/-- An actually reducible sparse expression. The outer n^d enumeration
is followed by the product of supported middle-vertex fibres. Rank choices
are bounded by their own occurrence multiplicities and filtered for exact
surjectivity. It never enumerates (nm)^d arbitrary alternating vertex words. -/
def supportedEvaluator {n m : ℕ} (d : ℕ) [NeZero d]
    (R : Matrix (Fin n) (Fin m) ℤ) (S : Matrix (Fin m) (Fin n) ℤ) : ℤ :=
  ∑ a : Fin d → Fin n, ∑ b ∈ middleWords R S a,
    ∑ l ∈ rankVectors S (a,b), vectorTerm S (a,b) l

def prunedEvaluator {n m : ℕ} (d : ℕ) [NeZero d]
    (R : Matrix (Fin n) (Fin m) ℤ) (S : Matrix (Fin m) (Fin n) ℤ) : ℤ :=
  ∑ a : Fin d → Fin n,
    ∑ b ∈ (middleWords R S a).filter (fun b => SkeletonMinimal (a,b)),
      ∑ l ∈ rankVectors S (a,b), vectorTerm S (a,b) l

/-- Only a smaller FIRST source triple is used for pruning. In particular
this does not compare whole unlabelled skeleton rotations, which would
incorrectly drop terms resolved by an earlier rank-label comparison. -/
theorem supportedEvaluator_eq_pruned {n m : ℕ} (d : ℕ) [NeZero d]
    (R : Matrix (Fin n) (Fin m) ℤ) (S : Matrix (Fin m) (Fin n) ℤ) :
    supportedEvaluator d R S = prunedEvaluator d R S := by
  classical
  unfold supportedEvaluator prunedEvaluator
  apply Finset.sum_congr rfl
  intro a _
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro b hb hn
  have hnot : ¬ SkeletonMinimal (a,b) := by
    intro h
    exact hn (Finset.mem_filter.mpr ⟨hb,h⟩)
  apply Finset.sum_eq_zero
  intro l _
  exact vectorTerm_zero_of_nonminimal S (a,b) l hnot

/-- A kernel-reduction shard fixes the first outside vertex. This is a
partition of the evaluator, with no supplied value or acceptance premise. -/
def prunedShard {n m : ℕ} (k : ℕ)
    (R : Matrix (Fin n) (Fin m) ℤ) (S : Matrix (Fin m) (Fin n) ℤ)
    (i : Fin n) : ℤ :=
  ∑ tail : Fin k → Fin n,
    ∑ b ∈ (middleWords R S (Fin.cons i tail)).filter
        (fun b => SkeletonMinimal (Fin.cons i tail,b)),
      ∑ l ∈ rankVectors S (Fin.cons i tail,b), vectorTerm S (Fin.cons i tail,b) l



/-- Exact equality with the signed lift of the actual polynomial. No
coefficient table or desired calibration occurs in this theorem. -/
theorem signedGyrationLift_eq_supportedEvaluator {n m : ℕ} (d : ℕ) [NeZero d]
    (R : Matrix (Fin n) (Fin m) ℤ) (S : Matrix (Fin m) (Fin n) ℤ)
    (hR : ∀ i j, R i j = 0 ∨ R i j = 1)
    (hS : ∀ j i, S j i = -1 ∨ S j i = 0 ∨ S j i = 1) :
    signedGyrationLift (d := d) (entries R S) = supportedEvaluator d R S := by
  classical
  rw [signedGyrationLift_supported_surjections R S hR hS]
  unfold supportedEvaluator
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro l hl
  exact rankedTerm_eq_vectorTerm S (a,b) l hl



end SignedSupport

end D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration
