/- GID: D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/EilenbergZilber/ShuffleRemoval
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Removal and insertion factorization of non-diagonal shuffle vertices. -/

/-
Copyright (c) 2026 Jeffrey Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey Li

Source: LeanPool/EilenbergZilber, revision 8bbde3a6de815108d41922c9362ebbe38422663a.
Original source: jeffrey-dot-li/lean-homology, revision
40c5aae235b0f499ebfc1e68ce574a62b531203c; author release
fd0147a1ffe4f3c14c247574e148893d7cdf8cf6 (LeanPool PR 588).
Modifications: receiving namespace and imports, module boundaries, exposure of
consumed private interfaces, canonical identifier spellings, and omission of unused
companion, reflexive binding, and frontal material.
-/

module

public import D5.S3.HomologicalAlgebra.EilenbergZilber.ShuffleSigns

@[expose] public section

noncomputable section

namespace D5.S3.HomologicalAlgebra.EilenbergZilber

namespace Shuffle

/-! ##### Diagonal cancellation

The LHS terms not in the image of `insertLeftStep` or `insertRightStep` are
"diagonal" terms: they arise from vertex removals where the steps on either
side have different types (one left, one right).  These cancel pairwise via
a sign-reversing involution that swaps the two steps around the removed vertex. -/

/-- A `(μ, r)` pair is a **diagonal term** if vertex `r` has one adjacent left
step and one adjacent right step (in either order LR or RL).
Boundary vertices (r = 0 or r = last) are never diagonal. -/
def isDiagonalVertex {p q : ℕ} (μ : Shuffle p q)
    (r : Index (p + q)) : Prop :=
  if h₁ : 0 < r.val then
    if h₂ : r.val < p + q then
      (isLeftStep μ ⟨r.val - 1, by omega⟩ ∧ ¬ isLeftStep μ ⟨r.val, h₂⟩) ∨
      (¬ isLeftStep μ ⟨r.val - 1, by omega⟩ ∧ isLeftStep μ ⟨r.val, h₂⟩)
    else False
  else False

instance decidablePredIsDiagonalVertex {p q : ℕ} (μ : Shuffle (p) (q)) :
    DecidablePred (isDiagonalVertex μ) := by
  intro r; unfold isDiagonalVertex; split_ifs <;> infer_instance

/-! ##### Insertion–diagonal interface

The insertion maps produce exactly the non-diagonal terms of the boundary sum.
Each insertion lands in the non-diagonal set, together they cover it, and
their images are disjoint. -/

/-- Left insertion always produces a non-diagonal vertex: the two steps
adjacent to the inserted vertex are both left steps (LL pattern). -/
lemma insertLeftStep_not_diagonal {p q : ℕ}
    (ν : Shuffle p (q)) (j : Fin (p + 2)) :
    ¬isDiagonalVertex (insertLeftStep ν j)
      ((insertLeftIndex ν j).cast (by omega)) := by
  by_contra h_contra
  generalize_proofs at *;
  unfold Shuffle.isDiagonalVertex at h_contra
  generalize_proofs at *;
  split_ifs at h_contra; simp_all +decide only [isLeftStep, Fin.val_cast, Fin.castSucc_mk,
      Fin.succ_mk, Fin.val_fin_lt, not_lt];
  cases h : ( ν.insertLeftIndex j : ℕ ) <;> simp_all +decide only [zero_tsub, Fin.zero_eta,
      zero_add, Fin.val_eq_zero_iff, add_tsub_cancel_right];
  · grind;
  · unfold Shuffle.insertLeftStep at *; simp_all +decide only [OrderHom.coe_mk];
    unfold Shuffle.insertLeftStepFun at *; simp_all +decide only [lt_add_iff_pos_right,
        ↓reduceDIte, lt_self_iff_false, Fin.succAbove_lt_iff, Fin.castSucc,
        Order.lt_add_one_iff, Order.add_one_le_iff, add_lt_iff_neg_left, Nat.add_eq_left,
        add_tsub_cancel_right, Fin.succAbove_le_iff];
    cases h_contra <;> try simp_all +decide only [Fin.succAbove]
    · -- Both neighbours lie before `j`, but the right one sits at `insertLeftIndex ν j` itself.
      rename_i n hlt
      have hb : n + 1 < p + q + 1 := by
        have := ‹↑(Fin.cast _ (ν.insertLeftIndex j)) < p + 1 + q›
        simp only [Fin.val_cast] at this
        omega
      have := (insertLeftIndex_iff ν j ⟨n + 1, hb⟩).mp (by simpa [Fin.lt_def] using hlt.2)
      simp [h] at this
    · split_ifs at * <;> simp_all +decide only [Fin.lt_def, Fin.val_castSucc, Fin.le_iff_val_le_val,
          not_lt, Fin.val_succ, Order.lt_add_one_iff, and_true]
      · omega
      · linarith! [ Fin.is_lt j ];
      · linarith! [ ν.1.monotone ( show ⟨ ‹_›, by linarith ⟩ ≤ ⟨ ‹_› + 1,
            by linarith ⟩ from Nat.le_succ _ ) ];
      · have := insertLeftIndex_iff ν j ⟨ ‹_›,
            by omega ⟩; simp_all +decide only [lt_add_iff_pos_right, iff_true];
        linarith! [ Fin.is_lt j ];

/-- Right insertion always produces a non-diagonal vertex: the two steps
adjacent to the inserted vertex are both right steps (RR pattern). -/
lemma insertRightStep_not_diagonal {p q : ℕ}
    (ν : Shuffle (p + 1) q) (k : Fin (q + 2)) :
    ¬isDiagonalVertex (insertRightStep ν k)
      ((insertRightIndex ν k).cast (by omega)) := by
  unfold Shuffle.isDiagonalVertex; simp +decide only [Fin.cast_eq_self, Fin.val_pos_iff,
      insertRightStep, dite_false_right, not_exists, not_or, not_and, Decidable.not_not];
  unfold Shuffle.isLeftStep; intros; simp_all +decide only [insertRightStepFun, Fin.val_fin_lt,
      Fin.castSucc_mk, OrderHom.coe_mk, Fin.succ_mk, add_tsub_cancel_right, Fin.eta,
      lt_self_iff_false, ↓reduceDIte, Nat.add_eq_left, not_lt];
  split_ifs at * <;> simp_all +decide only [not_lt, Fin.eta, lt_self_iff_false, not_false_eq_true,
      IsEmpty.forall_iff, Std.le_refl, forall_const, true_and, not_true_eq_false, Nat.add_eq_left];
  all_goals erw [ Fin.lt_def ] at *; simp_all +decide only [Fin.coe_ofNat_eq_mod,
      lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le, Nat.mod_eq_of_lt, Fin.val_pos_iff,
      tsub_lt_self_iff, and_self, add_lt_iff_neg_left, Fin.val_fin_lt, Nat.add_eq_left,
      implies_true, true_and];
  any_goals omega;
  · constructor <;> intro h <;> have := ν.1.monotone ( show ⟨ ( ν.insertRightIndex k : ℕ ) - 1,
        by omega ⟩ ≤ ⟨ ( ν.insertRightIndex k : ℕ ), by omega ⟩ from Nat.sub_le _ _
        ) <;> simp_all +decide [ Fin.le_iff_val_le_val ] ;
    · have := insertRightIndex_iff ν k ⟨ ( ν.insertRightIndex k : ℕ ) - 1,
          by omega ⟩; simp_all +decide [];
      have := coordSum_eq ν ⟨ ( ν.insertRightIndex k : ℕ ) - 1,
          by omega ⟩; have := coordSum_eq ν ⟨ ( ν.insertRightIndex k : ℕ ),
          by omega ⟩; simp_all +decide []; omega;
    · have := coordSum_eq ν ⟨ ( ν.insertRightIndex k : ℕ ), by omega ⟩; simp_all +decide [];
      have := ( insertRightIndex_iff ν k ⟨ ( ν.insertRightIndex k : ℕ ),
          by omega ⟩ ); simp_all +decide [];
      omega;
  · exact absurd ‹_› ( not_le_of_gt ( Nat.pred_lt ( ne_bot_of_gt ‹_› ) ) )



/- Every non-diagonal vertex of a `(p+1,q+1)`-shuffle is in the image of
either `insertLeftStep` (from a `(p, q+1)`-shuffle and face index `j`) or
`insertRightStep` (from a `(p+1, q)`-shuffle and face index `k`).

This covers interior LL/RR vertices and boundary vertices (r = 0 or r = last). -/
section

/-- A vertex `r` is a "left vertex" if every existing adjacent step is left.
At an interior vertex both steps must be left; at an endpoint only its existing edge is tested.
The predicate is vacuously true when the path has no edges. -/
def isLeftVertex {p q : ℕ} (μ : Shuffle p q) (r : Fin (p + q + 1)) : Prop :=
  (∀ k : Fin (p + q), k.succ = r → isLeftStep μ k) ∧
  (∀ k : Fin (p + q), k.castSucc = r → isLeftStep μ k)

/-- A vertex `r` is a "right vertex" if every existing adjacent step is right.
At an interior vertex both steps must be right; at an endpoint only its existing edge is tested.
The predicate is vacuously true when the path has no edges. -/
def isRightVertex {p q : ℕ} (μ : Shuffle p q) (r : Fin (p + q + 1)) : Prop :=
  (∀ k : Fin (p + q), k.succ = r → ¬Shuffle.isLeftStep μ k) ∧
  (∀ k : Fin (p + q), k.castSucc = r → ¬Shuffle.isLeftStep μ k)

/-- Inverse of `Fin.succAbove p`: maps `i` to `j` such that `p.succAbove j = i`,
assuming `i ≠ p`. -/
def finRemove {n : ℕ} (p : Fin (n + 2)) (i : Fin (n + 2)) : Fin (n + 1) :=
  if h : i < p then
    ⟨i.val, by omega⟩
  else
    ⟨i.val - 1, by
      have : i.val < n + 2 := i.isLt
      omega⟩

/-- Removing a left step at `r` (assuming `isLeftVertex μ r`). -/
def removeLeftFun {p q : ℕ} (μ : Shuffle (p + 1) q) (r : Fin (p + q + 2)) : Index (p +
    q) → Index p × Index q :=
  fun k =>
    let r' : Index (p + 1 + q) := r.cast (by omega)
    let k_mapped := r'.succAbove (k.cast (by omega))
    let val := μ.1 k_mapped
    (finRemove (μ.1 r').1 val.1, val.2)

/-- Removing a right step at `r` (assuming `isRightVertex μ r`). -/
def removeRightFun {p q : ℕ} (μ : Shuffle p (q + 1)) (r : Fin (p + q + 2)) : Index (p +
    q) → Index p × Index q :=
  fun k =>
    let r' : Index (p + q + 1) := r.cast (by omega)
    let k_mapped := r'.succAbove (k.cast (by omega))
    let val := μ.1 k_mapped
    (val.1, finRemove (μ.1 r').2 val.2)

lemma succAbove_finRemove {n : ℕ} (p : Fin (n + 2)) (i : Fin (n + 2)) (h : i ≠ p) :
    p.succAbove (finRemove p i) = i := by
  unfold finRemove
  split_ifs with hi
  · rw [Fin.succAbove_of_castSucc_lt _ _ hi]
    rfl
  · have hpi : p.val < i.val := Fin.lt_def.mp (lt_of_le_of_ne (not_lt.mp hi) (Ne.symm h))
    rw [Fin.succAbove_of_le_castSucc _ _ (Fin.le_def.mpr (by simp; omega))]
    ext
    simp
    omega

lemma finRemove_strictMono_on {n : ℕ} (p : Fin (n + 2)) :
    StrictMonoOn (finRemove p) {i | i ≠ p} := by
      -- To prove strict monotonicity, we need to show that if $i < j$ and both are not equal to
      -- $p$, then $\text{finRemove } p i < \text{finRemove } p j$.
      intros i hi j hj hij
      simp only [ne_eq, Set.mem_ofPred_eq, finRemove] at *;
      -- By definition of `finRemove`, we split into cases based on whether `i` and `j` are less
      -- than `p` or not.
      by_cases hip : i < p
      · by_cases hjp : j < p
        · aesop
        · -- Since $i < p$ and $j \geq p$, we have $i.val < j.val - 1$.
          have h_val : i.val < j.val - 1 := by
            grind
          generalize_proofs at *;
          split_ifs; aesop
      · split_ifs <;> simp_all +decide only [Fin.ext_iff, not_lt, Fin.mk_lt_mk]
        · omega
        · generalize_proofs at *
          exact tsub_lt_tsub_iff_right (Nat.one_le_iff_ne_zero.mpr <| by aesop) |>.2 hij

lemma ne_fst_of_isLeftVertex {p q : ℕ} {μ : Shuffle (p + 1) q} {r : Index ((p + 1) + q)}
    (h : isLeftVertex μ r) (k : Index ((p + 1) + q)) (hkr : k ≠ r) :
    (μ.1 k).1 ≠ (μ.1 r).1 := by
      -- Consider two cases: $k < r$ and $k > r$.
      by_cases h_cases : k.val < r.val;
      · -- Since $k < r$, we have $μ(k).1 ≤ μ(r-1).1$.
        have h_le : (μ.1 k).1 ≤ (μ.1 (Fin.mk (r.val - 1) (by omega))).1 := by
          exact μ.1.monotone ( Nat.le_sub_one_of_lt h_cases ) |>.1;
        rcases r with ⟨ _ | r, hr ⟩ <;> simp_all +decide only [Fin.zero_eta, ne_eq, zero_tsub,
            add_tsub_cancel_right];
        · tauto;
        · exact ne_of_lt ( lt_of_le_of_lt h_le ( h.1 ⟨ r, by linarith ⟩ rfl ) );
      · -- Since $k$ is not less than $r$, we have $k > r$.
        have h_k_gt_r : (r.val + 1 : ℕ) ≤ k.val := by
          exact Nat.succ_le_of_lt ( lt_of_le_of_ne ( le_of_not_gt h_cases ) ( Ne.symm <|
              by simpa [ Fin.ext_iff ] using hkr ) );
        -- Since $r$ is a left vertex, we have $(μ.1 r).1 < (μ.1 (r + 1)).1$.
        have h_left_vertex : (μ.1 r).1.val < (μ.1 (Fin.mk (r.val + 1) (by
        linarith [ Fin.is_lt r, Fin.is_lt k ]))).1.val := by
          all_goals generalize_proofs at *;
          have := h.2 ⟨ r.val, by linarith ⟩; aesop;
        generalize_proofs at *;
        exact ne_of_gt ( lt_of_lt_of_le h_left_vertex ( μ.1.monotone ( Nat.succ_le_of_lt h_k_gt_r )
            |> And.left ) )

lemma ne_snd_of_isRightVertex {p q : ℕ} {μ : Shuffle p (q + 1)} {r : Index (p + (q + 1))}
    (h : isRightVertex μ r) (k : Index (p + (q + 1))) (hkr : k ≠ r) :
    (μ.1 k).2 ≠ (μ.1 r).2 := by
  by_cases h_cases : k.val < r.val
  · have h_le : (μ.1 k).2 ≤ (μ.1 (Fin.mk (r.val - 1) (by omega))).2 :=
      (μ.1.monotone (Nat.le_sub_one_of_lt h_cases)).2
    rcases r with ⟨_ | r, hr⟩ <;> simp_all +decide only [Fin.zero_eta, ne_eq, zero_tsub,
        add_tsub_cancel_right]
    · tauto
    · have hnot := h.1 ⟨r, by omega⟩ rfl
      unfold isLeftStep at hnot
      have hidx1 : (⟨r, by omega⟩ : Fin (p + (q + 1))).castSucc =
          ⟨r, by omega⟩ := Fin.ext (by simp)
      have hidx2 : (⟨r, by omega⟩ : Fin (p + (q + 1))).succ =
          ⟨r + 1, hr⟩ := Fin.ext (by simp)
      rcases shuffle_step μ ⟨r, by omega⟩ with hs | hs
      · rw [hidx1, hidx2] at hnot hs; omega
      · rw [hidx1, hidx2] at hs
        exact ne_of_lt (lt_of_le_of_lt h_le (Fin.lt_def.mpr (by omega)))
  · have h_k_gt_r : r.val + 1 ≤ k.val := by
      exact Nat.succ_le_of_lt
        (lt_of_le_of_ne (le_of_not_gt h_cases)
          (Ne.symm (by simpa [Fin.ext_iff] using hkr)))
    have h_right_vertex :
        (μ.1 r).2.val < (μ.1 (Fin.mk (r.val + 1) (by omega))).2.val := by
      have hnot := h.2 ⟨r.val, by omega⟩ rfl
      unfold isLeftStep at hnot
      have hidx1 : (⟨r.val, by omega⟩ : Fin (p + (q + 1))).castSucc = r :=
        Fin.ext (by simp)
      have hidx2 : (⟨r.val, by omega⟩ : Fin (p + (q + 1))).succ =
          ⟨r.val + 1, by omega⟩ := Fin.ext (by simp)
      rcases shuffle_step μ ⟨r.val, by omega⟩ with hs | hs
      · rw [hidx1, hidx2] at hnot hs; omega
      · rw [hidx1, hidx2] at hs; omega
    exact ne_of_gt
      (lt_of_lt_of_le h_right_vertex
        ((μ.1.monotone (Nat.succ_le_of_lt h_k_gt_r)).2))

lemma removeLeft_is_shuffle {p q : ℕ} {μ : Shuffle (p + 1) q} {r : Fin (p + q + 2)}
    (h : isLeftVertex μ (r.cast (by omega))) :
    StrictMono (removeLeftFun μ r) := by
      intro i j hij;
      -- Let `v₁ = μ.1 (r.succAbove i)` and `v₂ = μ.1 (r.succAbove j)`.
      set v₁ := μ.1 (Fin.succAbove (Fin.cast (by omega) r) (i.cast (by omega)))
      set v₂ := μ.1 (Fin.succAbove (Fin.cast (by omega) r) (j.cast (by omega)));
      -- Since `μ` is a shuffle and `succAbove` is strictly monotone, `v₁ < v₂`.
      have hv₁v₂ : v₁ < v₂ := by
        refine lt_of_le_of_ne ?_ ?_
        · refine μ.1.monotone ?_
          simp +decide only [Fin.succAbove];
          split_ifs <;> simp_all +decide only [Fin.castSucc_le_castSucc_iff, Fin.cast_le_cast,
              not_lt, Fin.succ_le_castSucc_iff, Fin.cast_lt_cast, Fin.succ_le_succ_iff];
          · exact le_of_lt hij;
          · exact Nat.le_succ_of_le ( Nat.le_trans ( Nat.le_of_lt ‹_› ) ‹_› );
          · exact le_of_lt hij;
        · have := μ.2;
          intro H; have := @this ( Fin.succAbove ( Fin.cast ( by omega ) r ) ( Fin.cast (
              by omega ) i ) ) ( Fin.succAbove ( Fin.cast ( by omega ) r ) ( Fin.cast (
              by omega ) j ) ); simp_all +decide only [Fin.succAbove_inj, Fin.cast_inj];
          exact absurd ( this H ) hij.ne;
      -- Since `v₁.1 ≠ (μ.1 r).1` and `v₂.1 ≠ (μ.1 r).1` by `ne_fst_of_isLeftVertex`, we can apply
      -- `finRemove_strictMono_on`.
      have hv₁v₂_fst : v₁.1 ≠ (μ.1 (Fin.cast (by omega) r)).1 ∧ v₂.1 ≠ (μ.1 (Fin.cast (by omega)
          r)).1 := by
        apply And.intro;
        · have := ne_fst_of_isLeftVertex h (Fin.succAbove (Fin.cast (by omega) r) (i.cast
              (by omega))) ?_ <;> aesop;
        · apply ne_fst_of_isLeftVertex h;
          simp +decide [ Fin.succAbove_ne ];
      by_cases h : v₁.1 < v₂.1 <;> simp_all +decide only [Prod.lt_iff, true_and, ne_eq, false_and,
          false_or, not_lt];
      · have h_finRemove : finRemove (μ.1 (Fin.cast (by omega) r)).1 v₁.1 < finRemove (μ.1 (Fin.cast
            (by omega) r)).1 v₂.1 := by
          apply finRemove_strictMono_on
          · simp [hv₁v₂_fst]
          · exact hv₁v₂_fst.2;
          · exact h;
        exact Or.inl ⟨ h_finRemove, hv₁v₂.elim ( fun h => h ) fun h => h.2.le ⟩;
      · have h_eq : finRemove (μ.1 (Fin.cast (by omega) r)).1 v₁.1 = finRemove (μ.1 (Fin.cast
            (by omega) r)).1 v₂.1 := by
          rw [ le_antisymm hv₁v₂.1 h ];
        exact Or.inr ⟨ h_eq.le, hv₁v₂.2 ⟩

lemma removeRight_is_shuffle {p q : ℕ} {μ : Shuffle p (q + 1)} {r : Fin (p + q + 2)}
    (h : isRightVertex μ (r.cast (by omega))) :
    StrictMono (removeRightFun μ r) := by
      intro k l hkl
      simp only [Fin.cast_eq_self, removeRightFun, Prod.mk_lt_mk] at *;
      have h_comp : (μ.1 (r.succAbove k)).1 ≤ (μ.1 (r.succAbove l)).1 ∧ (μ.1 (r.succAbove
          k)).2 ≤ (μ.1 (r.succAbove l)).2 := by
        exact μ.1.monotone (by
        exact Fin.le_iff_val_le_val.mpr ( by simpa using hkl.le
                                              ) |> le_trans <| Fin.le_iff_val_le_val.mpr le_rfl;);
      have h_neq : (μ.1 (r.succAbove k)).2 ≠ (μ.1 r).2 ∧ (μ.1 (r.succAbove l)).2 ≠ (μ.1 r).2 := by
        have h_neq : ∀ k : Fin (p + q + 2), k ≠ r → (μ.1 k).2 ≠ (μ.1 r).2 := by
          exact fun k a => ne_snd_of_isRightVertex h k a
        generalize_proofs at *; aesop;
      cases lt_or_eq_of_le h_comp.1 <;> cases lt_or_eq_of_le h_comp.2 <;>
          simp_all +decide only [ne_eq, true_and, Std.le_refl, and_true, and_self,
          lt_self_iff_false, and_false, or_false, false_and, false_or, gt_iff_lt, or_self];
      · -- Since the second components are not equal and the first components are strictly
        -- increasing, the second component must be strictly increasing.
        have h_second_inc : (μ.1 (r.succAbove k)).2 < (μ.1 (r.succAbove l)).2 := by
          assumption;
        exact Or.inr ( finRemove_strictMono_on _ ( show ( μ.1 ( r.succAbove k ) ).2 ≠ ( μ.1 r ).2
            from h_neq.1 ) ( show ( μ.1 ( r.succAbove l ) ).2 ≠ ( μ.1 r ).2 from h_neq.2 )
            h_second_inc );
      · apply finRemove_strictMono_on;
        · exact h_neq.1;
        · aesop;
        · assumption;
      · have h_eq : (μ.1 (r.succAbove k)).1 = (μ.1 (r.succAbove l)).1 ∧ (μ.1 (r.succAbove
            k)).2 = (μ.1 (r.succAbove l)).2 := by
          aesop;
        have := μ.2; simp_all +decide [ Function.Injective ] ;
        specialize this ( show μ.1 ( r.succAbove k ) = μ.1 ( r.succAbove l ) from Prod.ext h_eq.1
            h_eq.2 ); simp_all +decide [];

/-- The shuffle obtained by removing a left step. -/
def removeLeft {p q : ℕ} (μ : Shuffle (p + 1) q) (r : Fin (p + q + 2))
    (h : isLeftVertex μ (r.cast (by omega))) : Shuffle p q :=
  ⟨⟨removeLeftFun μ r, (removeLeft_is_shuffle h).monotone⟩, (removeLeft_is_shuffle h).injective⟩

/-- The shuffle obtained by removing a right step. -/
def removeRight {p q : ℕ} (μ : Shuffle p (q + 1)) (r : Fin (p + q + 2))
    (h : isRightVertex μ (r.cast (by omega))) : Shuffle p q :=
  ⟨⟨removeRightFun μ r, (removeRight_is_shuffle h).monotone⟩, (removeRight_is_shuffle h).injective⟩

lemma finRemove_val_lt_iff {n : ℕ} {p : Fin (n + 2)} {i : Fin (n + 2)} (h : i ≠ p) :
    (finRemove p i).val < p.val ↔ i < p := by
      cases lt_or_gt_of_ne h <;> simp +decide [ *, D5.S3.HomologicalAlgebra.EilenbergZilber.Shuffle.finRemove ];
      grind

lemma insertIndex_removeLeft {p q : ℕ} {μ : Shuffle (p + 1) q} {r : Fin (p + q + 2)}
    (h : isLeftVertex μ (r.cast (by omega))) :
    insertLeftIndex (removeLeft μ r h) (μ.1 (r.cast (by omega))).1 = r.cast (by omega) := by
      refine Fin.ext ?_
      simp +decide only [isLeftVertex, Fin.cast_eq_self] at h ⊢;
      -- By definition of `isLeftVertex`, we know that for all `k`, if `k.castSucc = r.cast`, then
      -- `μ.isLeftStep k`.
      have h_fst_lt : ∀ k : Fin (p + q + 1), (μ.1 (Fin.succAbove (Fin.cast (by omega) r) (k.cast
          (by omega)))).1.val < (μ.1 (Fin.cast (by omega) r)).1.val ↔ k.val < r.val := by
        intro k; exact ⟨fun hk => by
          contrapose! hk;
          refine (μ.1.monotone ?_).1
          simp +decide [ Fin.le_iff_val_le_val, Fin.succAbove ];
          split_ifs <;> simp_all +decide [];
          linarith, fun hk => by
          have h_fst_lt : (μ.1 (Fin.succAbove (Fin.cast (by omega) r) (k.cast
              (by omega)))).1.val ≤ (μ.1 (Fin.cast (by omega) r)).1.val := by
            refine (μ.1.monotone ?_).1
            simp +decide [ Fin.le_iff_val_le_val, Fin.succAbove ];
            split_ifs <;> simp_all +decide [ Fin.lt_def ];
            linarith;
          refine lt_of_le_of_ne h_fst_lt ?_
          have := ne_fst_of_isLeftVertex h ( Fin.succAbove ( Fin.cast ( by omega ) r ) ( Fin.cast (
              by omega ) k ) ) ?_ <;> simp_all +decide only [Fin.ext_iff, Fin.val_succ,
              Fin.val_cast, Fin.val_castSucc, Fin.val_fin_le, ne_eq, not_false_eq_true];
          simp +decide only [Fin.succAbove];
          split_ifs <;> simp_all +decide only [Fin.lt_def, Fin.val_castSucc, Fin.val_cast,
              not_true_eq_false];
          exact Nat.ne_of_lt hk⟩;
      -- By definition of `insertLeftIndex`, we know that `insertLeftIndex ν j` is the number of `k`
      -- such that `(ν.1 k).1.val < j.val`.
      have h_insertLeftIndex : ∀ ν : Shuffle p q, ∀ j : Fin (p + 2), (ν.insertLeftIndex
          j).val = Finset.card (Finset.filter (fun k : Fin (p + q + 1) => (ν.1 k).1.val < j.val)
          Finset.univ) := by
        intro ν j; simp [insertLeftIndex]
      rw [h_insertLeftIndex, Finset.card_eq_of_bijective]
      · exact fun i hi => ⟨i, by linarith [Fin.is_lt r]⟩
      · intro a ha;
        use a.val;
        convert h_fst_lt a |>.1 _;
        · exact ⟨ fun h => h.1, fun h => ⟨ h, rfl ⟩ ⟩;
        · convert ha using 1
          rw [Finset.mem_filter_univ]
          simp +decide only [Fin.val_fin_lt, removeLeft, OrderHom.coe_mk, removeLeftFun];
          rw [ finRemove_val_lt_iff ];
          intro H; have := ne_fst_of_isLeftVertex h; simp_all +decide only [Fin.val_fin_lt,
              Subtype.forall, Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff, ne_eq,
              Fin.val_cast];
          specialize this ( Fin.succAbove ( Fin.cast ( by omega ) r ) ( Fin.cast (
              by omega ) a ) ); simp_all +decide only [Fin.succAbove, not_true_eq_false, imp_false,
              Decidable.not_not];
          split_ifs at this <;> simp_all +decide only [↓reduceIte, Fin.val_castSucc, Fin.val_cast,
              not_lt, Fin.val_succ];
          · exact absurd this ( ne_of_lt ‹_› );
          · grind;
      · intro i hi;
        convert h_fst_lt ⟨ i, by linarith [ Fin.is_lt r ] ⟩ |>.2 hi using 1
        rw [Finset.mem_filter_univ]
        simp +decide only [removeLeft, OrderHom.coe_mk, Fin.cast_mk, Fin.val_fin_lt];
        simp +decide only [removeLeftFun, Fin.cast_mk];
        rw [ finRemove_val_lt_iff ];
        have := ne_fst_of_isLeftVertex h ( Fin.succAbove ( Fin.cast ( by omega ) r ) ⟨ i,
            by linarith [ Fin.is_lt r ] ⟩ ) ?_ <;> simp_all +decide only [Fin.succAbove,
            Fin.val_fin_lt, Subtype.forall, Fin.castSucc_mk, Fin.succ_mk, ne_eq, not_false_eq_true];
        split_ifs <;> simp_all +decide only [Fin.ext_iff, Fin.val_succ, Fin.val_cast,
            Fin.val_castSucc, not_lt];
        · linarith;
        · exact absurd ‹_› ( not_le_of_gt ( Nat.lt_of_succ_le hi ) );
      · simp +contextual [ Fin.ext_iff ]

/-- `insertLeftStep` before the insertion index: the vertex of `ν`, with its first coordinate
pushed past `j`. -/
private lemma insertLeftStep_apply_of_lt {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2))
    (k : Fin ((p + 1) + q + 1)) (hk : k.val < (insertLeftIndex ν j).val) :
    (insertLeftStep ν j).1 k =
      (j.succAbove (ν.1 ⟨k, by have := (insertLeftIndex ν j).isLt; omega⟩).1,
        (ν.1 ⟨k, by have := (insertLeftIndex ν j).isLt; omega⟩).2) := by
  simp [insertLeftStep, insertLeftStepFun, hk]

/-- `insertLeftStep` at the insertion index: the new vertex `(j, t - j)`. -/
private lemma insertLeftStep_apply_of_eq {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2))
    (k : Fin ((p + 1) + q + 1)) (hk : k.val = (insertLeftIndex ν j).val) :
    (insertLeftStep ν j).1 k = (j, ⟨k.val - j.val, by have := insertLeftIndex_le ν j; omega⟩) := by
  simp [insertLeftStep, insertLeftStepFun, hk]

/-- `insertLeftStep` after the insertion index: the previous vertex of `ν`, with its first
coordinate pushed past `j`. -/
private lemma insertLeftStep_apply_of_gt {p q : ℕ} (ν : Shuffle p q) (j : Fin (p + 2))
    (k : Fin ((p + 1) + q + 1)) (hk : (insertLeftIndex ν j).val < k.val) :
    (insertLeftStep ν j).1 k =
      (j.succAbove (ν.1 ⟨k - 1, by omega⟩).1, (ν.1 ⟨k - 1, by omega⟩).2) := by
  simp [insertLeftStep, insertLeftStepFun, hk.not_gt, hk.ne']

/-- Every vertex of `removeLeft μ r h`, with its first coordinate pushed back past `(μ r).1`, is
the corresponding vertex of `μ` away from `r`. -/
private lemma succAbove_removeLeft_apply {p q : ℕ} {μ : Shuffle (p + 1) q} {r : Fin (p + q + 2)}
    (h : isLeftVertex μ (r.cast (by omega))) (i : Index (p + q)) :
    ((μ.1 (r.cast (by omega))).1.succAbove ((removeLeft μ r h).1 i).1,
        ((removeLeft μ r h).1 i).2) =
      μ.1 ((r.cast (by omega) : Index (p + 1 + q)).succAbove (i.cast (by omega))) :=
  Prod.ext (succAbove_finRemove _ _ (ne_fst_of_isLeftVertex h _ (Fin.succAbove_ne _ _))) rfl

lemma insertLeft_removeLeft {p q : ℕ} {μ : Shuffle (p + 1) q} {r : Fin (p + q + 2)}
    (h : isLeftVertex μ (r.cast (by omega))) :
    insertLeftStep (removeLeft μ r h) (μ.1 (r.cast (by omega))).1 = μ := by
  have ht : (insertLeftIndex (removeLeft μ r h) (μ.1 (r.cast (by omega))).1).val = r.val := by
    simpa using congrArg Fin.val (insertIndex_removeLeft h)
  refine Subtype.ext (OrderHom.ext _ _ (funext fun k => ?_))
  rcases lt_trichotomy k.val r.val with hk | hk | hk
  · -- before `r`: the vertex is unchanged by `succAbove r`
    rw [insertLeftStep_apply_of_lt _ _ k (by omega), succAbove_removeLeft_apply h]
    congr 1
    rw [Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def]; omega)]
    exact Fin.ext (by simp)
  · -- at `r`: the inserted vertex is `(μ r).1` paired with the complementary coordinate
    rw [insertLeftStep_apply_of_eq _ _ k (by omega)]
    have hkr : r.cast (by omega) = k := Fin.ext (by simp [hk])
    have h1 := congrArg (fun x => ((μ.1 x).1 : ℕ)) hkr
    have h2 := coordSum_eq μ k
    refine Prod.ext (congrArg (fun x => (μ.1 x).1) hkr) (Fin.ext ?_)
    dsimp only at h1 ⊢
    omega
  · -- after `r`: `succAbove r` shifts the preceding vertex back up to `k`
    rw [insertLeftStep_apply_of_gt _ _ k (by omega), succAbove_removeLeft_apply h]
    congr 1
    rw [Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)]
    exact Fin.ext (by simp; omega)

lemma insertIndex_removeRight {p q : ℕ} {μ : Shuffle p (q + 1)} {r : Fin (p + q + 2)}
    (h : isRightVertex μ (r.cast (by omega))) :
    insertRightIndex (removeRight μ r h) (μ.1 (r.cast (by omega))).2 = r.cast (by omega) := by
      have h_equiv : ∀ k : Fin (p + q + 1), (μ.1 (r.cast (by omega) |> Fin.succAbove <| k.cast
          (by omega))).2 < (μ.1 (Fin.cast (by omega) r)).2 ↔ k.val < r.val := by
        intro k
        constructor;
        · intro hk;
          contrapose! hk;
          exact μ.1.monotone (by
          simp +decide [ Fin.succAbove];
          split_ifs <;> simp_all +decide [ Fin.le_iff_val_le_val ];
          grind) |>.2;
        · intro hk
          have h_succ_above : (Fin.cast (by omega) r).succAbove (Fin.cast (by omega) k) < r := by
            simp +decide [ Fin.succAbove];
            split_ifs <;> simp_all +decide [ Fin.lt_def ];
          refine lt_of_le_of_ne ?_ ?_
          · exact μ.1.monotone h_succ_above.le |>.2;
          · apply ne_snd_of_isRightVertex h;
            exact ne_of_lt h_succ_above;
      norm_num [ Fin.ext_iff, Fin.val_mk, h_equiv ] at *;
      rw [ show ( μ.removeRight r h |> D5.S3.HomologicalAlgebra.EilenbergZilber.Shuffle.insertRightIndex ) ( ( μ.1 r
          ).2 ) = Finset.card ( Finset.filter ( fun k : Fin ( p + q + 1 ) => ( μ.1 ( r.succAbove k )
          ).2 < ( μ.1 r ).2 ) Finset.univ ) from ?_ ];
      · rw [Finset.card_eq_of_bijective]
        · exact fun i hi => ⟨i, by linarith [Fin.is_lt r]⟩
        · grind;
        · aesop;
        · aesop;
      · unfold D5.S3.HomologicalAlgebra.EilenbergZilber.Shuffle.insertRightIndex; simp +decide only
        congr! 2
        rename_i x hx
        simp only [removeRight, OrderHom.coe_mk, removeRightFun, Fin.cast_eq_self]
        have hne : (μ.1 (r.succAbove x)).2 ≠ (μ.1 r).2 :=
          ne_snd_of_isRightVertex h _ (Fin.succAbove_ne r x)
        rw [finRemove_val_lt_iff hne]

lemma isRightVertex_swap {p q : ℕ} {μ : Shuffle p q} {r : Fin (p + q + 1)} :
    isRightVertex μ r ↔ isLeftVertex μ.swap (r.cast (by omega)) := by
      simp +decide only [isRightVertex, isLeftVertex, swap, Fin.castOrderIso_apply];
      simp +decide only [isLeftStep];
      constructor;
      · intro h;
        constructor <;> intro k hk;
        · convert h.1 ⟨ k, by linarith [ Fin.is_lt k ] ⟩ _ using 1;
          · simp +decide only [Fin.succ, Fin.cast, Fin.mk.injEq, OrderHom.coe_mk, Fin.val_castSucc,
                Prod.fst_swap, Fin.val_fin_lt, Fin.castSucc_mk, not_lt] at hk ⊢;
            have := coordSum_eq μ ⟨ k, by linarith [ Fin.is_lt k ] ⟩; have := coordSum_eq μ ⟨ k +
                1, by linarith [ Fin.is_lt k ] ⟩; simp_all +decide only [Fin.val_fin_lt, not_lt,
                Fin.eta];
            constructor <;> intro <;> omega;
          · exact Fin.ext ( by simpa [ Fin.ext_iff ] using congr_arg Fin.val hk );
        · -- castSucc case: ¬isLeftStep at k ⇒ snd increases ⇒ isLeftStep for swap
          have hk' : (⟨k.val, by omega⟩ : Fin (p + q)).castSucc = r :=
            Fin.ext (by simpa [Fin.val_castSucc, Fin.val_cast] using congrArg Fin.val hk)
          have hnot : ¬isLeftStep μ ⟨k.val, by omega⟩ := h.2 _ hk'
          have hsnd : (μ.1 (⟨k.val, by omega⟩ : Fin (p + q)).castSucc).2.val <
              (μ.1 (⟨k.val, by omega⟩ : Fin (p + q)).succ).2.val := by
            have hiff := shuffle_fst_lt_iff_not_snd_lt μ ⟨k.val, by omega⟩
            exact Decidable.not_not.mp (mt hiff.mpr hnot)
          convert hsnd using 1 <;> rfl
      · intro h;
        constructor <;> intro k hk <;> simp_all +decide only [Fin.ext_iff, Fin.val_succ,
            Fin.val_cast, OrderHom.coe_mk, Fin.cast_castSucc, Prod.fst_swap, Fin.cast_succ_eq,
            Fin.val_fin_lt, Fin.val_castSucc, not_lt];
        · contrapose! h;
          intro h; specialize h ⟨ k, by linarith [ Fin.is_lt k ] ⟩ hk; simp_all +decide [ Fin.cast,
              Fin.castSucc ];
          have := coordSum_eq μ ( Fin.castAdd 1 k ); have := coordSum_eq μ k.succ;
              simp_all +decide [ Fin.castAdd, Fin.succ ];
          grind only [];
        · contrapose! h;
          intro h';
          use ⟨ r.val, by
            linarith [ Fin.is_lt k, Fin.is_lt r ] ⟩
          generalize_proofs at *;
          simp_all +decide only [Fin.castSucc, Fin.cast, Fin.castAdd_mk, Fin.succ_mk, Fin.eta,
              true_and];
          simp_all +decide only [Fin.castAdd, Fin.succ];
          convert le_of_not_gt fun h'' => _;
          have := coordSum_eq μ r; have := coordSum_eq μ ⟨ r.val + 1,
              by omega ⟩; simp_all +decide [ Fin.castLE ];
          linarith [ show ( μ.1 r |>.1 : ℕ ) < ( μ.1 ⟨ r.val + 1, by omega ⟩ |>.1 : ℕ ) from h,
              show ( μ.1 r |>.2 : ℕ ) < ( μ.1 ⟨ r.val + 1, by omega ⟩ |>.2 : ℕ ) from h'' ]

lemma removeRight_eq_swap_removeLeft {p q : ℕ} (μ : Shuffle p (q + 1)) (r : Fin (p + q + 2))
    (h : isRightVertex μ (r.cast (by omega))) :
    removeRight μ r h = (removeLeft μ.swap (r.cast (by omega)) (isRightVertex_swap.mp h)).swap := by
      unfold D5.S3.HomologicalAlgebra.EilenbergZilber.Shuffle.removeRight
          D5.S3.HomologicalAlgebra.EilenbergZilber.Shuffle.removeLeft
      generalize_proofs at *;
      unfold D5.S3.HomologicalAlgebra.EilenbergZilber.Shuffle.removeRightFun
          D5.S3.HomologicalAlgebra.EilenbergZilber.Shuffle.removeLeftFun
      generalize_proofs at *;
      ext ⟨ i, j ⟩
      · simp +decide only [Fin.cast_eq_self, OrderHom.coe_mk, Fin.cast_cast]
        unfold D5.S3.HomologicalAlgebra.EilenbergZilber.Shuffle.swap; simp +decide only [Fin.castOrderIso_apply,
            OrderHom.coe_mk, Fin.cast_cast, Fin.cast_eq_self, Prod.fst_swap, Prod.snd_swap,
            Prod.swap_prod_mk, Fin.cast_mk];
        congr! 2
        generalize_proofs at *; simp +arith +decide only [Fin.succAbove, Fin.castSucc_mk,
            Fin.succ_mk]; (
        congr! 2
        generalize_proofs at *; simp +arith +decide only [Fin.cast, Fin.mk_lt_mk] ; (
        split_ifs <;> simp +decide [ *, Fin.lt_def ] at * ;));
      · unfold D5.S3.HomologicalAlgebra.EilenbergZilber.Shuffle.swap; simp +decide only [Fin.cast_eq_self,
            OrderHom.coe_mk, Fin.castOrderIso_apply, Fin.cast_cast, Prod.fst_swap, Prod.snd_swap,
            Prod.swap_prod_mk, Fin.cast_mk];
        congr! 2;
        congr! 2; simp +decide [ Fin.succAbove ] ; ring_nf;
        split_ifs <;> simp +decide only [Fin.cast, Fin.mk.injEq, Nat.right_eq_add,
            Nat.add_eq_right];
        · exact ‹¬_› ( by simpa [ Fin.cast ] using ‹_› );
        · exact ‹¬_› ( by simpa [ Fin.cast ] using ‹_› )

lemma not_diagonal_iff_left_or_right {p q : ℕ} {μ : Shuffle (p + 1) (q + 1)} {r : Fin (p + q + 3)} :
    ¬isDiagonalVertex μ (r.cast (by omega)) ↔ isLeftVertex μ (r.cast
        (by omega)) ∨ isRightVertex μ (r.cast (by omega)) := by
      unfold isDiagonalVertex isLeftVertex isRightVertex
      generalize_proofs at *;
      split_ifs <;> simp_all +decide only [Fin.val_cast, not_or, not_and, Decidable.not_not,
          Fin.val_pos_iff, not_lt, true_iff, isEmpty_Prop, IsEmpty.forall_iff, imp_self,
          nonpos_iff_eq_zero, Fin.cast_zero, Fin.succ_ne_zero, implies_true,
          Fin.castSucc_eq_zero_iff, forall_eq, true_and, lt_self_iff_false, Fin.coe_ofNat_eq_mod,
          Nat.zero_mod, add_pos_iff, Order.lt_add_one_iff, zero_le, or_self, zero_tsub];
      · constructor <;> intro h <;> rcases r with ⟨ _ | r, hr ⟩ <;> norm_num at *;
        · tauto;
        · rcases em (μ.isLeftStep ⟨r, by linarith⟩) with h' | h' <;>
            simp_all +decide only [forall_const, not_true_eq_false, IsEmpty.forall_iff, and_true,
              Fin.ext_iff, Fin.val_succ, Nat.add_right_cancel_iff, Fin.val_castSucc,
              not_false_eq_true, true_and];
          · exact Or.inl ⟨fun k hk => by convert h' using 1; aesop,
                fun k hk => by convert h using 1; aesop⟩;
          · exact Or.inr ⟨ fun k hk => by convert h' using 2; exact Fin.ext hk,
                fun k hk => by convert h using 2; exact Fin.ext hk ⟩;
        · cases h <;> simp_all +decide [ Fin.ext_iff ];
      · simp_all +decide [ Fin.ext_iff ];
        grind +ring;
      · exact em _

end

lemma nondiag_mem_insertLeft_or_insertRight {p q : ℕ}
    (μ : Shuffle (p + 1) (q + 1)) (r : Index ((p + 1) + (q + 1)))
    (hr : ¬isDiagonalVertex μ r) :
    (∃ (j : Fin (p + 2)) (ν : Shuffle p (q + 1)),
      μ = insertLeftStep ν j ∧ (insertLeftIndex ν j).val = r.val) ∨
    (∃ (k : Fin (q + 2)) (ν : Shuffle (p + 1) q),
      μ = insertRightStep ν k ∧ (insertRightIndex ν k).val = r.val) := by
  -- By definition of diagonal vertex, if r is not diagonal, then it must be either left or right.
  have h_cases : isLeftVertex μ r ∨ isRightVertex μ r := by
    simpa [Fin.cast] using
      (not_diagonal_iff_left_or_right
        (μ := μ) (r := (⟨r.val, by omega⟩ : Fin (p + q + 3)))).mp
        (by simpa [Fin.cast] using hr)
  obtain h | h := h_cases <;> [left; right]
  · -- Left vertex case
    let rFin : Fin (p + (q + 1) + 2) := ⟨r.val, by omega⟩
    have hr_eq : (rFin.cast (by omega) : Index ((p + 1) + (q + 1))) = r := Fin.ext rfl
    have h' : isLeftVertex μ (rFin.cast (by omega)) := hr_eq ▸ h
    refine ⟨(μ.1 (rFin.cast (by omega))).1, removeLeft μ rFin h',
      (insertLeft_removeLeft h').symm, ?_⟩
    simpa [hr_eq] using congrArg Fin.val (insertIndex_removeLeft h')
  · -- Right vertex case
    let rFin : Fin ((p + 1) + q + 2) := ⟨r.val, by omega⟩
    have hr_eq : (rFin.cast (by omega) : Index ((p + 1) + (q + 1))) = r := Fin.ext rfl
    have h' : isRightVertex μ (rFin.cast (by omega)) := hr_eq ▸ h
    refine ⟨(μ.1 (rFin.cast (by omega))).2, removeRight μ rFin h', ?_, ?_⟩
    · have h_swap := removeRight_eq_swap_removeLeft μ rFin h'
      have h_ins := insertRightStep_eq_swap (removeRight μ rFin h')
        (μ.1 (rFin.cast (by omega))).2
      apply (swapEquiv (p + 1) (q + 1)).injective
      change μ.swap = ((μ.removeRight rFin h').insertRightStep
        (μ.1 (rFin.cast (by omega))).2).swap
      rw [h_ins, h_swap, swap_swap]
      let rFin' : Fin (q + (p + 1) + 2) := rFin.cast (by omega)
      have hL : isLeftVertex μ.swap (rFin'.cast (by omega)) := by
        have := isRightVertex_swap (μ := μ) (r := rFin.cast (by omega)) |>.mp h'
        convert this using 1
        exact Fin.ext rfl
      have hIL := insertLeft_removeLeft (μ := μ.swap) (r := rFin') hL
      convert hIL.symm using 2
      rfl
    · simpa [hr_eq] using congrArg Fin.val (insertIndex_removeRight h')

/-- Left insertion produces a left-type vertex: the step at (or just before)
the inserted vertex is a left step.  Here `isLeftType` checks `isLeftStep`
at index `min r.val ((p+1)+(q)-1)`. -/
lemma insertLeftStep_isLeftType {p q : ℕ}
    (ν : Shuffle p (q)) (j : Fin (p + 2)) :
    isLeftStep (insertLeftStep ν j)
      ⟨min (insertLeftIndex ν j).val ((p + 1) + (q) - 1), by omega⟩ := by
  cases min_cases ( ν.insertLeftIndex j : ℕ ) ( p + 1 + ( q ) - 1
      ) <;> simp_all +decide only [Nat.succ_add_sub_one, inf_eq_left, and_self, isLeftStep,
      inf_of_le_left, Fin.castSucc_mk, Fin.succ_mk, Fin.val_fin_lt, inf_eq_right, inf_of_le_right];
  · have := insertLeftStep_isLeftStep_at ν j ( by omega ); aesop;
  · -- Since the first component of the last element is (insertLeftIndex ν j).val, which is j.val +
    -- (q ), and the second component is 0, the pair (j, 0) is indeed the last element.
    have h_last : (insertLeftIndex ν j).val = j.val + (q) := by
      have h_last : (insertLeftIndex ν j).val ≤ j.val + (q) := by
        apply_rules [ insertLeftIndex_le ]
      generalize_proofs at *; (
      linarith [ Fin.is_lt j ])
    generalize_proofs at *;
    norm_num [ show ( ( ν.insertLeftStep j ) : Fin ( p + 1 + ( q ) + 1 ) → Index ( p + 1 ) × Index
        ( q  ) ) = insertLeftStepFun ν j from rfl, insertLeftStepFun ] at *;
    split_ifs <;> simp_all +decide [ Fin.succAbove ];
    · grind;
    · split_ifs <;> norm_num [ Fin.lt_def ] at * <;> omega;
    · omega

/-- Right insertion produces a non-left-type vertex: the step at (or just before)
the inserted vertex is a right step, not a left step. -/
lemma insertRightStep_not_isLeftType {p q : ℕ}
    (ν : Shuffle (p) q) (k : Fin (q + 2)) :
    ¬isLeftStep (insertRightStep ν k)
      ⟨min (insertRightIndex ν k).val ((p) + (q + 1) - 1), by omega⟩ := by
  intro h_left_step
  generalize_proofs at *;
  unfold isLeftStep at h_left_step;
  simp +decide only [insertRightStep, Nat.add_succ_sub_one, Fin.castSucc_mk, OrderHom.coe_mk,
      Fin.succ_mk, Fin.val_fin_lt] at h_left_step ⊢;
  unfold insertRightStepFun at h_left_step; simp +decide only [min_lt_iff, lt_self_iff_false,
      false_or, inf_eq_left, add_tsub_cancel_right] at h_left_step ⊢;
  split_ifs at h_left_step <;> try linarith [ Fin.is_lt ( ν.insertRightIndex k ) ] ;
  any_goals omega;
  · have := ν.1.monotone ( show ⟨ Min.min ( ν.insertRightIndex k : ℕ ) ( p + q ),
        by omega ⟩ ≤ ⟨ p + q, by omega ⟩ from Nat.min_le_right _ _
        ); simp_all +decide only [lt_self_iff_false, not_false_eq_true];
    have h_last : ν.1 ⟨p + q, by omega⟩ = (Fin.last (p), Fin.last q) := by
      exact Shuffle.apply_last ν
    generalize_proofs at *; simp_all +decide only [Nat.add_succ_sub_one, min_lt_iff,
        add_lt_add_iff_left, lt_add_iff_pos_right, or_true];
    simp_all +decide only [min_eq_right (by linarith : p + q ≤ (ν.insertRightIndex k : ℕ)),
        Std.le_refl];
    exact h_left_step.not_ge ( Nat.le_of_lt_succ <| by simp +arith +decide [ *] );
  · cases min_cases ( ν.insertRightIndex k : ℕ ) ( p + q ) <;> simp_all +decide [ Fin.lt_def ];
    have := insertRightIndex_iff ν k ⟨ ( ν.insertRightIndex k : ℕ ),
        by omega ⟩; simp_all +decide [];
    have := coordSum_eq ν ⟨ ( ν.insertRightIndex k : ℕ ), by omega ⟩; simp_all +decide []; omega;



end Shuffle

end D5.S3.HomologicalAlgebra.EilenbergZilber
