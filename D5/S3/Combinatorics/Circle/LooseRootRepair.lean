/- GID: D5/S3/Combinatorics/Circle/LooseRootRepair
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/LooseRootRepair
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.Finset.Basic, mathlib/module/Mathlib.Algebra.Order.BigOperators.Group.Finset]
   utility: none
   digest: A labelled finite mesh constructs a local physical two-root repair with a legal first slot. -/
module
public import D5.S3.Combinatorics.Circle.SourceWidth
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Local physical repair of a root-only cut

Only the first of two slots is made legal. All inventories consist of physical
labels, so equal weights never identify different occurrences. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.LooseRootRepair
open SourceWidth

/-- Add actual labels one at a time to a single virtual increment. -/
private theorem labelled_mesh {α : Type*} [DecidableEq α]
    (f : α → ℤ) (Y : Finset α) {δ c M : ℤ}
    (hδ : 0 < δ) (hδc : δ ≤ c) (hM : M ≤ δ + c)
    (hf : ∀ j ∈ Y, 0 < f j ∧ f j ≤ M)
    (U : ℤ) (hU : 0 ≤ U) (hUT : U < δ + ∑ j ∈ Y, f j) :
    ∃ A ⊆ Y, ∃ e : Bool,
      (∑ j ∈ A, f j) + (if e then δ else 0) ≤ U ∧
      U - ((∑ j ∈ A, f j) + (if e then δ else 0)) < c := by
  induction Y using Finset.induction_on generalizing U with
  | empty =>
    refine ⟨∅, Finset.empty_subset _, false, ?_, ?_⟩ <;> simp_all <;> omega
  | @insert j Y hj ih =>
    have hjf := hf j (Finset.mem_insert_self j Y)
    have hYf : ∀ x ∈ Y, 0 < f x ∧ f x ≤ M :=
      fun x hx => hf x (Finset.mem_insert_of_mem hx)
    have hsum : 0 ≤ ∑ x ∈ Y, f x :=
      Finset.sum_nonneg (fun x hx => le_of_lt (hYf x hx).1)
    rw [Finset.sum_insert hj] at hUT
    by_cases hlow : U < δ + ∑ x ∈ Y, f x
    · obtain ⟨A, hA, e, hz, hgap⟩ := ih hYf U hU hlow
      exact ⟨A, hA.trans (Finset.subset_insert j Y), e, hz, hgap⟩
    · by_cases hw : f j ≤ U
      · obtain ⟨A, hA, e, hz, hgap⟩ := ih hYf (U - f j) (by omega) (by omega)
        have hjA : j ∉ A := fun ha => hj (hA ha)
        refine ⟨insert j A, Finset.insert_subset_insert j hA, e, ?_, ?_⟩ <;>
          rw [Finset.sum_insert hjA] <;> omega
      · refine ⟨Y, Finset.subset_insert j Y, true, ?_, ?_⟩ <;> simp only [Bool.true_eq, ↓reduceIte]
        · omega
        · omega

private theorem inStrip_positive {α : Type*} {f : α → ℤ} {C h : ℤ}
    {l : List α} (hf : ∀ x ∈ l, 0 < f x)
    (hh : 0 ≤ h) (hend : h + (l.map f).sum ≤ C) : InStrip f C h l := by
  induction l generalizing h with
  | nil => simpa [InStrip] using And.intro hh hend
  | cons x xs ih =>
    have hx := hf x (by simp)
    have hxs : ∀ y ∈ xs, 0 < f y := fun y hy => hf y (by simp [hy])
    have hs : 0 ≤ (xs.map f).sum := List.sum_nonneg (by
      simpa using fun y hy => le_of_lt (hxs y hy))
    simp only [List.map_cons, List.sum_cons] at hend
    exact ⟨hh, by omega, ih hxs (by omega) (by omega)⟩

private theorem partition_inventory {α : Type*} [DecidableEq α]
    (Y A : Finset α) (hA : A ⊆ Y) :
    (A.toList ++ (Y \ A).toList).Perm Y.toList := by
  have hd : List.Disjoint A.toList (Y \ A).toList := by
    apply List.disjoint_left.mpr
    intro x hx hx'
    simp only [Finset.mem_toList, Finset.mem_sdiff] at hx hx'
    exact hx'.2 hx
  apply (List.perm_ext_iff_of_nodup
    (List.nodup_append.mpr ⟨Finset.nodup_toList _, Finset.nodup_toList _, hd⟩)
    (Finset.nodup_toList _)).mpr
  intro x
  simp only [List.mem_append, Finset.mem_toList, Finset.mem_sdiff]
  constructor
  · rintro (hx | hx)
    · exact hA hx
    · exact hx.1
  · intro hx
    by_cases ha : x ∈ A
    · exact Or.inl ha
    · exact Or.inr ⟨hx, ha⟩

private theorem physical_repair {α : Type*} [DecidableEq α]
    (f : α → ℤ) (Y : Finset α) (r s n m : α) (C B h b δ M : ℤ)
    (hlabels : (r :: s :: n :: m :: Y.toList).Nodup)
    (hr : f r = b + δ) (hs : f s = b) (hn : f n = -B)
    (hb : 0 < b) (hB : 0 < B) (hh : 0 ≤ h)
    (hδ : 0 < δ) (hδc : δ ≤ C - B) (hM : M ≤ δ + (C - B))
    (hf : ∀ x ∈ Y, 0 < f x ∧ f x ≤ M)
    (hU : 0 ≤ C - h - b) (hUT : C - h - b < δ + ∑ x ∈ Y, f x) :
    ∃ P Q : List α,
      (P ++ Q).Perm (r :: s :: Y.toList) ∧
      (P ++ Q).Nodup ∧ List.Disjoint P Q ∧
      P.toFinset ∪ Q.toFinset = insert r (insert s Y) ∧
      ((P.head? = some r ∧ Q.head? = some s) ∨
        (P.head? = some s ∧ Q.head? = some r)) ∧
      (∀ x ∈ P ++ Q, 0 < f x) ∧
      InStrip f C h (P ++ [n]) ∧
      (0 ≤ h + (P.map f).sum - B ∧ h + (P.map f).sum - B ≤ C - B) ∧
      (P.map f).sum + (Q.map f).sum = f r + f s + ∑ x ∈ Y, f x ∧
      ((P ++ [n]) ++ (Q ++ [m])).Perm ((r :: s :: Y.toList) ++ [n, m]) ∧
      h + (((P ++ [n]) ++ (Q ++ [m])).map f).sum =
        h + f r + f s + (∑ x ∈ Y, f x) + f n + f m := by
  obtain ⟨A, hA, e, hz, hgap⟩ := labelled_mesh f Y hδ hδc hM hf
    (C - h - b) hU hUT
  let a := if e then r else s
  let d := if e then s else r
  let P := a :: A.toList
  let Q := d :: (Y \ A).toList
  have hsplit := partition_inventory Y A hA
  have hp : (P ++ Q).Perm (r :: s :: Y.toList) := by
    have hm : (P ++ Q).Perm (a :: d :: (A.toList ++ (Y \ A).toList)) :=
      List.perm_middle.cons a
    have ht := hm.trans ((hsplit.cons d).cons a)
    cases e with
    | false => exact ht.trans (List.Perm.swap s r _)
    | true => exact ht
  have hbase : (r :: s :: Y.toList).Nodup := by
    have hsub : (r :: s :: Y.toList).Sublist (r :: s :: n :: m :: Y.toList) := by
      exact (List.Sublist.cons n (List.Sublist.cons m (.refl _))).cons₂ s |>.cons₂ r
    exact hsub.nodup hlabels
  have hnodup := hp.nodup_iff.mpr hbase
  have hdisjoint := (List.nodup_append.mp hnodup).2.2
  have hunion := hp.toFinset_eq
  simp only [List.toFinset_append, List.toFinset_cons, Finset.toFinset_toList] at hunion
  have hpositive : ∀ x ∈ P ++ Q, 0 < f x := by
    intro x hx
    have hx' := hp.mem_iff.mp hx
    simp only [List.mem_cons, Finset.mem_toList] at hx'
    rcases hx' with rfl | rfl | hx'
    · omega
    · omega
    · exact (hf x hx').1
  have hPpos : ∀ x ∈ P, 0 < f x := fun x hx => hpositive x (by simp [hx])
  have hP0 : 0 ≤ (P.map f).sum := List.sum_nonneg (by
    simpa using fun x hx => le_of_lt (hPpos x hx))
  have hmassP : (P.map f).sum = b +
      ((∑ x ∈ A, f x) + (if e then δ else 0)) := by
    cases e <;> simp [P, a, hr, hs, Finset.sum_toList] <;> ring
  have hpeak : h + (P.map f).sum ≤ C := by omega
  have hland : 0 ≤ h + (P.map f).sum - B ∧
      h + (P.map f).sum - B ≤ C - B := by omega
  have hstrip : InStrip f C h (P ++ [n]) := by
    apply inStrip_append (inStrip_positive hPpos hh hpeak)
    simp only [InStrip, hn]
    omega
  have hmass := (hp.map f).sum_eq
  simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons,
    Finset.sum_toList] at hmass
  have hword : ((P ++ [n]) ++ (Q ++ [m])).Perm ((r :: s :: Y.toList) ++ [n, m]) := by
    have hmove : ((P ++ [n]) ++ (Q ++ [m])).Perm ((P ++ Q) ++ [n, m]) := by
      simpa only [List.append_assoc] using
        (((List.perm_append_comm : ([n] ++ Q).Perm (Q ++ [n])).append_left P).append_right [m])
    exact hmove.trans (hp.append_right [n, m])
  refine ⟨P, Q, hp, hnodup, hdisjoint, hunion, ?_, hpositive, hstrip, hland,
    hmass, hword, ?_⟩
  · cases e <;> simp [P, Q, a, d]
  · have he := (hword.map f).sum_eq
    simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      List.map_nil, List.sum_nil, Finset.sum_toList] at he
    omega

/-- Source-local root geometry supplies the mesh gaps, without a subset or
partition witness. The strict previous-root premise excludes the constant
root-only orbit. The next slot is not asserted to be legal. -/
theorem source_cut_root_repair {α : Type*} [DecidableEq α]
    (f : α → ℤ) (Y : Finset α) (r s n m : α) (N Q C p B M h : ℤ)
    (hlabels : (r :: s :: n :: m :: Y.toList).Nodup)
    (hQ : 1 ≤ Q) (hN : N = 4 * Q - 1) (hC : C = (N - 1) / 2)
    (hB : B = N - 2 * p) (hp : Q ≤ p) (hpR : p ≤ f r)
    (hR : 3 * f r ≤ N) (hsQ : Q ≤ f s)
    (hs : f s = 4 * p - N) (hstrict : f s < p)
    (hn : f n = -B) (hm : f m < 0)
    (hf : ∀ x ∈ Y, 0 < f x ∧ f x ≤ M) (hsmall : 2 * M ≤ B)
    (hh : 0 ≤ h) (hbudget : h + f s ≤ C)
    (hover : C < h + f r + ∑ x ∈ Y, f x) :
    ∃ P Q' : List α,
      (P ++ Q').Perm (r :: s :: Y.toList) ∧
      (P ++ Q').Nodup ∧ List.Disjoint P Q' ∧
      P.toFinset ∪ Q'.toFinset = insert r (insert s Y) ∧
      ((P.head? = some r ∧ Q'.head? = some s) ∨
        (P.head? = some s ∧ Q'.head? = some r)) ∧
      (∀ x ∈ P ++ Q', 0 < f x) ∧
      InStrip f C h (P ++ [n]) ∧
      (0 ≤ h + (P.map f).sum - B ∧ h + (P.map f).sum - B ≤ C - B) ∧
      (P.map f).sum + (Q'.map f).sum = f r + f s + ∑ x ∈ Y, f x ∧
      ((P ++ [n]) ++ (Q' ++ [m])).Perm ((r :: s :: Y.toList) ++ [n, m]) ∧
      h + (((P ++ [n]) ++ (Q' ++ [m])).map f).sum =
        h + f r + f s + (∑ x ∈ Y, f x) + f n + f m := by
  have hhalf : C = 2 * Q - 1 := by omega
  have hδ : 0 < f r - f s := by omega
  have hδc : f r - f s ≤ C - B := by omega
  have hgap : M ≤ f r - f s + (C - B) := by omega
  exact physical_repair f Y r s n m C B h (f s) (f r - f s) M hlabels
    (by omega) rfl hn (by omega) (by omega) hh hδ hδc hgap hf (by omega) (by omega)

end D5.S3.Combinatorics.Circle.LooseRootRepair
