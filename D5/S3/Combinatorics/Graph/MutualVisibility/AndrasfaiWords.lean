/- GID: D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiWords
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiWords
   mirror-E: none(waiver:no-computational-evidence)
   anchors: []
   utility: none
   digest: Canonical membership words identify visibility with full periodic factor avoidance. -/

import D5.S3.Combinatorics.Graph.MutualVisibility.Andrasfai
import D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiLanguage
import Mathlib.Data.List.OfFn

/-! Labelled subset encoding and the cyclic boundary bridge. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiWords

open Andrasfai AndrasfaiLanguage

private instance modulus_neZero (m : ℕ) : NeZero (3 * m + 2) := ⟨by omega⟩

/-- Labels retain the original vertex names and the fixed origin. -/
def membershipLabels (m : ℕ) (X : Finset (Vertex m)) (i : Fin (3 * m + 2)) : Bool :=
  decide ((i.val : Vertex m) ∈ X)

/-- The finite word lists the actual subset membership in increasing representative order. -/
def membershipWord (m : ℕ) (X : Finset (Vertex m)) : List Bool :=
  List.ofFn (membershipLabels m X)

/-- Recover an actual vertex subset from its Boolean labels. -/
def subsetOfLabels (m : ℕ) (b : Fin (3 * m + 2) → Bool) : Finset (Vertex m) :=
  Finset.univ.filter (fun v => b ⟨v.val, ZMod.val_lt v⟩ = true)

private theorem subset_labels_inverse (m : ℕ) (X : Finset (Vertex m)) :
    subsetOfLabels m (membershipLabels m X) = X := by
  ext v
  simp [subsetOfLabels, membershipLabels]

private theorem labels_subset_inverse (m : ℕ) (b : Fin (3 * m + 2) → Bool) :
    membershipLabels m (subsetOfLabels m b) = b := by
  funext i
  simp [membershipLabels, subsetOfLabels, ZMod.val_natCast_of_lt i.isLt]

/-- A labelled subset and its full Boolean membership function are equivalent. -/
def subsetLabelsEquiv (m : ℕ) : Finset (Vertex m) ≃ (Fin (3 * m + 2) → Bool) where
  toFun := membershipLabels m
  invFun := subsetOfLabels m
  left_inv := subset_labels_inverse m
  right_inv := labels_subset_inverse m

/-- The membership word has the full original host order. -/
theorem membership_word_length (m : ℕ) (X : Finset (Vertex m)) :
    (membershipWord m X).length = 3 * m + 2 := by
  simp [membershipWord]

private theorem periodic_avoidance_replicate (w : List Bool) :
    PeriodicAvoidance w ↔ ∀ r, ¬ ContainsForbidden ((List.replicate r w).flatten) := by
  unfold PeriodicAvoidance
  apply forall_congr'
  intro r
  apply not_congr
  apply Iff.of_eq
  apply congrArg ContainsForbidden
  induction r with
  | zero => rfl
  | succ r ih =>
    change _ ++ w = _
    rw [List.replicate_succ', List.flatten_append, ih]
    simp

private def block (f : ℕ → Bool) (a n : ℕ) : List Bool :=
  List.ofFn (fun i : Fin n => f (a + i.val))

private theorem repeated_word (m : ℕ) (X : Finset (Vertex m)) (r : ℕ) :
    (List.replicate r (membershipWord m X)).flatten =
      block (fun i => decide ((i : Vertex m) ∈ X)) 0 (r * (membershipWord m X).length) := by
  rw [membership_word_length]
  simp only [block, zero_add]
  rw [membershipWord, ← List.ofFn_fin_repeat]
  congr 1
  funext i
  simp [Fin.repeat, Fin.modNat, membershipLabels, ZMod.natCast_mod]


private theorem block_append (f : ℕ → Bool) (a n l : ℕ) :
    block f a (n + l) = block f a n ++ block f (a + n) l := by
  simp [block, List.ofFn_add, Nat.add_assoc]

private theorem block_three (f : ℕ → Bool) (a : ℕ) :
    block f a 3 = [f a, f (a + 1), f (a + 2)] := by
  rfl

private theorem triples_block (f : ℕ → Bool) (a r : ℕ) :
    (∀ j < r, f (a + 3*j + 2) = true) → Triples (block f a (3*r)) := by
  induction r with
  | zero => intro _; exact Triples.nil
  | succ r ih =>
    intro h
    rw [show 3*(r+1) = 3*r+3 by omega, block_append, block_three]
    have hh := h r (by omega)
    rw [hh]
    exact Triples.snoc (ih (fun j hj => h j (by omega))) _ _

private theorem triples_positions {t : List Bool} (ht : Triples t) :
    ∃ r, t.length = 3*r ∧ ∀ j < r, t[3*j+2]? = some true := by
  induction ht with
  | nil => exact ⟨0, rfl, by omega⟩
  | @snoc t ht a b ih =>
    obtain ⟨r, hl, hp⟩ := ih
    refine ⟨r+1, by simp [hl]; omega, ?_⟩
    intro j hj
    by_cases hjr : j < r
    · rw [List.getElem?_append_left (by omega)]
      exact hp j hjr
    · have hj' : j = r := by omega
      subst j
      rw [List.getElem?_append_right (by omega), hl]
      simp [show 3*r+2-3*r = 2 by omega]

private theorem forbidden_block_iff (f : ℕ → Bool) (n : ℕ) :
    ContainsForbidden (block f 0 n) ↔
      ∃ a k, 1 ≤ k ∧ a + 3*k ≤ n ∧ f a = true ∧
        f (a + 3*k - 1) = true ∧ ∀ j < k, f (a + 1 + 3*j) = true := by
  constructor
  · rintro ⟨p, t, s, ht, he⟩
    obtain ⟨r, hl, hp⟩ := triples_positions ht
    have hlen := congrArg List.length he
    simp only [block, List.length_ofFn, List.length_append, List.length_cons,
      List.length_nil] at hlen
    have hget (i : ℕ) (hi : i < n) :
        (p ++ [true,true] ++ t ++ [true] ++ s)[i]? = some (f i) := by
      rw [← he]
      simp [block, hi]
    have hfirst := hget p.length (by omega)
    have hend := hget (p.length + 3*(r+1)-1) (by omega)
    have hleft : f p.length = true := by
      simp only [List.append_assoc] at hfirst
      rw [List.getElem?_append_right (by omega)] at hfirst
      simpa using hfirst.symm
    have hright : f (p.length + 3*(r+1)-1) = true := by
      rw [List.getElem?_append_left (by simp; omega),
        List.getElem?_append_right (by simp; omega)] at hend
      simpa [hl, show p.length + 3*(r+1)-1-(p.length+(3*r+1+1)) = 0 by omega] using hend.symm
    refine ⟨p.length, r+1, by omega, by omega, hleft, hright, ?_⟩
    intro j hj
    have hpos := hget (p.length + 1 + 3*j) (by omega)
    by_cases hj0 : j = 0
    · subst j
      simp only [List.append_assoc] at hpos
      rw [List.getElem?_append_right (by omega)] at hpos
      simpa using hpos.symm
    · have hjr : j-1 < r := by omega
      have hpt := hp (j-1) hjr
      rw [List.getElem?_append_left (by simp; omega),
        List.getElem?_append_left (by simp; omega),
        List.getElem?_append_right (by simp; omega)] at hpos
      have hind : p.length+1+3*j-(p.length+2) = 3*(j-1)+2 := by omega
      simp only [List.length_append, List.length_cons, List.length_nil] at hpos
      rw [hind, hpt] at hpos
      exact Option.some.inj hpos.symm
  · rintro ⟨a, k, hk, hbound, ha, hz, hall⟩
    let r := k-1
    have hkr : k = r+1 := by dsimp [r]; omega
    have htr : Triples (block f (a+2) (3*r)) := by
      apply triples_block
      intro j hj
      have hh := hall (j+1) (by omega)
      convert hh using 1
      congr 1
      omega
    have htotal : n = a + (2 + (3*r + (1 + (n-(a+3*k))))) := by omega
    refine ⟨block f 0 a, block f (a+2) (3*r),
      block f (a+3*k) (n-(a+3*k)), htr, ?_⟩
    conv_lhs => rw [htotal]
    simp only [block_append, zero_add]
    have hdouble : block f a 2 = [true,true] := by
      change [f a, f (a+1)] = _
      have hh := hall 0 hk
      simp only [Nat.mul_zero, Nat.add_zero] at hh
      rw [ha, hh]
    have hone : block f (a+2+3*r) 1 = [true] := by
      change [f (a+2+3*r)] = _
      rw [show a+2+3*r = a+3*k-1 by omega, hz]
    rw [hdouble, hone]
    simp only [List.append_assoc, show a+2+3*r+1 = a+3*k by omega]


private theorem factor_to_repetition (m : ℕ) (X : Finset (Vertex m))
    (u : Vertex m) (k : ℕ) (hf : ForbiddenFactor m X u k) :
    ∃ r, ContainsForbidden ((List.replicate r (membershipWord m X)).flatten) := by
  let f : ℕ → Bool := fun i => decide ((i : Vertex m) ∈ X)
  let a := u.val
  let r := a + 3*k
  have hk := hf.1
  have hbound : a + 3*k ≤ r*(3 * m + 2) := by
    dsimp [r]
    exact Nat.le_mul_of_pos_right _ (by omega)
  refine ⟨r, ?_⟩
  rw [repeated_word, membership_word_length]
  change ContainsForbidden (block f 0 (r*(3 * m + 2)))
  apply (forbidden_block_iff f _).mpr
  refine ⟨a, k, hf.1, hbound, ?_, ?_, ?_⟩
  · simpa [f, a] using hf.2.1
  · have he : a+3*k-1 = a+(3*k-1) := by omega
    simpa [f, he, Nat.cast_add, a] using hf.2.2.1
  · intro j hj
    have he : a+1+3*j = a+(1+3*j) := by omega
    simpa [f, he, Nat.cast_add, a] using hf.2.2.2 j hj

private theorem repetition_to_factor (m : ℕ) (X : Finset (Vertex m)) (r : ℕ)
    (hf : ContainsForbidden ((List.replicate r (membershipWord m X)).flatten)) :
    ∃ u k, ForbiddenFactor m X u k := by
  let f : ℕ → Bool := fun i => decide ((i : Vertex m) ∈ X)
  rw [repeated_word, membership_word_length] at hf
  change ContainsForbidden (block f 0 (r*(3 * m + 2))) at hf
  obtain ⟨a,k,hk,_,ha,hz,hall⟩ := (forbidden_block_iff f _).mp hf
  refine ⟨(a : Vertex m),k,hk,?_,?_,?_⟩
  · exact of_decide_eq_true ha
  · have he : a+3*k-1 = a+(3*k-1) := by omega
    simpa only [f, he, Nat.cast_add, decide_eq_true_eq] using hz
  · intro j hj
    have he : a+1+3*j = a+(1+3*j) := by omega
    simpa only [f, he, Nat.cast_add, decide_eq_true_eq] using hall j hj

/-- Actual original-host visibility is exactly avoidance in every finite
repetition of the canonical membership word, including every boundary crossing. -/
theorem visible_iff_word_periodic_avoidance (m : ℕ) (hm : 1 ≤ m)
    (X : Finset (Vertex m)) :
    Visible (host m) X ↔ PeriodicAvoidance (membershipWord m X) := by
  rw [visible_iff_periodic_avoidance m hm X, periodic_avoidance_replicate]
  constructor
  · intro hv r hr
    obtain ⟨u,k,hf⟩ := repetition_to_factor m X r hr
    exact hv u k hf
  · intro hp u k hf
    obtain ⟨r,hr⟩ := factor_to_repetition m X u k hf
    exact hp r hr


/-- The original graph of index one has exactly four visible labelled subsets. -/
theorem count_zero : count 0 = 4 := by
  classical
  have hv (X : Finset (Vertex 0)) : Visible (host 0) X := by
    apply (visible_iff_no_obstruction 0 X).mpr
    rintro ⟨u,k,hk,hkm,_⟩
    omega
  let e : Configuration (host 0) ≃ Finset (Vertex 0) :=
    { toFun := Subtype.val
      invFun := fun X => ⟨X, hv X⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  change Fintype.card (Configuration (host 0)) = 4
  rw [Fintype.card_congr e, Fintype.card_finset]
  norm_num [Vertex]

end D5.S3.Combinatorics.Graph.MutualVisibility.AndrasfaiWords
