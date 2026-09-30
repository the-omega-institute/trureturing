/- GID: D5/S3/Combinatorics/CardinalitySumAvoidingSubsets
   generality: I
   mirror-B: D5/B/S3/Combinatorics/CardinalitySumAvoidingSubsets
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The original cardinality-sum-avoiding subset count has the conjectured rational generating function. -/

/- The sequence counts subsets of [1,n] containing no two distinct elements whose
sum is their cardinality. Equal summands are allowed. The result is an identity
of formal power series over the rationals, including the empty-set case n=0.
-/

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
noncomputable section
open scoped BigOperators PowerSeries.WithPiTopology
open Polynomial PowerSeries

namespace D5.S3.Combinatorics.CardinalitySumAvoidingSubsets

private structure Code (n k : ℕ) where
  R : Finset ℕ
  L : Finset ℕ
  T : Finset ℕ
  hR : R ⊆ Finset.Icc 1 (k / 2)
  hL : L ⊆ R
  hmid : ∀ r ∈ R, 2 * r = k → r ∈ L
  hT : T ⊆ Finset.Icc k n
  hcard : R.card + T.card = k

private structure Lower (k : ℕ) where
  R : Finset ℕ
  L : Finset ℕ
  hR : R ⊆ Finset.Icc 1 (k / 2)
  hL : L ⊆ R
  hmid : ∀ r ∈ R, 2 * r = k → r ∈ L

def admissibleFamily (n : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (Finset.Icc 1 n).powerset.filter
    (fun S => ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x + y ≠ S.card)

def a (n : ℕ) : ℕ := (admissibleFamily n).card

set_option maxHeartbeats 3200000 in
-- The single proof contains the full pairing construction and series calculation.
/-- The generating-function identity for the original subset count. -/
theorem result :
    (1 - 2*PowerSeries.X + PowerSeries.X^2 - 2*PowerSeries.X^3 +
      PowerSeries.X^4 : PowerSeries ℚ) * PowerSeries.mk (fun n => (a n : ℚ)) =
      1 + PowerSeries.X^2 - PowerSeries.X^3 := by
  classical
  have lower_block_encoding
      (n k : ℕ) (S : Finset ℕ)
      (hS : S ⊆ Finset.Icc 1 n) (hcard : S.card = k)
      (hvalid : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x + y ≠ k) :
      let B := S.filter (fun x => x < k)
      let R := B.image (fun x => min x (k - x))
      R ⊆ Finset.Icc 1 (k / 2) ∧ R.card = B.card ∧
        B.card + (S.filter (fun x => k ≤ x)).card = k ∧
        B = (R ∩ S) ∪ ((R \ S).image (fun r => k - r)) ∧
        (∀ r ∈ R, r ≤ (k-1)/2 ∨ (k = 2*r ∧ r ∈ S)) := by
    dsimp
    have hinj : Set.InjOn (fun x => min x (k - x))
        (↑(S.filter (fun x => x < k)) : Set ℕ) := by
      intro x hx y hy heq
      dsimp at heq
      obtain ⟨hxS, hxk⟩ := Finset.mem_filter.mp hx
      obtain ⟨hyS, hyk⟩ := Finset.mem_filter.mp hy
      by_contra hne
      have hsum := hvalid x hxS y hyS hne
      rcases le_total x (k-x) with hxl | hxr <;>
        rcases le_total y (k-y) with hyl | hyr
      · rw [min_eq_left hxl, min_eq_left hyl] at heq
        exact hne heq
      · rw [min_eq_left hxl, min_eq_right hyr] at heq
        omega
      · rw [min_eq_right hxr, min_eq_left hyl] at heq
        omega
      · rw [min_eq_right hxr, min_eq_right hyr] at heq
        omega
    have hsub : (S.filter (fun x => x < k)).image (fun x => min x (k-x)) ⊆
        Finset.Icc 1 (k/2) := by
      intro r hr
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨hxS, hxk⟩ := Finset.mem_filter.mp hx
      have hxpos := (Finset.mem_Icc.mp (hS hxS)).1
      apply Finset.mem_Icc.mpr
      have ha := min_le_left x (k-x)
      have hb := min_le_right x (k-x)
      constructor
      · exact le_min hxpos (by omega)
      · omega
    have hc := Finset.card_image_iff.mpr hinj
    refine ⟨hsub, hc, ?_, ?_, ?_⟩
    · simpa [hcard] using (Finset.card_filter_add_card_filter_not (s := S) (fun x => x < k))
  
    · ext x
      constructor
      · intro hx
        obtain ⟨hxS, hxk⟩ := Finset.mem_filter.mp hx
        have hr : min x (k-x) ∈ (S.filter (fun x => x < k)).image
            (fun x => min x (k-x)) := Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hxS,hxk⟩, rfl⟩
        by_cases hlo : x ≤ k-x
        · apply Finset.mem_union_left
          apply Finset.mem_inter.mpr
          exact ⟨by simpa [min_eq_left hlo] using hr, hxS⟩
        · have hhi : k-x ≤ x := by omega
          apply Finset.mem_union_right
          apply Finset.mem_image.mpr
          refine ⟨k-x, Finset.mem_sdiff.mpr ⟨?_, ?_⟩, ?_⟩
          · simpa [min_eq_right hhi] using hr
          · intro hp
            have hn : x ≠ k-x := by omega
            have := hvalid x hxS (k-x) hp hn
            omega
          · omega
      · intro hx
        rcases Finset.mem_union.mp hx with hx | hx
        · obtain ⟨hr, hxS⟩ := Finset.mem_inter.mp hx
          have hb := Finset.mem_Icc.mp (hsub hr)
          exact Finset.mem_filter.mpr ⟨hxS, by omega⟩
        · obtain ⟨r, hr, heq⟩ := Finset.mem_image.mp hx
          obtain ⟨hrR, hrS⟩ := Finset.mem_sdiff.mp hr
          obtain ⟨y, hy, hry⟩ := Finset.mem_image.mp hrR
          obtain ⟨hyS, hyk⟩ := Finset.mem_filter.mp hy
          have hne : r ≠ y := by intro h; exact hrS (h ▸ hyS)
          have hmin : min y (k-y) = k-y := by
            rcases le_total y (k-y) with hl | hr
            · rw [min_eq_left hl] at hry
              exact False.elim (hne hry.symm)
            · exact min_eq_right hr
          rw [hmin] at hry
          have hxy : x = y := by omega
          exact hxy ▸ Finset.mem_filter.mpr ⟨hyS, hyk⟩
  
    · intro r hr
      by_cases hp : r ≤ (k-1)/2
      · exact Or.inl hp
      · right
        have hb := Finset.mem_Icc.mp (hsub hr)
        have hk : k = 2*r := by omega
        refine ⟨hk, ?_⟩
        obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hr
        obtain ⟨hxS, hxk⟩ := Finset.mem_filter.mp hx
        have hxr : x = r := by
          rcases le_total x (k-x) with hl | hr
          · rw [min_eq_left hl] at he
            exact he
          · rw [min_eq_right hr] at he
            omega
        exact hxr ▸ hxS

  let decode {n k : ℕ} (c : Code n k) : Finset ℕ :=
    (c.L ∪ (c.R \ c.L).image (fun r => k - r)) ∪ c.T

  have lower_bounds {n k : ℕ} (c : Code n k) {r : ℕ} (hr : r ∈ c.L) :
      1 ≤ r ∧ 2 * r ≤ k := by
    have := Finset.mem_Icc.mp (c.hR (c.hL hr))
    omega

  have right_bounds {n k : ℕ} (c : Code n k) {r : ℕ}
      (hr : r ∈ c.R) (hn : r ∉ c.L) : 1 ≤ r ∧ 2 * r < k := by
    have := Finset.mem_Icc.mp (c.hR hr)
    have hm : 2 * r ≠ k := fun h => hn (c.hmid r hr h)
    omega

  have decode_subset {n k : ℕ} (c : Code n k) (hk : 1 ≤ k) (hkn : k ≤ n) :
      decode c ⊆ Finset.Icc 1 n := by
    intro x hx
    simp only [decode, Finset.mem_union, Finset.mem_image, Finset.mem_sdiff] at hx
    rcases hx with (hx | ⟨r, ⟨hr, hn⟩, rfl⟩) | hx
    · have := lower_bounds c hx
      exact Finset.mem_Icc.mpr (by omega)
    · have := right_bounds c hr hn
      exact Finset.mem_Icc.mpr (by omega)
    · have := Finset.mem_Icc.mp (c.hT hx)
      exact Finset.mem_Icc.mpr (by omega)

  have decode_card {n k : ℕ} (c : Code n k) : (decode c).card = k := by
    have hd : Disjoint c.L ((c.R \ c.L).image (fun r => k-r)) := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      obtain ⟨r, hr, he⟩ := Finset.mem_image.mp hy
      obtain ⟨hr, hn⟩ := Finset.mem_sdiff.mp hr
      have := lower_bounds c hx
      have := right_bounds c hr hn
      omega
    have ht : Disjoint (c.L ∪ (c.R \ c.L).image (fun r => k-r)) c.T := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      have hb := Finset.mem_Icc.mp (c.hT hy)
      rcases Finset.mem_union.mp hx with hx | hx
      · have := lower_bounds c hx
        omega
      · obtain ⟨r, hr, he⟩ := Finset.mem_image.mp hx
        obtain ⟨hr, hn⟩ := Finset.mem_sdiff.mp hr
        have := right_bounds c hr hn
        omega
    have hi : Set.InjOn (fun r => k-r) (↑(c.R \ c.L) : Set ℕ) := by
      intro r hr s hs he
      dsimp at he
      have hb := right_bounds c (Finset.mem_sdiff.mp hr).1 (Finset.mem_sdiff.mp hr).2
      have hc := right_bounds c (Finset.mem_sdiff.mp hs).1 (Finset.mem_sdiff.mp hs).2
      omega
    have htotal := c.hcard
    have hc := Finset.card_sdiff_add_card_eq_card c.hL
    dsimp [decode]
    rw [Finset.card_union_of_disjoint ht, Finset.card_union_of_disjoint hd,
      Finset.card_image_iff.mpr hi]
    omega

  have decode_valid {n k : ℕ} (c : Code n k) (hk : 1 ≤ k) :
      ∀ x ∈ decode c, ∀ y ∈ decode c, x ≠ y → x+y ≠ k := by
    intro x hx y hy hne heq
    simp only [decode, Finset.mem_union, Finset.mem_image, Finset.mem_sdiff] at hx hy
    rcases hx with (hx | ⟨r, ⟨hr, hn⟩, rfl⟩) | hx <;>
      rcases hy with (hy | ⟨s, ⟨hs, hm⟩, rfl⟩) | hy
    · have := lower_bounds c hx
      have := lower_bounds c hy
      omega
    · have := lower_bounds c hx
      have := right_bounds c hs hm
      have hxs : x = s := by omega
      exact hm (hxs ▸ hx)
    · have := lower_bounds c hx
      have := Finset.mem_Icc.mp (c.hT hy)
      omega
    · have := right_bounds c hr hn
      have := lower_bounds c hy
      have hyr : y = r := by omega
      exact hn (hyr ▸ hy)
    · have := right_bounds c hr hn
      have := right_bounds c hs hm
      omega
    · have := right_bounds c hr hn
      have := Finset.mem_Icc.mp (c.hT hy)
      omega
    · have := Finset.mem_Icc.mp (c.hT hx)
      have := lower_bounds c hy
      omega
    · have := Finset.mem_Icc.mp (c.hT hx)
      have := right_bounds c hs hm
      omega
    · have := Finset.mem_Icc.mp (c.hT hx)
      have := Finset.mem_Icc.mp (c.hT hy)
      omega

  have recover_L {n k : ℕ} (c : Code n k) (hk : 1 ≤ k) :
      (decode c).filter (fun x => 2*x ≤ k) = c.L := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, hb⟩
      simp only [decode, Finset.mem_union, Finset.mem_image, Finset.mem_sdiff] at hx
      rcases hx with (hx | ⟨r, ⟨hr, hn⟩, rfl⟩) | hx
      · exact hx
      · have := right_bounds c hr hn
        omega
      · have := Finset.mem_Icc.mp (c.hT hx)
        omega
    · intro hx
      exact ⟨Finset.mem_union_left _ (Finset.mem_union_left _ hx), (lower_bounds c hx).2⟩

  have recover_T {n k : ℕ} (c : Code n k) :
      (decode c).filter (fun x => k ≤ x) = c.T := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, hb⟩
      simp only [decode, Finset.mem_union, Finset.mem_image, Finset.mem_sdiff] at hx
      rcases hx with (hx | ⟨r, ⟨hr, hn⟩, rfl⟩) | hx
      · have := lower_bounds c hx
        omega
      · have := right_bounds c hr hn
        omega
      · exact hx
    · intro hx
      exact ⟨Finset.mem_union_right _ hx, (Finset.mem_Icc.mp (c.hT hx)).1⟩

  have recover_R {n k : ℕ} (c : Code n k) :
      ((decode c).filter (fun x => x < k)).image (fun x => min x (k-x)) = c.R := by
    ext r
    constructor
    · intro hr
      obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hr
      obtain ⟨hx, hxk⟩ := Finset.mem_filter.mp hx
      simp only [decode, Finset.mem_union, Finset.mem_image, Finset.mem_sdiff] at hx
      rcases hx with (hx | ⟨s, ⟨hs, hn⟩, rfl⟩) | hx
      · have hb := lower_bounds c hx
        have hmin : min x (k-x) = x := min_eq_left (by omega)
        rw [hmin] at he
        exact he ▸ c.hL hx
      · have hb := right_bounds c hs hn
        have hmin : min (k-s) (k-(k-s)) = s := by
          rw [min_eq_right (by omega)]
          omega
        rw [hmin] at he
        exact he ▸ hs
      · have := Finset.mem_Icc.mp (c.hT hx)
        omega
    · intro hr
      have hb := Finset.mem_Icc.mp (c.hR hr)
      by_cases hl : r ∈ c.L
      · apply Finset.mem_image.mpr
        refine ⟨r, Finset.mem_filter.mpr ⟨?_, by omega⟩, ?_⟩
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ hl)
        · exact min_eq_left (by omega)
      · have hs := right_bounds c hr hl
        apply Finset.mem_image.mpr
        refine ⟨k-r, Finset.mem_filter.mpr ⟨?_, by omega⟩, ?_⟩
        · apply Finset.mem_union_left
          apply Finset.mem_union_right
          exact Finset.mem_image.mpr ⟨r, Finset.mem_sdiff.mpr ⟨hr,hl⟩, rfl⟩
        · rw [min_eq_right (by omega)]
          omega

  let Selected (n k : ℕ) := { S : Finset ℕ // S ⊆ Finset.Icc 1 n ∧ S.card = k ∧
    ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x+y ≠ k }

  let encode (n k : ℕ) (s : Selected n k) : Code n k := by
    let S := s.val
    refine ⟨(S.filter (fun x => x < k)).image (fun x => min x (k-x)),
      S.filter (fun x => 2*x ≤ k), S.filter (fun x => k ≤ x), ?_, ?_, ?_, ?_, ?_⟩
    all_goals
      have facts := lower_block_encoding n k S s.property.1 s.property.2.1 s.property.2.2
      dsimp at facts
      obtain ⟨hR, hRc, htotal, hsplit, hm⟩ := facts
    · exact hR
    · intro x hx
      obtain ⟨hxS, hxlo⟩ := Finset.mem_filter.mp hx
      have hxpos := (Finset.mem_Icc.mp (s.property.1 hxS)).1
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hxS, by omega⟩,
        min_eq_left (by omega)⟩
    · intro r hr he
      have hrS : r ∈ S := by
        have hb := Finset.mem_Icc.mp (hR hr)
        rcases hm r hr with h | h
        · omega
        · exact h.2
      exact Finset.mem_filter.mpr ⟨hrS, by omega⟩
    · intro x hx
      obtain ⟨hxS, hxl⟩ := Finset.mem_filter.mp hx
      have hxu := (Finset.mem_Icc.mp (s.property.1 hxS)).2
      exact Finset.mem_Icc.mpr ⟨hxl, hxu⟩
    · rw [hRc]
      exact htotal

  have decode_encode (n k : ℕ) (s : Selected n k) : decode (encode n k s) = s.val := by
    let S := s.val
    obtain ⟨hR, hRc, htotal, hsplit, hm⟩ :=
      lower_block_encoding n k S s.property.1 s.property.2.1 s.property.2.2
    have hL : S.filter (fun x => 2*x ≤ k) =
        ((S.filter (fun x => x < k)).image (fun x => min x (k-x))) ∩ S := by
      ext x
      constructor
      · intro hx
        obtain ⟨hxS, hxlo⟩ := Finset.mem_filter.mp hx
        have hxpos := (Finset.mem_Icc.mp (s.property.1 hxS)).1
        exact Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨x,
          Finset.mem_filter.mpr ⟨hxS, by omega⟩, min_eq_left (by omega)⟩, hxS⟩
      · intro hx
        obtain ⟨hr, hxS⟩ := Finset.mem_inter.mp hx
        have := Finset.mem_Icc.mp (hR hr)
        exact Finset.mem_filter.mpr ⟨hxS, by omega⟩
    have hd : ((S.filter (fun x => x < k)).image (fun x => min x (k-x))) \
          (S.filter (fun x => 2*x ≤ k)) =
        ((S.filter (fun x => x < k)).image (fun x => min x (k-x))) \ S := by
      rw [hL]
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_inter]
      tauto
    change ((S.filter (fun x => 2*x ≤ k) ∪
      (((S.filter (fun x => x < k)).image (fun x => min x (k-x))) \
        S.filter (fun x => 2*x ≤ k)).image (fun r => k-r)) ∪
      S.filter (fun x => k ≤ x)) = S
    rw [hd, hL, ← hsplit]
    simpa using Finset.filter_union_filter_not_eq (fun x => x < k) S

  have encode_decode (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (c : Code n k) :
      encode n k ⟨decode c, decode_subset c hk hkn, decode_card c, decode_valid c hk⟩ = c := by
    have hR := recover_R c
    have hL := recover_L c hk
    have hT := recover_T c
    generalize he : encode n k ⟨decode c, decode_subset c hk hkn,
      decode_card c, decode_valid c hk⟩ = d
    have eR : d.R = c.R := by rw [← he]; exact hR
    have eL : d.L = c.L := by rw [← he]; exact hL
    have eT : d.T = c.T := by rw [← he]; exact hT
    cases d
    cases c
    dsimp at eR eL eT
    subst_vars
    rfl

  let pairingEquiv (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) : Selected n k ≃ Code n k := {
    toFun := encode n k
    invFun := fun c => ⟨decode c, decode_subset c hk hkn, decode_card c, decode_valid c hk⟩
    left_inv := fun s => Subtype.ext (decode_encode n k s)
    right_inv := encode_decode n k hk hkn
  }

  letI lowerFintype (k : ℕ) : Fintype (Lower k) := by
    classical
    let f : Lower k → (Finset.Icc 1 (k/2)).powerset × (Finset.Icc 1 (k/2)).powerset :=
      fun l => (⟨l.R, Finset.mem_powerset.mpr l.hR⟩,
        ⟨l.L, Finset.mem_powerset.mpr (l.hL.trans l.hR)⟩)
    apply Fintype.ofInjective f
    intro a b h
    have hR : a.R = b.R := congrArg (fun p => p.1.val) h
    have hL : a.L = b.L := congrArg (fun p => p.2.val) h
    cases a
    cases b
    dsimp at hR hL
    subst_vars
    rfl

  have lower_card_le (k : ℕ) (l : Lower k) : l.R.card ≤ k := by
    have h := Finset.card_le_card l.hR
    simp only [Nat.card_Icc] at h
    omega

  let tailFamily (n k : ℕ) (l : Lower k) : Finset (Finset ℕ) :=
    (Finset.Icc k n).powersetCard (k - l.R.card)

  let codeTailEquiv (n k : ℕ) : Code n k ≃ Σ l : Lower k, (tailFamily n k l) := {
    toFun c := ⟨⟨c.R, c.L, c.hR, c.hL, c.hmid⟩,
      ⟨c.T, Finset.mem_powersetCard.mpr ⟨c.hT, by change c.T.card = k - c.R.card; have := c.hcard; omega⟩⟩⟩
    invFun s := ⟨s.1.R, s.1.L, s.2.val, s.1.hR, s.1.hL, s.1.hmid,
      (Finset.mem_powersetCard.mp s.2.property).1, by
        have ht := (Finset.mem_powersetCard.mp s.2.property).2
        have hl := lower_card_le k s.1
        omega⟩
    left_inv c := by cases c; rfl
    right_inv s := by rcases s with ⟨l, t⟩; cases l; cases t; rfl
  }

  letI codeFintype (n k : ℕ) : Fintype (Code n k) :=
    Fintype.ofEquiv (Σ l : Lower k, (tailFamily n k l)) (codeTailEquiv n k).symm

  let selectedFintype (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
      Fintype (Selected n k) := Fintype.ofEquiv (Code n k) (pairingEquiv n k hk hkn).symm

  have selected_tail_count (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
      @Fintype.card (Selected n k) (selectedFintype n k hk hkn) =
        ∑ l : Lower k, Nat.choose (n-k+1) (k-l.R.card) := by
    classical
    letI := selectedFintype n k hk hkn
    rw [Fintype.card_congr (pairingEquiv n k hk hkn),
      Fintype.card_congr (codeTailEquiv n k), Fintype.card_sigma]
    apply Finset.sum_congr rfl
    intro l hl
    rw [Fintype.card_coe]
    simp only [tailFamily, Finset.card_powersetCard, Nat.card_Icc]
    congr 1
    omega

  let freeRepresentatives (k : ℕ) (R : Finset ℕ) : Finset ℕ :=
    R.filter (fun r => 2*r ≠ k)

  let forcedRepresentatives (k : ℕ) (R : Finset ℕ) : Finset ℕ :=
    R.filter (fun r => 2*r = k)

  let lowerFiberEquiv (k : ℕ) (R : Finset ℕ)
      (hR : R ⊆ Finset.Icc 1 (k/2)) :
      {l : Lower k // l.R = R} ≃ (freeRepresentatives k R).powerset := by
    classical
    refine {
      toFun := fun l => ⟨l.val.L.filter (fun r => 2*r ≠ k),
        Finset.mem_powerset.mpr (by
          intro r hr
          obtain ⟨hr, hm⟩ := Finset.mem_filter.mp hr
          exact Finset.mem_filter.mpr ⟨l.property ▸ l.val.hL hr, hm⟩)⟩
      invFun := fun u => ⟨⟨R, u.val ∪ forcedRepresentatives k R, hR,
        by
          intro r hr
          rcases Finset.mem_union.mp hr with hr | hr
          · exact (Finset.mem_filter.mp (Finset.mem_powerset.mp u.property hr)).1
          · exact (Finset.mem_filter.mp hr).1,
        by
          intro r hr hm
          exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hr, hm⟩)⟩, rfl⟩
      left_inv := ?_
      right_inv := ?_ }
    · intro l
      apply Subtype.ext
      have hL : l.val.L.filter (fun r => 2*r ≠ k) ∪ forcedRepresentatives k R = l.val.L := by
        ext r
        simp only [forcedRepresentatives, Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨hr, hm⟩ | ⟨hr, hm⟩)
          · exact hr
          · exact l.val.hmid r (l.property.symm ▸ hr) hm
        · intro hr
          by_cases hm : 2*r = k
          · exact Or.inr ⟨l.property ▸ l.val.hL hr, hm⟩
          · exact Or.inl ⟨hr, hm⟩
      rcases l with ⟨l, hl⟩
      cases l
      dsimp at hl hL ⊢
      subst_vars
      simp only [hL]
    · intro u
      apply Subtype.ext
      ext r
      have hu := Finset.mem_powerset.mp u.property
      simp only [Finset.mem_filter, Finset.mem_union, forcedRepresentatives]
      constructor
      · rintro ⟨hr | ⟨hr, hm⟩, hn⟩
        · exact hr
        · exact False.elim (hn hm)
      · intro hr
        exact ⟨Or.inl hr, (Finset.mem_filter.mp (hu hr)).2⟩

  have lower_fixed_R_count (k : ℕ) (R : Finset ℕ)
      (hR : R ⊆ Finset.Icc 1 (k/2)) :
      Fintype.card {l : Lower k // l.R = R} = 2 ^ (freeRepresentatives k R).card := by
    classical
    rw [Fintype.card_congr (lowerFiberEquiv k R hR), Fintype.card_coe,
      Finset.card_powerset]

  have forcedRepresentatives_card (k : ℕ) (R : Finset ℕ) :
      (forcedRepresentatives k R).card =
        if k % 2 = 0 ∧ k/2 ∈ R then 1 else 0 := by
    classical
    by_cases hm : k % 2 = 0 ∧ k/2 ∈ R
    · have hs : forcedRepresentatives k R = {k/2} := by
        ext r
        simp only [forcedRepresentatives, Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hr, he⟩
          omega
        · intro he
          subst r
          exact ⟨hm.2, by omega⟩
      simp [hs, hm]
    · have hs : forcedRepresentatives k R = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro r hr
        obtain ⟨hr, he⟩ := Finset.mem_filter.mp hr
        apply hm
        have h : r = k/2 := by omega
        exact ⟨by omega, h ▸ hr⟩
      simp [hs, hm]

  have lower_weighted_fiber_bridge (k : ℕ) :
      (∑ l : Lower k, (Polynomial.X : Polynomial ℕ) ^ l.R.card) =
        ∑ R ∈ (Finset.Icc 1 (k/2)).powerset,
          (2 : Polynomial ℕ) ^ (freeRepresentatives k R).card * Polynomial.X ^ R.card := by
    classical
    rw [← Finset.sum_fiberwise_of_maps_to
      (s := Finset.univ) (t := (Finset.Icc 1 (k/2)).powerset)
      (g := fun l : Lower k => l.R)
      (fun l hl => Finset.mem_powerset.mpr l.hR)]
    apply Finset.sum_congr rfl
    intro R hR
    have hc : ((Finset.univ : Finset (Lower k)).filter (fun l => l.R = R)).card =
        2 ^ (freeRepresentatives k R).card := by
      rw [← Fintype.card_subtype]
      exact lower_fixed_R_count k R (Finset.mem_powerset.mp hR)
    calc
      _ = ∑ l ∈ (Finset.univ : Finset (Lower k)).filter (fun l => l.R = R),
          (Polynomial.X : Polynomial ℕ) ^ R.card := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [(Finset.mem_filter.mp hl).2]
      _ = _ := by simp [hc, nsmul_eq_mul]

  have representative_weight_product (k : ℕ) (R : Finset ℕ) :
      (2 : Polynomial ℕ) ^ (freeRepresentatives k R).card * Polynomial.X ^ R.card =
        ∏ r ∈ R, (if 2*r = k then (Polynomial.X : Polynomial ℕ) else 2*Polynomial.X) := by
    classical
    have hc := Finset.card_filter_add_card_filter_not (s := R) (fun r => 2*r = k)
    rw [← Finset.prod_filter_mul_prod_filter_not R (fun r => 2*r = k)]
    have hp : (∏ r ∈ R.filter (fun r => 2*r = k),
        (if 2*r = k then (Polynomial.X : Polynomial ℕ) else 2*Polynomial.X)) = Polynomial.X ^ (R.filter (fun r => 2*r = k)).card := by
      rw [Finset.prod_eq_pow_card]
      intro r hr
      simp [(Finset.mem_filter.mp hr).2]
    have hn : (∏ r ∈ R.filter (fun r => ¬ 2*r = k),
        (if 2*r = k then (Polynomial.X : Polynomial ℕ) else 2*Polynomial.X)) =
        (2*Polynomial.X) ^ (freeRepresentatives k R).card := by
      change _ = (2*Polynomial.X) ^ (R.filter (fun r => ¬ 2*r = k)).card
      apply Finset.prod_eq_pow_card
      intro r hr
      simp [(Finset.mem_filter.mp hr).2]
    rw [hp, hn, mul_pow]
    change (R.filter (fun r => 2*r = k)).card + (freeRepresentatives k R).card = R.card at hc
    rw [← hc, pow_add]
    ring

  have lower_weighted_product_bridge (k : ℕ) :
      (∑ l : Lower k, (Polynomial.X : Polynomial ℕ) ^ l.R.card) =
        ∏ r ∈ Finset.Icc 1 (k/2), (1 + if 2*r = k then (Polynomial.X : Polynomial ℕ) else 2*Polynomial.X) := by
    rw [lower_weighted_fiber_bridge, Finset.prod_one_add]
    apply Finset.sum_congr rfl
    intro R hR
    exact representative_weight_product k R

  have lower_size_polynomial (k : ℕ) (hk : 1 ≤ k) :
      (∑ l : Lower k, (Polynomial.X : Polynomial ℕ) ^ l.R.card) =
        (1 + 2*Polynomial.X) ^ ((k-1)/2) * (1+Polynomial.X) ^ (if k % 2 = 0 then 1 else 0) := by
    classical
    rw [lower_weighted_product_bridge,
      ← Finset.prod_filter_not_mul_prod_filter (Finset.Icc 1 (k/2)) (fun r => 2*r = k)]
    have hn : (Finset.Icc 1 (k/2)).filter (fun r => ¬ 2*r = k) =
        Finset.Icc 1 ((k-1)/2) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    have hc : ((Finset.Icc 1 (k/2)).filter (fun r => 2*r = k)).card =
        if k % 2 = 0 then 1 else 0 := by
      have h := forcedRepresentatives_card k (Finset.Icc 1 (k/2))
      dsimp [forcedRepresentatives] at h
      rw [h]
      by_cases he : k % 2 = 0
      · have hm : k/2 ∈ Finset.Icc 1 (k/2) := Finset.mem_Icc.mpr (by omega)
        simp [he, hm]
      · simp [he]
    have hp : (∏ r ∈ (Finset.Icc 1 (k/2)).filter (fun r => 2*r = k),
        (1 + if 2*r = k then (Polynomial.X : Polynomial ℕ) else 2*Polynomial.X)) =
        (1+Polynomial.X) ^ (if k % 2 = 0 then 1 else 0) := by
      rw [← hc]
      apply Finset.prod_eq_pow_card
      intro r hr
      simp [(Finset.mem_filter.mp hr).2]
    rw [hp, hn]
    congr 1
    calc
      _ = (1 + 2*(Polynomial.X : Polynomial ℕ)) ^ (Finset.Icc 1 ((k-1)/2)).card := by
        apply Finset.prod_eq_pow_card
        intro r hr
        have h : 2*r ≠ k := by have := Finset.mem_Icc.mp hr; omega
        simp [h]
      _ = _ := by simp

  let P (k : ℕ) : Polynomial ℕ :=
    (1 + 2*Polynomial.X) ^ ((k-1)/2) * (1+Polynomial.X) ^ (if k % 2 = 0 then 1 else 0)

  have lower_coefficient_card (k : ℕ) (hk : 1 ≤ k) (j : ℕ) :
      (P k).coeff j =
        ((Finset.univ : Finset (Lower k)).filter (fun l => l.R.card = j)).card := by
    classical
    change ((1 + 2*Polynomial.X) ^ ((k-1)/2) *
      (1+Polynomial.X) ^ (if k % 2 = 0 then 1 else 0) : Polynomial ℕ).coeff j = _
    rw [← lower_size_polynomial k hk, finsetSum_coeff]
    simp [Polynomial.coeff_X_pow, eq_comm, Finset.sum_boole]

  have selected_coefficient_count (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
      @Fintype.card (Selected n k) (selectedFintype n k hk hkn) =
        ∑ j ∈ Finset.range (k/2+1), (P k).coeff j * Nat.choose (n-k+1) (k-j) := by
    classical
    rw [selected_tail_count n k hk hkn]
    rw [← Finset.sum_fiberwise_of_maps_to
      (s := Finset.univ) (t := Finset.range (k/2+1))
      (g := fun l : Lower k => l.R.card)
      (by
        intro l hl
        have hb := Finset.card_le_card l.hR
        simp only [Nat.card_Icc] at hb
        exact Finset.mem_range.mpr (by omega))]
    apply Finset.sum_congr rfl
    intro j hj
    rw [lower_coefficient_card k hk j]
    calc
      _ = ∑ _l ∈ (Finset.univ : Finset (Lower k)).filter (fun l => l.R.card = j),
          Nat.choose (n-k+1) (k-j) := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [(Finset.mem_filter.mp hl).2]
      _ = _ := by simp [nsmul_eq_mul]

  have original_cardinality_decomposition (n : ℕ) :
      a n = 1 + ∑ k ∈ Finset.Icc 1 n,
        ((admissibleFamily n).filter (fun S => S.card = k)).card := by
    classical
    have hdecomp : (admissibleFamily n).card =
        ∑ k ∈ Finset.Icc 0 n,
          ((admissibleFamily n).filter (fun S => S.card = k)).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro S hS
      have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
      have hb := Finset.card_le_card hsub
      simp only [Nat.card_Icc] at hb
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩
    have hz : (admissibleFamily n).filter (fun S => S.card = 0) = {∅} := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro h
        exact Finset.card_eq_zero.mp h.2
      · intro h
        subst S
        simp [admissibleFamily]
    have hi : Finset.Icc 0 n = insert 0 (Finset.Icc 1 n) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    change (admissibleFamily n).card = _
    rw [hdecomp, hi, Finset.sum_insert (by simp), hz, Finset.card_singleton]

  have original_count_exact (n : ℕ) :
      a n = 1 + ∑ k ∈ Finset.Icc 1 n,
        ∑ j ∈ Finset.range (k / 2 + 1),
          (P k).coeff j * Nat.choose (n - k + 1) (k - j) := by
    classical
    rw [original_cardinality_decomposition]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    obtain ⟨hkpos, hkn⟩ := Finset.mem_Icc.mp hk
    letI := selectedFintype n k hkpos hkn
    let e : ((admissibleFamily n).filter (fun S => S.card = k)) ≃ Selected n k := {
      toFun := fun S => ⟨S.val, by
        obtain ⟨hS, hc⟩ := Finset.mem_filter.mp S.property
        obtain ⟨hsub, hv⟩ := Finset.mem_filter.mp hS
        exact ⟨Finset.mem_powerset.mp hsub, hc, by simpa [hc] using hv⟩⟩
      invFun := fun S => ⟨S.val, by
        apply Finset.mem_filter.mpr
        refine ⟨?_, S.property.2.1⟩
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_powerset.mpr S.property.1,
          by simpa [S.property.2.1] using S.property.2.2⟩⟩
      left_inv := fun S => Subtype.ext rfl
      right_inv := fun S => Subtype.ext rfl }
    rw [← Fintype.card_coe, Fintype.card_congr e]
    exact selected_coefficient_count n k hkpos hkn

  let U (d : ℕ) : PowerSeries ℚ := (invOneSubPow ℚ d).val

  let F (k : ℕ) : PowerSeries ℚ := mk fun n =>
    if k ≤ n then
      ∑ j ∈ Finset.range (k/2+1), ((P k).coeff j : ℚ) * (Nat.choose (n-k+1) (k-j) : ℚ)
    else 0

  have original_summand_coeff (n k : ℕ) :
      PowerSeries.coeff n (F k) = if k ≤ n then
        ((∑ j ∈ Finset.range (k/2+1), (P k).coeff j * Nat.choose (n-k+1) (k-j) : ℕ) : ℚ)
      else 0 := by
    simp [F, Nat.cast_sum, Nat.cast_mul]

  have shifted_binomial (k r : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) :
      (mk fun n => if k ≤ n then (Nat.choose (n-k+1) r : ℚ) else 0) =
        (PowerSeries.X : PowerSeries ℚ)^(k+r-1) * U (r+1) := by
    apply PowerSeries.ext
    intro n
    dsimp only [U]
    rw [coeff_mk, PowerSeries.coeff_X_pow_mul', invOneSubPow_val_succ_eq_mk_add_choose, coeff_mk]
    by_cases hkn : k ≤ n
    · rw [if_pos hkn]
      by_cases hshift : k+r-1 ≤ n
      · rw [if_pos hshift]
        congr 1
        congr 1
        omega
      · rw [if_neg hshift, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    · rw [if_neg hkn, if_neg (by omega : ¬ k+r-1 ≤ n)]

  have fixed_k_finite (k : ℕ) (hk : 1 ≤ k) :
      F k = ∑ j ∈ Finset.range (k/2+1),
        PowerSeries.C ((P k).coeff j : ℚ) * ((PowerSeries.X : PowerSeries ℚ)^(2*k-j-1) * U (k-j+1)) := by
    apply PowerSeries.ext
    intro n
    dsimp only [F]
    rw [coeff_mk, map_sum]
    by_cases hkn : k ≤ n
    · rw [if_pos hkn]
      apply Finset.sum_congr rfl
      intro j hj
      have hjk : j ≤ k/2 := by have := Finset.mem_range.mp hj; omega
      have hr : 1 ≤ k-j := by omega
      have he : k+(k-j)-1 = 2*k-j-1 := by omega
      have h := congrArg (PowerSeries.coeff n) (shifted_binomial k (k-j) hk hr)
      rw [he, coeff_mk, if_pos hkn] at h
      rw [PowerSeries.coeff_C_mul, ← h]
    · rw [if_neg hkn]
      symm
      apply Finset.sum_eq_zero
      intro j hj
      have hjk : j ≤ k/2 := by have := Finset.mem_range.mp hj; omega
      have hr : 1 ≤ k-j := by omega
      have he : k+(k-j)-1 = 2*k-j-1 := by omega
      have h := congrArg (PowerSeries.coeff n) (shifted_binomial k (k-j) hk hr)
      rw [he, coeff_mk, if_neg hkn] at h
      rw [PowerSeries.coeff_C_mul, ← h, mul_zero]

  let E : MvPolynomial (Fin 2) ℚ →+* PowerSeries ℚ :=
    MvPolynomial.eval₂Hom PowerSeries.C ![1-PowerSeries.X, PowerSeries.X]

  have homogenized_sum (p : Polynomial ℚ) (d : ℕ) (hp : p.natDegree ≤ d) :
      E (p.homogenize d) = ∑ j ∈ Finset.range (d+1),
        PowerSeries.C (p.coeff j) * (1-PowerSeries.X)^j * (PowerSeries.X : PowerSeries ℚ)^(d-j) := by
    have h := congrArg (fun q : Polynomial ℚ => E (q.homogenize d))
      (p.as_sum_range_C_mul_X_pow' (by omega : p.natDegree < d+1))
    rw [h, Polynomial.homogenize_finsetSum, map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjd : j ≤ d := by have := Finset.mem_range.mp hj; omega
    simp [Polynomial.homogenize_X_pow hjd, E, mul_assoc]

  have fixed_k_factored (k : ℕ) (hk : 1 ≤ k)
      (hp : ((P k).map (Nat.castRingHom ℚ)).natDegree ≤ k/2) :
      F k = (PowerSeries.X : PowerSeries ℚ)^(2*k-1-k/2) * U (k+1) *
        E (((P k).map (Nat.castRingHom ℚ)).homogenize (k/2)) := by
    rw [fixed_k_finite k hk, homogenized_sum _ _ hp, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjd : j ≤ k/2 := by have := Finset.mem_range.mp hj; omega
    have hjk : j ≤ k-1 := by omega
    have he : 2*k-j-1 = (2*k-1-k/2)+(k/2-j) := by omega
    have hd : (k-j+1)+j = k+1 := by omega
    have hu : (1-PowerSeries.X : PowerSeries ℚ)^j * U (k+1) = U (k-j+1) := by
      simpa only [U, hd] using
        one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val ℚ (k-j+1) j
    simp only [Polynomial.coeff_map]
    change PowerSeries.C ((P k).coeff j : ℚ) * (PowerSeries.X^(2*k-j-1) * U (k-j+1)) =
      PowerSeries.X^(2*k-1-k/2) * U (k+1) * (PowerSeries.C ((P k).coeff j : ℚ) * (1-PowerSeries.X)^j * PowerSeries.X^(k/2-j))
    rw [he, pow_add, ← hu]
    ring

  let polyA : Polynomial ℚ := 1 + Polynomial.C 2 * Polynomial.X

  let B : Polynomial ℚ := 1 + Polynomial.X

  let R : PowerSeries ℚ := PowerSeries.X^3 * (2-PowerSeries.X) * U 2

  have parity_factorization (m : ℕ) :
      F (2*m+1) = PowerSeries.X * U 2 * R^m ∧
      F (2*m+2) = PowerSeries.X^2 * U 3 * R^m := by
    have hA : polyA.natDegree ≤ 1 := by
      apply Polynomial.natDegree_add_le_of_degree_le
      · simp
      · simpa using (Polynomial.natDegree_C_mul_le (2 : ℚ) Polynomial.X)
    have hB : B.natDegree ≤ 1 := by
      apply Polynomial.natDegree_add_le_of_degree_le <;> simp [B]
    have hAm : (polyA^m).natDegree ≤ m := by
      simpa using Polynomial.natDegree_pow_le_of_le m hA
    have hAmB : (polyA^m*B).natDegree ≤ m+1 :=
      Polynomial.natDegree_mul_le_of_le hAm hB
    have hoe : (2*m+1)%2 = 1 := by omega
    have hee : (2*m+2)%2 = 0 := by omega
    have hdo : (2*m+1)/2 = m := by omega
    have hde : (2*m+2)/2 = m+1 := by omega
    have hpo : (P (2*m+1)).map (Nat.castRingHom ℚ) = polyA^m := by
      simp [P, hoe, polyA, map_ofNat]
    have hpe : (P (2*m+2)).map (Nat.castRingHom ℚ) = polyA^m*B := by
      simp [P, hee, hdo, polyA, B, map_ofNat]
    have hpow : (polyA^m).homogenize m = (polyA.homogenize 1)^m := by
      simpa using (Polynomial.homogenize_finsetProd
        (s := Finset.range m) (p := fun _ => polyA) (n := fun _ => 1)
        (by intro i hi; exact hA))
    have hEA : E (polyA.homogenize 1) = 2-PowerSeries.X := by
      dsimp only [polyA]
      rw [Polynomial.homogenize_add, Polynomial.homogenize_one,
        Polynomial.homogenize_C_mul,
        Polynomial.homogenize_X (by decide : (1 : ℕ) ≠ 0)]
      simp [E, map_ofNat]
      ring
    have hEB : E (B.homogenize 1) = 1 := by
      simp [B, E, Polynomial.homogenize_X (by decide : (1 : ℕ) ≠ 0)]
    have hU : U (2*m) = (U 2)^m := by
      simp only [U, invOneSubPow_eq_inv_one_sub_pow, pow_mul, Units.val_pow_eq_pow_val]
    have hUo : U (2*m+2) = (U 2)^m * U 2 := by
      dsimp only [U]
      rw [invOneSubPow_add, Units.val_mul]
      change U (2*m) * U 2 = _
      rw [hU]
    have hUe : U (2*m+3) = (U 2)^m * U 3 := by
      dsimp only [U]
      rw [invOneSubPow_add, Units.val_mul]
      change U (2*m) * U 3 = _
      rw [hU]
    constructor
    · rw [fixed_k_factored (2*m+1) (by omega) (by simpa [hpo, hdo] using hAm),
        hpo, hdo, hpow, map_pow, hEA]
      have hx : 2*(2*m+1)-1-m = 1+3*m := by omega
      have hu : 2*m+1+1 = 2*m+2 := by omega
      rw [hx, hu, hUo]
      simp only [R, mul_pow, pow_add, pow_mul, pow_one]
      ring
    · rw [fixed_k_factored (2*m+2) (by omega) (by simpa [hpe, hde] using hAmB),
        hpe, hde, Polynomial.homogenize_mul _ _ hAm hB, hpow, map_mul, map_pow,
        hEA, hEB, mul_one]
      have hx : 2*(2*m+2)-1-(m+1) = 2+3*m := by omega
      have hu : 2*m+2+1 = 2*m+3 := by omega
      rw [hx, hu, hUe]
      simp only [R, mul_pow, pow_add, pow_mul]
      ring

  letI : TopologicalSpace ℚ := ⊥
  letI : DiscreteTopology ℚ := ⟨rfl⟩

  let seriesA : PowerSeries ℚ := mk fun n => (a n : ℚ)

  have coeff_F_vanish (n k : ℕ) (h : n < k) : PowerSeries.coeff n (F k) = 0 := by
    simp [F, not_le.mpr h]

  have F_summable : Summable (fun k : ℕ => F (k+1)) := by
    rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
    intro n
    apply summable_of_hasFiniteSupport
    apply (Finset.range n).finite_toSet.subset
    intro k hk
    simp only [Function.mem_support] at hk
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra h
    exact hk (coeff_F_vanish n (k+1) (by omega))

  have coeff_tsum_F (n : ℕ) :
      PowerSeries.coeff n (∑' k : ℕ, F (k+1)) = ∑ k ∈ Finset.range n, PowerSeries.coeff n (F (k+1)) := by
    calc
      _ = ∑' k : ℕ, PowerSeries.coeff n (F (k+1)) :=
        F_summable.map_tsum (PowerSeries.coeff n).toAddMonoidHom
          (PowerSeries.WithPiTopology.continuous_coeff ℚ n)
      _ = _ := by
        apply tsum_eq_sum
        intro k hk
        exact coeff_F_vanish n (k+1) (by have := Finset.mem_range.not.mp hk; omega)

  have original_series_sum : seriesA = U 1 + ∑' k : ℕ, F (k+1) := by
    classical
    apply PowerSeries.ext
    intro n
    rw [map_add, coeff_tsum_F]
    have hU : PowerSeries.coeff n (U 1) = 1 := by
      simp [U, invOneSubPow_val_succ_eq_mk_add_choose]
    rw [hU]
    have hs : (∑ k ∈ Finset.range n, PowerSeries.coeff n (F (k+1))) =
        ∑ k ∈ Finset.Icc 1 n, PowerSeries.coeff n (F k) := by
      apply Finset.sum_bij (fun k _ => k+1)
      · intro k hk
        exact Finset.mem_Icc.mpr ⟨by omega, by have := Finset.mem_range.mp hk; omega⟩
      · intro k hk l hl he
        omega
      · intro k hk
        refine ⟨k-1, ?_, ?_⟩
        · have := Finset.mem_Icc.mp hk
          apply Finset.mem_range.mpr
          omega
        · have := Finset.mem_Icc.mp hk
          omega
      · intro k hk
        rfl
    rw [hs]
    have hc := congrArg (fun z : ℕ => (z : ℚ)) (original_count_exact n)
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_sum, Nat.cast_mul] at hc
    dsimp only [seriesA]
    rw [coeff_mk, hc]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [original_summand_coeff, if_pos (Finset.mem_Icc.mp hk).2]
    simp only [Nat.cast_sum, Nat.cast_mul]

  have R_constantCoeff : constantCoeff R = 0 := by
    simp [R]

  have parity_sum : (∑' k : ℕ, F (k+1)) =
      (PowerSeries.X * U 2 + PowerSeries.X^2 * U 3) * ∑' m : ℕ, R^m := by
    have hp := PowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero R_constantCoeff
    have ho : Summable (fun m : ℕ => F (2*m+1)) := by
      simpa only [(parity_factorization _).1] using hp.mul_left (PowerSeries.X * U 2)
    have he : Summable (fun m : ℕ => F (2*m+2)) := by
      simpa only [(parity_factorization _).2] using hp.mul_left (PowerSeries.X^2 * U 3)
    have h := tsum_even_add_odd (f := fun k : ℕ => F (k+1)) ho
      (by simpa only [Nat.add_assoc] using he)
    rw [← h]
    simp only [Nat.add_assoc, (parity_factorization _).1, (parity_factorization _).2]
    rw [hp.tsum_mul_left, hp.tsum_mul_left, add_mul]

  let t : PowerSeries ℚ := 1-PowerSeries.X
  let G : PowerSeries ℚ := ∑' m : ℕ, R^m
  let D : PowerSeries ℚ := 1 - 2*PowerSeries.X + PowerSeries.X^2 - 2*PowerSeries.X^3 + PowerSeries.X^4
  have hgeo : (1-R)*G = 1 :=
    PowerSeries.WithPiTopology.one_sub_mul_tsum_pow_of_constantCoeff_eq_zero R_constantCoeff
  have h1 : t * U 1 = 1 := by
    simpa [t, U] using
      (one_sub_pow_add_mul_invOneSubPow_val_eq_one_sub_pow ℚ (d := 0) 1)
  have h2 : t^2 * U 2 = 1 := by
    simpa [t, U] using
      (one_sub_pow_add_mul_invOneSubPow_val_eq_one_sub_pow ℚ (d := 0) 2)
  have h32 : t * U 3 = U 2 := by
    simpa [t, U] using
      (one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val ℚ (d := 2) 1)
  have h21 : t * U 2 = U 1 := by
    simpa [t, U] using
      (one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val ℚ (d := 1) 1)
  have hfactor : PowerSeries.X * U 2 + PowerSeries.X^2 * U 3 = PowerSeries.X * U 3 := by
    rw [← h32]
    dsimp [t]
    ring
  have hA : seriesA = U 1 + PowerSeries.X * U 3 * G := by
    rw [original_series_sum, parity_sum, hfactor]
  have hD : D = t^2 * (1-R) := by
    calc
      D = t^2 - PowerSeries.X^3*(2-PowerSeries.X) := by dsimp [D, t]; ring
      _ = t^2 - PowerSeries.X^3*(2-PowerSeries.X)*(t^2*U 2) := by rw [h2]; ring
      _ = t^2*(1-R) := by dsimp [R]; ring
  have hmain : D*(PowerSeries.X*U 3*G) = PowerSeries.X*U 1 := by
    calc
      D*(PowerSeries.X*U 3*G) = PowerSeries.X*(t*(t*U 3))*((1-R)*G) := by rw [hD]; ring
      _ = PowerSeries.X*U 1 := by rw [h32, h21, hgeo]; ring
  have hnum : D+PowerSeries.X = t*(1+PowerSeries.X^2-PowerSeries.X^3) := by dsimp [D, t]; ring
  change D*seriesA = _
  rw [hA, mul_add, hmain]
  calc
    D*U 1 + PowerSeries.X*U 1 = (D+PowerSeries.X)*U 1 := by ring
    _ = (1+PowerSeries.X^2-PowerSeries.X^3)*(t*U 1) := by rw [hnum]; ring
    _ = 1+PowerSeries.X^2-PowerSeries.X^3 := by rw [h1, mul_one]

end D5.S3.Combinatorics.CardinalitySumAvoidingSubsets
