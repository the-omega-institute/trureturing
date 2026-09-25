/- GID: D5/S3/Combinatorics/ArrowWilfGapData
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArrowWilfGapData
   mirror-E: none(waiver:gap-encoding-for-arrow-wilf-bijections)
   anchors: [mathlib/module/Mathlib.Algebra.Order.Antidiag.FinsuppEquiv]
   utility: none
   digest: Gap vectors split a filler word into blocks interleaved after a distinguished skeleton. -/

import D5.S3.Combinatorics.ArrowWilfCountingCore
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.List.SplitLengths

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArrowWilfGapData

noncomputable section

open D5.S3.Combinatorics.ArrowWilfFixedInsertion
open D5.S3.Combinatorics.ArrowWilfCountingCore

/-- Weak compositions of `t` indexed by a finite label type. -/
abbrev GapsOn (ι : Type*) [Fintype ι] [DecidableEq ι] (t : ℕ) :=
  ↑((Finset.univ : Finset ι).finsuppAntidiag t)

/-- Weak compositions of `t` into `r` linearly labelled gaps. -/
abbrev Gaps (r t : ℕ) := GapsOn (Fin r) t

/-- The list of part sizes of a gap vector. -/
def gapList {r t : ℕ} (g : Gaps r t) : List ℕ :=
  List.ofFn fun i : Fin r => g.1 i

/-- Gap vectors that are positive on a prescribed collection of slots. -/
abbrev PositiveGapsOn (ι : Type*) [Fintype ι] [DecidableEq ι]
    (t : ℕ) (R : Finset ι) :=
  {g : GapsOn ι t // ∀ i ∈ R, 0 < g.1 i}

/-- Positive weak compositions with linearly labelled gaps. -/
abbrev PositiveGaps (r t : ℕ) (R : Finset (Fin r)) :=
  PositiveGapsOn (Fin r) t R

/-- One unit in every slot belonging to `R`. -/
def gapIndicator {ι : Type*} (R : Finset ι) : ι →₀ ℕ :=
  Finsupp.indicator R fun _ _ => 1

/-- Subtracting the mandatory unit identifies positive gaps with ordinary residual gaps. -/
def positiveGapsEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    {t : ℕ} {R : Finset ι} (hRt : R.card ≤ t) :
    PositiveGapsOn ι t R ≃ GapsOn ι (t - R.card) where
  toFun g := by
    let z : ι →₀ ℕ := g.1.1 - gapIndicator R
    refine ⟨z, ?_⟩
    rw [Finset.mem_finsuppAntidiag]
    constructor
    · have hle : ∀ i ∈ (Finset.univ : Finset ι), gapIndicator R i ≤ g.1.1 i := by
        intro i hi
        by_cases hiR : i ∈ R
        · rw [gapIndicator, Finsupp.indicator_of_mem hiR]
          exact g.2 i hiR
        · rw [gapIndicator, Finsupp.indicator_of_notMem hiR]
          exact Nat.zero_le _
      change (∑ i ∈ (Finset.univ : Finset ι),
        (g.1.1 i - gapIndicator R i)) = t - R.card
      rw [Finset.sum_tsub_distrib _ hle]
      have hg := (Finset.mem_finsuppAntidiag.mp g.1.2).1
      rw [hg]
      have hind : ∑ i ∈ (Finset.univ : Finset ι), gapIndicator R i = R.card := by
        calc
          _ = ∑ i ∈ R, gapIndicator R i := by
            symm
            apply Finset.sum_subset (Finset.subset_univ R)
            intro i hi hiR
            rw [gapIndicator, Finsupp.indicator_of_notMem hiR]
          _ = R.card := by simp [gapIndicator, Finsupp.indicator_of_mem]
      rw [hind]
    · exact Finset.subset_univ _
  invFun z := by
    let g : ι →₀ ℕ := z.1 + gapIndicator R
    refine ⟨⟨g, ?_⟩, ?_⟩
    · rw [Finset.mem_finsuppAntidiag]
      constructor
      · simp only [g, Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib]
        have hz := (Finset.mem_finsuppAntidiag.mp z.2).1
        rw [hz]
        have hind : ∑ i ∈ (Finset.univ : Finset ι), gapIndicator R i = R.card := by
          calc
            _ = ∑ i ∈ R, gapIndicator R i := by
              symm
              apply Finset.sum_subset (Finset.subset_univ R)
              intro i hi hiR
              rw [gapIndicator, Finsupp.indicator_of_notMem hiR]
            _ = R.card := by simp [gapIndicator, Finsupp.indicator_of_mem]
        rw [hind, Nat.sub_add_cancel hRt]
      · exact Finset.subset_univ _
    · intro i hi
      change 0 < z.1 i + gapIndicator R i
      rw [gapIndicator, Finsupp.indicator_of_mem hi]
      omega
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    ext i
    change (g.1.1 i - gapIndicator R i) + gapIndicator R i = g.1.1 i
    by_cases hiR : i ∈ R
    · apply Nat.sub_add_cancel
      rw [gapIndicator, Finsupp.indicator_of_mem hiR]
      exact g.2 i hiR
    · rw [gapIndicator, Finsupp.indicator_of_notMem hiR]
      simp
  right_inv z := by
    apply Subtype.ext
    ext i
    change (z.1 i + gapIndicator R i) - gapIndicator R i = z.1 i
    exact Nat.add_sub_cancel_right _ _

/-- Read the gap following a support value, with zero outside the support. -/
def gapAt (H : Finset ℕ) {t : ℕ} (g : GapsOn (Option ↑H) t) (x : ℕ) : ℕ :=
  if hx : x ∈ H then g.1 (some ⟨x, hx⟩) else 0

/-- Put the leading gap first, then read the remaining gaps in skeleton order. -/
def gapSizes (H : Finset ℕ) {t : ℕ} (p : Word H) (g : GapsOn (Option ↑H) t) :
    List ℕ :=
  g.1 none :: p.1.map (gapAt H g)

/-- Skeleton order only permutes the labelled gap coordinates. -/
theorem gapSizes_length_sum (H : Finset ℕ) {t : ℕ} (p : Word H)
    (g : GapsOn (Option ↑H) t) :
    (gapSizes H p g).length = H.card + 1 ∧ (gapSizes H p g).sum = t := by
  have hp : p.1.Perm H.toList := by
    simpa [words, List.mem_permutations] using p.2
  constructor
  · simp [gapSizes, hp.length_eq]
  · have hmap := hp.map (gapAt H g)
    have hsumMap : (p.1.map (gapAt H g)).sum = (H.toList.map (gapAt H g)).sum :=
      hmap.sum_eq
    rw [gapSizes, List.sum_cons, hsumMap]
    have hg := (Finset.mem_finsuppAntidiag.mp g.2).1
    calc
      g.1 none + (H.toList.map (gapAt H g)).sum =
          g.1 none + ∑ h : ↑H, g.1 (some h) := by
        congr 1
        rw [← List.sum_toFinset (gapAt H g) H.nodup_toList]
        rw [← Finset.sum_attach]
        rw [Finset.toList_toFinset]
        apply Finset.sum_congr rfl
        intro h hh
        simp [gapAt]
      _ = ∑ i : Option ↑H, g.1 i := (Fintype.sum_option _).symm
      _ = (Finset.univ : Finset (Option ↑H)).sum g.1 := by rfl
      _ = t := hg

/-- Place the `i`-th block immediately after the `i`-th skeleton entry. -/
def afterBlocks {α : Type*} : List α → List (List α) → List α
  | [], _ => []
  | a :: s, [] => a :: s
  | a :: s, b :: bs => a :: (b ++ afterBlocks s bs)

/-- Interleaving blocks only rearranges the skeleton followed by the flattened blocks. -/
theorem afterBlocks_perm {α : Type*} {s : List α} {bs : List (List α)}
    (hlen : bs.length = s.length) :
    (afterBlocks s bs).Perm (s ++ bs.flatten) := by
  induction s generalizing bs with
  | nil =>
      have : bs = [] := List.eq_nil_of_length_eq_zero hlen
      subst bs
      simp [afterBlocks]
  | cons a s ih =>
      rcases bs with _ | ⟨b, bs⟩
      · simp at hlen
      · simp only [List.length_cons, Nat.succ.injEq] at hlen
        have htail := ih hlen
        have hmove : (b ++ s ++ bs.flatten).Perm (s ++ b ++ bs.flatten) := by
          exact List.perm_append_comm.append_right bs.flatten
        have h := (htail.append_left b).trans (by
          simpa [List.append_assoc] using hmove)
        simpa [afterBlocks, List.flatten, List.append_assoc] using h.cons a

/-- Filtering for skeleton entries recovers the skeleton from a valid interleaving. -/
theorem filter_afterBlocks_skeleton {α : Type*} (P : α → Bool)
    {s : List α} {bs : List (List α)} (hlen : bs.length = s.length)
    (hs : ∀ a ∈ s, P a) (hb : ∀ b ∈ bs, ∀ x ∈ b, ¬ P x) :
    (afterBlocks s bs).filter P = s := by
  induction s generalizing bs with
  | nil =>
      have : bs = [] := List.eq_nil_of_length_eq_zero hlen
      subst bs
      simp [afterBlocks]
  | cons a s ih =>
      rcases bs with _ | ⟨b, bs⟩
      · simp at hlen
      · simp only [List.length_cons, Nat.succ.injEq] at hlen
        have ha : P a := hs a (by simp)
        have hs' : ∀ x ∈ s, P x := by
          intro x hx
          exact hs x (by simp [hx])
        have hb0 : ∀ x ∈ b, ¬ P x := hb b (by simp)
        have hbs : ∀ c ∈ bs, ∀ x ∈ c, ¬ P x := by
          intro c hc
          exact hb c (by simp [hc])
        simp [afterBlocks, ha, List.filter_eq_nil_iff.mpr hb0, ih hlen hs' hbs]

/-- Filtering for filler entries recovers the flattened block list from a valid interleaving. -/
theorem filter_afterBlocks_fillers {α : Type*} (P : α → Bool)
    {s : List α} {bs : List (List α)} (hlen : bs.length = s.length)
    (hs : ∀ a ∈ s, P a) (hb : ∀ b ∈ bs, ∀ x ∈ b, ¬ P x) :
    (afterBlocks s bs).filter (fun x => !P x) = bs.flatten := by
  induction s generalizing bs with
  | nil =>
      have : bs = [] := List.eq_nil_of_length_eq_zero hlen
      subst bs
      simp [afterBlocks]
  | cons a s ih =>
      rcases bs with _ | ⟨b, bs⟩
      · simp at hlen
      · simp only [List.length_cons, Nat.succ.injEq] at hlen
        have ha : P a := hs a (by simp)
        have hs' : ∀ x ∈ s, P x := by
          intro x hx
          exact hs x (by simp [hx])
        have hb0 : ∀ x ∈ b, ¬ P x := hb b (by simp)
        have hbfalse : ∀ x ∈ b, P x = false := by
          intro x hx
          exact Bool.eq_false_iff.mpr (hb0 x hx)
        have hbs : ∀ c ∈ bs, ∀ x ∈ c, ¬ P x := by
          intro c hc
          exact hb c (by simp [hc])
        simp [afterBlocks, ha, ih hlen hs' hbs, List.flatten]
        exact hbfalse

/-- A prefix consisting entirely of values below `g` does not change the singleton block of `g`. -/
theorem fixedSyntax_append_small_iff {g : ℕ} {u q : List ℕ} (hg : g ∈ q)
    (hu : ∀ x ∈ u, x < g) :
    FixedSyntax g (u ++ q) ↔ FixedSyntax g q := by
  induction u with
  | nil => rfl
  | cons x u ih =>
      have hxg : x < g := hu x (by simp)
      have hxu : ∀ y ∈ u, y < g := by
        intro y hy
        exact hu y (by simp [hy])
      have htail : g ∈ u ++ q := by simp [hg]
      have hhead : FixedSyntax g (x :: (u ++ q)) ↔ FixedSyntax g (u ++ q) := by
        cases hq : u ++ q with
        | nil => simp [hq] at htail
        | cons y r => simp [hq, FixedSyntax, Nat.ne_of_lt hxg, hxg]
      change FixedSyntax g (x :: (u ++ q)) ↔ FixedSyntax g q
      rw [hhead, ih hxu]

/-- A low block destroys exactly the skeleton fixed point immediately preceding that block. -/
theorem fixedSyntax_afterBlocks_iff {g : ℕ} {s : List ℕ} {bs : List (List ℕ)}
    (hs : s.Nodup) (hlen : bs.length = s.length) (hg : g ∈ s)
    (hsmall : ∀ b ∈ bs, ∀ x ∈ b, x < g) :
    FixedSyntax g (afterBlocks s bs) ↔
      FixedSyntax g s ∧ bs.getD (s.idxOf g) [] = [] := by
  induction s generalizing bs with
  | nil => simp at hg
  | cons a s ih =>
      have hs' := hs.of_cons
      rcases bs with _ | ⟨b, bs⟩
      · simp at hlen
      · simp only [List.length_cons, Nat.succ.injEq] at hlen
        have hbsmall : ∀ x ∈ b, x < g := hsmall b (by simp)
        have hbssmall : ∀ c ∈ bs, ∀ x ∈ c, x < g := by
          intro c hc
          exact hsmall c (by simp [hc])
        by_cases hag : a = g
        · subst a
          rcases b with _ | ⟨x, b⟩
          · rcases s with _ | ⟨y, s⟩
            · have : bs = [] := List.eq_nil_of_length_eq_zero hlen
              subst bs
              simp [afterBlocks, FixedSyntax]
            · rcases bs with _ | ⟨c, cs⟩
              · simp at hlen
              · simp [afterBlocks, FixedSyntax]
          · have hxg : x < g := hbsmall x (by simp)
            rcases s with _ | ⟨y, s⟩ <;>
              simp [afterBlocks, FixedSyntax, Nat.ne_of_lt hxg, Nat.not_lt_of_ge hxg.le]
        · have hgs : g ∈ s := by simpa [Ne.symm hag] using hg
          have hgafter : g ∈ afterBlocks s bs :=
            (afterBlocks_perm hlen).mem_iff.mpr (by simp [hgs])
          by_cases haglt : a < g
          · have habsmall : ∀ x ∈ a :: b, x < g := by
              intro x hx
              rcases List.mem_cons.mp hx with rfl | hx
              · exact haglt
              · exact hbsmall x hx
            have hright := fixedSyntax_append_small_iff hgafter habsmall
            have hleft := fixedSyntax_append_small_iff hgs (u := [a]) (by simp [haglt])
            have hleft' : FixedSyntax g (a :: s) ↔ FixedSyntax g s := by
              simpa using hleft
            change FixedSyntax g ((a :: b) ++ afterBlocks s bs) ↔
              FixedSyntax g (a :: s) ∧ (b :: bs).getD ((a :: s).idxOf g) [] = []
            rw [hright, hleft', ih hs' hlen hgs hbssmall]
            simp [hag]
          · have hnotleft : ¬ FixedSyntax g (a :: s) := by
              rcases s with _ | ⟨y, s⟩
              · simp at hgs
              · simp [FixedSyntax, hag, haglt]
            have hnotright : ¬ FixedSyntax g (a :: (b ++ afterBlocks s bs)) := by
              have hne : b ++ afterBlocks s bs ≠ [] := by
                intro he
                have : g ∈ b ++ afterBlocks s bs := by simp [hgafter]
                rw [he] at this
                simp at this
              cases hq : b ++ afterBlocks s bs with
              | nil => exact (hne hq).elim
              | cons y r => simp [hq, FixedSyntax, hag, haglt]
            change FixedSyntax g (a :: (b ++ afterBlocks s bs)) ↔
              FixedSyntax g (a :: s) ∧ (b :: bs).getD ((a :: s).idxOf g) [] = []
            simp [hnotleft, hnotright]

end

end D5.S3.Combinatorics.ArrowWilfGapData
