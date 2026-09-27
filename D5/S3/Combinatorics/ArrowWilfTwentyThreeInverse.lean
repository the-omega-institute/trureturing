/- GID: D5/S3/Combinatorics/ArrowWilfTwentyThreeInverse
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArrowWilfTwentyThreeInverse
   mirror-E: none(waiver:inverse-gap-encoding-for-the-twenty-three-arrow-pattern)
   anchors: [mathlib/module/Mathlib.Data.List.SplitLengths]
   utility: none
   digest: The smallest-fixed-point stratum is parsed into its derangement prefix and upper-tail gaps. -/

import D5.S3.Combinatorics.ArrowWilfTwentyThreeCount
import D5.S3.Combinatorics.ArrowWilfTwelveSurject
import Mathlib.Data.List.SplitLengths

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArrowWilfTwentyThreeInverse

noncomputable section

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.ArrowWilfCharacterization
open D5.S3.Combinatorics.ArrowWilfCountingCore
open D5.S3.Combinatorics.ArrowWilfFixedInsertion
open D5.S3.Combinatorics.ArrowWilfGapData
open D5.S3.Combinatorics.ArrowWilfTwelveCount
open D5.S3.Combinatorics.ArrowWilfTwentyThreeCount
open D5.S3.Combinatorics.ArrowWilfTwelveSurject

/-- Avoiding words with smallest fixed point exactly `m`. -/
abbrev MinAvoiders (n m : ℕ) :=
  {p : Word (fullSupport n) //
    ¬ Contains [2, 3] [(1, 1)] 3 p.1 ∧
      hat p.1 m = m ∧
      ∀ g ∈ fullSupport n, g < m → hat p.1 g ≠ g}

noncomputable instance (n m : ℕ) : Fintype (MinAvoiders n m) := by
  classical exact inferInstance

/-- The forward construction belongs to its intended smallest-fixed-point stratum. -/
def minAvoiderOfData {n m r : ℕ} (hm : 1 ≤ m) (hmn : m < n)
    (d : TwentyThreeData n m r) : MinAvoiders n m := by
  refine ⟨(twentyThreeAvoider hm hmn d).1, ?_⟩
  refine ⟨(twentyThreeAvoider hm hmn d).2,
    twentyThreeList_fixed_m hm hmn d, ?_⟩
  intro g hg hgm
  have hp : (twentyThreeList d).Perm (List.range' 1 n) :=
    twentyThreeList_perm hm hmn.le d
  have hmem : g ∈ twentyThreeList d := hp.mem_iff.mpr (by
    have hg' : g ∈ (fullSupport n).toList := Finset.mem_toList.mpr hg
    simpa [fullSupport] using hg')
  exact twentyThreeList_no_lower_fixed hm hmn.le d hgm hmem

/-- Every avoiding word with smallest fixed point `m<n` has the decorated
    prefix and upper-tail block shape before the blocks are counted. -/
theorem minAvoider_normal_form {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n)
    (p : MinAvoiders n m) :
    ∃ u : List ℕ, ∃ bs : List (List ℕ),
      p.1.1 = u ++ m :: afterBlocks (upperDescending n m) bs ∧
      (∀ x ∈ u, x < m) ∧
      bs.length = (upperDescending n m).length ∧
      (∀ b ∈ bs, ∀ x ∈ b, x < m) := by
  let P : ℕ → Bool := fun x => decide (m < x)
  let U := upperDescending n m
  have hp : p.1.1.Perm (List.range' 1 n) := by
    have hp' : p.1.1.Perm (fullSupport n).toList := by
      simpa [words, List.mem_permutations] using p.1.2
    exact hp'.trans (by
      apply List.perm_of_nodup_nodup_toFinset_eq
      · exact (fullSupport n).nodup_toList
      · exact List.nodup_range'
      · simp [fullSupport])
  have hnodup : p.1.1.Nodup := hp.nodup_iff.mpr List.nodup_range'
  have hmMem : m ∈ p.1.1 := hp.mem_iff.mpr (by
    simp only [List.mem_range', one_mul]
    exact ⟨m - 1, by omega, by omega⟩)
  rcases split_at_member hmMem with ⟨u, v, heq⟩
  have hnot : m ∉ u := by
    have hn : (u ++ m :: v).Nodup := by simpa [heq] using hnodup
    intro hmu
    exact (List.nodup_append'.mp hn).2.2 hmu (by simp)
  have hmnotV : m ∉ v := by
    have hn : (u ++ m :: v).Nodup := by simpa [heq] using hnodup
    exact (List.nodup_cons.mp (List.nodup_append'.mp hn).2.1).1
  have hsyntax : FixedSyntax m (u ++ m :: v) := by
    simpa [heq] using (fixedSyntax_iff_hat_fixed hnodup hmMem).mpr p.2.2.1
  rcases fixedSyntax_split hnot hsyntax with ⟨hu, hv⟩
  have hpreFilter : u.filter P = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    exact (show ¬ decide (m < x) from by
      simpa [P] using Nat.not_lt_of_ge (hu x hx).le)
  have hupper := upper_filter_eq_of_avoids hmn.le p.2.1 hmMem p.2.2.1
  have hvFilter : v.filter P = U := by
    rw [heq, List.filter_append, hpreFilter] at hupper
    simpa [P, U] using hupper
  rcases hv with hvnil | ⟨x, xs, hv, hmx⟩
  · subst v
    have hlen := congrArg List.length hvFilter
    simp [U, upperDescending] at hlen
    omega
  · subst v
    rcases interleave_decompose_head P (by simpa [P] using hmx) with
      ⟨bs, hlen, hbs, hshape⟩
    have hlenU : bs.length = U.length := by
      rw [hvFilter] at hlen
      exact hlen
    have hshapeU : x :: xs = afterBlocks U bs := by
      rw [hvFilter] at hshape
      exact hshape
    have hsmall : ∀ b ∈ bs, ∀ y ∈ b, y < m := by
      intro b hb y hy
      have hyNot : ¬ m < y := by
        have := hbs b hb y hy
        simpa [P] using this
      have hyFlat : y ∈ bs.flatten := List.mem_flatten.mpr ⟨b, hb, hy⟩
      have hyTail : y ∈ x :: xs := by
        rw [hshapeU]
        exact (afterBlocks_perm hlenU).mem_iff.mpr
          (by simp [hyFlat])
      have hne : y ≠ m := by
        intro he
        subst y
        exact hmnotV hyTail
      omega
    refine ⟨u, bs, ?_, hu, hlenU, hsmall⟩
    rw [heq, hshapeU]

/-- The prefix of a smallest-fixed-point normal form is a derangement word. -/
theorem normal_prefix_no_fixed {n m : ℕ} (p : MinAvoiders n m)
    {u : List ℕ} {bs : List (List ℕ)}
    (heq : p.1.1 = u ++ m :: afterBlocks (upperDescending n m) bs)
    (hu : ∀ x ∈ u, x < m) :
    ∀ g ∈ u, hat u g ≠ g := by
  have hpperm : p.1.1.Perm (fullSupport n).toList := by
    simpa [words, List.mem_permutations] using p.1.2
  have hpNodup : p.1.1.Nodup := hpperm.nodup_iff.mpr (fullSupport n).nodup_toList
  have huNodup : u.Nodup := by
    have hfull : (u ++ m :: afterBlocks (upperDescending n m) bs).Nodup := by
      simpa [heq] using hpNodup
    exact (List.nodup_append'.mp hfull).1
  intro g hg hfix
  have hgS : g ∈ fullSupport n := by
    apply Finset.mem_toList.mp
    apply hpperm.mem_iff.mp
    rw [heq]
    simp [hg]
  have hsyntax : FixedSyntax g u :=
    (fixedSyntax_iff_hat_fixed huNodup hg).mpr hfix
  have hwhole : FixedSyntax g p.1.1 := by
    rw [heq]
    exact (fixedSyntax_append_greater_iff (hu g hg) hg).mpr hsyntax
  have hgmem : g ∈ p.1.1 := by rw [heq]; simp [hg]
  have hwholeFix := (fixedSyntax_iff_hat_fixed hpNodup hgmem).mp hwhole
  exact p.2.2.2 g hgS (hu g hg) hwholeFix

/-- The prefix and all tail fillers partition the lower support. -/
theorem normal_support_split {n m : ℕ} (hmn : m ≤ n) (p : MinAvoiders n m)
    {u : List ℕ} {bs : List (List ℕ)}
    (heq : p.1.1 = u ++ m :: afterBlocks (upperDescending n m) bs)
    (hu : ∀ x ∈ u, x < m)
    (hlen : bs.length = (upperDescending n m).length)
    (hbs : ∀ b ∈ bs, ∀ x ∈ b, x < m) :
    let R := bs.flatten.toFinset
    R ⊆ lowerSupport m ∧
      u.toFinset = lowerSupport m \ R ∧
      u.Nodup ∧ bs.flatten.Nodup := by
  let U := upperDescending n m
  let rho := bs.flatten
  let R := rho.toFinset
  have hp : p.1.1.Perm (List.range' 1 n) := by
    have hp' : p.1.1.Perm (fullSupport n).toList := by
      simpa [words, List.mem_permutations] using p.1.2
    exact hp'.trans (by
      apply List.perm_of_nodup_nodup_toFinset_eq
      · exact (fullSupport n).nodup_toList
      · exact List.nodup_range'
      · simp [fullSupport])
  have hparts : (u ++ m :: U ++ rho).Perm (List.range' 1 n) := by
    have ht := (afterBlocks_perm hlen).cons m |>.append_left u
    have ht' : p.1.1.Perm (u ++ m :: U ++ rho) := by
      simpa [heq, U, rho, List.append_assoc] using ht
    exact ht'.symm.trans hp
  have hnodup : (u ++ m :: U ++ rho).Nodup :=
    hparts.nodup_iff.mpr List.nodup_range'
  have huNodup : u.Nodup := by
    have h : (u ++ (m :: U ++ rho)).Nodup := by
      simpa [List.append_assoc, List.cons_append] using hnodup
    exact (List.nodup_append'.mp h).1
  have hrhoNodup : rho.Nodup := by
    have h : (m :: U ++ rho).Nodup := by
      have h' : (u ++ (m :: U ++ rho)).Nodup := by
        simpa [List.append_assoc, List.cons_append] using hnodup
      exact (List.nodup_append'.mp h').2.1
    have h' : (U ++ rho).Nodup := (List.nodup_cons.mp h).2
    exact (List.nodup_append'.mp h').2.1
  have hRsub : R ⊆ lowerSupport m := by
    intro x hx
    have hxrho : x ∈ rho := by simpa [R] using hx
    have hxlow : x < m := by
      rcases List.mem_flatten.mp hxrho with ⟨b, hb, hxb⟩
      exact hbs b hb x hxb
    have hxrange : x ∈ List.range' 1 n :=
      hparts.mem_iff.mp (by simp [hxrho])
    simp only [List.mem_range', one_mul] at hxrange
    rcases hxrange with ⟨i, hi, rfl⟩
    simp [lowerSupport, List.mem_range']
    omega
  have huSupport : u.toFinset = lowerSupport m \ R := by
    ext x
    constructor
    · intro hx
      have hxu : x ∈ u := by simpa using hx
      have hxrange : x ∈ List.range' 1 n :=
        hparts.mem_iff.mp (by simp [hxu])
      have hxlt := hu x hxu
      have hxLow : x ∈ lowerSupport m := by
        simp only [List.mem_range', one_mul] at hxrange
        rcases hxrange with ⟨i, hi, rfl⟩
        simp [lowerSupport, List.mem_range']
        omega
      have hxNotR : x ∉ R := by
        intro hxR
        have hxrho : x ∈ rho := by simpa [R] using hxR
        have hn : (u ++ (m :: U ++ rho)).Nodup := by
          simpa [List.append_assoc, List.cons_append] using hnodup
        exact (List.nodup_append'.mp hn).2.2 hxu (by simp [hxrho])
      exact Finset.mem_sdiff.mpr ⟨hxLow, hxNotR⟩
    · intro hx
      have hxLow := (Finset.mem_sdiff.mp hx).1
      have hxNotR := (Finset.mem_sdiff.mp hx).2
      have hxFull : x ∈ List.range' 1 n := by
        simp [lowerSupport, List.mem_range'] at hxLow
        rcases hxLow with ⟨i, hi, rfl⟩
        simp only [List.mem_range', one_mul]
        exact ⟨i, by omega, rfl⟩
      have hxParts := hparts.mem_iff.mpr hxFull
      simp only [List.mem_append, List.mem_cons] at hxParts
      rcases hxParts with hxU | hxR
      · rcases hxU with hxu | hxm | hxUpper
        · simpa using hxu
        · have hxm' : x = m := hxm
          simp [lowerSupport, List.mem_range'] at hxLow
          omega
        · have hxUpper' : m < x := by
            simp [U, upperDescending, List.mem_range'] at hxUpper
            omega
          have hxLower' : x < m := by
            simp [lowerSupport, List.mem_range'] at hxLow
            omega
          omega
      · exact (hxNotR (by simpa [R, rho] using hxR)).elim
  exact ⟨hRsub, huSupport, huNodup, hrhoNodup⟩

/-- The lower prefix and filler order become the derangement and ordering
    components of the inverse data. -/
theorem normal_lower_words {n m : ℕ} (hmn : m ≤ n) (p : MinAvoiders n m)
    {u : List ℕ} {bs : List (List ℕ)}
    (heq : p.1.1 = u ++ m :: afterBlocks (upperDescending n m) bs)
    (hu : ∀ x ∈ u, x < m)
    (hlen : bs.length = (upperDescending n m).length)
    (hbs : ∀ b ∈ bs, ∀ x ∈ b, x < m) :
    let R := bs.flatten.toFinset
    ∃ rho : Word R, ∃ sigma : NoFixed (lowerSupport m \ R),
      rho.1 = bs.flatten ∧ sigma.1.1 = u := by
  let R := bs.flatten.toFinset
  rcases normal_support_split hmn p heq hu hlen hbs with
    ⟨hRsub, huSupport, huNodup, hrhoNodup⟩
  let rho : Word R := by
    refine ⟨bs.flatten, ?_⟩
    change bs.flatten ∈ words R
    rw [words, List.mem_toFinset, List.mem_permutations]
    apply List.perm_of_nodup_nodup_toFinset_eq
    · exact hrhoNodup
    · exact R.nodup_toList
    · simp [R]
  let sigma : NoFixed (lowerSupport m \ R) := by
    refine ⟨⟨u, ?_⟩, ?_⟩
    · change u ∈ words (lowerSupport m \ R)
      rw [words, List.mem_toFinset, List.mem_permutations]
      apply List.perm_of_nodup_nodup_toFinset_eq
      · exact huNodup
      · exact (lowerSupport m \ R).nodup_toList
      · simpa [R] using huSupport
    · intro g hg
      have hgu : g ∈ u := by
        have hg' : g ∈ u.toFinset := by
          rw [huSupport]
          exact hg
        simpa using hg'
      exact normal_prefix_no_fixed p heq hu g hgu
  exact ⟨rho, sigma, rfl, rfl⟩

/-- The upper skeleton's blocks determine the corresponding labelled gap vector. -/
theorem upper_gaps_of_blocks (n m : ℕ) (bs : List (List ℕ))
    (hlen : bs.length = (upperDescending n m).length) :
    ∃ g : GapsOn ↑(upperSupport n m) bs.flatten.length,
      upperGapSizes n m g = bs.map List.length := by
  let H := upperSupport n m
  let U := upperDescending n m
  let s : Word H := by
    refine ⟨U, ?_⟩
    change U ∈ words H
    rw [words, List.mem_toFinset, List.mem_permutations]
    apply List.perm_of_nodup_nodup_toFinset_eq
    · exact List.nodup_reverse.mpr List.nodup_range'
    · exact H.nodup_toList
    · simp [U, upperDescending, H, upperSupport]
  have hlen' : bs.length = s.1.length := hlen
  let og := gapsOfBlocks H s [] bs hlen'
  let z : ↑H →₀ ℕ := Finsupp.onFinset Finset.univ (fun x => og.1 (some x)) (by simp)
  have hz : z ∈ (Finset.univ : Finset ↑H).finsuppAntidiag bs.flatten.length := by
    rw [Finset.mem_finsuppAntidiag]
    constructor
    · have hog := (Finset.mem_finsuppAntidiag.mp og.2).1
      change (∑ x : ↑H, z x) = bs.flatten.length
      have hzero : og.1 none = 0 := by simp [og, gapsOfBlocks, blockLengths]
      have hsum : (∑ x : ↑H, og.1 (some x)) = bs.flatten.length := by
        have hh : (∑ x : Option ↑H, og.1 x) = bs.flatten.length := by
          simpa using hog
        rw [Fintype.sum_option, hzero, zero_add] at hh
        exact hh
      simpa [z] using hsum
    · exact Finset.subset_univ _
  refine ⟨⟨z, hz⟩, ?_⟩
  change U.map (fun x => if hx : x ∈ H then z ⟨x, hx⟩ else 0) =
    bs.map List.length
  have halign := blockLengths_aligned H s [] bs hlen'
  simpa [z, og, gapsOfBlocks, U] using halign

/-- Every nonexceptional avoiding word is generated by decorated 23-pattern data. -/
theorem minAvoider_surjective {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n)
    (p : MinAvoiders n m) :
    ∃ r : ℕ, ∃ d : TwentyThreeData n m r,
      minAvoiderOfData hm hmn d = p := by
  rcases minAvoider_normal_form hm hmn p with
    ⟨u, bs, heq, hu, hlen, hbs⟩
  let R := bs.flatten.toFinset
  let r := bs.flatten.length
  rcases normal_support_split hmn.le p heq hu hlen hbs with
    ⟨hRsub, huSupport, huNodup, hrhoNodup⟩
  rcases normal_lower_words hmn.le p heq hu hlen hbs with
    ⟨rho, sigma, hrho, hsigma⟩
  rcases upper_gaps_of_blocks n m bs hlen with ⟨g, hg⟩
  have hRcard : R.card = r := by
    simpa [R, r] using (List.toFinset_card_of_nodup hrhoNodup)
  let R' : ↑((lowerSupport m).powersetCard r) :=
    ⟨R, Finset.mem_powersetCard.mpr ⟨hRsub, hRcard⟩⟩
  let d : TwentyThreeData n m r :=
    { R := R', rho := rho, sigma := sigma, gaps := g }
  refine ⟨r, d, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change twentyThreeList d = p.1.1
  rw [heq]
  change sigma.1.1 ++ m :: afterBlocks (upperDescending n m)
    ((upperGapSizes n m g).splitLengths rho.1) =
    u ++ m :: afterBlocks (upperDescending n m) bs
  rw [hsigma, hrho, hg, splitLengths_map_length_flatten]

/-- A run of unselected entries before the next selected entry is unique. -/
theorem filler_prefix_unique {α : Type*} (P : α → Bool) {a : α}
    (ha : P a) {b c v w : List α}
    (hb : ∀ x ∈ b, ¬ P x) (hc : ∀ x ∈ c, ¬ P x)
    (heq : b ++ a :: v = c ++ a :: w) : b = c ∧ v = w := by
  induction b generalizing c with
  | nil =>
      cases c with
      | nil => simpa using heq
      | cons y ys =>
          have hay : a = y := by
            simpa only [List.nil_append, List.cons_append, List.head?_cons,
              Option.some.injEq] using
              congrArg List.head? heq
          exact (hc y (by simp) (hay ▸ ha)).elim
  | cons x xs ih =>
      cases c with
      | nil =>
          have hxa : x = a := by
            simpa only [List.cons_append, List.nil_append, List.head?_cons,
              Option.some.injEq] using
              congrArg List.head? heq
          exact (hb x (by simp) (hxa ▸ ha)).elim
      | cons y ys =>
          have hxy : x = y := by
            have hh := congrArg List.head? heq
            simpa only [List.cons_append, List.head?_cons, Option.some.injEq] using hh
          subst y
          have htail : xs ++ a :: v = ys ++ a :: w := by
            have hh := heq
            simp only [List.cons_append, List.cons.injEq] at hh
            exact hh.2
          have hxs : ∀ z ∈ xs, ¬P z := by
            intro z hz
            exact hb z (by simp [hz])
          have hys : ∀ z ∈ ys, ¬P z := by
            intro z hz
            exact hc z (by simp [hz])
          rcases ih hxs hys htail with ⟨rfl, hvw⟩
          exact ⟨rfl, hvw⟩

/-- The filler blocks of an interleaving are uniquely determined by its word. -/
theorem afterBlocks_unique {α : Type*} (P : α → Bool)
    {s : List α} {bs cs : List (List α)}
    (hs : ∀ a ∈ s, P a)
    (hblen : bs.length = s.length) (hclen : cs.length = s.length)
    (hb : ∀ b ∈ bs, ∀ x ∈ b, ¬P x)
    (hc : ∀ c ∈ cs, ∀ x ∈ c, ¬P x)
    (heq : afterBlocks s bs = afterBlocks s cs) : bs = cs := by
  induction s generalizing bs cs with
  | nil =>
      have hbs : bs = [] := List.eq_nil_of_length_eq_zero hblen
      have hcs : cs = [] := List.eq_nil_of_length_eq_zero hclen
      simp [hbs, hcs]
  | cons a s ih =>
      rcases bs with _ | ⟨b, bs⟩
      · simp at hblen
      rcases cs with _ | ⟨c, cs⟩
      · simp at hclen
      have hblen' : bs.length = s.length := by simpa using hblen
      have hclen' : cs.length = s.length := by simpa using hclen
      have hb' : ∀ d ∈ bs, ∀ x ∈ d, ¬P x := by
        intro d hd x hx
        exact hb d (by simp [hd]) x hx
      have hc' : ∀ d ∈ cs, ∀ x ∈ d, ¬P x := by
        intro d hd x hx
        exact hc d (by simp [hd]) x hx
      have hb0 : ∀ x ∈ b, ¬P x := hb b (by simp)
      have hc0 : ∀ x ∈ c, ¬P x := hc c (by simp)
      cases s with
      | nil =>
          have hbn : bs = [] := List.eq_nil_of_length_eq_zero hblen'
          have hcn : cs = [] := List.eq_nil_of_length_eq_zero hclen'
          subst bs
          subst cs
          simp [afterBlocks] at heq
          exact congrArg List.singleton heq
      | cons z zs =>
          have hz : P z := hs z (by simp)
          have htail :
              b ++ afterBlocks (z :: zs) bs =
                c ++ afterBlocks (z :: zs) cs := by
            have hh := heq
            simp only [afterBlocks, List.cons.injEq] at hh
            exact hh.2
          have hrest : ∃ v w,
              afterBlocks (z :: zs) bs = z :: v ∧
              afterBlocks (z :: zs) cs = z :: w := by
            cases bs with
            | nil =>
                cases cs with
                | nil => exact ⟨zs, zs, rfl, rfl⟩
                | cons c' cs' => exact ⟨zs, c' ++ afterBlocks zs cs', rfl, rfl⟩
            | cons b' bs' =>
                cases cs with
                | nil => exact ⟨b' ++ afterBlocks zs bs', zs, rfl, rfl⟩
                | cons c' cs' =>
                    exact ⟨b' ++ afterBlocks zs bs',
                      c' ++ afterBlocks zs cs', rfl, rfl⟩
          rcases hrest with ⟨v, w, hv, hw⟩
          rw [hv, hw] at htail
          rcases filler_prefix_unique P hz hb0 hc0 htail with ⟨rfl, hvw⟩
          have hinner : afterBlocks (z :: zs) bs =
              afterBlocks (z :: zs) cs := by simpa [hv, hw] using hvw
          have hs' : ∀ x ∈ z :: zs, P x := by
            intro x hx
            exact hs x (by simp [hx])
          have hbsEq := ih hs' hblen' hclen' hb' hc' hinner
          exact congrArg (List.cons b) hbsEq

/-- Gap coordinates are recovered from their values in the upper skeleton order. -/
theorem upperGapSizes_injective {n m r : ℕ}
    {g h : GapsOn ↑(upperSupport n m) r}
    (heq : upperGapSizes n m g = upperGapSizes n m h) : g = h := by
  apply Subtype.ext
  ext x
  let U := upperDescending n m
  let H := upperSupport n m
  have hUperm : U.Perm H.toList := by
    apply List.perm_of_nodup_nodup_toFinset_eq
    · exact List.nodup_reverse.mpr List.nodup_range'
    · exact H.nodup_toList
    · simp [U, upperDescending, H, upperSupport]
  have hxU : x.1 ∈ U := hUperm.mem_iff.mpr (Finset.mem_toList.mpr x.2)
  let i := U.idxOf x.1
  have hi : i < U.length := List.idxOf_lt_length_of_mem hxU
  have hiG : i < (upperGapSizes n m g).length := by
    simpa [upperGapSizes] using hi
  have hiH : i < (upperGapSizes n m h).length := by
    simpa [upperGapSizes] using hi
  have hval := congrArg (fun l : List ℕ => l.getD i 0) heq
  have hUg : U.getD i 0 = x.1 := by
    rw [List.getD_eq_getElem (l := U) 0 hi, List.getElem_idxOf hi]
  have hreadG :
      (upperGapSizes n m g).getD i 0 = g.1 x := by
    rw [List.getD_eq_getElem (l := upperGapSizes n m g) 0 hiG]
    simp only [upperGapSizes, List.getElem_map]
    rw [List.getElem_idxOf hi]
    simp [x.2]
  have hreadH :
      (upperGapSizes n m h).getD i 0 = h.1 x := by
    rw [List.getD_eq_getElem (l := upperGapSizes n m h) 0 hiH]
    simp only [upperGapSizes, List.getElem_map]
    rw [List.getElem_idxOf hi]
    simp [x.2]
  rw [hreadG, hreadH] at hval
  exact hval

/-- Splitting a duplicate-free word at the first occurrence of `m` is unique. -/
theorem split_at_member_unique {m : ℕ} {u u' v v' : List ℕ}
    (hnot : m ∉ u) (hnot' : m ∉ u')
    (heq : u ++ m :: v = u' ++ m :: v') : u = u' ∧ v = v' := by
  induction u generalizing u' with
  | nil =>
      cases u' with
      | nil => simpa using heq
      | cons x xs =>
          have hmx : m = x := by
            have hh := congrArg List.head? heq
            simpa only [List.nil_append, List.cons_append, List.head?_cons,
              Option.some.injEq] using hh
          exact (hnot' (by simp [hmx])).elim
  | cons x xs ih =>
      cases u' with
      | nil =>
          have hxm : x = m := by
            have hh := congrArg List.head? heq
            simpa only [List.cons_append, List.nil_append, List.head?_cons,
              Option.some.injEq] using hh
          exact (hnot (by simp [hxm])).elim
      | cons y ys =>
          have hxy : x = y := by
            have hh := congrArg List.head? heq
            simpa only [List.cons_append, List.head?_cons,
              Option.some.injEq] using hh
          subst y
          have htail : xs ++ m :: v = ys ++ m :: v' := by
            have hh := heq
            simp only [List.cons_append, List.cons.injEq] at hh
            exact hh.2
          have hnxs : m ∉ xs := by
            intro h
            exact hnot (by simp [h])
          have hnys : m ∉ ys := by
            intro h
            exact hnot' (by simp [h])
          rcases ih hnxs hnys htail with ⟨rfl, hv⟩
          exact ⟨rfl, hv⟩

/-- Every block in the forward construction contains only lower entries. -/
theorem data_normal_bounds {n m r : ℕ} (d : TwentyThreeData n m r) :
    let bs := (upperGapSizes n m d.gaps).splitLengths d.rho.1
    (∀ x ∈ d.sigma.1.1, x < m) ∧
      bs.length = (upperDescending n m).length ∧
      (∀ b ∈ bs, ∀ x ∈ b, x < m) ∧
      bs.flatten = d.rho.1 := by
  let bs := (upperGapSizes n m d.gaps).splitLengths d.rho.1
  have hRsub : d.R.1 ⊆ lowerSupport m :=
    (Finset.mem_powersetCard.mp d.R.2).1
  have hRcard : d.R.1.card = r := (Finset.mem_powersetCard.mp d.R.2).2
  have hrho : d.rho.1.Perm d.R.1.toList := by
    simpa [words, List.mem_permutations] using d.rho.2
  have hsigma : d.sigma.1.1.Perm (lowerSupport m \ d.R.1).toList := by
    simpa [words, List.mem_permutations] using d.sigma.1.2
  have hpre : ∀ x ∈ d.sigma.1.1, x < m := by
    intro x hx
    have hxL := Finset.mem_toList.mp (hsigma.mem_iff.mp hx)
    have hxLow := (Finset.mem_sdiff.mp hxL).1
    simp [lowerSupport, List.mem_range'] at hxLow
    omega
  have hgap := upperGapSizes_length_sum n m d.gaps
  have hlen : bs.length = (upperDescending n m).length := by
    simp [bs, upperDescending, hgap.1]
  have hflat : bs.flatten = d.rho.1 := by
    apply List.flatten_splitLengths
    simp [hrho.length_eq, hRcard, hgap.2]
  have hblocks : ∀ b ∈ bs, ∀ x ∈ b, x < m := by
    intro b hb x hx
    have hxrho : x ∈ d.rho.1 := by
      rw [← hflat]
      exact List.mem_flatten.mpr ⟨b, hb, hx⟩
    have hxR := Finset.mem_toList.mp (hrho.mem_iff.mp hxrho)
    have hxLow := hRsub hxR
    simp [lowerSupport, List.mem_range'] at hxLow
    omega
  exact ⟨hpre, hlen, hblocks, hflat⟩

/-- Decorated data are uniquely determined by their produced word, even when
    the number of selected lower values is not known in advance. -/
theorem twentyThreeList_unique {n m r₁ r₂ : ℕ}
    (d₁ : TwentyThreeData n m r₁) (d₂ : TwentyThreeData n m r₂)
    (heq : twentyThreeList d₁ = twentyThreeList d₂) :
    ∃ _h : r₁ = r₂, HEq d₁ d₂ := by
  let bs₁ := (upperGapSizes n m d₁.gaps).splitLengths d₁.rho.1
  let bs₂ := (upperGapSizes n m d₂.gaps).splitLengths d₂.rho.1
  rcases data_normal_bounds d₁ with ⟨hpre₁, hlen₁, hblocks₁, hflat₁⟩
  rcases data_normal_bounds d₂ with ⟨hpre₂, hlen₂, hblocks₂, hflat₂⟩
  have hnot₁ : m ∉ d₁.sigma.1.1 := by
    intro h
    exact (Nat.lt_irrefl m) (hpre₁ m h)
  have hnot₂ : m ∉ d₂.sigma.1.1 := by
    intro h
    exact (Nat.lt_irrefl m) (hpre₂ m h)
  have hsplit : d₁.sigma.1.1 = d₂.sigma.1.1 ∧
      afterBlocks (upperDescending n m) bs₁ =
        afterBlocks (upperDescending n m) bs₂ := by
    have hh : d₁.sigma.1.1 ++ m :: afterBlocks (upperDescending n m) bs₁ =
        d₂.sigma.1.1 ++ m :: afterBlocks (upperDescending n m) bs₂ := by
      simpa [twentyThreeList, bs₁, bs₂] using heq
    exact split_at_member_unique hnot₁ hnot₂ hh
  have hU : ∀ x ∈ upperDescending n m, decide (m < x) := by
    intro x hx
    simp only [decide_eq_true_eq]
    simp [upperDescending, List.mem_range'] at hx
    omega
  have hblocks₁' : ∀ b ∈ bs₁, ∀ x ∈ b, ¬ decide (m < x) := by
    intro b hb x hx
    simpa using Nat.not_lt_of_ge (hblocks₁ b hb x hx).le
  have hblocks₂' : ∀ b ∈ bs₂, ∀ x ∈ b, ¬ decide (m < x) := by
    intro b hb x hx
    simpa using Nat.not_lt_of_ge (hblocks₂ b hb x hx).le
  have hbs : bs₁ = bs₂ :=
    afterBlocks_unique (fun x => decide (m < x)) hU hlen₁ hlen₂
      hblocks₁' hblocks₂' hsplit.2
  have hrho : d₁.rho.1 = d₂.rho.1 := by
    calc
      d₁.rho.1 = bs₁.flatten := hflat₁.symm
      _ = bs₂.flatten := congrArg List.flatten hbs
      _ = d₂.rho.1 := hflat₂
  have hlenR₁ : d₁.rho.1.length = r₁ := by
    have hp : d₁.rho.1.Perm d₁.R.1.toList := by
      simpa [words, List.mem_permutations] using d₁.rho.2
    rw [hp.length_eq]
    simpa using (Finset.mem_powersetCard.mp d₁.R.2).2
  have hlenR₂ : d₂.rho.1.length = r₂ := by
    have hp : d₂.rho.1.Perm d₂.R.1.toList := by
      simpa [words, List.mem_permutations] using d₂.rho.2
    rw [hp.length_eq]
    simpa using (Finset.mem_powersetCard.mp d₂.R.2).2
  have hr : r₁ = r₂ := by rw [← hlenR₁, hrho, hlenR₂]
  subst r₂
  have hR₁ : d₁.R.1 = d₁.rho.1.toFinset := by
    have hp : d₁.rho.1.Perm d₁.R.1.toList := by
      simpa [words, List.mem_permutations] using d₁.rho.2
    ext x
    simpa using (hp.mem_iff (a := x)).symm
  have hR₂ : d₂.R.1 = d₂.rho.1.toFinset := by
    have hp : d₂.rho.1.Perm d₂.R.1.toList := by
      simpa [words, List.mem_permutations] using d₂.rho.2
    ext x
    simpa using (hp.mem_iff (a := x)).symm
  have hR : d₁.R = d₂.R := by
    apply Subtype.ext
    rw [hR₁, hR₂, hrho]
  have hsizes₁ : upperGapSizes n m d₁.gaps = bs₁.map List.length := by
    have hsum := (upperGapSizes_length_sum n m d₁.gaps).2
    have hsuff : (upperGapSizes n m d₁.gaps).sum ≤ d₁.rho.1.length := by
      omega
    exact (List.map_splitLengths_length d₁.rho.1
      (upperGapSizes n m d₁.gaps) hsuff).symm
  have hsizes₂ : upperGapSizes n m d₂.gaps = bs₂.map List.length := by
    have hsum := (upperGapSizes_length_sum n m d₂.gaps).2
    have hsuff : (upperGapSizes n m d₂.gaps).sum ≤ d₂.rho.1.length := by
      omega
    exact (List.map_splitLengths_length d₂.rho.1
      (upperGapSizes n m d₂.gaps) hsuff).symm
  have hgaps : d₁.gaps = d₂.gaps :=
    upperGapSizes_injective (hsizes₁.trans ((congrArg (List.map List.length) hbs).trans
      hsizes₂.symm))
  have hd : d₁ = d₂ := by
    cases d₁ with
    | mk R₁ rho₁ sigma₁ gaps₁ =>
      cases d₂ with
      | mk R₂ rho₂ sigma₂ gaps₂ =>
        simp only at hR hrho hsplit hgaps
        subst R₂
        have hrhoEq : rho₁ = rho₂ := Subtype.ext hrho
        subst rho₂
        have hsigmaEq : sigma₁ = sigma₂ := by
          apply Subtype.ext
          apply Subtype.ext
          exact hsplit.1
        subst sigma₂
        subst gaps₂
        rfl
  exact ⟨rfl, hd ▸ HEq.rfl⟩

/-- All admissible choices of the filler subset size. -/
abbrev TwentyThreeFamily (n m : ℕ) :=
  Σ r : Fin m, TwentyThreeData n m r.1

/-- The decorated family maps into the smallest-fixed-point stratum. -/
def twentyThreeFamilyMap {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n) :
    TwentyThreeFamily n m → MinAvoiders n m
  | ⟨r, d⟩ => minAvoiderOfData hm hmn d

/-- The nonexceptional stratum is in bijection with its decorated family. -/
def twentyThreeFamilyEquiv {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n) :
    TwentyThreeFamily n m ≃ MinAvoiders n m := by
  refine Equiv.ofBijective (twentyThreeFamilyMap hm hmn) ⟨?_, ?_⟩
  · rintro ⟨r₁, d₁⟩ ⟨r₂, d₂⟩ heq
    have hlist : twentyThreeList d₁ = twentyThreeList d₂ :=
      congrArg (fun p : MinAvoiders n m => p.1.1) heq
    rcases twentyThreeList_unique d₁ d₂ hlist with ⟨hr, hd⟩
    have hrFin : r₁ = r₂ := Fin.ext hr
    cases hrFin
    cases hd
    rfl
  · intro p
    rcases minAvoider_surjective hm hmn p with ⟨r, d, hd⟩
    have hr : r < m := by
      have hRsub : d.R.1 ⊆ lowerSupport m :=
        (Finset.mem_powersetCard.mp d.R.2).1
      have hRcard : d.R.1.card = r :=
        (Finset.mem_powersetCard.mp d.R.2).2
      have hcard := Finset.card_le_card hRsub
      rw [hRcard] at hcard
      have hlow : (lowerSupport m).card = m - 1 := by
        simp [lowerSupport, List.toFinset_card_of_nodup List.nodup_range']
      rw [hlow] at hcard
      omega
    exact ⟨⟨⟨r, hr⟩, d⟩, hd⟩

end

end D5.S3.Combinatorics.ArrowWilfTwentyThreeInverse
