/- GID: D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiSymmetricTargets
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiSymmetricTargets
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: Symmetric numerical sets with Frobenius number 2h-1 number 2^(h-1); half of them avoid the row-deletion image. -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#456)
escape_witness: count (a symmetric numerical set with Frobenius number 2h - 1 is determined by
  its gaps below h, and every subset of {1, ..., h - 1} occurs), with gaps_eq_of_low and
  sym_build as its injectivity and surjectivity halves.
proof_shape:
  low, build, buildSet: private definitions; consumer: count.
  gap_pos, gap_le, sym_iff, ite_t, ite_f, mem_build, top_mem_build: bind-only helpers;
    consumers: frob_odd, low_mem,
    gaps_eq_of_low, frob_build, sym_build, low_build.
  frob_odd: content; consumer: result.
  low_mem, frob_build, low_build: content helpers; consumer: count.
  gaps_eq_of_low, sym_build: content; consumer: count.
  count: content; consumer: result.
  result: content.
Direct frozen dependencies: D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation
  (NumericalSet, members, frobenius, Semigroup, Symmetric, AlmostSymmetric, phi, phi_omits_one);
  D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiOrdinaryFiber (ordinary, result).
Search record (§3.1): the frozen Partitions modules prove the omission of 1, the fixed points
  and the ordinary fiber; no D5 module or pinned Mathlib declaration counts symmetric numerical
  sets by Frobenius number.
-/

import D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiOrdinaryFiber
import Mathlib.Tactic

/-! # Symmetric targets of pseudo-Frobenius row deletion

A symmetric numerical set has odd Frobenius number. For `h ≥ 1` there are exactly `2^(h-1)`
symmetric numerical sets with Frobenius number `2h - 1`, one for each choice of gaps among
`1, …, h - 1`. For `h ≥ 2` exactly `2^(h-2)` of them contain `1` and `2^(h-2)` omit it; none of
those containing `1` is the row deletion of a numerical semigroup. The unique numerical set with Frobenius number `1` is
`ℕ₀ ∖ {1}`, which is the row deletion of an almost symmetric semigroup.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiSymmetricTargets

open D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation (NumericalSet members frobenius
  Semigroup Symmetric AlmostSymmetric phi phi_omits_one)

private theorem gap_pos (U : NumericalSet) {n : ℕ} (hn : n ∈ U.gaps) : 1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; exact absurd hn U.zero_not_gap
  · exact h

private theorem gap_le (U : NumericalSet) {n : ℕ} (hn : n ∈ U.gaps) : n ≤ frobenius U :=
  Finset.le_max' _ _ hn

private theorem sym_iff (U : NumericalSet) (hU : Symmetric U) {a : ℕ} (ha : a ≤ frobenius U) :
    a ∈ U.gaps ↔ frobenius U - a ∉ U.gaps := by
  have h := hU a ha
  change (a ∉ U.gaps ↔ ¬ (frobenius U - a ∉ U.gaps)) at h
  tauto

private theorem ite_t {c : Prop} [Decidable c] {a b : Prop} (hc : c) :
    (if c then a else b) = a := by simp [hc]

private theorem ite_f {c : Prop} [Decidable c] {a b : Prop} (hc : ¬ c) :
    (if c then a else b) = b := by simp [hc]

/-- A symmetric numerical set has odd Frobenius number. -/
private theorem frob_odd (U : NumericalSet) (hU : Symmetric U) (k : ℕ) : frobenius U ≠ 2 * k := by
  intro hk
  have h := sym_iff U hU (a := k) (by omega)
  rw [show frobenius U - k = k by omega] at h
  tauto

/-- The gaps below `h`. -/
private def low (h : ℕ) (U : NumericalSet) : Finset ℕ := U.gaps.filter (· < h)

/-- The gap set with Frobenius number `2h - 1` whose gaps below `h` are `B`. -/
private def build (h : ℕ) (B : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 (2 * h - 1)).filter (fun n => if n < h then n ∈ B else 2 * h - 1 - n ∉ B)

private theorem mem_build {h : ℕ} {B : Finset ℕ} {n : ℕ} : n ∈ build h B ↔
    1 ≤ n ∧ n ≤ 2 * h - 1 ∧ (if n < h then n ∈ B else 2 * h - 1 - n ∉ B) := by
  rw [build, Finset.mem_filter, Finset.mem_Icc, and_assoc]

private theorem top_mem_build {h : ℕ} (hh : 1 ≤ h) {B : Finset ℕ}
    (hB : B ⊆ Finset.Icc 1 (h - 1)) : 2 * h - 1 ∈ build h B := by
  refine mem_build.mpr ⟨by omega, le_rfl, ?_⟩
  rw [ite_f (c := 2 * h - 1 < h) (by omega), Nat.sub_self]
  intro h0
  have := Finset.mem_Icc.mp (hB h0)
  omega

/-- The numerical set built from a choice of gaps below `h`. -/
private def buildSet (h : ℕ) (hh : 1 ≤ h) (B : Finset ℕ) (hB : B ⊆ Finset.Icc 1 (h - 1)) :
    NumericalSet where
  gaps := build h B
  proper := ⟨_, top_mem_build hh hB⟩
  zero_not_gap := fun h0 => by have := (mem_build.mp h0).1; omega

private theorem frob_build (h : ℕ) (hh : 1 ≤ h) (B : Finset ℕ)
    (hB : B ⊆ Finset.Icc 1 (h - 1)) : frobenius (buildSet h hh B hB) = 2 * h - 1 :=
  le_antisymm (Finset.max'_le _ _ _ fun _ hn => (mem_build.mp hn).2.1)
    (Finset.le_max' _ _ (top_mem_build hh hB))

private theorem sym_build (h : ℕ) (hh : 1 ≤ h) (B : Finset ℕ)
    (hB : B ⊆ Finset.Icc 1 (h - 1)) : Symmetric (buildSet h hh B hB) := by
  intro a ha
  rw [frob_build] at ha ⊢
  change (a ∉ build h B ↔ ¬ (2 * h - 1 - a ∉ build h B))
  rw [not_not, mem_build, mem_build]
  have hB' : ∀ n, n ∈ B → 1 ≤ n ∧ n ≤ h - 1 := fun n hn => Finset.mem_Icc.mp (hB hn)
  rcases Nat.lt_or_ge a 1 with h0 | h1
  · obtain rfl : a = 0 := by omega
    rw [Nat.sub_zero, ite_t (c := 0 < h) (by omega), ite_f (c := 2 * h - 1 < h) (by omega),
      Nat.sub_self]
    have h0B : (0 : ℕ) ∉ B := fun h0 => by have := hB' 0 h0; omega
    have hn : ¬ (1 ≤ 0) := by omega
    have h1f : 1 ≤ 2 * h - 1 := by omega
    tauto
  rcases Nat.lt_or_ge a h with hlo | hhi
  · rw [ite_t hlo, ite_f (c := 2 * h - 1 - a < h) (by omega), show 2 * h - 1 - (2 * h - 1 - a) = a by omega]
    have e1 : 1 ≤ 2 * h - 1 - a := by omega
    have e2 : 2 * h - 1 - a ≤ 2 * h - 1 := by omega
    tauto
  rcases Nat.lt_or_ge a (2 * h - 1) with hlt | hge
  · rw [ite_f (c := a < h) (by omega), ite_t (c := 2 * h - 1 - a < h) (by omega)]
    have e1 : 1 ≤ 2 * h - 1 - a := by omega
    have e2 : 2 * h - 1 - a ≤ 2 * h - 1 := by omega
    tauto
  · obtain rfl : a = 2 * h - 1 := by omega
    rw [ite_f (c := 2 * h - 1 < h) (by omega), Nat.sub_self]
    have h0B : (0 : ℕ) ∉ B := fun h0 => by have := hB' 0 h0; omega
    have hn : ¬ (1 ≤ 0) := by omega
    tauto

private theorem low_build (h : ℕ) (hh : 1 ≤ h) (B : Finset ℕ)
    (hB : B ⊆ Finset.Icc 1 (h - 1)) : low h (buildSet h hh B hB) = B := by
  ext n
  change n ∈ (build h B).filter (· < h) ↔ n ∈ B
  rw [Finset.mem_filter, mem_build]
  constructor
  · rintro ⟨⟨_, _, hm⟩, hn⟩
    rwa [ite_t hn] at hm
  · intro hn
    have := Finset.mem_Icc.mp (hB hn)
    exact ⟨⟨by omega, by omega, by rwa [ite_t (c := n < h) (by omega)]⟩, by omega⟩

private theorem low_mem (h : ℕ) (U : NumericalSet) :
    low h U ∈ (Finset.Icc 1 (h - 1)).powerset := by
  rw [Finset.mem_powerset]
  intro n hn
  obtain ⟨hg, hlt⟩ := Finset.mem_filter.mp hn
  exact Finset.mem_Icc.mpr ⟨gap_pos U hg, by omega⟩

private theorem gaps_eq_of_low (h : ℕ) (U V : NumericalSet) (hU : Symmetric U)
    (hV : Symmetric V) (hfU : frobenius U = 2 * h - 1) (hfV : frobenius V = 2 * h - 1)
    (hl : low h U = low h V) : U = V := by
  have key : ∀ n, n < h → (n ∈ U.gaps ↔ n ∈ V.gaps) := by
    intro n hn
    have e := Finset.ext_iff.mp hl n
    simpa only [low, Finset.mem_filter, hn, and_true] using e
  have hh : 1 ≤ h := by
    have := gap_pos U (Finset.max'_mem U.gaps U.proper)
    change 1 ≤ frobenius U at this
    omega
  have hg : U.gaps = V.gaps := by
    ext n
    rcases Nat.lt_or_ge n h with hn | hn
    · exact key n hn
    rcases Nat.lt_or_ge (2 * h - 1) n with hf | hf
    · constructor
      · intro hm; have := gap_le U hm; omega
      · intro hm; have := gap_le V hm; omega
    have hnU : n ≤ frobenius U := by rw [hfU]; exact hf
    have hnV : n ≤ frobenius V := by rw [hfV]; exact hf
    rw [sym_iff U hU hnU, sym_iff V hV hnV, hfU, hfV]
    exact not_congr (key (2 * h - 1 - n) (by omega))
  cases U
  cases V
  cases hg
  rfl

/-- A symmetric numerical set with Frobenius number `2h - 1` is determined by its gaps below
`h`, and every subset of `{1, …, h - 1}` occurs; any condition on those gaps is counted on the
subsets. -/
private theorem count (h : ℕ) (hh : 1 ≤ h) (Q : Finset ℕ → Prop) [DecidablePred Q] :
    {U : NumericalSet | Symmetric U ∧ frobenius U = 2 * h - 1 ∧ Q (low h U)}.ncard =
      ((Finset.Icc 1 (h - 1)).powerset.filter Q).card := by
  rw [← Set.ncard_coe_finset]
  apply Set.ncard_congr (fun U _ => low h U)
  · rintro U ⟨_, _, hq⟩
    exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨low_mem h U, hq⟩)
  · rintro U V ⟨hU, hfU, _⟩ ⟨hV, hfV, _⟩ hl
    exact gaps_eq_of_low h U V hU hV hfU hfV hl
  · intro B hB
    obtain ⟨hBp, hq⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hB)
    have hB' := Finset.mem_powerset.mp hBp
    refine ⟨buildSet h hh B hB', ⟨sym_build h hh B hB', frob_build h hh B hB', ?_⟩,
      low_build h hh B hB'⟩
    rw [low_build]
    exact hq

/-- Symmetric numerical sets have odd Frobenius number; those with Frobenius number `2h - 1`
number `2^(h-1)`. For `h ≥ 2`, exactly `2^(h-2)` of them contain `1` and `2^(h-2)` omit it, so at
least `2^(h-2)` lie outside the row-deletion image of every numerical semigroup. The only numerical set with
Frobenius number `1` is `ℕ₀ ∖ {1}`, the row deletion of an almost symmetric semigroup. -/
theorem result :
    (∀ (U : NumericalSet) (k : ℕ), Symmetric U → frobenius U ≠ 2 * k) ∧
    (∀ h : ℕ, 1 ≤ h →
      {U : NumericalSet | Symmetric U ∧ frobenius U = 2 * h - 1}.ncard = 2 ^ (h - 1)) ∧
    (∀ h : ℕ, 2 ≤ h →
      {U : NumericalSet | Symmetric U ∧ frobenius U = 2 * h - 1 ∧ 1 ∈ members U}.ncard =
        2 ^ (h - 2) ∧
      {U : NumericalSet | Symmetric U ∧ frobenius U = 2 * h - 1 ∧ 1 ∉ members U}.ncard =
        2 ^ (h - 2) ∧
      2 ^ (h - 2) ≤ {U : NumericalSet | Symmetric U ∧ frobenius U = 2 * h - 1 ∧
        ∀ S : NumericalSet, Semigroup S → phi S ≠ members U}.ncard) ∧
    (∀ U : NumericalSet, frobenius U = 1 →
      members U = {n | n ≠ 1} ∧ ∃ S : NumericalSet, AlmostSymmetric S ∧ phi S = members U) := by
  classical
  have hall : ∀ h : ℕ, 1 ≤ h →
      {U : NumericalSet | Symmetric U ∧ frobenius U = 2 * h - 1}.ncard = 2 ^ (h - 1) := by
    intro h hh
    have e := count h hh (fun _ => True)
    have hs : {U : NumericalSet | Symmetric U ∧ frobenius U = 2 * h - 1 ∧ True} =
        {U : NumericalSet | Symmetric U ∧ frobenius U = 2 * h - 1} := by
      ext U; simp only [Set.mem_ofPred_eq, and_true]
    rw [hs, Finset.filter_true_of_mem (fun _ _ => trivial), Finset.card_powerset,
      Nat.card_Icc] at e
    rw [e]
    all_goals congr 1
  refine ⟨fun U k hU => frob_odd U hU k, hall, ?_, ?_⟩
  · intro h hh
    have hf : (Finset.Icc 1 (h - 1)).powerset.filter (fun B => 1 ∉ B) =
        (Finset.Icc 2 (h - 1)).powerset := by
      ext B
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_iff, Finset.mem_Icc]
      constructor
      · rintro ⟨hs, h1⟩ n hn
        have := hs hn
        refine ⟨?_, this.2⟩
        by_contra hlt
        obtain rfl : n = 1 := by omega
        exact h1 hn
      · intro hs
        exact ⟨fun n hn => ⟨by have := hs hn; omega, (hs hn).2⟩,
          fun h1 => by have := hs h1; omega⟩
    have hone : {U : NumericalSet | Symmetric U ∧ frobenius U = 2 * h - 1 ∧ 1 ∈ members U}.ncard
        = 2 ^ (h - 2) := by
      have e := count h (by omega) (fun B => 1 ∉ B)
      have hs : {U : NumericalSet | Symmetric U ∧ frobenius U = 2 * h - 1 ∧ 1 ∉ low h U} =
          {U : NumericalSet | Symmetric U ∧ frobenius U = 2 * h - 1 ∧ 1 ∈ members U} := by
        ext U
        simp only [Set.mem_ofPred_eq, low, Finset.mem_filter, not_and]
        change _ ↔ _ ∧ _ ∧ 1 ∉ U.gaps
        constructor
        · rintro ⟨a, b, c⟩; exact ⟨a, b, fun h1 => c h1 (by omega)⟩
        · rintro ⟨a, b, c⟩; exact ⟨a, b, fun h1 _ => c h1⟩
      rw [hs, hf, Finset.card_powerset, Nat.card_Icc] at e
      rw [e]
      all_goals congr 1
    have hgap : {U : NumericalSet | Symmetric U ∧ frobenius U = 2 * h - 1 ∧ 1 ∉ members U}.ncard
        = 2 ^ (h - 2) := by
      have e := count h (by omega) (fun B => 1 ∈ B)
      have hs : {U : NumericalSet | Symmetric U ∧ frobenius U = 2 * h - 1 ∧ 1 ∈ low h U} =
          {U : NumericalSet | Symmetric U ∧ frobenius U = 2 * h - 1 ∧ 1 ∉ members U} := by
        ext U
        simp only [Set.mem_ofPred_eq, low, Finset.mem_filter]
        change _ ↔ _ ∧ _ ∧ ¬ (1 ∉ U.gaps)
        rw [not_not]
        constructor
        · rintro ⟨a, b, c, _⟩; exact ⟨a, b, c⟩
        · rintro ⟨a, b, c⟩; exact ⟨a, b, c, by omega⟩
      have hsplit := Finset.card_filter_add_card_filter_not
        (s := (Finset.Icc 1 (h - 1)).powerset) (fun B => 1 ∈ B)
      rw [hf, Finset.card_powerset, Finset.card_powerset, Nat.card_Icc, Nat.card_Icc] at hsplit
      rw [← hs, e]
      have h1 : h - 1 + 1 - 1 = h - 2 + 1 := by omega
      have h2 : h - 1 + 1 - 2 = h - 2 := by omega
      rw [h1, h2, pow_succ] at hsplit
      omega
    refine ⟨hone, hgap, ?_⟩
    rw [← hone]
    have hfin : {U : NumericalSet | Symmetric U ∧ frobenius U = 2 * h - 1}.Finite := by
      apply Set.finite_of_ncard_pos
      rw [hall h (by omega)]
      positivity
    apply Set.ncard_le_ncard _ (hfin.subset fun U hU => ⟨hU.1, hU.2.1⟩)
    rintro U ⟨hU, hf, h1⟩
    refine ⟨hU, hf, fun S hS he => phi_omits_one S hS ?_⟩
    rw [he]
    exact h1
  · intro U hU
    have hg : ∀ n, n ∈ U.gaps ↔ n = 1 := by
      intro n
      constructor
      · intro hn
        have := gap_pos U hn
        have := gap_le U hn
        omega
      · rintro rfl
        rw [← hU]
        exact Finset.max'_mem _ _
    have hm : members U = {n | n ≠ 1} := by
      ext n
      change n ∉ U.gaps ↔ n ≠ 1
      rw [hg]
    have ho := (DelgadoSuerYesilPhiOrdinaryFiber.result).2 2 le_rfl
    exact ⟨hm, _, ho.2.1, by rw [hm]; exact ho.2.2.2.2⟩

end D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiSymmetricTargets
