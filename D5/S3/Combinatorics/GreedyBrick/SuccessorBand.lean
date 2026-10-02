/- GID: D5/S3/Combinatorics/GreedyBrick/SuccessorBand
   generality: G
   mirror-B: D5/B/S3/Combinatorics/GreedyBrick/SuccessorBand
   mirror-E: none(waiver:unbounded-chronological-induction)
   anchors: [mathlib/module/Mathlib.Data.Finset.Card, mathlib/module/Mathlib.Order.Interval.Finset.Nat]
   utility: none
   digest: Exact-reset event histories satisfy the successor birth band by chronological predecessor injection. -/

import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Monotone.Basic
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GreedyBrick.SuccessorBand

/-- Finite capacities at a rest endpoint. Bin i occupies list index i-1;
absent bins are never assigned a default capacity. -/
structure RestState where
  endpoint : ℕ
  capacity : List ℕ
  bounded : ∀ c ∈ capacity, c ≤ endpoint

/-- Exact first-zero rest-event relation. Prefix positivity enforces that k
is the least zero, or the new bin h+1 if all old capacities are positive.
Every target coordinate is covered by prefix, reset, or suffix clauses.
This definition does not assert that the literal row process realizes it. -/
structure RestEventStep (s t : RestState) (k : ℕ) : Prop where
  label_pos : 0 < k
  label_le : k ≤ s.capacity.length + 1
  endpoint_eq : t.endpoint = s.endpoint + k
  height_eq : t.capacity.length = max s.capacity.length k
  prefix_pos : ∀ j : Fin s.capacity.length, j.val + 1 < k →
    0 < s.capacity.get j
  first_zero : k ≤ s.capacity.length → s.capacity[k - 1]? = some 0
  prefix_decrement : ∀ j : Fin s.capacity.length, j.val + 1 < k →
    t.capacity[j.val]? = some (s.capacity.get j - 1)
  reset : t.capacity[k - 1]? = some t.endpoint
  suffix_unchanged : ∀ j : Fin s.capacity.length, k < j.val + 1 →
    t.capacity[j.val]? = some (s.capacity.get j)

/-- Event indices are chronological ranks; endpoints are actual brick lengths.
`birth h` is used only at positive heights. `pred` is used only at renewals. -/
structure EventSequence where
  endpoint : ℕ → ℕ
  bin : ℕ → ℕ
  height : ℕ → ℕ
  birth : ℕ → ℕ
  pred : ℕ → ℕ

/-- A repeated event at its bin, rather than that bin's unique birth. -/
def EventSequence.Renewal (E : EventSequence) (t : ℕ) : Prop :=
  t ≠ E.birth (E.bin t)

/-- Higher-bin renewals strictly before the indicated event. -/
noncomputable def higherRenewals (E : EventSequence) (i t : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range t).filter fun g => i < E.bin g ∧ E.Renewal g

/-- Source obligations for the rest-event history. No band or reciprocity
statement is a field. The balance is the subtraction-free form of
`n = (H-h) + (rho(f)-rho(e))` for an immediate same-bin pair. -/
structure EventLaws (E : EventSequence) : Prop where
  bin_pos : ∀ t, 0 < E.bin t
  bin_le_height : ∀ t, E.bin t ≤ E.height t
  height_mono : Monotone E.height
  birth_height : ∀ h, 0 < h → E.height (E.birth h) = h
  birth_bin : ∀ h, 0 < h → E.bin (E.birth h) = h
  birth_cut : ∀ h, 0 < h → ∀ t, E.height t < h ↔ t < E.birth h
  endpoint_step : ∀ t, E.endpoint (t + 1) = E.endpoint t + E.bin (t + 1)
  pred_lt : ∀ f, E.Renewal f → E.pred f < f
  pred_bin : ∀ f, E.Renewal f → E.bin (E.pred f) = E.bin f
  pred_immediate : ∀ f, E.Renewal f → ∀ g,
    E.pred f < g → g < f → E.bin g ≠ E.bin f
  reset_balance : ∀ f, E.Renewal f →
    E.endpoint (E.pred f) + E.height (E.pred f) +
      (higherRenewals E (E.bin f) (E.pred f)).card =
    E.height f + (higherRenewals E (E.bin f) f).card

/-- Every renewal's immediate predecessor has height h and its renewal has
height H in [b_h,b_(h+1)), with b_h the actual endpoint of birth h.
The substantive lower bound is a strong chronological induction: under a
first violation, the injective predecessor pairing lands before birth h,
where too few higher events can account for the exact reset capacity. -/
theorem successor_band (E : EventSequence) (L : EventLaws E)
    (f : ℕ) (hf : E.Renewal f) :
    E.endpoint (E.birth (E.height (E.pred f))) ≤ E.height f ∧
      E.height f < E.endpoint (E.birth (E.height (E.pred f) + 1)) := by
  classical
  have endpoint_mono : Monotone E.endpoint :=
    monotone_nat_of_le_succ fun t => by rw [L.endpoint_step]; omega
  have height_pos (t : ℕ) : 0 < E.height t :=
    lt_of_lt_of_le (L.bin_pos t) (L.bin_le_height t)
  have birth_before (t : ℕ) : E.birth (E.height t) ≤ t := by
    by_contra hh
    have ht : t < E.birth (E.height t) := by omega
    have := (L.birth_cut (E.height t) (height_pos t) t).mpr ht
    omega
  have pred_injective : ∀ a, E.Renewal a → ∀ b, E.Renewal b →
      E.pred a = E.pred b → a = b := by
    intro a ha b hb hab
    have hbins : E.bin a = E.bin b := by
      rw [← L.pred_bin a ha, ← L.pred_bin b hb, hab]
    rcases lt_trichotomy a b with hlt | heq | hgt
    · exact False.elim ((L.pred_immediate b hb a
        (by rw [← hab]; exact L.pred_lt a ha) hlt) hbins)
    · exact heq
    · exact False.elim ((L.pred_immediate a ha b
        (by rw [hab]; exact L.pred_lt b hb) hgt) hbins.symm)
  have lower : ∀ t, E.Renewal t →
      E.endpoint (E.birth (E.height (E.pred t))) ≤ E.height t := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro ht
      by_contra bad
      let e := E.pred t
      let i := E.bin t
      let h := E.height e
      have hh : 0 < h := height_pos e
      have hbad : E.height t < E.endpoint (E.birth h) := by
        change ¬ E.endpoint (E.birth h) ≤ E.height t at bad
        omega
      have he : e < t := L.pred_lt t ht
      have hi : 0 < i := L.bin_pos t
      have hih : i ≤ h := by
        have := L.bin_le_height e
        have := L.pred_bin t ht
        change E.bin e = i at this
        omega
      have heheight : h ≤ E.height t := L.height_mono (Nat.le_of_lt he)
      let sources := (Finset.range (E.birth h)).filter fun g => i < E.bin g
      have pairing : (higherRenewals E i t).card ≤ sources.card := by
        apply Finset.card_le_card_of_injOn E.pred
        · intro g hg
          obtain ⟨hgt, hig, hgr⟩ := Finset.mem_filter.mp hg
          have hgt' : g < t := Finset.mem_range.mp hgt
          have hgLower := ih g hgt' hgr
          have hgHeight := L.height_mono (Nat.le_of_lt hgt')
          have hp : 0 < E.height (E.pred g) := height_pos (E.pred g)
          have hp_lt : E.height (E.pred g) < h := by
            by_contra hn
            have hle : h ≤ E.height (E.pred g) := by omega
            have hbirth : E.birth h ≤ E.birth (E.height (E.pred g)) := by
              by_contra hb
              have hb' : E.birth (E.height (E.pred g)) < E.birth h := by omega
              have hx := (L.birth_cut h hh _).mpr hb'
              rw [L.birth_height _ hp] at hx
              omega
            have hm := endpoint_mono hbirth
            omega
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_range.mpr ((L.birth_cut h hh _).mp hp_lt), ?_⟩
          simpa only [L.pred_bin g hgr] using hig
        · intro a ha b hb hab
          exact pred_injective a (Finset.mem_filter.mp ha).2.2
            b (Finset.mem_filter.mp hb).2.2 hab
      let births := sources.filter fun g => ¬ E.Renewal g
      let renewals := sources.filter E.Renewal
      have hsplit : births.card + renewals.card = sources.card := by
        simpa only [births, renewals, Nat.add_comm] using
          (Finset.card_filter_add_card_filter_not (s := sources) E.Renewal)
      have births_bound : births.card ≤ h - i := by
        have hcard : births.card ≤ (Finset.Ico (i + 1) h).card := by
          apply Finset.card_le_card_of_injOn E.bin
          · intro g hg
            obtain ⟨hgs, hgb⟩ := Finset.mem_filter.mp hg
            obtain ⟨hgr, hig⟩ := Finset.mem_filter.mp hgs
            have gh : E.height g < h :=
              (L.birth_cut h hh g).mpr (Finset.mem_range.mp hgr)
            have bg : g = E.birth (E.bin g) := by simpa [EventSequence.Renewal] using hgb
            have hbheight : E.height g = E.bin g := by
              exact (congrArg E.height bg).trans (L.birth_height _ (L.bin_pos g))
            apply Finset.mem_Ico.mpr
            omega
          · intro a ha b hb hab
            have ba : a = E.birth (E.bin a) := by
              simpa [EventSequence.Renewal] using (Finset.mem_filter.mp ha).2
            have bb : b = E.birth (E.bin b) := by
              simpa [EventSequence.Renewal] using (Finset.mem_filter.mp hb).2
            exact ba.trans ((congrArg E.birth hab).trans bb.symm)
        rw [Nat.card_Ico] at hcard
        omega
      have renewals_bound : renewals.card ≤ (higherRenewals E i e).card := by
        apply Finset.card_le_card
        intro g hg
        obtain ⟨hgs, hgr⟩ := Finset.mem_filter.mp hg
        obtain ⟨hgb, hig⟩ := Finset.mem_filter.mp hgs
        have hge : g < e := lt_of_lt_of_le (Finset.mem_range.mp hgb) (birth_before e)
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hge, hig, hgr⟩
      have balance := L.reset_balance t ht
      have nlower := endpoint_mono (birth_before e)
      change E.endpoint e + h + (higherRenewals E i e).card =
        E.height t + (higherRenewals E i t).card at balance
      change E.endpoint (E.birth h) ≤ E.endpoint e at nlower
      omega
  refine ⟨lower f hf, ?_⟩
  let e := E.pred f
  let h := E.height e
  have he : e < f := L.pred_lt f hf
  have hheight : h ≤ E.height f := L.height_mono (Nat.le_of_lt he)
  have rho_mono : (higherRenewals E (E.bin f) e).card ≤
      (higherRenewals E (E.bin f) f).card := by
    apply Finset.card_le_card
    intro g hg
    obtain ⟨hge, hgi⟩ := Finset.mem_filter.mp hg
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp hge) he), hgi⟩
  have balance := L.reset_balance f hf
  change E.endpoint e + h + (higherRenewals E (E.bin f) e).card =
    E.height f + (higherRenewals E (E.bin f) f).card at balance
  have upper_reset : E.height f ≤ E.endpoint e + h := by omega
  let q := E.birth (h + 1)
  have heq : e < q := (L.birth_cut (h + 1) (by omega) e).mp (by omega)
  have hq : 0 < q := by omega
  have hpq : q - 1 + 1 = q := by omega
  have heprev : e ≤ q - 1 := by omega
  have htime := endpoint_mono heprev
  have hstep := L.endpoint_step (q - 1)
  rw [hpq] at hstep
  have hbin : E.bin q = h + 1 := L.birth_bin _ (by omega)
  rw [hbin] at hstep
  change E.height f < E.endpoint q
  omega

#print axioms successor_band
end D5.S3.Combinatorics.GreedyBrick.SuccessorBand
