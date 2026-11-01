/- GID: D5/S1/Words/AdmissibleWords/UncrossingFiber
   generality: G
   mirror-B: D5/B/S1/Words/AdmissibleWords/UncrossingFiber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Multiset.Sum, mathlib/module/Mathlib.Data.Finset.Card]
   utility: none
   digest: Bounded residual uncrossing reaches explicit threshold rows and connects original native admissible occupancy fibers via a fence bijection. -/

import D5.S1.Words.AdmissibleWords.AdmissibleCount
import Mathlib.Data.Finset.Card
import Mathlib.Data.Multiset.Sum
import Mathlib.Data.Fintype.Fin
import Mathlib.Logic.Relation
import Mathlib.Tactic

/-! Quantitative meet-join sorting on finite Boolean row fibers. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.AdmissibleWords.UncrossingFiber

open D5.S1.Words.AdmissibleWords.AdmissibleCount

variable {V : Type} [Fintype V] [DecidableEq V]

def height (A : Finset V) : Nat := A.card

def energy (M : Multiset (Finset V)) : Nat :=
  (M.map (fun A => (height A) ^ 2)).sum

def margin (M : Multiset (Finset V)) (v : V) : Nat :=
  (M.map (fun A => if v ∈ A then 1 else 0)).sum

theorem margin_le_card (M : Multiset (Finset V)) (v : V) :
    margin M v ≤ M.card := by
  induction M using Multiset.induction_on with
  | empty => simp [margin]
  | @cons A M ih =>
      by_cases hA : v ∈ A
      · have hle := Nat.add_le_add_left ih 1
        simpa [margin, hA, Nat.add_comm] using hle
      · have hle : margin M v ≤ M.card + 1 := Nat.le_succ_of_le ih
        simpa [margin, hA] using hle

theorem margin_eq_card_iff {M : Multiset (Finset V)} (v : V) :
    margin M v = M.card ↔ ∀ A, A ∈ M → v ∈ A := by
  classical
  induction M using Multiset.induction_on with
  | empty => simp [margin]
  | @cons A M ih =>
      by_cases hA : v ∈ A
      · simp only [margin, Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons,
          if_pos hA]
        constructor
        · intro h B hB
          rcases Multiset.mem_cons.mp hB with rfl | hB
          · exact hA
          · have hm : margin M v = M.card := by
              have h' : 1 + (M.map (fun A => if v ∈ A then 1 else 0)).sum = M.card + 1 := h
              have hsum : (M.map (fun A => if v ∈ A then 1 else 0)).sum = M.card := by
                omega
              simpa [margin] using hsum
            exact (ih.mp hm) B hB
        · intro h
          have hm : margin M v = M.card := ih.mpr (fun B hB => h B (by simp [hB]))
          have hsum : (M.map (fun A => if v ∈ A then 1 else 0)).sum = M.card := by
            simpa [margin] using hm
          omega
      · simp only [margin, Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons,
          if_neg hA]
        have hle := margin_le_card M v
        constructor
        · intro h
          have h' : margin M v = M.card + 1 := by simpa [margin] using h
          exfalso
          omega
        · intro h
          exact (hA (h A (by simp))).elim

theorem margin_erase_add {M : Multiset (Finset V)} {A : Finset V}
    (hA : A ∈ M) (v : V) :
    margin (M.erase A) v + (if v ∈ A then 1 else 0) = margin M v := by
  rw [← Multiset.cons_erase hA]
  simp [margin, Nat.add_comm]

def Comparable (M : Multiset (Finset V)) : Prop :=
  ∀ ⦃A⦄, A ∈ M → ∀ ⦃B⦄, B ∈ M → A ⊆ B ∨ B ⊆ A

theorem exists_min_row {M : Multiset (Finset V)} (hM : Comparable M) (hne : M ≠ 0) :
    ∃ A, A ∈ M ∧ ∀ ⦃B⦄, B ∈ M → A ⊆ B := by
  induction M using Multiset.induction_on with
  | empty => contradiction
  | @cons A M ih =>
      by_cases hM0 : M = 0
      · subst M
        exact ⟨A, by simp, by
          intro B hB
          have hBA : B = A := by simpa using hB
          simpa [hBA]⟩
      · have hcomp : Comparable M := by
          intro B hB C hC
          exact hM (A := B) (B := C) (by simp [hB]) (by simp [hC])
        obtain ⟨B, hB, hBmin⟩ := ih hcomp hM0
        rcases hM (A := A) (B := B) (by simp) (by simp [hB]) with hAB | hBA
        · refine ⟨A, by simp, ?_⟩
          intro C hC
          have hC' : C = A ∨ C ∈ M := by simpa using hC
          rcases hC' with rfl | hC
          · exact Finset.Subset.rfl
          · exact hAB.trans (hBmin hC)
        · refine ⟨B, by simp [hB], ?_⟩
          intro C hC
          have hC' : C = A ∨ C ∈ M := by simpa using hC
          rcases hC' with rfl | hC
          · exact hBA
          · exact hBmin hC

theorem comparable_margin_unique {M N : Multiset (Finset V)}
    (hM : Comparable M) (hN : Comparable N) (hcard : M.card = N.card)
    (hmarg : ∀ v, margin M v = margin N v) : M = N := by
  classical
  induction hcm : M.card using Nat.strong_induction_on generalizing M N with
  | h k ih =>
      by_cases hzero : M = 0
      · have hNzero : N = 0 := by
          apply Multiset.card_eq_zero.mp
          calc
            N.card = M.card := hcard.symm
            _ = 0 := by simpa [hzero]
        exact hzero.trans hNzero.symm
      · obtain ⟨A, hAM, hAmin⟩ := exists_min_row hM hzero
        have hNzero : N ≠ 0 := by
          intro hN0
          subst N
          have : M.card = 0 := by simpa using hcard
          exact hzero (Multiset.card_eq_zero.mp this)
        obtain ⟨C, hCN, hCmin⟩ := exists_min_row hN hNzero
        have hAchar : ∀ v, v ∈ A ↔ margin M v = M.card := by
          intro v
          constructor
          · intro hv
            exact margin_eq_card_iff v |>.2 (fun B hB => hAmin hB hv)
          · intro hv
            by_contra hvA
            have hnot : ¬ (∀ B, B ∈ M → v ∈ B) := by
              intro hall
              exact hvA (hall A hAM)
            exact hnot (margin_eq_card_iff v |>.1 hv)
        have hCchar : ∀ v, v ∈ C ↔ margin N v = N.card := by
          intro v
          constructor
          · intro hv
            exact margin_eq_card_iff v |>.2 (fun B hB => hCmin hB hv)
          · intro hv
            by_contra hvC
            have hnot : ¬ (∀ B, B ∈ N → v ∈ B) := by
              intro hall
              exact hvC (hall C hCN)
            exact hnot (margin_eq_card_iff v |>.1 hv)
        have hAC : A = C := by
          ext v
          have hmc : margin M v = M.card ↔ margin N v = N.card := by
            constructor <;> intro h
            · rw [← hcard, ← hmarg v]
              exact h
            · rw [hcard, hmarg v]
              exact h
          exact (hAchar v).trans (hmc.trans (hCchar v).symm)
        have hcard' : (M.erase A).card = (N.erase C).card := by
          rw [Multiset.card_erase_of_mem hAM, Multiset.card_erase_of_mem hCN, hcard]
        have hM' : Comparable (M.erase A) := by
          intro B hB D hD
          exact hM (Multiset.mem_of_mem_erase hB) (Multiset.mem_of_mem_erase hD)
        have hN' : Comparable (N.erase C) := by
          intro B hB D hD
          exact hN (Multiset.mem_of_mem_erase hB) (Multiset.mem_of_mem_erase hD)
        have hmarg' : ∀ v, margin (M.erase A) v = margin (N.erase C) v := by
          intro v
          have hleft := margin_erase_add hAM v
          have hright := margin_erase_add hCN v
          have hm := hmarg v
          have hind : (if v ∈ A then 1 else 0) = (if v ∈ C then 1 else 0) := by
            simp [hAC]
          omega
        have hsmall : (M.erase A).card < k := by
          rw [← hcm]
          exact Multiset.card_erase_lt_of_mem hAM
        have hrec := ih _ hsmall hM' hN' hcard' hmarg' rfl
        calc
          M = A ::ₘ M.erase A := (Multiset.cons_erase hAM).symm
          _ = C ::ₘ M.erase A := by rw [hAC]
          _ = C ::ₘ N.erase C := by rw [hrec]
          _ = N := Multiset.cons_erase hCN

def FamilyRows (L : Finset (Finset V)) (M : Multiset (Finset V)) : Prop :=
  ∀ ⦃A⦄, A ∈ M → A ∈ L

def ClosedFamily (L : Finset (Finset V)) : Prop :=
  ∀ ⦃A⦄, A ∈ L → ∀ ⦃B⦄, B ∈ L → A ∩ B ∈ L ∧ A ∪ B ∈ L

/-- One genuine join-meet exchange, with the two selected rows occurring in the input.
The residual multiset makes repetitions and empty rows explicit. -/
def ForwardStep (M N : Multiset (Finset V)) : Prop :=
  ∃ (R : Multiset (Finset V)) (A B : Finset V),
    (¬ A ⊆ B) ∧ (¬ B ⊆ A) ∧
      M = A ::ₘ B ::ₘ R ∧ N = (A ∩ B) ::ₘ (A ∪ B) ::ₘ R

inductive ForwardRoute : Multiset (Finset V) → Multiset (Finset V) → Nat → Prop
  | zero (M) : ForwardRoute M M 0
  | succ {M N P k} : ForwardStep M N → ForwardRoute N P k → ForwardRoute M P (k + 1)

theorem forwardStep_card {M N : Multiset (Finset V)} (h : ForwardStep M N) : M.card = N.card := by
  rcases h with ⟨R, A, B, _, _, rfl, rfl⟩
  simp [Multiset.card_cons]

theorem forwardStep_margin {M N : Multiset (Finset V)} (h : ForwardStep M N) :
    ∀ v, margin M v = margin N v := by
  rcases h with ⟨R, A, B, hAB, hBA, rfl, rfl⟩
  intro v
  by_cases hA : v ∈ A <;> by_cases hB : v ∈ B <;>
    simp [margin, hA, hB]

theorem forwardStep_family {L : Finset (Finset V)}
    (hL : ClosedFamily L) {M N : Multiset (Finset V)}
    (hM : FamilyRows L M) (h : ForwardStep M N) : FamilyRows L N := by
  rcases h with ⟨R, A, B, hAB, hBA, rfl, rfl⟩
  intro C hC
  simp only [Multiset.mem_cons] at hC
  rcases hC with rfl | rfl | hC
  · exact (hL (hM (by simp)) (hM (by simp))).1
  · exact (hL (hM (by simp)) (hM (by simp))).2
  · exact hM (by simp [hC])

theorem forwardRoute_card {M N : Multiset (Finset V)} {k : Nat}
    (h : ForwardRoute M N k) : M.card = N.card := by
  induction h with
  | zero => rfl
  | @succ M N P k hs hr ih =>
      exact (forwardStep_card hs).trans ih

theorem forwardRoute_margin {M N : Multiset (Finset V)} {k : Nat}
    (h : ForwardRoute M N k) : ∀ v, margin M v = margin N v := by
  induction h with
  | zero => simp
  | @succ M N P k hs hr ih =>
      intro v
      exact (forwardStep_margin hs v).trans (ih v)

theorem forwardRoute_family {L : Finset (Finset V)}
    (hL : ClosedFamily L) {M N : Multiset (Finset V)} {k : Nat}
    (hM : FamilyRows L M) (h : ForwardRoute M N k) : FamilyRows L N := by
  induction h with
  | zero => exact hM
  | @succ M N P k hs hr ih =>
      exact ih (forwardStep_family hL hM hs)

private theorem card_inter_add_card_sdiff (A B : Finset V) :
    (A ∩ B).card + (A \ B).card = A.card := by
  exact Finset.card_inter_add_card_sdiff A B

private theorem card_union_eq (A B : Finset V) :
    (A ∪ B).card = (A ∩ B).card + (A \ B).card + (B \ A).card := by
  have hA := card_inter_add_card_sdiff A B
  have hB : (A ∩ B).card + (B \ A).card = B.card := by
    simpa [Finset.inter_comm] using card_inter_add_card_sdiff B A
  have hu := Finset.card_union_add_card_inter A B
  omega

theorem forwardStep_energy {M N : Multiset (Finset V)} (h : ForwardStep M N) :
    ∃ A B R, (¬ A ⊆ B) ∧ (¬ B ⊆ A) ∧
      M = A ::ₘ B ::ₘ R ∧ N = (A ∩ B) ::ₘ (A ∪ B) ::ₘ R ∧
      energy N = energy M +
        2 * (A \ B).card * (B \ A).card := by
  rcases h with ⟨R, A, B, hAB, hBA, rfl, rfl⟩
  refine ⟨A, B, R, hAB, hBA, rfl, rfl, ?_⟩
  simp only [energy, height, Multiset.map_cons, Multiset.sum_cons]
  rw [card_union_eq]
  have hcardA : A.card = (A ∩ B).card + (A \ B).card :=
    (card_inter_add_card_sdiff A B).symm
  have hcardB : B.card = (A ∩ B).card + (B \ A).card := by
    simpa [Finset.inter_comm] using (card_inter_add_card_sdiff B A).symm
  nlinarith [hcardA, hcardB]

private theorem card_sdiff_pos_of_not_subset {A B : Finset V} (h : ¬ A ⊆ B) :
    0 < (A \ B).card := by
  have : (A \ B).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hz
    apply h
    intro x hx
    by_contra hxb
    have : x ∈ A \ B := Finset.mem_sdiff.mpr ⟨hx, hxb⟩
    simpa [hz] using this
  exact Finset.card_pos.mpr this

theorem forwardStep_energy_gap {M N : Multiset (Finset V)} (h : ForwardStep M N) :
    energy M + 2 ≤ energy N := by
  obtain ⟨A, B, R, hAB, hBA, rfl, rfl, he⟩ := forwardStep_energy h
  rw [he]
  have ha : 1 ≤ (A \ B).card := card_sdiff_pos_of_not_subset hAB
  have hb : 1 ≤ (B \ A).card := card_sdiff_pos_of_not_subset hBA
  have hab : 1 ≤ (A \ B).card * (B \ A).card := Nat.mul_le_mul ha hb
  have hp : 2 ≤ 2 * (A \ B).card * (B \ A).card := by
    simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hab
  omega

theorem forwardStep_energy_strict {M N : Multiset (Finset V)} (h : ForwardStep M N) :
    energy M < energy N := by
  have := forwardStep_energy_gap h
  omega

theorem energy_le_card_mul_fintype_card_sq (M : Multiset (Finset V)) :
    energy M ≤ M.card * (Fintype.card V) ^ 2 := by
  classical
  induction M using Multiset.induction_on with
  | empty => simp [energy]
  | @cons A M ih =>
      simp only [energy, Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
      have hA : A.card ≤ Fintype.card V := Finset.card_le_univ A
      have hpow : A.card ^ 2 ≤ (Fintype.card V) ^ 2 := Nat.pow_le_pow_left hA 2
      calc
        height A ^ 2 + energy M ≤ (Fintype.card V) ^ 2 +
            M.card * (Fintype.card V) ^ 2 := Nat.add_le_add hpow ih
        _ = (M.card + 1) * (Fintype.card V) ^ 2 := by
          simp [Nat.add_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
            Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

theorem comparable_of_no_forward_step (M : Multiset (Finset V))
    (h : ¬ ∃ N, ForwardStep M N) : Comparable M := by
  intro A hA B hB
  by_contra hn
  push_neg at hn
  have hne : A ≠ B := by
    intro e
    subst B
    exact hn.1 (fun x hx => hx)
  obtain ⟨R, hR⟩ := Multiset.exists_cons_of_mem hA
  have hB' : B ∈ R := by
    rw [hR] at hB
    have hne' : B ≠ A := Ne.symm hne
    simpa [hne'] using hB
  obtain ⟨S, hS⟩ := Multiset.exists_cons_of_mem hB'
  have hshape : M = A ::ₘ B ::ₘ S := by simpa [hR, hS]
  refine False.elim (h ⟨(A ∩ B) ::ₘ (A ∪ B) ::ₘ S, ?_⟩)
  exact ⟨S, A, B, hn.1, hn.2, hshape, rfl⟩

theorem exists_forward_route_to_comparable (M : Multiset (Finset V)) :
    ∃ k N, 2 * k + energy M ≤ M.card * (Fintype.card V) ^ 2 ∧
      k ≤ M.card * (Fintype.card V) ^ 2 / 2 ∧ ForwardRoute M N k ∧ Comparable N := by
  classical
  let bound := M.card * (Fintype.card V) ^ 2
  have hMbound : energy M ≤ bound := energy_le_card_mul_fintype_card_sq M
  let P : Nat → Prop := fun s => ∀ (X : Multiset (Finset V)), X.card = M.card →
    bound - energy X = s →
      ∃ k N, k ≤ (bound - energy X) / 2 ∧
        ForwardRoute X N k ∧ Comparable N
  have hP : ∀ s, P s := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      intro X hXcard hs
      by_cases hc : Comparable X
      · exact ⟨0, X, by omega, .zero X, hc⟩
      · have hpair : ∃ Y, ForwardStep X Y := by
          by_contra hno
          exact hc (comparable_of_no_forward_step X hno)
        obtain ⟨Y, hXY⟩ := hpair
        have hYcard : Y.card = M.card := by
          calc
            Y.card = X.card := (forwardStep_card hXY).symm
            _ = M.card := hXcard
        have hE : energy X < energy Y := forwardStep_energy_strict hXY
        have hboundY : energy Y ≤ bound := by
          calc
            energy Y ≤ Y.card * (Fintype.card V) ^ 2 :=
              energy_le_card_mul_fintype_card_sq Y
            _ = bound := by simp [bound, hYcard]
        have hslackY : bound - energy Y < s := by omega
        obtain ⟨k, Z, hk, hr, hz⟩ :=
          ih (bound - energy Y) hslackY Y hYcard (by rfl)
        refine ⟨k + 1, Z, ?_, .succ hXY hr, hz⟩
        have hstep : 2 ≤ energy Y - energy X := by
          have := forwardStep_energy_gap hXY
          omega
        have hk' : k * 2 ≤ bound - energy Y := by
          exact (Nat.le_div_iff_mul_le Nat.zero_lt_two).mp hk
        apply (Nat.le_div_iff_mul_le Nat.zero_lt_two).mpr
        omega
  obtain ⟨k, N, hk, hr, hc⟩ := hP (bound - energy M) M rfl rfl
  have hk2 := (Nat.le_div_iff_mul_le Nat.zero_lt_two).mp hk
  refine ⟨k, N, ?_, ?_, hr, hc⟩
  · dsimp [bound] at *
    omega
  · dsimp [bound] at *
    omega

theorem same_margin_common_comparable {M N : Multiset (Finset V)}
    (hcard : M.card = N.card) (hmarg : ∀ v, margin M v = margin N v) :
    ∃ k l P,
      k ≤ M.card * (Fintype.card V) ^ 2 / 2 ∧
        l ≤ N.card * (Fintype.card V) ^ 2 / 2 ∧
          ForwardRoute M P k ∧ ForwardRoute N P l ∧ Comparable P := by
  obtain ⟨k, P, _, hk, hr, hcP⟩ := exists_forward_route_to_comparable M
  obtain ⟨l, Q, _, hl, hs, hcQ⟩ := exists_forward_route_to_comparable N
  have hPQcard : P.card = Q.card :=
    (forwardRoute_card hr).symm.trans (hcard.trans (forwardRoute_card hs))
  have hPQmarg : ∀ v, margin P v = margin Q v := by
    intro v
    exact (forwardRoute_margin hr v).symm.trans ((hmarg v).trans (forwardRoute_margin hs v))
  have hPQ : P = Q := comparable_margin_unique hcP hcQ hPQcard hPQmarg
  refine ⟨k, l, P, hk, hl, hr, ?_, hcP⟩
  simpa [hPQ] using hs

/-- The zero-based forced row, formed from an actual multiset's mass and margins. -/
def thresholdRow (M : Multiset (Finset V)) (j : Fin M.card) : Finset V :=
  Finset.univ.filter (fun v => M.card - margin M v ≤ j.val)

/-- Indexing by `Fin M.card` retains repeated and empty threshold rows. -/
def thresholdRows (M : Multiset (Finset V)) : Multiset (Finset V) :=
  Finset.univ.val.map (thresholdRow M)

private theorem mem_thresholdRow (M : Multiset (Finset V)) (j : Fin M.card) (v : V) :
    v ∈ thresholdRow M j ↔ M.card - margin M v ≤ j.val := by
  simp [thresholdRow]

private theorem thresholdRows_card (M : Multiset (Finset V)) :
    (thresholdRows M).card = M.card := by
  simp [thresholdRows]

private theorem thresholdRows_comparable (M : Multiset (Finset V)) :
    Comparable (thresholdRows M) := by
  intro A hA B hB
  obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hA
  obtain ⟨j, _, rfl⟩ := Multiset.mem_map.mp hB
  rcases le_total i.val j.val with hij | hji
  · exact Or.inl (fun v hv => (mem_thresholdRow M j v).mpr
      (le_trans ((mem_thresholdRow M i v).mp hv) hij))
  · exact Or.inr (fun v hv => (mem_thresholdRow M i v).mpr
      (le_trans ((mem_thresholdRow M j v).mp hv) hji))

private theorem thresholdRows_margin (M : Multiset (Finset V)) (v : V) :
    margin (thresholdRows M) v = margin M v := by
  simp only [margin, thresholdRows, Multiset.map_map, Function.comp_def]
  change (∑ j : Fin M.card, if v ∈ thresholdRow M j then 1 else 0) = margin M v
  simp only [mem_thresholdRow, Finset.sum_boole, Nat.cast_id]
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin M.card))) (fun j => j.val < M.card - margin M v)
  rw [Fin.card_filter_val_lt] at h
  simp only [not_lt, Finset.card_univ, Fintype.card_fin] at h
  have hc := margin_le_card M v
  omega

/-- The constructed sorting route reaches the explicit threshold multiset, with its
initial energy charged to the same budget as the number of exchanges. -/
theorem sort_to_threshold (M : Multiset (Finset V)) :
    ∃ k, 2 * k + energy M ≤ M.card * (Fintype.card V) ^ 2 ∧
      k ≤ M.card * (Fintype.card V) ^ 2 / 2 ∧ ForwardRoute M (thresholdRows M) k := by
  obtain ⟨k, N, he, hk, hr, hc⟩ := exists_forward_route_to_comparable M
  have hn : N = thresholdRows M := comparable_margin_unique hc
    (thresholdRows_comparable M) ((forwardRoute_card hr).symm.trans (thresholdRows_card M).symm)
    (fun v => (forwardRoute_margin hr v).symm.trans (thresholdRows_margin M v).symm)
  exact ⟨k, he, hk, hn ▸ hr⟩

/-- Threshold rows belong to the closed family because an actual sorting route produces
that endpoint. No feasibility of independently prescribed margins is assumed. -/
theorem thresholdRows_family {L : Finset (Finset V)} (hL : ClosedFamily L)
    {M : Multiset (Finset V)} (hM : FamilyRows L M) :
    FamilyRows L (thresholdRows M) ∧ ∀ j : Fin M.card, thresholdRow M j ∈ L := by
  obtain ⟨k, _, _, hr⟩ := sort_to_threshold M
  have hf := forwardRoute_family hL hM hr
  exact ⟨hf, fun j => hf (Multiset.mem_map.mpr ⟨j, by simp, rfl⟩)⟩

/-- An undirected residual exchange in a fixed family, with legal endpoints. -/
def ExchangeStep (L : Finset (Finset V)) (M N : Multiset (Finset V)) : Prop :=
  (ForwardStep M N ∨ ForwardStep N M) ∧ FamilyRows L M ∧ FamilyRows L N

/-- A genuine finite path, using Mathlib's reflexive transitive closure. -/
def ExchangePath (L : Finset (Finset V)) (M N : Multiset (Finset V)) : Prop :=
  Relation.ReflTransGen (ExchangeStep L) M N

private theorem forwardRoute_exchangePath {L : Finset (Finset V)} (hL : ClosedFamily L)
    {M N : Multiset (Finset V)} {k : Nat} (hM : FamilyRows L M)
    (h : ForwardRoute M N k) : ExchangePath L M N := by
  induction h with
  | zero => exact .refl
  | @succ M N P k hs hr ih =>
    have hN := forwardStep_family hL hM hs
    exact Relation.ReflTransGen.head ⟨Or.inl hs, hM, hN⟩ (ih hN)

private theorem exchangePath_reverse {L : Finset (Finset V)}
    {M N : Multiset (Finset V)} (h : ExchangePath L M N) : ExchangePath L N M := by
  induction h with
  | refl => exact .refl
  | tail hr hs ih =>
    exact Relation.ReflTransGen.head ⟨hs.1.symm, hs.2.2, hs.2.1⟩ ih

/-- Every reachable intermediate state remains in the same family, mass and coordinate fiber. -/
theorem exchangePath_invariants {L : Finset (Finset V)}
    {M N : Multiset (Finset V)} (hM : FamilyRows L M) (h : ExchangePath L M N) :
    FamilyRows L N ∧ N.card = M.card ∧ ∀ v, margin N v = margin M v := by
  induction h with
  | refl => exact ⟨hM, rfl, fun _ => rfl⟩
  | @tail N P hr hs ih =>
    rcases hs.1 with hs' | hs'
    · exact ⟨hs.2.2, (forwardStep_card hs').symm.trans ih.2.1,
        fun v => (forwardStep_margin hs' v).symm.trans (ih.2.2 v)⟩
    · exact ⟨hs.2.2, (forwardStep_card hs').trans ih.2.1,
        fun v => (forwardStep_margin hs' v).trans (ih.2.2 v)⟩

/-- Reverse one constructed normalization route and concatenate it with the other.
The closure records actual residual exchanges, including all intermediate states. -/
theorem same_margin_connected {L : Finset (Finset V)} (hL : ClosedFamily L)
    {M N : Multiset (Finset V)} (hM : FamilyRows L M) (hN : FamilyRows L N)
    (hc : M.card = N.card) (hm : ∀ v, margin M v = margin N v) :
    ExchangePath L M N := by
  obtain ⟨k, l, P, _, _, hr, hs, _⟩ := same_margin_common_comparable hc hm
  exact Relation.ReflTransGen.trans (forwardRoute_exchangePath hL hM hr)
    (exchangePath_reverse (forwardRoute_exchangePath hL hN hs))

def fence (n : Nat) (A : Finset (Fin n)) : Prop :=
  ∀ (i j : Fin n), i.val + 1 = j.val →
    ((Even i.val → (i ∈ A → j ∈ A)) ∧
      (¬ Even i.val → (j ∈ A → i ∈ A)))

theorem fence_inter_union {n : Nat} {A B : Finset (Fin n)}
    (hA : fence n A) (hB : fence n B) : fence n (A ∩ B) ∧ fence n (A ∪ B) := by
  constructor
  · intro i j hij
    have hAi := hA i j hij
    have hBi := hB i j hij
    constructor
    · intro he h
      have h' := Finset.mem_inter.mp h
      exact Finset.mem_inter.mpr ⟨hAi.1 he h'.1, hBi.1 he h'.2⟩
    · intro he h
      have h' := Finset.mem_inter.mp h
      exact Finset.mem_inter.mpr ⟨hAi.2 he h'.1, hBi.2 he h'.2⟩
  · intro i j hij
    have hAi := hA i j hij
    have hBi := hB i j hij
    constructor
    · intro he h
      rcases Finset.mem_union.mp h with h | h
      · exact Finset.mem_union.mpr (Or.inl (hAi.1 he h))
      · exact Finset.mem_union.mpr (Or.inr (hBi.1 he h))
    · intro he h
      rcases Finset.mem_union.mp h with h | h
      · exact Finset.mem_union.mpr (Or.inl (hAi.2 he h))
      · exact Finset.mem_union.mpr (Or.inr (hBi.2 he h))

def phi {n : Nat} (w : Fin n → Bool) : Fin n → Bool :=
  fun i => if Even i.val then w i else !w i

def support {n : Nat} (w : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i => w i = true)

theorem phi_involutive {n : Nat} (w : Fin n → Bool) : phi (phi w) = w := by
  funext i
  by_cases he : Even i.val <;> simp [phi, he]

theorem support_phi_injective {n : Nat} :
    Function.Injective (fun w : Fin n → Bool => support (phi w)) := by
  intro w z h
  have hphi : phi w = phi z := by
    funext i
    have hi : i ∈ support (phi w) ↔ i ∈ support (phi z) := by
      have h' : support (phi w) = support (phi z) := by simpa using h
      rw [h']
    have hi' : (phi w i = true) ↔ (phi z i = true) := by
      simpa [support] using hi
    cases hw : phi w i <;> cases hz : phi z i <;> simp [hw, hz] at hi' ⊢
  calc
    w = phi (phi w) := (phi_involutive w).symm
    _ = phi (phi z) := congrArg phi hphi
    _ = z := phi_involutive z

private theorem adm_adjacent {n : Nat} (w : Fin n → Bool) (hw : Adm n w)
    (i j : Fin n) (hij : i.val + 1 = j.val) : ¬ (w i = true ∧ w j = true) := by
  have h := (adm_iff_no_adjacent_true n w).mp hw i j hij
  simpa only [Bool.eq_false_iff, not_and_or] using h

theorem phi_support_fence {n : Nat} {w : Fin n → Bool} (hw : Adm n w) :
    fence n (support (phi w)) := by
  intro i j hij
  constructor
  · intro he hi
    by_contra hj
    have hje : ¬ Even j.val := by
      rw [← hij]
      exact Nat.even_add_one.not_left.mpr he
    have hi' : phi w i = true := by simpa [support] using hi
    have hj' : phi w j = false := by simpa [support] using hj
    have hfalse : w i = true ∧ w j = true := by
      simp [phi, he, hje] at hi' hj'
      exact ⟨hi', hj'⟩
    exact (adm_adjacent w hw i j hij) hfalse
  · intro he hj
    by_contra hi
    have hje : Even j.val := by
      rw [← hij]
      exact Nat.even_add_one.mpr he
    have hj' : phi w j = true := by simpa [support] using hj
    have hi' : phi w i = false := by simpa [support] using hi
    have hfalse : w i = true ∧ w j = true := by
      simp [phi, he, hje] at hi' hj'
      exact ⟨hi', hj'⟩
    exact (adm_adjacent w hw i j hij) hfalse

private theorem adm_of_adjacent {n : Nat} (w : Fin n → Bool)
    (h : ∀ i j : Fin n, i.val + 1 = j.val → ¬ (w i = true ∧ w j = true)) : Adm n w := by
  apply (adm_iff_no_adjacent_true n w).mpr
  intro i j hij
  simpa only [Bool.eq_false_iff, not_and_or] using h i j hij

/-- Alternating complement identifies exactly the native admissibility predicate. -/
theorem phi_support_fence_iff {n : Nat} (w : Fin n → Bool) :
    fence n (support (phi w)) ↔ Adm n w := by
  refine ⟨?_, phi_support_fence⟩
  intro h
  apply adm_of_adjacent w
  intro i j hij ⟨hi, hj⟩
  by_cases he : Even i.val
  · have hje : ¬ Even j.val := by
      rw [← hij]
      exact Nat.even_add_one.not_left.mpr he
    have hi' : i ∈ support (phi w) := by simp [support, phi, he, hi]
    have hj' := (h i j hij).1 he hi'
    simpa [support, phi, hje, hj] using hj'
  · have hje : Even j.val := by
      rw [← hij]
      exact Nat.even_add_one.mpr he
    have hj' : j ∈ support (phi w) := by simp [support, phi, hje, hj]
    have hi' := (h i j hij).2 he hj'
    simpa [support, phi, he, hi] using hi'

def wordOfSupport {n : Nat} (A : Finset (Fin n)) : Fin n → Bool :=
  fun i => decide (i ∈ A)

private theorem support_wordOfSupport {n : Nat} (A : Finset (Fin n)) :
    support (wordOfSupport A) = A := by
  ext i
  simp [support, wordOfSupport]

/-- Inverse to the Phi support map on every row, including arbitrary intermediate fence rows. -/
def unphi {n : Nat} (A : Finset (Fin n)) : Fin n → Bool := phi (wordOfSupport A)

private theorem support_phi_unphi {n : Nat} (A : Finset (Fin n)) :
    support (phi (unphi A)) = A := by
  rw [unphi, phi_involutive, support_wordOfSupport]

private theorem unphi_support_phi {n : Nat} (w : Fin n → Bool) :
    unphi (support (phi w)) = w := by
  apply support_phi_injective
  exact support_phi_unphi _

private theorem unphi_adm {n : Nat} {A : Finset (Fin n)} (hA : fence n A) :
    Adm n (unphi A) := by
  apply (phi_support_fence_iff _).mp
  simpa only [support_phi_unphi] using hA

/-- An involutive Boolean change of coordinates yields a bijection to fence upper sets. -/
def admFenceEquiv (n : Nat) :
    {w : Fin n → Bool // Adm n w} ≃ {A : Finset (Fin n) // fence n A} where
  toFun w := ⟨support (phi w.val), phi_support_fence w.property⟩
  invFun A := ⟨unphi A.val, unphi_adm A.property⟩
  left_inv w := Subtype.ext (unphi_support_phi w.val)
  right_inv A := Subtype.ext (support_phi_unphi A.val)

noncomputable def fenceFamily (n : Nat) : Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.filter (fence n)

theorem mem_fenceFamily {n : Nat} {A : Finset (Fin n)} :
    A ∈ fenceFamily n ↔ fence n A := by
  simp [fenceFamily]

theorem fenceFamily_closed (n : Nat) : ClosedFamily (fenceFamily n) := by
  intro A hA B hB
  have hAf : fence n A := (mem_fenceFamily.mp hA)
  have hBf : fence n B := (mem_fenceFamily.mp hB)
  have h := fence_inter_union hAf hBf
  exact ⟨mem_fenceFamily.mpr h.1, mem_fenceFamily.mpr h.2⟩

/-- Original occupied-row counts, before alternating complement. -/
def occupancyCount {n : Nat} (M : Multiset (Fin n → Bool)) (i : Fin n) : Nat :=
  (M.map (fun w => if w i = true then 1 else 0)).sum

def phiRows {n : Nat} (M : Multiset (Fin n → Bool)) : Multiset (Finset (Fin n)) :=
  M.map (fun w => support (phi w))

def unphiRows {n : Nat} (M : Multiset (Finset (Fin n))) : Multiset (Fin n → Bool) :=
  M.map unphi

def NativeRows {n : Nat} (M : Multiset (Fin n → Bool)) : Prop :=
  ∀ ⦃w⦄, w ∈ M → Adm n w

private theorem unphiRows_phiRows {n : Nat} (M : Multiset (Fin n → Bool)) :
    unphiRows (phiRows M) = M := by
  simp [unphiRows, phiRows, Multiset.map_map, Function.comp_def, unphi_support_phi]

private theorem phiRows_unphiRows {n : Nat} (M : Multiset (Finset (Fin n))) :
    phiRows (unphiRows M) = M := by
  simp [unphiRows, phiRows, Multiset.map_map, Function.comp_def, support_phi_unphi]

private theorem nativeRows_phiRows {n : Nat} {M : Multiset (Fin n → Bool)}
    (hM : NativeRows M) : FamilyRows (fenceFamily n) (phiRows M) := by
  intro A hA
  obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hA
  exact mem_fenceFamily.mpr (phi_support_fence (hM hw))

private theorem nativeRows_unphiRows {n : Nat} {M : Multiset (Finset (Fin n))}
    (hM : FamilyRows (fenceFamily n) M) : NativeRows (unphiRows M) := by
  intro w hw
  obtain ⟨A, hA, rfl⟩ := Multiset.mem_map.mp hw
  exact ((admFenceEquiv n).symm ⟨A, mem_fenceFamily.mp (hM hA)⟩).property

private theorem occupancyCount_le_card {n : Nat} (M : Multiset (Fin n → Bool)) (i : Fin n) :
    occupancyCount M i ≤ M.card := by
  simpa [margin, occupancyCount, support, Multiset.map_map, Function.comp_def] using
    margin_le_card (M.map support) i

/-- Multiplicities are counted by multiset sums: odd coordinates have complementary counts. -/
theorem phiRows_margin {n : Nat} (M : Multiset (Fin n → Bool)) (i : Fin n) :
    margin (phiRows M) i =
      if Even i.val then occupancyCount M i else M.card - occupancyCount M i := by
  induction M using Multiset.induction_on with
  | empty => simp [phiRows, margin, occupancyCount]
  | cons w M ih =>
    have hle := occupancyCount_le_card M i
    by_cases he : Even i.val <;> cases hw : w i <;>
      simp [phiRows, margin, support, phi, occupancyCount, he, hw] at ih ⊢ <;>
      simp only [occupancyCount] at hle <;> omega

/-- A native residual exchange replaces the two actual word occurrences by the inverse
images of the transformed meet and join; original supports need not be union-closed. -/
def NativeForwardStep {n : Nat} (M N : Multiset (Fin n → Bool)) : Prop :=
  NativeRows M ∧ ∃ (R : Multiset (Fin n → Bool)) (a b : Fin n → Bool),
    (¬ support (phi a) ⊆ support (phi b)) ∧
    (¬ support (phi b) ⊆ support (phi a)) ∧
    M = a ::ₘ b ::ₘ R ∧
    N = unphi (support (phi a) ∩ support (phi b)) ::ₘ
      unphi (support (phi a) ∪ support (phi b)) ::ₘ R

/-- Finite undirected paths on the actual all-n native word configurations. -/
def NativePath {n : Nat} (M N : Multiset (Fin n → Bool)) : Prop :=
  Relation.ReflTransGen (Relation.SymmGen NativeForwardStep) M N

private theorem nativeForwardStep_legal {n : Nat} {M N : Multiset (Fin n → Bool)}
    (h : NativeForwardStep M N) : NativeRows N := by
  rcases h with ⟨hM, R, a, b, _, _, rfl, rfl⟩
  have ha := phi_support_fence (hM (by simp : a ∈ a ::ₘ b ::ₘ R))
  have hb := phi_support_fence (hM (by simp : b ∈ a ::ₘ b ::ₘ R))
  intro w hw
  rcases Multiset.mem_cons.mp hw with rfl | hw
  · exact unphi_adm (fence_inter_union ha hb).1
  rcases Multiset.mem_cons.mp hw with rfl | hw
  · exact unphi_adm (fence_inter_union ha hb).2
  · exact hM (by simp [hw])

private theorem nativeForwardStep_encode {n : Nat} {M N : Multiset (Fin n → Bool)}
    (h : NativeForwardStep M N) : ForwardStep (phiRows M) (phiRows N) := by
  rcases h with ⟨_, R, a, b, hab, hba, rfl, rfl⟩
  refine ⟨phiRows R, support (phi a), support (phi b), hab, hba, ?_, ?_⟩
  · simp [phiRows]
  · simp [phiRows, support_phi_unphi]

/-- Pull every actual residual lattice exchange back to legal admissible words. -/
theorem adm_phi_forward_consumer {n : Nat} {M N : Multiset (Finset (Fin n))}
    (hM : FamilyRows (fenceFamily n) M) (h : ForwardStep M N) :
    NativeForwardStep (unphiRows M) (unphiRows N) := by
  refine ⟨nativeRows_unphiRows hM, ?_⟩
  rcases h with ⟨R, A, B, hab, hba, rfl, rfl⟩
  refine ⟨unphiRows R, unphi A, unphi B, ?_, ?_, ?_, ?_⟩
  · simpa only [support_phi_unphi] using hab
  · simpa only [support_phi_unphi] using hba
  · simp [unphiRows]
  · simp [unphiRows, support_phi_unphi]

private theorem nativePath_encode {n : Nat} {M N : Multiset (Fin n → Bool)}
    (h : NativePath M N) : ExchangePath (fenceFamily n) (phiRows M) (phiRows N) := by
  refine Relation.ReflTransGen.lift phiRows ?_ M N h
  intro X Y hXY
  rcases hXY with hs | hs
  · exact ⟨Or.inl (nativeForwardStep_encode hs), nativeRows_phiRows hs.1,
      nativeRows_phiRows (nativeForwardStep_legal hs)⟩
  · exact ⟨Or.inr (nativeForwardStep_encode hs), nativeRows_phiRows (nativeForwardStep_legal hs),
      nativeRows_phiRows hs.1⟩

private theorem exchangePath_decode {n : Nat} {M N : Multiset (Finset (Fin n))}
    (h : ExchangePath (fenceFamily n) M N) : NativePath (unphiRows M) (unphiRows N) := by
  refine Relation.ReflTransGen.lift unphiRows ?_ M N h
  intro X Y hXY
  rcases hXY.1 with hs | hs
  · exact Or.inl (adm_phi_forward_consumer hXY.2.1 hs)
  · exact Or.inr (adm_phi_forward_consumer hXY.2.2 hs)

/-- Every native intermediate state is admissible and preserves the ORIGINAL occupancy
fiber. This applies to every prefix of the constructed path, in either direction. -/
theorem nativePath_invariants {n : Nat} {M N : Multiset (Fin n → Bool)}
    (hM : NativeRows M) (h : NativePath M N) :
    NativeRows N ∧ N.card = M.card ∧ ∀ i, occupancyCount N i = occupancyCount M i := by
  have hi := exchangePath_invariants (nativeRows_phiRows hM) (nativePath_encode h)
  have hn := nativeRows_unphiRows hi.1
  rw [unphiRows_phiRows] at hn
  have hc : N.card = M.card := by simpa [phiRows] using hi.2.1
  refine ⟨hn, hc, ?_⟩
  intro i
  have hm := hi.2.2 i
  rw [phiRows_margin, phiRows_margin] at hm
  have hleM := occupancyCount_le_card M i
  have hleN := occupancyCount_le_card N i
  by_cases he : Even i.val <;> simp only [he, if_true, if_false] at hm <;> omega

/-- The canonical native endpoint is defined AFTER Phi; its transformed rows are thresholds. -/
def nativeCanonical {n : Nat} (M : Multiset (Fin n → Bool)) : Multiset (Fin n → Bool) :=
  unphiRows (thresholdRows (phiRows M))

/-- A complete bounded sorting route, its legal native pullback, and the explicit canonical
endpoint. The initial-energy budget is retained, as well as the weaker floor bound. -/
theorem adm_phi_route_bound {n : Nat} (M : Multiset (Fin n → Bool)) (hM : NativeRows M) :
    ∃ k, 2 * k + energy (phiRows M) ≤ M.card * n ^ 2 ∧ k ≤ M.card * n ^ 2 / 2 ∧
      ForwardRoute (phiRows M) (thresholdRows (phiRows M)) k ∧
      NativePath M (nativeCanonical M) ∧ NativeRows (nativeCanonical M) ∧
      phiRows (nativeCanonical M) = thresholdRows (phiRows M) ∧
      (∀ j : Fin (phiRows M).card, Adm n (unphi (thresholdRow (phiRows M) j))) ∧
      (∀ k' P, ForwardRoute (phiRows M) P k' → Comparable P →
        P = thresholdRows (phiRows M)) := by
  obtain ⟨k, he, hk, hr⟩ := sort_to_threshold (phiRows M)
  have hrows := nativeRows_phiRows hM
  have hf := thresholdRows_family (fenceFamily_closed n) hrows
  have hp := exchangePath_decode (forwardRoute_exchangePath (fenceFamily_closed n) hrows hr)
  rw [unphiRows_phiRows] at hp
  refine ⟨k, ?_, ?_, hr, hp, nativeRows_unphiRows hf.1,
    phiRows_unphiRows _, ?_, ?_⟩
  · simpa [phiRows] using he
  · simpa [phiRows] using hk
  · intro j
    exact unphi_adm (mem_fenceFamily.mp (hf.2 j))
  · intro k' P hP hcP
    exact comparable_margin_unique hcP (thresholdRows_comparable _)
      ((forwardRoute_card hP).symm.trans (thresholdRows_card _).symm)
      (fun i => (forwardRoute_margin hP i).symm.trans (thresholdRows_margin _ i).symm)

/-- Equal ORIGINAL mass and occupancies give an actual undirected path through native
admissible multisets and the same threshold endpoint after Phi. -/
theorem adm_phi_fiber_common_endpoint {n : Nat} {M N : Multiset (Fin n → Bool)}
    (hM : NativeRows M) (hN : NativeRows N) (hc : M.card = N.card)
    (hm : ∀ i, occupancyCount M i = occupancyCount N i) :
    NativePath M N ∧ nativeCanonical M = nativeCanonical N ∧
      (∃ k, 2 * k + energy (phiRows M) ≤ M.card * n ^ 2 ∧ k ≤ M.card * n ^ 2 / 2 ∧
        ForwardRoute (phiRows M) (phiRows (nativeCanonical M)) k ∧
        NativePath M (nativeCanonical M)) ∧
      (∀ X, NativePath M X → NativeRows X ∧ X.card = M.card ∧
        ∀ i, occupancyCount X i = occupancyCount M i) := by
  have hpc : (phiRows M).card = (phiRows N).card := by simpa [phiRows] using hc
  have hpm : ∀ i, margin (phiRows M) i = margin (phiRows N) i := by
    intro i
    rw [phiRows_margin, phiRows_margin, hc, hm i]
  have hp := exchangePath_decode (same_margin_connected (fenceFamily_closed n)
    (nativeRows_phiRows hM) (nativeRows_phiRows hN) hpc hpm)
  rw [unphiRows_phiRows, unphiRows_phiRows] at hp
  have ht : thresholdRows (phiRows M) = thresholdRows (phiRows N) :=
    comparable_margin_unique (thresholdRows_comparable _) (thresholdRows_comparable _)
      ((thresholdRows_card _).trans (hpc.trans (thresholdRows_card _).symm))
      (fun i => (thresholdRows_margin _ i).trans ((hpm i).trans (thresholdRows_margin _ i).symm))
  obtain ⟨k, he, hk, hr, hnative, _, hencode, _, _⟩ := adm_phi_route_bound M hM
  refine ⟨hp, congrArg unphiRows ht, ⟨k, he, hk, ?_, hnative⟩,
    fun X hX => nativePath_invariants hM hX⟩
  simpa only [hencode] using hr

end D5.S1.Words.AdmissibleWords.UncrossingFiber
