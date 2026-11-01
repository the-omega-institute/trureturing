/- GID: D5/S1/Words/AdmissibleWords/UncrossingFiber
   generality: G
   mirror-B: D5/B/S1/Words/AdmissibleWords/UncrossingFiber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Multiset, mathlib/module/Mathlib.Data.Finset.Card]
   utility: none
   digest: Finite Boolean uncrossing preserves coordinate margins and admits a bounded forward route to comparable support; the admissible-word consumer transports the route through alternating complement. -/

import D5.S1.Words.AdmissibleWords.AdmissibleCount
import Mathlib.Data.Finset.Card
import Mathlib.Data.Multiset.Sum
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
    ∃ A B R, M = A ::ₘ B ::ₘ R ∧ N = (A ∩ B) ::ₘ (A ∪ B) ::ₘ R ∧
      energy N = energy M +
        2 * (A \ B).card * (B \ A).card := by
  rcases h with ⟨R, A, B, hAB, hBA, rfl, rfl⟩
  refine ⟨A, B, R, rfl, rfl, ?_⟩
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

theorem forwardStep_energy_strict {M N : Multiset (Finset V)} (h : ForwardStep M N) :
    energy M < energy N := by
  rcases h with ⟨R, A, B, hAB, hBA, rfl, rfl⟩
  have hcardA : A.card = (A ∩ B).card + (A \ B).card :=
    (card_inter_add_card_sdiff A B).symm
  have hcardB : B.card = (A ∩ B).card + (B \ A).card := by
    simpa [Finset.inter_comm] using (card_inter_add_card_sdiff B A).symm
  have he : energy ((A ∩ B) ::ₘ (A ∪ B) ::ₘ R) =
      energy (A ::ₘ B ::ₘ R) + 2 * (A \ B).card * (B \ A).card := by
    simp only [energy, height, Multiset.map_cons, Multiset.sum_cons]
    rw [card_union_eq]
    nlinarith [hcardA, hcardB]
  rw [he]
  have ha : 0 < (A \ B).card := card_sdiff_pos_of_not_subset hAB
  have hb : 0 < (B \ A).card := card_sdiff_pos_of_not_subset hBA
  have hp : 0 < 2 * (A \ B).card * (B \ A).card := by
    exact Nat.mul_pos (Nat.mul_pos (by omega) ha) hb
  omega

theorem forwardStep_energy_gap {M N : Multiset (Finset V)} (h : ForwardStep M N) :
    energy M + 2 ≤ energy N := by
  rcases h with ⟨R, A, B, hAB, hBA, rfl, rfl⟩
  have hcardA : A.card = (A ∩ B).card + (A \ B).card :=
    (card_inter_add_card_sdiff A B).symm
  have hcardB : B.card = (A ∩ B).card + (B \ A).card := by
    simpa [Finset.inter_comm] using (card_inter_add_card_sdiff B A).symm
  have he : energy ((A ∩ B) ::ₘ (A ∪ B) ::ₘ R) =
      energy (A ::ₘ B ::ₘ R) + 2 * (A \ B).card * (B \ A).card := by
    simp only [energy, height, Multiset.map_cons, Multiset.sum_cons]
    rw [card_union_eq]
    nlinarith [hcardA, hcardB]
  rw [he]
  have ha : 0 < (A \ B).card := card_sdiff_pos_of_not_subset hAB
  have hb : 0 < (B \ A).card := card_sdiff_pos_of_not_subset hBA
  have ha1 : 1 ≤ (A \ B).card := by omega
  have hb1 : 1 ≤ (B \ A).card := by omega
  have hab : 1 ≤ (A \ B).card * (B \ A).card := by
    exact (Nat.mul_le_mul ha1 hb1)
  have hp : 2 ≤ 2 * (A \ B).card * (B \ A).card := by
    have := Nat.mul_le_mul_left 2 hab
    simpa [Nat.mul_assoc] using this
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
    ∃ k N, k ≤ M.card * (Fintype.card V) ^ 2 / 2 ∧
      ForwardRoute M N k ∧ Comparable N := by
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
  refine ⟨k, N, ?_, hr, hc⟩
  have hnonneg : 0 ≤ energy M := Nat.zero_le _
  omega

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
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases n with
    | zero => have hi := i.isLt; have hj := j.isLt; omega
    | succ n =>
      revert hij
      refine Fin.cases (fun hij => ?_) (fun k hij => ?_) i
      · have hj : j = 1 := Fin.ext (by simpa using hij.symm)
        simpa [hj] using hw.1
      · revert hij
        refine Fin.cases (fun hij => ?_) (fun l hij => ?_) j
        · simp only [Fin.val_zero, Fin.val_succ] at hij; omega
        · exact ih (Fin.tail w) hw.2 k l (by simpa using hij)

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

theorem adm_phi_route_bound {n : Nat} (M : Multiset (Fin n → Bool))
    (hM : ∀ ⦃w⦄, w ∈ M → Adm n w) :
    ∃ k N, k ≤ M.card * (Fintype.card (Fin n)) ^ 2 / 2 ∧
      ForwardRoute (M.map (fun w => support (phi w))) N k ∧ Comparable N ∧
      FamilyRows (fenceFamily n) N ∧
      ∀ i, margin (M.map (fun w => support (phi w))) i = margin N i := by
  let rows : Multiset (Finset (Fin n)) := M.map (fun w => support (phi w))
  have hrows : FamilyRows (fenceFamily n) rows := by
    intro A hA
    obtain ⟨w, hw, hAw⟩ := Multiset.mem_map.mp hA
    subst A
    exact mem_fenceFamily.mpr (phi_support_fence (hM hw))
  obtain ⟨k, N, hk, hr, hc⟩ := exists_forward_route_to_comparable rows
  have hfamily := forwardRoute_family (fenceFamily_closed n) hrows hr
  refine ⟨k, N, ?_, hr, hc, hfamily, forwardRoute_margin hr⟩
  simpa [rows] using hk

theorem adm_phi_canonical_endpoint_unique {n : Nat} (M : Multiset (Fin n → Bool))
    (hM : ∀ ⦃w⦄, w ∈ M → Adm n w) :
    ∃ k N, k ≤ M.card * (Fintype.card (Fin n)) ^ 2 / 2 ∧
      ForwardRoute (M.map (fun w => support (phi w))) N k ∧ Comparable N ∧
      FamilyRows (fenceFamily n) N ∧
      (∀ i, margin (M.map (fun w => support (phi w))) i = margin N i) ∧
      (∀ k' N', ForwardRoute (M.map (fun w => support (phi w))) N' k' →
        Comparable N' → N' = N) := by
  obtain ⟨k, N, hk, hr, hc, hfamily, hmarg⟩ := adm_phi_route_bound M hM
  refine ⟨k, N, hk, hr, hc, hfamily, hmarg, ?_⟩
  intro k' N' hr' hc'
  apply comparable_margin_unique hc' hc
  · exact (forwardRoute_card hr').symm.trans (forwardRoute_card hr)
  · intro i
    exact (forwardRoute_margin hr' i).symm.trans (forwardRoute_margin hr i)

theorem adm_phi_forward_consumer {n : Nat} (w₁ w₂ : Fin n → Bool)
    (h₁ : Adm n w₁) (h₂ : Adm n w₂)
    (h₁₂ : ¬ support (phi w₁) ⊆ support (phi w₂))
    (h₂₁ : ¬ support (phi w₂) ⊆ support (phi w₁)) :
    ForwardStep ({support (phi w₁), support (phi w₂)} : Multiset (Finset (Fin n)))
      ({support (phi w₁) ∩ support (phi w₂),
        support (phi w₁) ∪ support (phi w₂)} : Multiset (Finset (Fin n))) ∧
      fence n (support (phi w₁)) ∧ fence n (support (phi w₂)) := by
  refine ⟨⟨0, support (phi w₁), support (phi w₂), h₁₂, h₂₁, by simp, by simp⟩,
    phi_support_fence h₁, phi_support_fence h₂⟩

end D5.S1.Words.AdmissibleWords.UncrossingFiber
