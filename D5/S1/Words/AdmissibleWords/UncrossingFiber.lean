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

def Comparable (M : Multiset (Finset V)) : Prop :=
  ∀ ⦃A⦄, A ∈ M → ∀ ⦃B⦄, B ∈ M → A ⊆ B ∨ B ⊆ A

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
  · exact hM hC

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
      exact ih (forwardStep_family hL hM hs) hr

private theorem card_inter_add_card_sdiff (A B : Finset V) :
    (A ∩ B).card + (A \ B).card = A.card := by
  exact Finset.card_inter_add_card_sdiff A B

private theorem card_union_eq (A B : Finset V) :
    (A ∪ B).card = (A ∩ B).card + (A \ B).card + (B \ A).card := by
  have hA := card_inter_add_card_sdiff A B
  have hB := card_inter_add_card_sdiff B A
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
    card_inter_add_card_sdiff A B
  have hcardB : B.card = (A ∩ B).card + (B \ A).card := by
    simpa [Finset.inter_comm] using card_inter_add_card_sdiff B A
  omega

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
  obtain ⟨A, B, R, hM, hN, he⟩ := forwardStep_energy h
  rw [he]
  rcases h with ⟨_, _, _, hAB, hBA, _, _⟩
  have ha : 0 < (A \ B).card := card_sdiff_pos_of_not_subset hAB
  have hb : 0 < (B \ A).card := card_sdiff_pos_of_not_subset hBA
  omega

theorem energy_le_card_mul_fintype_card_sq (M : Multiset (Finset V)) :
    energy M ≤ M.card * (Fintype.card V) ^ 2 := by
  classical
  induction M using Multiset.induction_on with
  | empty => simp [energy]
  | @cons A M ih =>
      simp only [energy, Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
      have hA : A.card ≤ Fintype.card V := Finset.card_le_univ A
      nlinarith [Nat.pow_le_pow_left hA 2]

theorem comparable_of_no_forward_step (M : Multiset (Finset V))
    (h : ¬ ∃ N, ForwardStep M N) : Comparable M := by
  intro A hA B hB
  by_contra hn
  push_neg at hn
  have hne : A ≠ B := by
    intro e
    subst B
    exact hn.1 (Subset.rfl)
  obtain ⟨R, hR⟩ := Multiset.exists_cons_of_mem hA
  have hB' : B ∈ R := by
    rw [← hR] at hB
    simpa [hne] using hB
  obtain ⟨S, hS⟩ := Multiset.exists_cons_of_mem hB'
  have hshape : M = A ::ₘ B ::ₘ S := by simpa [hR, hS, Multiset.cons_assoc]
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
          have := forwardStep_energy_strict hXY
          omega
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
  intro i j hij
  have hAi := hA i j hij
  have hBi := hB i j hij
  constructor
  · constructor
    · intro he h
      have h' := Finset.mem_inter.mp h
      exact Finset.mem_inter.mpr ⟨hAi.1 he h'.1, hBi.1 he h'.2⟩
    · intro he h
      have h' := Finset.mem_inter.mp h
      exact Finset.mem_inter.mpr ⟨hAi.2 he h'.1, hBi.2 he h'.2⟩
  · constructor
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
        · exact ih hw.2 k l (by simpa using hij)

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
      rw [phi, phi] at hi' hj'
      simp [he, hje] at hi' hj'
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
      rw [phi, phi] at hi' hj'
      simp [he, hje] at hi' hj'
      exact ⟨hi', hj'⟩
    exact (adm_adjacent w hw i j hij) hfalse

def fenceFamily (n : Nat) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fence n)

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
