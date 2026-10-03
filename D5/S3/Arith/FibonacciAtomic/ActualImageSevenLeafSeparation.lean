/- GID: D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Seven-leaf separation of equal-size nonconflicting actual third images. -/

import D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition
import Mathlib.Data.Finset.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.ActualImageSevenLeafSeparation

open GenealogicalFiberTransport (Source substitution composition)

/-- The actual third iterate of the original substitution. -/
def thirdImage (t : Source) : Source := substitution^[3] t

/-- The finite-set view of the public actual leaf enumeration. -/
def leafAddresses (p : Source) : Finset (List Bool) :=
  (ActualTreeReadoutAcquisition.leaves p).toFinset

/-- The label projection of the public four-valued actual readout. -/
def leafLabel (p : Source) (u : List Bool) : Option Bool :=
  match ActualTreeReadoutAcquisition.readout u p with
  | .alpha => some true
  | .beta => some false
  | .branch | .absent => none

/-- Shared literal leaf addresses, computed by simultaneous tree recursion. -/
def sharedLeaves : Source → Source → ℕ
  | .of _, .of _ => 1
  | .mul p q, .mul r s => sharedLeaves p r + sharedLeaves q s
  | _, _ => 0

/-- Labels are compared only when both trees have a leaf at the same address. -/
def Nonconflict : Source → Source → Prop
  | .of a, .of b => a = b
  | .mul p q, .mul r s => Nonconflict p r ∧ Nonconflict q s
  | _, _ => True

/-- The number of leaves whose literal addresses are not shared. -/
def unsharedLeaves (p q : Source) : ℕ := p.length - sharedLeaves p q

/-- The literal second, third, and fourth alpha iterates used in the sharp pair. -/
def E : Source := .mul (.of false) (.of true)
def A : Source := .mul E (.of false)
def C : Source := .mul A E

/-- The two original ordered preimages of the sharp thirteen-leaf pair. -/
def pThirteen : Source := .mul (.of false) (.mul (.of true) (.of false))
def qThirteen : Source := .mul (.mul (.of true) (.of false)) (.of false)

/-- The sharp pair, retaining all brackets and labels. -/
def PThirteen : Source := .mul C (.mul A C)
def QThirteen : Source := .mul (.mul A C) C

/-- The six shared labelled addresses of the literal sharp pair. -/
def sharpShared : Finset (List Bool × Bool) :=
  {([false, false, false, false], false),
   ([false, false, false, true], true),
   ([false, false, true], false),
   ([true, false, false, false], false),
   ([true, false, false, true], true),
   ([true, false, true], false)}

set_option maxHeartbeats 1000000 in
-- The paired source induction and exact finite address computation share one proof budget.
/-- Exact address semantics, universal separation, and literal same-composition sharpness. -/
theorem seven_leaf_separation :
    (∀ p : Source, (leafAddresses p).card = p.length ∧
      ∀ u : List Bool, u ∈ leafAddresses p ↔ ∃ b, leafLabel p u = some b) ∧
    (∀ p q : Source,
      sharedLeaves p q = (leafAddresses p ∩ leafAddresses q).card ∧
      unsharedLeaves p q = (leafAddresses p \ leafAddresses q).card ∧
      (Nonconflict p q ↔ ∀ (u : List Bool) (a b : Bool),
        leafLabel p u = some a → leafLabel q u = some b → a = b)) ∧
    (∀ (P Q : Source) (n : ℕ),
      P ∈ Set.range thirdImage → Q ∈ Set.range thirdImage →
      P ≠ Q → P.length = n → Q.length = n → Nonconflict P Q →
      11 ≤ n ∧ unsharedLeaves P Q = unsharedLeaves Q P ∧
        7 ≤ unsharedLeaves P Q ∧ sharedLeaves P Q ≤ n - 7) ∧
    (PThirteen = thirdImage pThirteen ∧ QThirteen = thirdImage qThirteen ∧
      PThirteen ≠ QThirteen ∧ Nonconflict PThirteen QThirteen ∧
      composition PThirteen = (5, 8) ∧ composition QThirteen = (5, 8) ∧
      PThirteen.length = 13 ∧ QThirteen.length = 13 ∧
      sharedLeaves PThirteen QThirteen = 6 ∧
      unsharedLeaves PThirteen QThirteen = 7 ∧
      unsharedLeaves QThirteen PThirteen = 7 ∧
      (leafAddresses PThirteen ∩ leafAddresses QThirteen).image
        (fun u => (u, (leafLabel PThirteen u).getD false)) = sharpShared) := by
  have addresses_of (b : Bool) : leafAddresses (.of b) = {[]} := rfl
  have addresses_mul (p q : Source) : leafAddresses (p * q) =
      (leafAddresses p).image (false :: ·) ∪
        (leafAddresses q).image (true :: ·) := by
    ext u
    simp [leafAddresses, ActualTreeReadoutAcquisition.leaves, Finset.mem_image]
  have label_of (b : Bool) : leafLabel (.of b) [] = some b := by
    cases b <;> rfl
  have label_of_cons (b c : Bool) (u : List Bool) :
      leafLabel (.of b) (c :: u) = none := rfl
  have label_mul_nil (p q : Source) : leafLabel (p * q) [] = none := rfl
  have label_mul_left (p q : Source) (u : List Bool) :
      leafLabel (p * q) (false :: u) = leafLabel p u := rfl
  have label_mul_right (p q : Source) (u : List Bool) :
      leafLabel (p * q) (true :: u) = leafLabel q u := rfl
  have prefix_disjoint (s t : Finset (List Bool)) :
      Disjoint (s.image (false :: ·)) (t.image (true :: ·)) := by
    apply Finset.disjoint_left.mpr
    intro u hu hv
    rcases Finset.mem_image.mp hu with ⟨a, _, ha⟩
    rcases Finset.mem_image.mp hv with ⟨b, _, hb⟩
    have h := ha.trans hb.symm
    cases h
  have prefix_inj (b : Bool) : Function.Injective (List.cons b) := by
    intro u v h
    exact (List.cons.inj h).2
  have paired_card (s t : Finset (List Bool)) :
      (s.image (false :: ·) ∪ t.image (true :: ·)).card = s.card + t.card := by
    rw [Finset.card_union_of_disjoint (prefix_disjoint s t),
      Finset.card_image_of_injective _ (prefix_inj false),
      Finset.card_image_of_injective _ (prefix_inj true)]
  have addresses_card (p : Source) : (leafAddresses p).card = p.length := by
    induction p with
    | of b => simp [addresses_of, FreeMagma.length]
    | mul p q hp hq =>
      simp only [FreeMagma.mul_eq, addresses_mul, paired_card, FreeMagma.length, hp, hq]
  have label_address (p : Source) (u : List Bool) :
      u ∈ leafAddresses p ↔ ∃ b, leafLabel p u = some b := by
    induction p generalizing u with
    | of b => cases u <;> simp [addresses_of, label_of, label_of_cons]
    | mul p q hp hq =>
      cases u with
      | nil => simp [addresses_mul, label_mul_nil]
      | cons b u =>
        cases b <;> simp [addresses_mul, label_mul_left, label_mul_right,
          Finset.mem_image, hp, hq]
  have addresses_inter (p q r s : Source) :
      leafAddresses (.mul p q) ∩ leafAddresses (.mul r s) =
      (leafAddresses p ∩ leafAddresses r).image (false :: ·) ∪
        (leafAddresses q ∩ leafAddresses s).image (true :: ·) := by
    ext u
    cases u with
    | nil => simp [addresses_mul]
    | cons b u => cases b <;> simp [addresses_mul, Finset.mem_image]
  have shared_card (p q : Source) :
      sharedLeaves p q = (leafAddresses p ∩ leafAddresses q).card := by
    induction p generalizing q with
    | of b =>
      cases q with
      | of c => simp [sharedLeaves, addresses_of]
      | mul q r => simp [sharedLeaves, addresses_of, addresses_mul]
    | mul p r hp hr =>
      cases q with
      | of b => simp [sharedLeaves, addresses_of, addresses_mul]
      | mul q s =>
        rw [addresses_inter, paired_card]
        exact congrArg₂ Nat.add (hp q) (hr s)
  have shared_le (p q : Source) : sharedLeaves p q ≤ p.length := by
    rw [shared_card, ← addresses_card]
    exact Finset.card_le_card Finset.inter_subset_left
  have unshared_card (p q : Source) :
      unsharedLeaves p q = (leafAddresses p \ leafAddresses q).card := by
    have h := Finset.card_sdiff_add_card_inter (leafAddresses p) (leafAddresses q)
    rw [addresses_card, ← shared_card] at h
    dsimp [unsharedLeaves]
    omega
  have nc_semantics (p q : Source) :
      Nonconflict p q ↔ ∀ (u : List Bool) (a b : Bool),
        leafLabel p u = some a → leafLabel q u = some b → a = b := by
    induction p generalizing q with
    | of a =>
      cases q with
      | of b =>
        constructor
        · intro h u c d hc hd
          cases u with
          | nil =>
            simp only [label_of, Option.some.injEq] at hc hd
            subst c; subst d; exact h
          | cons c u => simp [label_of_cons] at hc
        · intro h
          exact h [] a b (label_of a) (label_of b)
      | mul q r =>
        constructor
        · intro _ u c d hc hd
          cases u <;> simp [label_of, label_of_cons, label_mul_nil] at hc hd
        · intro _; trivial
    | mul p r hp hr =>
      cases q with
      | of b =>
        constructor
        · intro _ u c d hc hd
          cases u <;> simp [label_of_cons, label_mul_nil] at hc hd
        · intro _; trivial
      | mul q s =>
        constructor
        · rintro ⟨hl, hr'⟩ u a b ha hb
          cases u with
          | nil => simp [label_mul_nil] at ha
          | cons c u =>
            cases c
            · exact (hp q).mp hl u a b ha hb
            · exact (hr s).mp hr' u a b ha hb
        · intro h
          exact ⟨(hp q).mpr (fun u a b ha hb => h (false :: u) a b ha hb),
            (hr s).mpr (fun u a b ha hb => h (true :: u) a b ha hb)⟩
  have nc_symm (p q : Source) : Nonconflict p q → Nonconflict q p := by
    intro h
    apply (nc_semantics q p).mpr
    intro u a b ha hb
    exact ((nc_semantics p q).mp h u b a hb ha).symm
  have shared_symm (p q : Source) : sharedLeaves p q = sharedLeaves q p := by
    simp only [shared_card, Finset.inter_comm]
  have unshared_mul (p q r s : Source) :
      unsharedLeaves (.mul p q) (.mul r s) =
        unsharedLeaves p r + unsharedLeaves q s := by
    have hp := shared_le p r
    have hq := shared_le q s
    simp only [unsharedLeaves, FreeMagma.length, sharedLeaves]
    omega
  have r_mul (p q : Source) : thirdImage (.mul p q) =
      .mul (thirdImage p) (thirdImage q) := rfl
  have r_alpha : thirdImage (.of true) = A := rfl
  have r_beta : thirdImage (.of false) = C := rfl
  have minimum (p : Source) : 3 ≤ (thirdImage p).length := by
    induction p with
    | of b => cases b <;> decide
    | mul p q hp hq => rw [r_mul]; change 3 ≤ _ + _; omega
  have not_alpha_minimum (p : Source) (h : p ≠ .of true) :
      5 ≤ (thirdImage p).length := by
    cases p with
    | of b =>
      cases b with
      | false => decide
      | true => exact False.elim (h rfl)
    | mul p q =>
      have hp := minimum p
      have hq := minimum q
      rw [r_mul]; change 5 ≤ _ + _; omega
  have atom_image (b : Bool) (p : Source) :
      Nonconflict (.of b) (thirdImage p) ∧
      sharedLeaves (.of b) (thirdImage p) = 0 := by
    cases p with
    | of a => cases a <;> exact ⟨True.intro, rfl⟩
    | mul p q => rw [r_mul]; exact ⟨True.intro, rfl⟩
  have e_image (p : Source) :
      Nonconflict E (thirdImage p) ↔ p ≠ .of true := by
    cases p with
    | of b =>
      cases b with
      | false =>
        constructor
        · intro _ h; cases h
        · intro _; exact ⟨True.intro, True.intro⟩
      | true => simp [r_alpha, Nonconflict, E, A]
    | mul p q =>
      rw [r_mul]
      constructor
      · intro _ h; cases h
      · intro _
        exact ⟨(atom_image false p).1, (atom_image true q).1⟩
  have e_shared (p : Source) (h : p ≠ .of true) :
      sharedLeaves E (thirdImage p) = 0 := by
    cases p with
    | of b =>
      cases b with
      | false => rfl
      | true => exact False.elim (h rfl)
    | mul p q =>
      rw [r_mul]
      change sharedLeaves (.of false) (thirdImage p) +
        sharedLeaves (.of true) (thirdImage q) = 0
      rw [(atom_image false p).2, (atom_image true q).2]
  have a_composite (p q : Source) (h :
      Nonconflict A (.mul (thirdImage p) (thirdImage q))) :
      p ≠ .of true ∧ sharedLeaves A (.mul (thirdImage p) (thirdImage q)) = 0 ∧
        8 ≤ (.mul (thirdImage p) (thirdImage q) : Source).length := by
    have hp := (e_image p).mp h.1
    have hn := not_alpha_minimum p hp
    have hq := minimum q
    refine ⟨hp, ?_, ?_⟩
    · change sharedLeaves E (thirdImage p) + sharedLeaves (.of false) (thirdImage q) = 0
      rw [e_shared p hp, (atom_image false q).2]
    · change 8 ≤ _ + _; omega
  let Up (p q : Source) : Prop := p.length < q.length ∧ 3 ≤ p.length ∧
    8 ≤ q.length ∧ 2 ≤ unsharedLeaves p q ∧ 5 ≤ unsharedLeaves q p
  let Big (p q : Source) : Prop := 11 ≤ p.length ∧ 11 ≤ q.length ∧
    7 ≤ unsharedLeaves p q ∧ 7 ≤ unsharedLeaves q p
  have atomic_composite (b : Bool) (p q : Source)
      (h : Nonconflict (thirdImage (.of b)) (.mul (thirdImage p) (thirdImage q))) :
      Up (thirdImage (.of b)) (.mul (thirdImage p) (thirdImage q)) := by
    cases b with
    | true =>
      rw [r_alpha] at h ⊢
      have hc := a_composite p q h
      have hs := hc.2.1
      have hsr := (shared_symm A (.mul (thirdImage p) (thirdImage q))).symm.trans hs
      have ha : A.length = 3 := rfl
      simp only [Up, unsharedLeaves, hs, hsr, ha]
      simp only [FreeMagma.length] at hc ⊢
      omega
    | false =>
      rw [r_beta] at h ⊢
      have hy := (e_image q).mp h.2
      have hnq := not_alpha_minimum q hy
      have hsq := e_shared q hy
      have hc : C.length = 5 := rfl
      cases p with
      | of a =>
        cases a with
        | false =>
          have hf : ¬ Nonconflict A C := by simp [Nonconflict, A, C, E]
          exact False.elim (hf h.1)
        | true =>
          rw [r_alpha] at h ⊢
          have hs : sharedLeaves C (.mul A (thirdImage q)) = 3 := by
            change sharedLeaves A A + sharedLeaves E (thirdImage q) = 3
            rw [hsq]; rfl
          have hsr := shared_symm C (.mul A (thirdImage q))
          have hsr' := hsr.symm.trans hs
          have ha : A.length = 3 := rfl
          simp only [Up, unsharedLeaves, hs, hsr', hc, FreeMagma.length, ha]
          omega
      | mul p r =>
        rw [r_mul] at h ⊢
        have hx := a_composite p r h.1
        have hs : sharedLeaves C (.mul (.mul (thirdImage p) (thirdImage r))
            (thirdImage q)) = 0 := by
          change sharedLeaves A (.mul (thirdImage p) (thirdImage r)) +
            sharedLeaves E (thirdImage q) = 0
          rw [hx.2.1, hsq]
        have hsr := shared_symm C
          (.mul (.mul (thirdImage p) (thirdImage r)) (thirdImage q))
        have hsr' := hsr.symm.trans hs
        simp only [Up, unsharedLeaves, hs, hsr', hc]
        simp only [FreeMagma.length] at hx ⊢
        omega
  have combine (p q r s : Source)
      (hl : p = r ∨ Up p r ∨ Up r p ∨ Big p r)
      (hr : q = s ∨ Up q s ∨ Up s q ∨ Big q s) :
      FreeMagma.mul p q = FreeMagma.mul r s ∨ Up (.mul p q) (.mul r s) ∨
        Up (.mul r s) (.mul p q) ∨ Big (.mul p q) (.mul r s) := by
    have hpr := unshared_mul p q r s
    have hrp := unshared_mul r s p q
    rcases hl with hl | hl | hl | hl <;> rcases hr with hr | hr | hr | hr
    all_goals
      try have hln := congrArg FreeMagma.length hl
      try have hrn := congrArg FreeMagma.length hr
      simp only [Up, Big, FreeMagma.length] at *
      first
      | exact Or.inl (congrArg₂ FreeMagma.mul hl hr)
      | right; left; omega
      | right; right; left; omega
      | right; right; right; omega
  have comparison (p q : Source) (h : Nonconflict (thirdImage p) (thirdImage q)) :
      thirdImage p = thirdImage q ∨ Up (thirdImage p) (thirdImage q) ∨
        Up (thirdImage q) (thirdImage p) ∨ Big (thirdImage p) (thirdImage q) := by
    induction p generalizing q with
    | of b =>
      cases q with
      | of c =>
        cases b <;> cases c
        · exact Or.inl rfl
        · exact False.elim (by exact (show ¬ Nonconflict C A by
            simp [Nonconflict, C, A, E]) h)
        · exact False.elim (by exact (show ¬ Nonconflict A C by
            simp [Nonconflict, A, C, E]) h)
        · exact Or.inl rfl
      | mul q s =>
        rw [r_mul] at h ⊢
        exact Or.inr (Or.inl (atomic_composite b q s h))
    | mul p r hp hr =>
      cases q with
      | of b =>
        rw [r_mul] at h ⊢
        exact Or.inr (Or.inr (Or.inl (atomic_composite b p r (nc_symm _ _ h))))
      | mul q s =>
        rw [r_mul, r_mul] at h ⊢
        exact combine _ _ _ _ (hp q h.1) (hr s h.2)
  refine ⟨fun p => ⟨addresses_card p, label_address p⟩, ?_, ?_, ?_⟩
  · intro p q
    exact ⟨shared_card p q, unshared_card p q, nc_semantics p q⟩
  · intro P Q n hP hQ hne hPn hQn hnc
    rcases hP with ⟨p, rfl⟩
    rcases hQ with ⟨q, rfl⟩
    have hbig : Big (thirdImage p) (thirdImage q) := by
      rcases comparison p q hnc with heq | hup | hdown | hbig
      · exact False.elim (hne heq)
      · dsimp [Up] at hup; omega
      · dsimp [Up] at hdown; omega
      · exact hbig
    have hs := shared_symm (thirdImage p) (thirdImage q)
    dsimp [Big, unsharedLeaves] at hbig
    dsimp [unsharedLeaves]
    omega
  · dsimp [PThirteen, QThirteen, pThirteen, qThirteen, A, C, E,
      thirdImage, Nonconflict, sharedLeaves, unsharedLeaves,
      composition, FreeMagma.length, sharpShared]
    decide

end D5.S3.Arith.FibonacciAtomic.ActualImageSevenLeafSeparation

#print axioms D5.S3.Arith.FibonacciAtomic.ActualImageSevenLeafSeparation.seven_leaf_separation
