/- GID: D5/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Sharp alpha separation of actual third images. -/

import D5.S3.Arith.FibonacciAtomic.ActualImageSevenLeafSeparation
import D5.S3.Arith.FibonacciAtomic.ActualImageAddressCertificate
import D5.S3.Arith.FibonacciAtomic.SourceTransportCentralizer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.ActualImageAlphaSeparation

open GenealogicalFiberTransport (Source substitution composition)
open ActualImageAddressCertificate (ActualImage replace alpha_mul)
open ActualLeafHistoryRigidity (alphaLeaves subtree OutputContext)
open ActualImageSevenLeafSeparation (leafAddresses leafLabel sharedLeaves unsharedLeaves Nonconflict E A C)

open ActualTreeReadoutAcquisition (Address)

/-- The directed alpha deficit uses the original alpha-address sets. -/
def delta (P Q : Source) : ℕ := (alphaLeaves P \ alphaLeaves Q).card

/-- Apply a map to every fixed sibling and insert the tree at the hole. -/
def fillContext (g : Source → Source) : OutputContext → Source → Source
  | .hole, X => X
  | .left H R, X => .mul ((fillContext g H) X) (g R)
  | .right L H, X => .mul (g L) ((fillContext g H) X)

/-- Two holes separated at their lowest common ancestor. The Boolean records
which named hole occurs in its left branch. Fixed siblings remain source trees. -/
structure TwoHole where
  outer : OutputContext
  left : OutputContext
  right : OutputContext
  swapped : Bool

/-- Insert both named holes, applying the same map to all fixed source trees. -/
def TwoHole.fill (J : TwoHole) (g : Source → Source) (X Y : Source) : Source :=
  (ActualImageAlphaSeparation.fillContext g J.outer)
    (if J.swapped then
      .mul ((ActualImageAlphaSeparation.fillContext g J.left) Y)
        ((ActualImageAlphaSeparation.fillContext g J.right) X)
    else .mul ((ActualImageAlphaSeparation.fillContext g J.left) X)
      ((ActualImageAlphaSeparation.fillContext g J.right) Y))

/-- The two named hole addresses. -/
def TwoHole.addresses (J : TwoHole) : Address × Address :=
  if J.swapped then
    (J.outer.holeAddress ++ true :: J.right.holeAddress,
      J.outer.holeAddress ++ false :: J.left.holeAddress)
  else (J.outer.holeAddress ++ false :: J.left.holeAddress,
    J.outer.holeAddress ++ true :: J.right.holeAddress)

/-- Canonical divergence is computed on complete preimages, stopping whenever
they agree and recording the current address at an atom-compound comparison. -/
def frontier : Source → Source → Finset Address
  | S, T => if S = T then ∅ else
    match S, T with
    | .mul L R, .mul U V => (frontier L U).image (List.cons false) ∪
        (frontier R V).image (List.cons true)
    | _, _ => {[]}

/-- Count frontier holes at which the first preimage is atomic. -/
def forwardCount : Source → Source → ℕ
  | .of _, .mul _ _ => 1
  | .mul L R, .mul U V => forwardCount L U + forwardCount R V
  | _, _ => 0

/-- The literal normal form includes the complete common context, both hole
addresses, the canonical frontier, and both actual address replacements. -/
def NormalForm (S T : Source) : Prop := ∃ J : TwoHole, ∃ y : Source,
  (y = .of false ∨ y = .mul (.of true) (.of true)) ∧
  S = J.fill id (.of false) (.mul (.of true) y) ∧
  T = J.fill id (.mul (.of true) y) (.of false) ∧
  frontier S T = {J.addresses.1, J.addresses.2} ∧
  (frontier S T).card = 2 ∧
  ¬ J.addresses.1.IsPrefix J.addresses.2 ∧
  ¬ J.addresses.2.IsPrefix J.addresses.1 ∧
  substitution^[3] S = replace (replace (substitution^[3] (J.fill id (.of false) (.of false)))
    J.addresses.1 C) J.addresses.2 (.mul A (substitution^[3] y)) ∧
  substitution^[3] T = replace (replace (substitution^[3] (J.fill id (.of false) (.of false)))
    J.addresses.1 (.mul A (substitution^[3] y))) J.addresses.2 C

/-- Sharp alpha separation, retaining
all literal two-hole equality cases. -/
theorem result :
    (∀ S T : Source, substitution^[3] S ≠ substitution^[3] T →
      FreeMagma.length (substitution^[3] S) = FreeMagma.length (substitution^[3] T) →
      Nonconflict (substitution^[3] S) (substitution^[3] T) →
      3 ≤ delta (substitution^[3] S) (substitution^[3] T) ∧
      3 ≤ delta (substitution^[3] T) (substitution^[3] S) ∧
      (delta (substitution^[3] S) (substitution^[3] T) = 3 ↔ NormalForm S T) ∧
      (delta (substitution^[3] T) (substitution^[3] S) = 3 ↔ NormalForm S T) ∧
      (delta (substitution^[3] S) (substitution^[3] T) = 3 →
        composition (substitution^[3] S) = composition (substitution^[3] T) ∧
        composition S = composition T)) ∧
    (∀ J : TwoHole, ∀ y : Source,
      (y = .of false ∨ y = .mul (.of true) (.of true)) →
      let S := J.fill id (.of false) (.mul (.of true) y)
      let T := J.fill id (.mul (.of true) y) (.of false)
      substitution^[3] S ∈ ActualImage 3 ∧ substitution^[3] T ∈ ActualImage 3 ∧
      NormalForm S T ∧ substitution^[3] S ≠ substitution^[3] T ∧
      FreeMagma.length (substitution^[3] S) = FreeMagma.length (substitution^[3] T) ∧ Nonconflict (substitution^[3] S) (substitution^[3] T) ∧
      delta (substitution^[3] S) (substitution^[3] T) = 3 ∧ delta (substitution^[3] T) (substitution^[3] S) = 3 ∧
      composition (substitution^[3] S) = composition (substitution^[3] T) ∧ composition S = composition T ∧
      unsharedLeaves (substitution^[3] S) (substitution^[3] T) = (if y = .of false then 7 else 8) ∧
      unsharedLeaves (substitution^[3] T) (substitution^[3] S) = (if y = .of false then 7 else 8)) := by
  let f : Source → Source := substitution^[3]
  have f_alpha : f (.of true) = A := rfl
  have f_beta : f (.of false) = C := rfl
  have f_pair (p q : Source) : f (.mul p q) = .mul (f p) (f q) := by
    exact Function.Semiconj₂.iterate
      (show Function.Semiconj₂ substitution FreeMagma.mul FreeMagma.mul from
        fun p q => substitution.map_mul p q) 3 p q
  have injective : Function.Injective f :=
    SourceTransportCentralizer.source_transport_centralizer.2.2.1 f ⟨f_pair, fun _ => rfl⟩
  have eq_A (p : Source) : f p = A ↔ p = .of true :=
    ⟨fun h => injective (h.trans f_alpha.symm), fun h => by rw [h, f_alpha]⟩
  have pref_disjoint (X Y : Finset Address) :
      Disjoint (X.image (List.cons false)) (Y.image (List.cons true)) := by
    simp only [Finset.disjoint_left, Finset.mem_image]
    rintro _ ⟨u, _, rfl⟩ ⟨v, _, he⟩
    cases he
  have n_pair (X Y : Source) : FreeMagma.length (.mul X Y) = FreeMagma.length X + FreeMagma.length Y := rfl
  have s_pair (X Y Z W : Source) :
      sharedLeaves (.mul X Y) (.mul Z W) = sharedLeaves X Z + sharedLeaves Y W := rfl
  have nc_pair (X Y Z W : Source) :
      Nonconflict (.mul X Y) (.mul Z W) ↔ Nonconflict X Z ∧ Nonconflict Y W := Iff.rfl
  have nc_symm (X Y : Source) : Nonconflict X Y → Nonconflict Y X := by
    intro h
    apply (ActualImageSevenLeafSeparation.seven_leaf_separation.2.1 Y X).2.2.mpr
    intro u a b ha hb
    exact ((ActualImageSevenLeafSeparation.seven_leaf_separation.2.1 X Y).2.2.mp
      h u b a hb ha).symm
  have s_le (X Y : Source) : sharedLeaves X Y ≤ FreeMagma.length X := by
    rw [(ActualImageSevenLeafSeparation.seven_leaf_separation.2.1 X Y).1,
      ← (ActualImageSevenLeafSeparation.seven_leaf_separation.1 X).1]
    exact Finset.card_le_card Finset.inter_subset_left
  have nu_pair (X Y Z W : Source) :
      unsharedLeaves (.mul X Y) (.mul Z W) = unsharedLeaves X Z + unsharedLeaves Y W := by
    have h1 := s_le X Z
    have h2 := s_le Y W
    simp only [unsharedLeaves, n_pair, s_pair]
    omega
  have s_self (X : Source) : sharedLeaves X X = FreeMagma.length X := by rw [(ActualImageSevenLeafSeparation.seven_leaf_separation.2.1 X X).1,
    Finset.inter_self, (ActualImageSevenLeafSeparation.seven_leaf_separation.1 X).1]
  have nu_self (X : Source) : unsharedLeaves X X = 0 := by simp [unsharedLeaves, s_self]
  have root (p : Source) : ∃ X Y, f p = .mul X Y := by
    cases p with
    | of b => cases b <;> first | exact ⟨A, E, f_beta⟩ | exact ⟨E, .of false, f_alpha⟩
    | mul p q => exact ⟨f p, f q, f_pair p q⟩
  have counts : FreeMagma.length A = 3 ∧ FreeMagma.length C = 5 ∧ FreeMagma.length E = 2 := by decide
  let m (X : Source) := (alphaLeaves X).card
  let shared (X Y : Source) := (alphaLeaves X ∩ alphaLeaves Y).card
  have m_pair (X Y : Source) : m (.mul X Y) = m X + m Y := by
    dsimp only [m]
    rw [FreeMagma.mul_eq, alpha_mul, Finset.card_union_of_disjoint (pref_disjoint _ _)]
    simp only [Finset.card_image_of_injective _ List.cons_injective]
  have shared_pair (X Y Z W : Source) :
      shared (.mul X Y) (.mul Z W) = shared X Z + shared Y W := by
    have hi : alphaLeaves (.mul X Y) ∩ alphaLeaves (.mul Z W) =
        ((alphaLeaves X ∩ alphaLeaves Z).image (List.cons false)) ∪
        ((alphaLeaves Y ∩ alphaLeaves W).image (List.cons true)) := by
      ext u; cases u with
      | nil => simp [alpha_mul, alphaLeaves, leafAddresses, ActualTreeReadoutAcquisition.leaves, ActualTreeReadoutAcquisition.readout]
      | cons b u => cases b <;> simp [alpha_mul, alphaLeaves, leafAddresses, ActualTreeReadoutAcquisition.leaves, ActualTreeReadoutAcquisition.readout]
    dsimp only [shared]; rw [hi, Finset.card_union_of_disjoint (pref_disjoint _ _)]
    simp only [Finset.card_image_of_injective _ List.cons_injective]
  have delta_eq (X Y : Source) : delta X Y = m X - shared X Y :=
    by simpa only [delta, m, shared, Finset.inter_comm] using
      (Finset.card_sdiff (s := alphaLeaves Y) (t := alphaLeaves X))
  have shared_le (X Y : Source) : shared X Y ≤ m X :=
    Finset.card_le_card Finset.inter_subset_left
  have shared_symm (X Y : Source) : shared X Y = shared Y X := by
    simp only [shared, Finset.inter_comm]
  have delta_pair (X Y Z W : Source) :
      delta (.mul X Y) (.mul Z W) = delta X Z + delta Y W := by
    have h1 := shared_le X Z; have h2 := shared_le Y W
    rw [delta_eq, delta_eq, delta_eq, m_pair, shared_pair]; omega
  have delta_self (X : Source) : delta X X = 0 := by simp [delta]
  have alpha_leaves (X : Source) : alphaLeaves X ⊆ leafAddresses X :=
    Finset.filter_subset _ _
  have shared_zero (X Y : Source) (h : sharedLeaves X Y = 0) : shared X Y = 0 := by
    have hh := Finset.card_le_card (Finset.inter_subset_inter (alpha_leaves X) (alpha_leaves Y))
    rw [← (ActualImageSevenLeafSeparation.seven_leaf_separation.2.1 X Y).1] at hh
    change shared X Y ≤ sharedLeaves X Y at hh
    omega
  have alpha_nil (p : Source) : [] ∉ alphaLeaves (f p) := by
    obtain ⟨X, Y, he⟩ := root p; rw [he]; simp [alpha_mul, alphaLeaves, leafAddresses, ActualTreeReadoutAcquisition.leaves, ActualTreeReadoutAcquisition.readout]
  have shared_E (p : Source) : shared E (f p) = 0 := by
    cases p with
    | of b => cases b <;> decide
    | mul p q =>
      have hE : alphaLeaves E = {[true]} := by decide
      rw [f_pair]
      simp [shared, hE, alpha_mul, alpha_nil, FreeMagma.mul_eq]
  have m_counts : m A = 1 ∧ m C = 2 := by decide
  have min_alpha (p : Source) : 1 ≤ m (f p) := by
    induction p with
    | of b => cases b <;> simp only [f_alpha, f_beta] <;> omega
    | mul p q hp hq => rw [f_pair, m_pair]; omega
  have one_alpha (p : Source) (h : m (f p) = 1) : p = .of true := by
    cases p with
    | of b => cases b <;> simp only [f_alpha, f_beta] at h <;> first | rfl | omega
    | mul p q =>
      have hp := min_alpha p; have hq := min_alpha q
      rw [f_pair, m_pair] at h; omega
  have two_alpha (p : Source) (h : m (f p) = 2) :
      p = .of false ∨ p = .mul (.of true) (.of true) := by
    cases p with
    | of b => cases b <;> simp only [f_alpha, f_beta] at h <;> first | exact Or.inl rfl | omega
    | mul p q =>
      have hp := min_alpha p; have hq := min_alpha q
      rw [f_pair, m_pair] at h
      rw [one_alpha p (by omega), one_alpha q (by omega)]; exact Or.inr rfl
  have min_size (p : Source) : 3 ≤ FreeMagma.length (f p) :=
    ActualImageSevenLeafSeparation.minimum p
  have not_A_size (p : Source) (hp : f p ≠ A) : 5 ≤ FreeMagma.length (f p) :=
    ActualImageSevenLeafSeparation.not_alpha_minimum p
      (fun h => hp ((eq_A p).mpr h))
  have E_actual (p : Source) :
      (Nonconflict E (f p) ↔ f p ≠ A) ∧
      sharedLeaves E (f p) = if f p = A then 1 else 0 := by
    constructor
    · exact (ActualImageSevenLeafSeparation.e_image p).trans (not_congr (eq_A p).symm)
    · by_cases hp : p = .of true
      · subst p; rw [f_alpha, if_pos rfl]; rfl
      · rw [if_neg (fun h => hp ((eq_A p).mp h))]
        exact ActualImageSevenLeafSeparation.e_shared p hp
  have A_compound (p q : Source) :
      (Nonconflict A (.mul (f p) (f q)) ↔ f p ≠ A) ∧
      (Nonconflict A (.mul (f p) (f q)) →
        sharedLeaves A (.mul (f p) (f q)) = 0) := by
    constructor
    · constructor
      · intro h
        exact fun he => (ActualImageSevenLeafSeparation.a_composite p q h).1
          ((eq_A p).mp he)
      · intro h
        exact ⟨(ActualImageSevenLeafSeparation.e_image p).mpr
          (fun hp => h ((eq_A p).mpr hp)),
          (ActualImageSevenLeafSeparation.atom_image false q).1⟩
    · intro h
      exact (ActualImageSevenLeafSeparation.a_composite p q h).2.1
  have A_C_conflict : ¬ Nonconflict A C := by
    simp [Nonconflict, A, C, E]
  have alpha_table (b : Bool) (p q : Source)
      (h : Nonconflict (f (.of b)) (.mul (f p) (f q))) :
      1 ≤ delta (f (.of b)) (.mul (f p) (f q)) ∧
      2 ≤ delta (.mul (f p) (f q)) (f (.of b)) ∧
      (delta (f (.of b)) (.mul (f p) (f q)) = 1 →
        FreeMagma.length (f (.of b)) + 5 ≤ FreeMagma.length (.mul (f p) (f q)) ∨
          (b = false ∧ p = .of true ∧
            FreeMagma.length (.mul (f p) (f q)) = 3 + FreeMagma.length (f q))) ∧
      (delta (.mul (f p) (f q)) (f (.of b)) = 2 →
        b = false ∧ p = .of true ∧
          (q = .of false ∨ q = .mul (.of true) (.of true))) := by
    cases b with
    | true =>
      rw [f_alpha] at h ⊢
      have hp := (A_compound p q).1.mp h
      have hs := shared_zero A (.mul (f p) (f q)) ((A_compound p q).2 h)
      have hm := min_alpha p; have hq := min_alpha q
      have hm2 : 2 ≤ m (f p) := by
        by_contra hn; exact hp (by rw [one_alpha p (by omega), f_alpha])
      have hn := not_A_size p hp; have hqn := min_size q
      rw [delta_eq, delta_eq, shared_symm (.mul (f p) (f q)) A, hs, m_pair]
      simp only [n_pair]; refine ⟨by omega, by omega, fun _ => Or.inl (by omega), ?_⟩
      omega
    | false =>
      rw [f_beta] at h ⊢
      obtain ⟨hL, hR⟩ := (nc_pair A E (f p) (f q)).mp h
      have hq := (E_actual q).1.mp hR
      have hqm := min_alpha q
      have hqm2 : 2 ≤ m (f q) := by
        by_contra hn; exact hq (by rw [one_alpha q (by omega), f_alpha])
      cases p with
      | of b =>
        cases b with
        | false => rw [f_beta] at hL; exact (A_C_conflict hL).elim
        | true =>
          have hs : shared C (.mul (f (.of true)) (f q)) = 1 := by
            change shared (.mul A E) (.mul (f (.of true)) (f q)) = 1
            rw [shared_pair, f_alpha, shared_E]; simp only [shared, Finset.inter_self]; exact m_counts.1
          rw [delta_eq, delta_eq, shared_symm (.mul (f (.of true)) (f q)) C,
            hs, m_pair, f_alpha]
          refine ⟨by omega, by omega, fun _ => Or.inr ⟨rfl, rfl, ?_⟩, ?_⟩
          · rw [n_pair, counts.1]
          · intro he; exact ⟨rfl, rfl, two_alpha q (by omega)⟩
      | mul p r =>
        rw [f_pair] at hL ⊢
        have hp := (A_compound p r).1.mp hL
        have hpm := min_alpha p; have hrm := min_alpha r
        have hp2 : 2 ≤ m (f p) := by
          by_contra hn; exact hp (by rw [one_alpha p (by omega), f_alpha])
        have hs : shared C (.mul (.mul (f p) (f r)) (f q)) = 0 := by
          change shared (.mul A E) (.mul (.mul (f p) (f r)) (f q)) = 0
          rw [shared_pair, shared_zero A _ ((A_compound p r).2 hL), shared_E]
        rw [delta_eq, delta_eq, shared_symm (.mul (.mul (f p) (f r)) (f q)) C,
          hs, m_pair, m_pair]
        exact ⟨by omega, by omega, by omega, by omega⟩
  have small_5 (p : Source) (h : FreeMagma.length (f p) ≤ 5) : f p = A ∨ f p = C := by
    cases p with
    | of b => cases b <;> first | exact Or.inr f_beta | exact Or.inl f_alpha
    | mul p q =>
      have hp := min_size p
      have hq := min_size q
      rw [f_pair, n_pair] at h
      omega
  have small_6 (p : Source) (h : FreeMagma.length (f p) ≤ 6) :
      f p = A ∨ f p = C ∨ f p = .mul A A := by
    cases p with
    | of b =>
      cases b <;> first | exact Or.inr (Or.inl f_beta) | exact Or.inl f_alpha
    | mul p q =>
      have hp := min_size p
      have hq := min_size q
      rw [f_pair, n_pair] at h
      have lp := small_5 p (by omega)
      have lq := small_5 q (by omega)
      rw [f_pair]
      rcases lp with lp | lp <;> rcases lq with lq | lq
      all_goals rw [lp, lq] at h ⊢
      · exact Or.inr (Or.inr rfl)
      all_goals omega
  have alpha_bound (p q : Source) (hc : Nonconflict (f p) (f q)) :
      forwardCount p q + 2 * forwardCount q p ≤ delta (f p) (f q) := by
    induction p generalizing q with
    | of b =>
      cases q with
      | of c =>
        cases b <;> cases c <;> simp only [forwardCount] <;> omega
      | mul q t => rw [f_pair] at hc ⊢; exact (alpha_table b q t hc).1
    | mul p r hp hr =>
      cases q with
      | of b =>
        rw [f_pair] at hc ⊢
        exact (alpha_table b p r (nc_symm _ _ hc)).2.1
      | mul q t =>
        rw [f_pair, f_pair, nc_pair] at hc
        have hL := hp q hc.1; have hR := hr t hc.2
        rw [f_pair, f_pair, delta_pair]; simp only [forwardCount]; omega
  have zero_same (p q : Source) (hc : Nonconflict (f p) (f q))
      (hk : forwardCount p q = 0) (hl : forwardCount q p = 0) : p = q := by
    induction p generalizing q with
    | of b =>
      cases q with
      | of c =>
        cases b <;> cases c
        · rfl
        · rw [f_beta, f_alpha] at hc; exact (A_C_conflict (nc_symm _ _ hc)).elim
        · rw [f_alpha, f_beta] at hc; exact (A_C_conflict hc).elim
        · rfl
      | mul q t => simp [forwardCount] at hk
    | mul p r hp hr =>
      cases q with
      | of b => simp [forwardCount] at hl
      | mul q t =>
        rw [f_pair, f_pair, nc_pair] at hc
        simp only [forwardCount] at hk hl
        rw [hp q hc.1 (by omega) (by omega), hr t hc.2 (by omega) (by omega)]
  have one_side (p q : Source) (hc : Nonconflict (f p) (f q))
      (hl : forwardCount q p = 0) :
      FreeMagma.length (f p) ≤ FreeMagma.length (f q) ∧ (0 < forwardCount p q → FreeMagma.length (f p) < FreeMagma.length (f q)) := by
    induction p generalizing q with
    | of b =>
      cases q with
      | of c =>
        have he := zero_same (.of b) (.of c) hc rfl rfl
        rw [he]; exact ⟨le_rfl, by simp [forwardCount]⟩
      | mul q t =>
        rw [f_pair] at hc ⊢
        have hq := min_size q
        have ht := min_size t
        have he : FreeMagma.length (f (.of b)) < FreeMagma.length (.mul (f q) (f t)) := by
          cases b <;> simp only [f_alpha, f_beta, n_pair, counts.1, counts.2.1] <;> omega
        exact ⟨he.le, fun _ => he⟩
    | mul p r hp hr =>
      cases q with
      | of b => simp [forwardCount] at hl
      | mul q t =>
        rw [f_pair, f_pair, nc_pair] at hc
        simp only [forwardCount] at hl
        have hL := hp q hc.1 (by omega); have hR := hr t hc.2 (by omega)
        rw [f_pair, f_pair, n_pair, n_pair]; simp only [forwardCount]; constructor <;> omega
  have map_one (H : OutputContext) (X : Source) : f ((fillContext id H) X) = (fillContext f H) (f X) := by
    induction H with
    | hole => rfl
    | left H R ih => simp only [fillContext, id_eq, f_pair, ih]
    | right L H ih => simp only [fillContext, id_eq, f_pair, ih]
  have map_two (J : TwoHole) (X Y : Source) :
      f (J.fill id X Y) = J.fill f (f X) (f Y) := by
    cases h : J.swapped <;> simp only [TwoHole.fill, h, Bool.false_eq_true,
      ↓reduceIte, map_one, f_pair]
  have one_data (g : Source → Source) (H : OutputContext) (X Y : Source) :
      delta ((fillContext g H) X) ((fillContext g H) Y) = delta X Y ∧
      unsharedLeaves ((fillContext g H) X) ((fillContext g H) Y) = unsharedLeaves X Y ∧
      FreeMagma.length ((fillContext g H) X) + FreeMagma.length Y = FreeMagma.length ((fillContext g H) Y) + FreeMagma.length X ∧
      (Nonconflict ((fillContext g H) X) ((fillContext g H) Y) ↔ Nonconflict X Y) ∧
      (composition X = composition Y → composition ((fillContext g H) X) = composition ((fillContext g H) Y)) := by
    have nc_self (Z : Source) : Nonconflict Z Z :=
      (ActualImageSevenLeafSeparation.seven_leaf_separation.2.1 Z Z).2.2.mpr
        (fun _ _ _ ha hb => Option.some.inj (ha.symm.trans hb))
    induction H with
    | hole => exact ⟨rfl, rfl, Nat.add_comm _ _, Iff.rfl, id⟩
    | left H R ih =>
      simp only [fillContext, delta_pair, delta_self, nu_pair, nu_self,
        add_zero, n_pair, nc_pair, nc_self, and_true]
      exact ⟨ih.1, ih.2.1, by omega, ih.2.2.2.1,
        fun he => by simp only [composition, ih.2.2.2.2 he]⟩
    | right L H ih =>
      simp only [fillContext, delta_pair, delta_self, nu_pair, nu_self,
        zero_add, n_pair, nc_pair, nc_self, true_and]
      exact ⟨ih.1, ih.2.1, by omega, ih.2.2.2.1,
        fun he => by simp only [composition, ih.2.2.2.2 he]⟩
  have two_data (g : Source → Source) (J : TwoHole) (X Y U V : Source) :
      delta (J.fill g X Y) (J.fill g U V) = delta X U + delta Y V ∧
      unsharedLeaves (J.fill g X Y) (J.fill g U V) = unsharedLeaves X U + unsharedLeaves Y V ∧
      FreeMagma.length (J.fill g X Y) + FreeMagma.length U + FreeMagma.length V = FreeMagma.length (J.fill g U V) + FreeMagma.length X + FreeMagma.length Y ∧
      (Nonconflict (J.fill g X Y) (J.fill g U V) ↔ Nonconflict X U ∧ Nonconflict Y V) := by
    have hL := one_data g J.left X U; have hR := one_data g J.right Y V
    have hL' := one_data g J.left Y V; have hR' := one_data g J.right X U
    cases h : J.swapped <;>
      simp only [TwoHole.fill, h, Bool.false_eq_true, ↓reduceIte,
        (one_data g J.outer _ _).1, (one_data g J.outer _ _).2.1,
        (one_data g J.outer _ _).2.2.2.1, delta_pair, nu_pair, nc_pair]
    · exact ⟨by rw [hL.1, hR.1], by rw [hL.2.1, hR.2.1],
        by have ho := (one_data g J.outer (.mul ((fillContext g J.left) X) ((fillContext g J.right) Y))
            (.mul ((fillContext g J.left) U) ((fillContext g J.right) V))).2.2.1
           simp only [n_pair] at ho; omega,
        by rw [hL.2.2.2.1, hR.2.2.2.1]⟩
    · exact ⟨by rw [hL'.1, hR'.1, Nat.add_comm],
        by rw [hL'.2.1, hR'.2.1, Nat.add_comm],
        by have ho := (one_data g J.outer (.mul ((fillContext g J.left) Y) ((fillContext g J.right) X))
            (.mul ((fillContext g J.left) V) ((fillContext g J.right) U))).2.2.1
           simp only [n_pair] at ho; omega,
        by rw [hL'.2.2.2.1, hR'.2.2.2.1, and_comm]⟩
  have path_replace (g : Source → Source) (H : OutputContext) (M X : Source) (u : Address) :
      replace ((fillContext g H) M) (H.holeAddress ++ u) X = (fillContext g H) (replace M u X) := by
    induction H with
    | hole => rfl
    | left H R ih => simpa only [fillContext, OutputContext.holeAddress, List.cons_append, replace] using congrArg (fun z => FreeMagma.mul z (g R)) ih
    | right L H ih => simpa only [fillContext, OutputContext.holeAddress, List.cons_append, replace] using congrArg (FreeMagma.mul (g L)) ih
  have literal_two (g : Source → Source) (J : TwoHole) (X Y Z W : Source) :
      replace (replace (J.fill g Z W) J.addresses.1 X) J.addresses.2 Y = J.fill g X Y := by
    have at_hole (H : OutputContext) (P Q : Source) : replace ((fillContext g H) P) H.holeAddress Q = (fillContext g H) Q :=
      by simpa only [List.append_nil, replace] using path_replace g H P Q []
    cases h : J.swapped <;> simp only [TwoHole.fill, TwoHole.addresses, h,
      Bool.false_eq_true, ↓reduceIte, path_replace, replace, at_hole]
  have frontier_self (S : Source) : frontier S S = ∅ := by cases S <;> simp [frontier]
  have frontier_pair (S T U V : Source) : frontier (.mul S T) (.mul U V) =
      (frontier S U).image (List.cons false) ∪ (frontier T V).image (List.cons true) := by
    by_cases he : (.mul S T : Source) = .mul U V
    · injection he with hS hT; subst U; subst V; simp only [frontier_self, Finset.image_empty, Finset.union_empty]
    · simp only [frontier, if_neg he]
  have frontier_one (H : OutputContext) (S T : Source) :
      frontier ((fillContext id H) S) ((fillContext id H) T) = (frontier S T).image (fun u => H.holeAddress ++ u) := by
    induction H with
    | hole => simp [fillContext, OutputContext.holeAddress]
    | left H R ih => simp only [fillContext, id_eq, OutputContext.holeAddress, frontier_pair,
        frontier_self, Finset.image_empty, Finset.union_empty, ih,
        Finset.image_image, Function.comp_def, List.cons_append]
    | right L H ih => simp only [fillContext, id_eq, OutputContext.holeAddress, frontier_pair,
        frontier_self, Finset.image_empty, Finset.empty_union, ih,
        Finset.image_image, Function.comp_def, List.cons_append]
  have context_frontier (J : TwoHole) (b c : Bool) (X Y U V : Source) :
      frontier (J.fill id (.of b) (.mul U V)) (J.fill id (.mul X Y) (.of c)) =
        {J.addresses.1, J.addresses.2} := by
    have atom_front (b : Bool) (X Y : Source) : frontier (.of b) (.mul X Y) = {[]} ∧
        frontier (.mul X Y) (.of b) = {[]} := by simp [frontier]
    cases h : J.swapped <;> simp only [TwoHole.fill, TwoHole.addresses, h,
      Bool.false_eq_true, ↓reduceIte, frontier_one, frontier_pair, (atom_front _ _ _).1,
      (atom_front _ _ _).2, Finset.image_singleton, List.append_nil,
      Finset.image_union, Finset.singleton_union, Finset.image_insert, Finset.image_singleton]
    all_goals first | rfl | exact Finset.pair_comm _ _
  have addresses_apart (J : TwoHole) :
      ¬ J.addresses.1.IsPrefix J.addresses.2 ∧ ¬ J.addresses.2.IsPrefix J.addresses.1 := by
    cases h : J.swapped <;> simp [TwoHole.addresses, h, List.prefix_self_append_iff]
  have one_hole (p q : Source) (hc : Nonconflict (f p) (f q))
      (hk : forwardCount p q = 1) (hl : forwardCount q p = 0) :
      ∃ H : OutputContext, ∃ b : Bool, ∃ X Y : Source,
        p = (fillContext id H) (.of b) ∧ q = (fillContext id H) (.mul X Y) ∧
          Nonconflict (f (.of b)) (.mul (f X) (f Y)) := by
    induction p generalizing q with
    | of b =>
      cases q with
      | of c => simp [forwardCount] at hk
      | mul X Y => exact ⟨.hole, b, X, Y, rfl, rfl, by simpa only [f_pair] using hc⟩
    | mul p r hp hr =>
      cases q with
      | of b => simp [forwardCount] at hl
      | mul q t =>
        rw [f_pair, f_pair, nc_pair] at hc
        simp only [forwardCount] at hk hl
        by_cases hL : forwardCount p q = 0
        · have he := zero_same p q hc.1 hL (by omega)
          obtain ⟨H, b, X, Y, h1, h2, h3⟩ := hr t hc.2 (by omega) (by omega)
          exact ⟨.right p H, b, X, Y, by simp [fillContext, h1],
            by simp [fillContext, he, h2], h3⟩
        · have he := zero_same r t hc.2 (by omega) (by omega)
          obtain ⟨H, b, X, Y, h1, h2, h3⟩ := hp q hc.1 (by omega) (by omega)
          exact ⟨.left H r, b, X, Y, by simp [fillContext, h1],
            by simp [fillContext, he, h2], h3⟩
  have two_holes (p q : Source) (hc : Nonconflict (f p) (f q))
      (hk : forwardCount p q = 1) (hl : forwardCount q p = 1) :
      ∃ J : TwoHole, ∃ b c : Bool, ∃ X Y U V : Source,
        p = J.fill id (.of b) (.mul U V) ∧
        q = J.fill id (.mul X Y) (.of c) ∧
        Nonconflict (f (.of b)) (.mul (f X) (f Y)) ∧
        Nonconflict (f (.of c)) (.mul (f U) (f V)) := by
    induction p generalizing q with
    | of b => cases q <;> simp [forwardCount] at hk hl
    | mul p r hp hr =>
      cases q with
      | of b => simp [forwardCount] at hk
      | mul q t =>
        rw [f_pair, f_pair, nc_pair] at hc
        simp only [forwardCount] at hk hl
        by_cases hkL : forwardCount p q = 0
        · by_cases hlL : forwardCount q p = 0
          · have he := zero_same p q hc.1 hkL hlL
            obtain ⟨J, b, c, X, Y, U, V, h1, h2, h3, h4⟩ := hr t hc.2 (by omega) (by omega)
            exact ⟨{ J with outer := .right p J.outer }, b, c, X, Y, U, V,
              by simpa [TwoHole.fill, fillContext] using congrArg (FreeMagma.mul p) h1,
              by simpa [TwoHole.fill, fillContext, ← he] using congrArg (FreeMagma.mul p) h2,
              h3, h4⟩
          · obtain ⟨H, c, U, V, h1, h2, h3⟩ :=
              one_hole q p (nc_symm _ _ hc.1) (by omega) hkL
            obtain ⟨K, b, X, Y, h4, h5, h6⟩ := one_hole r t hc.2 (by omega) (by omega)
            exact ⟨⟨.hole, H, K, true⟩, b, c, X, Y, U, V,
              by simp [TwoHole.fill, fillContext, h2, h4],
              by simp [TwoHole.fill, fillContext, h1, h5], h6, h3⟩
        · by_cases hlL : forwardCount q p = 0
          · obtain ⟨H, b, X, Y, h1, h2, h3⟩ := one_hole p q hc.1 (by omega) hlL
            obtain ⟨K, c, U, V, h4, h5, h6⟩ :=
              one_hole t r (nc_symm _ _ hc.2) (by omega) (by omega)
            exact ⟨⟨.hole, H, K, false⟩, b, c, X, Y, U, V,
              by simp [TwoHole.fill, fillContext, h1, h5],
              by simp [TwoHole.fill, fillContext, h2, h4], h3, h6⟩
          · have he := zero_same r t hc.2 (by omega) (by omega)
            obtain ⟨J, b, c, X, Y, U, V, h1, h2, h3, h4⟩ := hp q hc.1 (by omega) (by omega)
            exact ⟨{ J with outer := .left J.outer r }, b, c, X, Y, U, V,
              by simpa [TwoHole.fill, fillContext] using congrArg (fun z => FreeMagma.mul z r) h1,
              by simpa [TwoHole.fill, fillContext, ← he] using congrArg (fun z => FreeMagma.mul z r) h2,
              h3, h4⟩
  have swap_composition (g : Source → Source) (J : TwoHole) (X Y : Source) :
      composition (J.fill g X Y) = composition (J.fill g Y X) := by
    have total (H : OutputContext) (U V : Source) :
        composition ((fillContext g H) U) + composition V = composition ((fillContext g H) V) + composition U := by
      induction H with
      | hole => exact add_comm _ _
      | left H R ih =>
        simpa only [fillContext, composition, add_assoc, add_left_comm, add_comm] using congrArg (fun z => z + composition (g R)) ih
      | right L H ih =>
        simpa only [fillContext, composition, add_assoc, add_left_comm, add_comm] using congrArg (fun z => composition (g L) + z) ih
    have hL := total J.left X Y; have hR := total J.right X Y
    apply (one_data g J.outer _ _).2.2.2.2
    cases h : J.swapped <;> simp only [TwoHole.fill, h, Bool.false_eq_true, ↓reduceIte] at ⊢
    all_goals apply Prod.ext <;> have a := congrArg Prod.fst hL <;> have b := congrArg Prod.snd hL <;>
      have c := congrArg Prod.fst hR <;> have d := congrArg Prod.snd hR <;>
      simp only [composition, Prod.fst_add, Prod.snd_add] at * <;> omega
  have normal_data (J : TwoHole) (y : Source)
      (hy : y = .of false ∨ y = .mul (.of true) (.of true)) :
      let S := J.fill id (.of false) (.mul (.of true) y)
      let T := J.fill id (.mul (.of true) y) (.of false)
      NormalForm S T ∧ f S ≠ f T ∧ FreeMagma.length (f S) = FreeMagma.length (f T) ∧ Nonconflict (f S) (f T) ∧
      delta (f S) (f T) = 3 ∧ delta (f T) (f S) = 3 ∧
      composition (f S) = composition (f T) ∧ composition S = composition T ∧
      unsharedLeaves (f S) (f T) = (if y = .of false then 7 else 8) ∧
      unsharedLeaves (f T) (f S) = (if y = .of false then 7 else 8) := by
    dsimp only
    have hn : NormalForm (J.fill id (.of false) (.mul (.of true) y))
        (J.fill id (.mul (.of true) y) (.of false)) := by
      refine ⟨J, y, hy, rfl, rfl, context_frontier J false false (.of true) y (.of true) y,
        ?_, (addresses_apart J).1, (addresses_apart J).2, ?_, ?_⟩
      · rw [context_frontier]; apply Finset.card_pair_eq_two_iff.mpr
        intro he; apply (addresses_apart J).1; rw [he]
      all_goals change f _ = replace (replace (f _) _ _) _ _
      all_goals rw [map_two, map_two, f_pair, f_alpha, f_beta]
      · exact (literal_two f J C (.mul A (f y)) C C).symm
      · exact (literal_two f J (.mul A (f y)) C C C).symm
    have d := two_data f J C (.mul A (f y)) (.mul A (f y)) C
    have e := two_data f J (.mul A (f y)) C C (.mul A (f y))
    have local_data : Nonconflict C (.mul A (f y)) ∧ Nonconflict (.mul A (f y)) C ∧
        delta C (.mul A (f y)) + delta (.mul A (f y)) C = 3 ∧
        unsharedLeaves C (.mul A (f y)) + unsharedLeaves (.mul A (f y)) C = (if y = .of false then 7 else 8) := by
      rcases hy with rfl | rfl <;>
        simp only [f_pair, f_alpha, f_beta, A, C, E, Nonconflict] <;> decide
    have hd : delta (f (J.fill id (.of false) (.mul (.of true) y)))
        (f (J.fill id (.mul (.of true) y) (.of false))) = 3 := by
      rw [map_two, map_two, f_pair, f_alpha, f_beta, d.1]; exact local_data.2.2.1
    refine ⟨hn, ?_, ?_, ?_, hd, ?_, ?_, ?_, ?_, ?_⟩
    · intro he; rw [he, delta_self] at hd; omega
    · rw [map_two, map_two, f_pair, f_alpha, f_beta]; have hh := d.2.2.1; omega
    · rw [map_two, map_two, f_pair, f_alpha, f_beta, d.2.2.2]; exact ⟨local_data.1, local_data.2.1⟩
    · rw [map_two, map_two, f_pair, f_alpha, f_beta, e.1, Nat.add_comm]; exact local_data.2.2.1
    · rw [map_two, map_two, f_pair, f_alpha, f_beta]; exact swap_composition f J _ _
    · exact swap_composition id J _ _
    · rw [map_two, map_two, f_pair, f_alpha, f_beta, d.2.1]; exact local_data.2.2.2
    · rw [map_two, map_two, f_pair, f_alpha, f_beta, e.2.1, Nat.add_comm]; exact local_data.2.2.2
  have positive_count (S T : Source) (hne : f S ≠ f T) (he : FreeMagma.length (f S) = FreeMagma.length (f T))
      (hc : Nonconflict (f S) (f T)) : 0 < forwardCount S T := by
    by_contra hn
    have hz : forwardCount S T = 0 := by omega
    have ht : 0 < forwardCount T S := by
      by_contra hn; exact hne (congrArg f (zero_same S T hc hz (by omega)))
    have hh := (one_side T S (nc_symm _ _ hc) hz).2 ht; omega
  have minimal (S T : Source) (hne : f S ≠ f T) (he : FreeMagma.length (f S) = FreeMagma.length (f T))
      (hc : Nonconflict (f S) (f T)) (hd : delta (f S) (f T) = 3) : NormalForm S T := by
    have hk := positive_count S T hne he hc
    have hl := positive_count T S (Ne.symm hne) he.symm (nc_symm _ _ hc)
    have hb := alpha_bound S T hc
    obtain ⟨J, b, c, X, Y, U, V, hS, hT, h1, h2⟩ := two_holes S T hc (by omega) (by omega)
    have d := two_data f J (f (.of b)) (.mul (f U) (f V)) (.mul (f X) (f Y)) (f (.of c))
    have a := alpha_table b X Y h1; have z := alpha_table c U V h2
    simp only [hS, hT, map_two, f_pair] at hd he
    have balance : FreeMagma.length (f (.of b)) + FreeMagma.length (.mul (f U) (f V)) =
        FreeMagma.length (.mul (f X) (f Y)) + FreeMagma.length (f (.of c)) := by have hgap := d.2.2.1; omega
    have hsmall : delta (.mul (f U) (f V)) (f (.of c)) = 2 := by rw [d.1] at hd; omega
    obtain ⟨rfl, rfl, hv⟩ := z.2.2.2 hsmall
    have nv : FreeMagma.length (f V) = 5 ∨ FreeMagma.length (f V) = 6 := by
      rcases hv with rfl | rfl
      · exact Or.inl (by decide)
      · exact Or.inr (by decide)
    simp only [f_alpha, f_beta, n_pair, counts.1, counts.2.1] at balance
    have hforward : delta (f (.of b)) (.mul (f X) (f Y)) = 1 := by rw [d.1] at hd; omega
    rcases a.2.2.1 hforward with hbad | ⟨rfl, rfl, _⟩
    · rw [n_pair] at hbad; omega
    · have hsize : FreeMagma.length (f Y) = FreeMagma.length (f V) := by
        simp only [f_alpha, f_beta, n_pair, counts.1, counts.2.1] at balance; omega
      have hY : Y = V := by
        apply injective
        rcases small_6 Y (by omega) with hY | hY | hY
        all_goals rw [hY] at hsize ⊢
        all_goals rcases hv with hv | hv <;> simp only [hv, f_beta, f_pair, f_alpha] at hsize ⊢
        all_goals simp only [n_pair, counts.1, counts.2.1, counts.2.2] at hsize
        all_goals first | rfl | omega
      subst Y
      rw [hS, hT]; exact (normal_data J V hv).1
  have normal_converse (S T : Source) (h : NormalForm S T) :
      delta (f S) (f T) = 3 ∧ composition (f S) = composition (f T) ∧ composition S = composition T := by
    obtain ⟨J, y, hy, rfl, rfl, _⟩ := h
    have d := normal_data J y hy; exact ⟨d.2.2.2.2.1, d.2.2.2.2.2.2.1, d.2.2.2.2.2.2.2.1⟩
  have normal_symm (S T : Source) (h : NormalForm S T) : NormalForm T S := by
    obtain ⟨J, y, hy, rfl, rfl, _⟩ := h
    let K : TwoHole := { J with swapped := !J.swapped }
    have d := (normal_data K y hy).1
    cases hj : J.swapped <;> simpa only [K, TwoHole.fill, hj, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte] using d
  refine ⟨?_, ?_⟩
  · intro S T hne he hc
    change f S ≠ f T at hne
    change FreeMagma.length (f S) = FreeMagma.length (f T) at he
    change Nonconflict (f S) (f T) at hc
    change 3 ≤ delta (f S) (f T) ∧ 3 ≤ delta (f T) (f S) ∧
      (delta (f S) (f T) = 3 ↔ NormalForm S T) ∧
      (delta (f T) (f S) = 3 ↔ NormalForm S T) ∧
      (delta (f S) (f T) = 3 → composition (f S) = composition (f T) ∧ composition S = composition T)
    have hk := positive_count S T hne he hc
    have hl := positive_count T S (Ne.symm hne) he.symm (nc_symm _ _ hc)
    have hb := alpha_bound S T hc
    have hr := alpha_bound T S (nc_symm _ _ hc)
    refine ⟨by omega, by omega, ⟨minimal S T hne he hc, fun h => (normal_converse S T h).1⟩,
      ⟨fun h => normal_symm T S (minimal T S (Ne.symm hne) he.symm (nc_symm _ _ hc) h),
        fun h => (normal_converse T S (normal_symm S T h)).1⟩, ?_⟩
    intro hd; exact (normal_converse S T (minimal S T hne he hc hd)).2
  · intro J y hy
    exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩, normal_data J y hy⟩

end D5.S3.Arith.FibonacciAtomic.ActualImageAlphaSeparation
