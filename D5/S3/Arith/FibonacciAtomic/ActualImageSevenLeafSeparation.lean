/- GID: D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Seven unshared leaves and the smallest nonconflicting actual image pair. -/

import D5.S3.Arith.FibonacciAtomic.ActualImageAddressCertificate
import D5.S3.Arith.FibonacciAtomic.SourceTransportCentralizer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.ActualImageSevenLeafSeparation

open GenealogicalFiberTransport (Source substitution composition)
open ActualImageAddressCertificate (ActualImage leafAddresses alphaAddresses out subtree replace)
open D5.S0.History.FiniteDescriptionSelfCode (FiniteDescription)

/-- Number of leaves in the actual ordered source. -/
def n (P : Source) : ℕ := (leafAddresses P).card

/-- Number of common leaf addresses; labels are checked separately. -/
def s (P Q : Source) : ℕ := (leafAddresses P ∩ leafAddresses Q).card

/-- Leaves of the first tree whose addresses are not leaves of the second. -/
def nu (P Q : Source) : ℕ := n P - s P Q

/-- Agreement is required only at shared leaf addresses. -/
def NC (P Q : Source) : Prop :=
  ∀ u ∈ leafAddresses P ∩ leafAddresses Q, out P u = out Q u

/-- The ordered beta-alpha pair. -/
def E : Source := .mul (.of false) (.of true)

/-- The three-step image of alpha. -/
def A : Source := .mul E (.of false)

/-- The three-step image of beta. -/
def C : Source := .mul A E

/-- The smallest compound image that is nonconflicting with A. -/
def B : Source := .mul C A

/-- The directed alpha deficit uses the original alpha-address sets. -/
def delta (P Q : Source) : ℕ := (alphaAddresses P \ alphaAddresses Q).card

/-- The alpha weight is the cardinality of the original alpha-address set. -/
def mu (P : Source) : ℕ := (alphaAddresses P).card

/-- A source context with one occurrence of its hole and complete fixed siblings. -/
inductive OneHole
  | hole
  | left (context : OneHole) (fixed : Source)
  | right (fixed : Source) (context : OneHole)

/-- Apply a map to every fixed sibling and insert the tree at the hole. -/
def OneHole.fill (g : Source → Source) : OneHole → Source → Source
  | .hole, X => X
  | .left H R, X => .mul (H.fill g X) (g R)
  | .right L H, X => .mul (g L) (H.fill g X)

/-- The address of the unique hole, retaining left and right order. -/
def OneHole.address : OneHole → FiniteDescription
  | .hole => []
  | .left H _ => false :: H.address
  | .right _ H => true :: H.address

/-- Two holes separated at their lowest common ancestor. The Boolean records
which named hole occurs in its left branch. Fixed siblings remain source trees. -/
structure TwoHole where
  outer : OneHole
  left : OneHole
  right : OneHole
  swapped : Bool

/-- Insert both named holes, applying the same map to all fixed source trees. -/
def TwoHole.fill (J : TwoHole) (g : Source → Source) (X Y : Source) : Source :=
  J.outer.fill g (if J.swapped then .mul (J.left.fill g Y) (J.right.fill g X)
    else .mul (J.left.fill g X) (J.right.fill g Y))

/-- The two named hole addresses. -/
def TwoHole.addresses (J : TwoHole) : FiniteDescription × FiniteDescription :=
  if J.swapped then
    (J.outer.address ++ true :: J.right.address,
      J.outer.address ++ false :: J.left.address)
  else (J.outer.address ++ false :: J.left.address,
    J.outer.address ++ true :: J.right.address)

/-- Canonical divergence is computed on complete preimages, stopping whenever
they agree and recording the current address at an atom-compound comparison. -/
def frontier : Source → Source → Finset FiniteDescription
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

/-- Sharp separation for all actual three-step images, with the literal extremal
sources, the complete eleven-leaf classification, and the finite-family bound. -/
theorem result :
    ((∀ P Q : Source, P ∈ ActualImage 3 → Q ∈ ActualImage 3 → P ≠ Q →
      n P = n Q → NC P Q →
      11 ≤ n P ∧ nu P Q = nu Q P ∧ 7 ≤ nu P Q ∧ s P Q ≤ n P - 7) ∧
    (∃ P13 Q13 : Source,
      P13 = .mul C (.mul A C) ∧ Q13 = .mul (.mul A C) C ∧
      P13 = substitution^[3] (.mul (.of false) (.mul (.of true) (.of false))) ∧
      Q13 = substitution^[3] (.mul (.mul (.of true) (.of false)) (.of false)) ∧
      P13 ∈ ActualImage 3 ∧ Q13 ∈ ActualImage 3 ∧ P13 ≠ Q13 ∧ NC P13 Q13 ∧
      composition P13 = (5, 8) ∧ composition Q13 = (5, 8) ∧
      n P13 = 13 ∧ n Q13 = 13 ∧ s P13 Q13 = 6 ∧ nu P13 Q13 = 7 ∧ nu Q13 P13 = 7) ∧
    (∀ P Q : Source, P ∈ ActualImage 3 → Q ∈ ActualImage 3 → P ≠ Q →
      n P = 11 → n Q = 11 → NC P Q →
      ({P, Q} : Finset Source) = {.mul A B, .mul B A}) ∧
    ((.mul A B : Source) ∈ ActualImage 3 ∧ (.mul B A : Source) ∈ ActualImage 3 ∧
      (.mul A B : Source) ≠ .mul B A ∧ n (.mul A B) = 11 ∧ n (.mul B A) = 11 ∧
      NC (.mul A B) (.mul B A)) ∧
    (∀ F : Finset Source,
      (∀ P ∈ F, P ∈ ActualImage 3 ∧ n P = 11) →
      (∀ P ∈ F, ∀ Q ∈ F, P ≠ Q → NC P Q) → F.card ≤ 2)) ∧
    (∀ S T : Source, substitution^[3] S ≠ substitution^[3] T →
      n (substitution^[3] S) = n (substitution^[3] T) →
      NC (substitution^[3] S) (substitution^[3] T) →
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
      n (substitution^[3] S) = n (substitution^[3] T) ∧ NC (substitution^[3] S) (substitution^[3] T) ∧
      delta (substitution^[3] S) (substitution^[3] T) = 3 ∧ delta (substitution^[3] T) (substitution^[3] S) = 3 ∧
      composition (substitution^[3] S) = composition (substitution^[3] T) ∧ composition S = composition T ∧
      nu (substitution^[3] S) (substitution^[3] T) = (if y = .of false then 7 else 8) ∧
      nu (substitution^[3] T) (substitution^[3] S) = (if y = .of false then 7 else 8)) := by
  let f : Source → Source := substitution^[3]
  have f_alpha : f (.of true) = A := rfl
  have f_beta : f (.of false) = C := rfl
  have f_pair (p q : Source) : f (.mul p q) = .mul (f p) (f q) := by
    change substitution (substitution (substitution (p * q))) =
      substitution (substitution (substitution p)) *
        substitution (substitution (substitution q))
    simp only [map_mul]
  have pref_disjoint (X Y : Finset FiniteDescription) :
      Disjoint (X.image (List.cons false)) (Y.image (List.cons true)) := by
    simp only [Finset.disjoint_left, Finset.mem_image]
    rintro _ ⟨u, _, rfl⟩ ⟨v, _, he⟩
    cases he
  have n_pair (X Y : Source) : n (.mul X Y) = n X + n Y := by
    exact Finset.card_union_of_disjoint (pref_disjoint _ _) |>.trans
      (by simp only [Finset.card_image_of_injective _ List.cons_injective]; rfl)
  have s_pair (X Y Z W : Source) :
      s (.mul X Y) (.mul Z W) = s X Z + s Y W := by
    have hi : leafAddresses (.mul X Y) ∩ leafAddresses (.mul Z W) =
        ((leafAddresses X ∩ leafAddresses Z).image (List.cons false)) ∪
        ((leafAddresses Y ∩ leafAddresses W).image (List.cons true)) := by
      ext u
      cases u with
      | nil => simp [leafAddresses]
      | cons b u => cases b <;> simp [leafAddresses]
    unfold s
    rw [hi, Finset.card_union_of_disjoint (pref_disjoint _ _)]
    simp only [Finset.card_image_of_injective _ List.cons_injective]
  have nc_pair (X Y Z W : Source) :
      NC (.mul X Y) (.mul Z W) ↔ NC X Z ∧ NC Y W := by
    constructor
    · intro h
      constructor
      · intro u hu
        exact h (false :: u) (by simpa [leafAddresses] using hu)
      · intro u hu
        exact h (true :: u) (by simpa [leafAddresses] using hu)
    · rintro ⟨hL, hR⟩ u hu
      cases u with
      | nil => simp [leafAddresses] at hu
      | cons b u =>
        cases b with
        | false => exact hL u (by simpa [leafAddresses] using hu)
        | true => exact hR u (by simpa [leafAddresses] using hu)
  have leaf_branch (b : Bool) (X Y : Source) :
      s (.of b) (.mul X Y) = 0 ∧ s (.mul X Y) (.of b) = 0 ∧
      NC (.of b) (.mul X Y) ∧ NC (.mul X Y) (.of b) := by
    simp [s, NC, leafAddresses]
  have nc_symm (X Y : Source) : NC X Y → NC Y X := by
    intro h u hu
    exact (h u (by simpa only [Finset.inter_comm] using hu)).symm
  have s_symm (X Y : Source) : s X Y = s Y X := by
    simp only [s, Finset.inter_comm]
  have s_le (X Y : Source) : s X Y ≤ n X :=
    Finset.card_le_card Finset.inter_subset_left
  have nu_pair (X Y Z W : Source) :
      nu (.mul X Y) (.mul Z W) = nu X Z + nu Y W := by
    have h1 := s_le X Z
    have h2 := s_le Y W
    simp only [nu, n_pair, s_pair]
    omega
  have s_self (X : Source) : s X X = n X := by simp [s, n]
  have nu_self (X : Source) : nu X X = 0 := by simp [nu, s_self]
  have root (p : Source) : ∃ X Y, f p = .mul X Y := by
    cases p with
    | of b => cases b <;> first | exact ⟨A, E, f_beta⟩ | exact ⟨E, .of false, f_alpha⟩
    | mul p q => exact ⟨f p, f q, f_pair p q⟩
  have leaf_actual (b : Bool) (p : Source) :
      s (.of b) (f p) = 0 ∧ NC (.of b) (f p) := by
    obtain ⟨X, Y, he⟩ := root p
    rw [he]
    exact ⟨(leaf_branch b X Y).1, (leaf_branch b X Y).2.2.1⟩
  have compound_ne_A (p q : Source) : .mul (f p) (f q) ≠ A := by
    obtain ⟨X, Y, he⟩ := root q
    rw [he]
    intro h
    injection h with _ hR
    cases hR
  have counts : n A = 3 ∧ n C = 5 ∧ n E = 2 ∧ n B = 8 := by decide
  let m (X : Source) := mu X
  let shared (X Y : Source) := (alphaAddresses X ∩ alphaAddresses Y).card
  have m_pair (X Y : Source) : m (.mul X Y) = m X + m Y := by
    exact Finset.card_union_of_disjoint (pref_disjoint _ _) |>.trans
      (by simp only [Finset.card_image_of_injective _ List.cons_injective]; rfl)
  have shared_pair (X Y Z W : Source) :
      shared (.mul X Y) (.mul Z W) = shared X Z + shared Y W := by
    have hi : alphaAddresses (.mul X Y) ∩ alphaAddresses (.mul Z W) =
        ((alphaAddresses X ∩ alphaAddresses Z).image (List.cons false)) ∪
        ((alphaAddresses Y ∩ alphaAddresses W).image (List.cons true)) := by
      ext u; cases u with
      | nil => simp [alphaAddresses]
      | cons b u => cases b <;> simp [alphaAddresses]
    dsimp only [shared]; rw [hi, Finset.card_union_of_disjoint (pref_disjoint _ _)]
    simp only [Finset.card_image_of_injective _ List.cons_injective]
  have delta_eq (X Y : Source) : delta X Y = m X - shared X Y :=
    by simpa only [delta, m, mu, shared, Finset.inter_comm] using
      (Finset.card_sdiff (s := alphaAddresses Y) (t := alphaAddresses X))
  have shared_le (X Y : Source) : shared X Y ≤ m X :=
    Finset.card_le_card Finset.inter_subset_left
  have shared_symm (X Y : Source) : shared X Y = shared Y X := by
    simp only [shared, Finset.inter_comm]
  have delta_pair (X Y Z W : Source) :
      delta (.mul X Y) (.mul Z W) = delta X Z + delta Y W := by
    have h1 := shared_le X Z; have h2 := shared_le Y W
    rw [delta_eq, delta_eq, delta_eq, m_pair, shared_pair]; omega
  have delta_self (X : Source) : delta X X = 0 := by simp [delta]
  have alpha_leaves (X : Source) : alphaAddresses X ⊆ leafAddresses X := by
    induction X with
    | of b => cases b <;> simp [alphaAddresses, leafAddresses]
    | mul X Y hX hY =>
      exact Finset.union_subset_union (Finset.image_subset_image hX) (Finset.image_subset_image hY)
  have shared_zero (X Y : Source) (h : s X Y = 0) : shared X Y = 0 := by
    have hh := Finset.card_le_card (Finset.inter_subset_inter (alpha_leaves X) (alpha_leaves Y))
    change shared X Y ≤ s X Y at hh; omega
  have alpha_nil (p : Source) : [] ∉ alphaAddresses (f p) := by
    obtain ⟨X, Y, he⟩ := root p; rw [he]; simp [alphaAddresses]
  have shared_E (p : Source) : shared E (f p) = 0 := by
    cases p with
    | of b => cases b <;> simp [shared, f_alpha, f_beta, E, A, C, alphaAddresses]
    | mul p q =>
      rw [f_pair]; simp [shared, E, alphaAddresses, alpha_nil]
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
  have min_size (p : Source) : 3 ≤ n (f p) := by
    induction p with
    | of b => cases b <;> simp only [f_alpha, f_beta] <;> omega
    | mul p q hp hq => rw [f_pair, n_pair]; omega
  have not_A_size (p : Source) (hp : f p ≠ A) : 5 ≤ n (f p) := by
    cases p with
    | of b =>
      cases b with
      | false => rw [f_beta]; omega
      | true => exact (hp f_alpha).elim
    | mul p q =>
      have h1 := min_size p
      have h2 := min_size q
      rw [f_pair, n_pair]
      omega
  have E_actual (p : Source) :
      (NC E (f p) ↔ f p ≠ A) ∧ s E (f p) = if f p = A then 1 else 0 := by
    cases p with
    | of b =>
      cases b with
      | false =>
        rw [f_beta]
        have ca : C ≠ A := by decide
        have ec : NC E C := by simp [NC, E, A, C, leafAddresses]
        rw [if_neg ca]
        exact ⟨⟨fun _ => ca, fun _ => ec⟩, by simp [s, E, A, C, leafAddresses]⟩
      | true =>
        rw [f_alpha, if_pos rfl]
        simp [NC, s, E, A, leafAddresses, out]
    | mul p q =>
      have h1 := leaf_actual false p
      have h2 := leaf_actual true q
      rw [f_pair]
      change (NC (.mul (.of false) (.of true)) (.mul (f p) (f q)) ↔ _) ∧
        s (.mul (.of false) (.of true)) (.mul (f p) (f q)) = _
      rw [nc_pair, s_pair, if_neg (compound_ne_A p q)]
      exact ⟨⟨fun _ => compound_ne_A p q, fun _ => ⟨h1.2, h2.2⟩⟩,
        by omega⟩
  have A_compound (p q : Source) :
      (NC A (.mul (f p) (f q)) ↔ f p ≠ A) ∧
      (NC A (.mul (f p) (f q)) → s A (.mul (f p) (f q)) = 0) := by
    have he := E_actual p
    have hl := leaf_actual false q
    constructor
    · change NC (.mul E (.of false)) (.mul (f p) (f q)) ↔ _
      rw [nc_pair]
      simpa only [hl.2, and_true] using he.1
    · intro h
      have hE : NC E (f p) := (nc_pair E (.of false) (f p) (f q)).mp h |>.1
      change s (.mul E (.of false)) (.mul (f p) (f q)) = 0
      rw [s_pair, he.2, if_neg (he.1.mp hE), hl.1]
  have A_C_conflict : ¬ NC A C := by
    simp [NC, A, C, E, leafAddresses, out]
  have alpha_table (b : Bool) (p q : Source)
      (h : NC (f (.of b)) (.mul (f p) (f q))) :
      1 ≤ delta (f (.of b)) (.mul (f p) (f q)) ∧
      2 ≤ delta (.mul (f p) (f q)) (f (.of b)) ∧
      (delta (f (.of b)) (.mul (f p) (f q)) = 1 →
        n (f (.of b)) + 5 ≤ n (.mul (f p) (f q)) ∨
          (b = false ∧ p = .of true ∧
            n (.mul (f p) (f q)) = 3 + n (f q))) ∧
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
  have atomic_comparison (b : Bool) (p q : Source)
      (h : NC (f (.of b)) (.mul (f p) (f q))) :
      n (f (.of b)) < n (.mul (f p) (f q)) ∧
      3 ≤ n (f (.of b)) ∧ 8 ≤ n (.mul (f p) (f q)) ∧
      2 ≤ nu (f (.of b)) (.mul (f p) (f q)) ∧
      5 ≤ nu (.mul (f p) (f q)) (f (.of b)) := by
    cases b with
    | true =>
      rw [f_alpha] at h ⊢
      have hp := (A_compound p q).1.mp h
      have hn := not_A_size p hp
      have hq := min_size q
      have hs := (A_compound p q).2 h
      have ht := s_symm (.mul (f p) (f q)) A
      simp only [n_pair, nu] at ⊢
      omega
    | false =>
      rw [f_beta] at h ⊢
      change NC (.mul A E) (.mul (f p) (f q)) at h
      obtain ⟨hL, hR⟩ := (nc_pair A E (f p) (f q)).mp h
      have hq := not_A_size q ((E_actual q).1.mp hR)
      have heq : s E (f q) = 0 := by
        rw [(E_actual q).2, if_neg ((E_actual q).1.mp hR)]
      cases p with
      | of b =>
        cases b with
        | false => rw [f_beta] at hL; exact (A_C_conflict hL).elim
        | true =>
          have hs : s C (.mul (f (.of true)) (f q)) = 3 := by
            change s (.mul A E) (.mul (f (.of true)) (f q)) = 3
            rw [s_pair, f_alpha, s_self, heq]
            omega
          have ht := s_symm (.mul (f (.of true)) (f q)) C
          simp only [n_pair, nu, f_alpha] at ⊢ ht hs
          omega
      | mul p r =>
        rw [f_pair] at hL ⊢
        have hp := not_A_size p ((A_compound p r).1.mp hL)
        have hr := min_size r
        have hs : s C (.mul (.mul (f p) (f r)) (f q)) = 0 := by
          change s (.mul A E) (.mul (.mul (f p) (f r)) (f q)) = 0
          rw [s_pair, (A_compound p r).2 hL, heq]
        have ht := s_symm (.mul (.mul (f p) (f r)) (f q)) C
        simp only [n_pair, nu] at ⊢ ht
        omega
  let Oriented (X Y : Source) : Prop :=
    n X < n Y ∧ 3 ≤ n X ∧ 8 ≤ n Y ∧ 2 ≤ nu X Y ∧ 5 ≤ nu Y X
  let Mixed (X Y : Source) : Prop :=
    11 ≤ n X ∧ 11 ≤ n Y ∧ 7 ≤ nu X Y ∧ 7 ≤ nu Y X
  have comparison (p q : Source) (h : NC (f p) (f q)) :
      f p = f q ∨ Oriented (f p) (f q) ∨ Oriented (f q) (f p) ∨ Mixed (f p) (f q) := by
    induction p generalizing q with
    | of b =>
      cases q with
      | of c =>
        cases b <;> cases c
        · exact Or.inl rfl
        · rw [f_alpha, f_beta] at h
          exact (A_C_conflict (nc_symm _ _ h)).elim
        · rw [f_alpha, f_beta] at h
          exact (A_C_conflict h).elim
        · exact Or.inl rfl
      | mul p q =>
        rw [f_pair] at h ⊢
        exact Or.inr (Or.inl (atomic_comparison b p q h))
    | mul p r hp hr =>
      cases q with
      | of b =>
        rw [f_pair] at h ⊢
        exact Or.inr (Or.inr (Or.inl (atomic_comparison b p r (nc_symm _ _ h))))
      | mul q t =>
        rw [f_pair, f_pair] at h ⊢
        obtain ⟨hL, hR⟩ := (nc_pair _ _ _ _).mp h
        have hl := hp q hL
        have ht := hr t hR
        have np := min_size p
        have nr := min_size r
        have nq := min_size q
        have nt := min_size t
        rcases hl with he | hl | hl | hl
        · rcases ht with he' | ht | ht | ht
          · exact Or.inl (congrArg₂ FreeMagma.mul he he')
          all_goals
            have hz1 : nu (f p) (f q) = 0 := by rw [he, nu_self]
            have hz2 : nu (f q) (f p) = 0 := by rw [he, nu_self]
            have hn : n (f p) = n (f q) := congrArg n he
            simp only [Oriented, Mixed, n_pair, nu_pair] at *
            omega
        all_goals
          rcases ht with he | ht | ht | ht
          · have hz1 : nu (f r) (f t) = 0 := by rw [he, nu_self]
            have hz2 : nu (f t) (f r) = 0 := by rw [he, nu_self]
            have hn : n (f r) = n (f t) := congrArg n he
            simp only [Oriented, Mixed, n_pair, nu_pair] at *
            omega
          all_goals
            simp only [Oriented, Mixed, n_pair, nu_pair] at *
            omega
  have small_5 (p : Source) (h : n (f p) ≤ 5) : f p = A ∨ f p = C := by
    cases p with
    | of b => cases b <;> first | exact Or.inr f_beta | exact Or.inl f_alpha
    | mul p q =>
      have hp := min_size p
      have hq := min_size q
      rw [f_pair, n_pair] at h
      omega
  have small_8 (p : Source) (h : n (f p) ≤ 8) :
      f p = A ∨ f p = C ∨ f p = .mul A A ∨ f p = .mul A C ∨ f p = B := by
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
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
      · omega
  have size_11 (p : Source) (h : n (f p) = 11) :
      f p = .mul A (.mul A C) ∨ f p = .mul A B ∨
      f p = .mul C (.mul A A) ∨ f p = .mul (.mul A A) C ∨
      f p = .mul (.mul A C) A ∨ f p = .mul B A := by
    cases p with
    | of b => cases b <;> simp only [f_alpha, f_beta] at h <;> omega
    | mul p q =>
      have hp := min_size p
      have hq := min_size q
      rw [f_pair, n_pair] at h
      have lp := small_8 p (by omega)
      have lq := small_8 q (by omega)
      rw [f_pair]
      rcases lp with lp | lp | lp | lp | lp <;>
        rcases lq with lq | lq | lq | lq | lq
      all_goals rw [lp, lq] at h ⊢
      all_goals simp only [B, n_pair, counts.1, counts.2.1] at h
      all_goals first | omega | simp only [B, true_or, or_true, eq_self]
  have alpha_bound (p q : Source) (hc : NC (f p) (f q)) :
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
  have zero_same (p q : Source) (hc : NC (f p) (f q))
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
  have one_side (p q : Source) (hc : NC (f p) (f q))
      (hl : forwardCount q p = 0) :
      n (f p) ≤ n (f q) ∧ (0 < forwardCount p q → n (f p) < n (f q)) := by
    induction p generalizing q with
    | of b =>
      cases q with
      | of c =>
        have he := zero_same (.of b) (.of c) hc rfl rfl
        rw [he]; exact ⟨le_rfl, by simp [forwardCount]⟩
      | mul q t =>
        rw [f_pair] at hc ⊢
        have he := (atomic_comparison b q t hc).1
        exact ⟨he.le, fun _ => he⟩
    | mul p r hp hr =>
      cases q with
      | of b => simp [forwardCount] at hl
      | mul q t =>
        rw [f_pair, f_pair, nc_pair] at hc
        simp only [forwardCount] at hl
        have hL := hp q hc.1 (by omega); have hR := hr t hc.2 (by omega)
        rw [f_pair, f_pair, n_pair, n_pair]; simp only [forwardCount]; constructor <;> omega
  have map_one (H : OneHole) (X : Source) : f (H.fill id X) = H.fill f (f X) := by
    induction H with
    | hole => rfl
    | left H R ih => simp only [OneHole.fill, id_eq, f_pair, ih]
    | right L H ih => simp only [OneHole.fill, id_eq, f_pair, ih]
  have map_two (J : TwoHole) (X Y : Source) :
      f (J.fill id X Y) = J.fill f (f X) (f Y) := by
    cases h : J.swapped <;> simp only [TwoHole.fill, h, Bool.false_eq_true,
      ↓reduceIte, map_one, f_pair]
  have one_data (g : Source → Source) (H : OneHole) (X Y : Source) :
      delta (H.fill g X) (H.fill g Y) = delta X Y ∧
      nu (H.fill g X) (H.fill g Y) = nu X Y ∧
      n (H.fill g X) + n Y = n (H.fill g Y) + n X ∧
      (NC (H.fill g X) (H.fill g Y) ↔ NC X Y) ∧
      (composition X = composition Y → composition (H.fill g X) = composition (H.fill g Y)) := by
    have nc_self (Z : Source) : NC Z Z := fun _ _ => rfl
    induction H with
    | hole => exact ⟨rfl, rfl, Nat.add_comm _ _, Iff.rfl, id⟩
    | left H R ih =>
      simp only [OneHole.fill, delta_pair, delta_self, nu_pair, nu_self,
        add_zero, n_pair, nc_pair, nc_self, and_true]
      exact ⟨ih.1, ih.2.1, by omega, ih.2.2.2.1,
        fun he => by simp only [composition, ih.2.2.2.2 he]⟩
    | right L H ih =>
      simp only [OneHole.fill, delta_pair, delta_self, nu_pair, nu_self,
        zero_add, n_pair, nc_pair, nc_self, true_and]
      exact ⟨ih.1, ih.2.1, by omega, ih.2.2.2.1,
        fun he => by simp only [composition, ih.2.2.2.2 he]⟩
  have two_data (g : Source → Source) (J : TwoHole) (X Y U V : Source) :
      delta (J.fill g X Y) (J.fill g U V) = delta X U + delta Y V ∧
      nu (J.fill g X Y) (J.fill g U V) = nu X U + nu Y V ∧
      n (J.fill g X Y) + n U + n V = n (J.fill g U V) + n X + n Y ∧
      (NC (J.fill g X Y) (J.fill g U V) ↔ NC X U ∧ NC Y V) := by
    have hL := one_data g J.left X U; have hR := one_data g J.right Y V
    have hL' := one_data g J.left Y V; have hR' := one_data g J.right X U
    cases h : J.swapped <;>
      simp only [TwoHole.fill, h, Bool.false_eq_true, ↓reduceIte,
        (one_data g J.outer _ _).1, (one_data g J.outer _ _).2.1,
        (one_data g J.outer _ _).2.2.2.1, delta_pair, nu_pair, nc_pair]
    · exact ⟨by rw [hL.1, hR.1], by rw [hL.2.1, hR.2.1],
        by have ho := (one_data g J.outer (.mul (J.left.fill g X) (J.right.fill g Y))
            (.mul (J.left.fill g U) (J.right.fill g V))).2.2.1
           simp only [n_pair] at ho; omega,
        by rw [hL.2.2.2.1, hR.2.2.2.1]⟩
    · exact ⟨by rw [hL'.1, hR'.1, Nat.add_comm],
        by rw [hL'.2.1, hR'.2.1, Nat.add_comm],
        by have ho := (one_data g J.outer (.mul (J.left.fill g Y) (J.right.fill g X))
            (.mul (J.left.fill g V) (J.right.fill g U))).2.2.1
           simp only [n_pair] at ho; omega,
        by rw [hL'.2.2.2.1, hR'.2.2.2.1, and_comm]⟩
  have path_replace (g : Source → Source) (H : OneHole) (M X : Source) (u : FiniteDescription) :
      replace (H.fill g M) (H.address ++ u) X = H.fill g (replace M u X) := by
    induction H with
    | hole => rfl
    | left H R ih => simpa only [OneHole.fill, OneHole.address, List.cons_append, replace] using congrArg (fun z => FreeMagma.mul z (g R)) ih
    | right L H ih => simpa only [OneHole.fill, OneHole.address, List.cons_append, replace] using congrArg (FreeMagma.mul (g L)) ih
  have literal_two (g : Source → Source) (J : TwoHole) (X Y Z W : Source) :
      replace (replace (J.fill g Z W) J.addresses.1 X) J.addresses.2 Y = J.fill g X Y := by
    have at_hole (H : OneHole) (P Q : Source) : replace (H.fill g P) H.address Q = H.fill g Q :=
      by simpa only [List.append_nil, replace] using path_replace g H P Q []
    cases h : J.swapped <;> simp only [TwoHole.fill, TwoHole.addresses, h,
      Bool.false_eq_true, ↓reduceIte, path_replace, replace, at_hole]
  have frontier_self (S : Source) : frontier S S = ∅ := by cases S <;> simp [frontier]
  have frontier_pair (S T U V : Source) : frontier (.mul S T) (.mul U V) =
      (frontier S U).image (List.cons false) ∪ (frontier T V).image (List.cons true) := by
    by_cases he : (.mul S T : Source) = .mul U V
    · injection he with hS hT; subst U; subst V; simp only [frontier_self, Finset.image_empty, Finset.union_empty]
    · simp only [frontier, if_neg he]
  have frontier_one (H : OneHole) (S T : Source) :
      frontier (H.fill id S) (H.fill id T) = (frontier S T).image (fun u => H.address ++ u) := by
    induction H with
    | hole => simp [OneHole.fill, OneHole.address]
    | left H R ih => simp only [OneHole.fill, id_eq, OneHole.address, frontier_pair,
        frontier_self, Finset.image_empty, Finset.union_empty, ih,
        Finset.image_image, Function.comp_def, List.cons_append]
    | right L H ih => simp only [OneHole.fill, id_eq, OneHole.address, frontier_pair,
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
  have one_hole (p q : Source) (hc : NC (f p) (f q))
      (hk : forwardCount p q = 1) (hl : forwardCount q p = 0) :
      ∃ H : OneHole, ∃ b : Bool, ∃ X Y : Source,
        p = H.fill id (.of b) ∧ q = H.fill id (.mul X Y) ∧
          NC (f (.of b)) (.mul (f X) (f Y)) := by
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
          exact ⟨.right p H, b, X, Y, by simp [OneHole.fill, h1],
            by simp [OneHole.fill, he, h2], h3⟩
        · have he := zero_same r t hc.2 (by omega) (by omega)
          obtain ⟨H, b, X, Y, h1, h2, h3⟩ := hp q hc.1 (by omega) (by omega)
          exact ⟨.left H r, b, X, Y, by simp [OneHole.fill, h1],
            by simp [OneHole.fill, he, h2], h3⟩
  have two_holes (p q : Source) (hc : NC (f p) (f q))
      (hk : forwardCount p q = 1) (hl : forwardCount q p = 1) :
      ∃ J : TwoHole, ∃ b c : Bool, ∃ X Y U V : Source,
        p = J.fill id (.of b) (.mul U V) ∧
        q = J.fill id (.mul X Y) (.of c) ∧
        NC (f (.of b)) (.mul (f X) (f Y)) ∧
        NC (f (.of c)) (.mul (f U) (f V)) := by
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
              by simpa [TwoHole.fill, OneHole.fill] using congrArg (FreeMagma.mul p) h1,
              by simpa [TwoHole.fill, OneHole.fill, ← he] using congrArg (FreeMagma.mul p) h2,
              h3, h4⟩
          · obtain ⟨H, c, U, V, h1, h2, h3⟩ :=
              one_hole q p (nc_symm _ _ hc.1) (by omega) hkL
            obtain ⟨K, b, X, Y, h4, h5, h6⟩ := one_hole r t hc.2 (by omega) (by omega)
            exact ⟨⟨.hole, H, K, true⟩, b, c, X, Y, U, V,
              by simp [TwoHole.fill, OneHole.fill, h2, h4],
              by simp [TwoHole.fill, OneHole.fill, h1, h5], h6, h3⟩
        · by_cases hlL : forwardCount q p = 0
          · obtain ⟨H, b, X, Y, h1, h2, h3⟩ := one_hole p q hc.1 (by omega) hlL
            obtain ⟨K, c, U, V, h4, h5, h6⟩ :=
              one_hole t r (nc_symm _ _ hc.2) (by omega) (by omega)
            exact ⟨⟨.hole, H, K, false⟩, b, c, X, Y, U, V,
              by simp [TwoHole.fill, OneHole.fill, h1, h5],
              by simp [TwoHole.fill, OneHole.fill, h2, h4], h3, h6⟩
          · have he := zero_same r t hc.2 (by omega) (by omega)
            obtain ⟨J, b, c, X, Y, U, V, h1, h2, h3, h4⟩ := hp q hc.1 (by omega) (by omega)
            exact ⟨{ J with outer := .left J.outer r }, b, c, X, Y, U, V,
              by simpa [TwoHole.fill, OneHole.fill] using congrArg (fun z => FreeMagma.mul z r) h1,
              by simpa [TwoHole.fill, OneHole.fill, ← he] using congrArg (fun z => FreeMagma.mul z r) h2,
              h3, h4⟩
  have swap_composition (g : Source → Source) (J : TwoHole) (X Y : Source) :
      composition (J.fill g X Y) = composition (J.fill g Y X) := by
    have total (H : OneHole) (U V : Source) :
        composition (H.fill g U) + composition V = composition (H.fill g V) + composition U := by
      induction H with
      | hole => exact add_comm _ _
      | left H R ih =>
        simpa only [OneHole.fill, composition, add_assoc, add_left_comm, add_comm] using congrArg (fun z => z + composition (g R)) ih
      | right L H ih =>
        simpa only [OneHole.fill, composition, add_assoc, add_left_comm, add_comm] using congrArg (fun z => composition (g L) + z) ih
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
      NormalForm S T ∧ f S ≠ f T ∧ n (f S) = n (f T) ∧ NC (f S) (f T) ∧
      delta (f S) (f T) = 3 ∧ delta (f T) (f S) = 3 ∧
      composition (f S) = composition (f T) ∧ composition S = composition T ∧
      nu (f S) (f T) = (if y = .of false then 7 else 8) ∧
      nu (f T) (f S) = (if y = .of false then 7 else 8) := by
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
    have local_data : NC C (.mul A (f y)) ∧ NC (.mul A (f y)) C ∧
        delta C (.mul A (f y)) + delta (.mul A (f y)) C = 3 ∧
        nu C (.mul A (f y)) + nu (.mul A (f y)) C = (if y = .of false then 7 else 8) := by
      rcases hy with rfl | rfl <;> unfold NC <;> decide
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
  have injective : Function.Injective f :=
    SourceTransportCentralizer.source_transport_centralizer.2.2.1 f ⟨f_pair, fun _ => rfl⟩
  have positive_count (S T : Source) (hne : f S ≠ f T) (he : n (f S) = n (f T))
      (hc : NC (f S) (f T)) : 0 < forwardCount S T := by
    by_contra hn
    have hz : forwardCount S T = 0 := by omega
    have ht : 0 < forwardCount T S := by
      by_contra hn; exact hne (congrArg f (zero_same S T hc hz (by omega)))
    have hh := (one_side T S (nc_symm _ _ hc) hz).2 ht; omega
  have minimal (S T : Source) (hne : f S ≠ f T) (he : n (f S) = n (f T))
      (hc : NC (f S) (f T)) (hd : delta (f S) (f T) = 3) : NormalForm S T := by
    have hk := positive_count S T hne he hc
    have hl := positive_count T S (Ne.symm hne) he.symm (nc_symm _ _ hc)
    have hb := alpha_bound S T hc
    obtain ⟨J, b, c, X, Y, U, V, hS, hT, h1, h2⟩ := two_holes S T hc (by omega) (by omega)
    have d := two_data f J (f (.of b)) (.mul (f U) (f V)) (.mul (f X) (f Y)) (f (.of c))
    have a := alpha_table b X Y h1; have z := alpha_table c U V h2
    simp only [hS, hT, map_two, f_pair] at hd he
    have balance : n (f (.of b)) + n (.mul (f U) (f V)) =
        n (.mul (f X) (f Y)) + n (f (.of c)) := by have hgap := d.2.2.1; omega
    have hsmall : delta (.mul (f U) (f V)) (f (.of c)) = 2 := by rw [d.1] at hd; omega
    obtain ⟨rfl, rfl, hv⟩ := z.2.2.2 hsmall
    have nv : n (f V) = 5 ∨ n (f V) = 6 := by
      rcases hv with rfl | rfl
      · exact Or.inl (by decide)
      · exact Or.inr (by decide)
    simp only [f_alpha, f_beta, n_pair, counts.1, counts.2.1] at balance
    have hforward : delta (f (.of b)) (.mul (f X) (f Y)) = 1 := by rw [d.1] at hd; omega
    rcases a.2.2.1 hforward with hbad | ⟨rfl, rfl, _⟩
    · rw [n_pair] at hbad; omega
    · have hsize : n (f Y) = n (f V) := by
        simp only [f_alpha, f_beta, n_pair, counts.1, counts.2.1] at balance; omega
      have hY : Y = V := by
        apply injective
        rcases small_8 Y (by omega) with hY | hY | hY | hY | hY
        all_goals rw [hY] at hsize ⊢
        all_goals rcases hv with hv | hv <;> simp only [hv, f_beta, f_pair, f_alpha] at hsize ⊢
        all_goals simp only [n_pair, counts.1, counts.2.1, counts.2.2.2, B] at hsize
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
  have rigidity (P Q : Source) (hP : P ∈ ActualImage 3) (hQ : Q ∈ ActualImage 3)
      (hne : P ≠ Q) (hp : n P = 11) (hq : n Q = 11) (hc : NC P Q) :
      (P = .mul A B ∧ Q = .mul B A) ∨ (P = .mul B A ∧ Q = .mul A B) := by
    obtain ⟨p, rfl⟩ := hP
    obtain ⟨q, rfl⟩ := hQ
    rcases size_11 p hp with lp | lp | lp | lp | lp | lp <;>
      rcases size_11 q hq with lq | lq | lq | lq | lq | lq
    all_goals change f p ≠ f q at hne
    all_goals change NC (f p) (f q) at hc
    all_goals change (f p = _ ∧ f q = _) ∨ (f p = _ ∧ f q = _)
    all_goals rw [lp, lq] at hne hc ⊢
    all_goals
      first
      | exact (hne rfl).elim
      | (revert hc; unfold NC; decide)
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro P Q hP hQ hne he hc
      obtain ⟨p, rfl⟩ := hP
      obtain ⟨q, rfl⟩ := hQ
      change f p ≠ f q at hne
      change n (f p) = n (f q) at he
      change NC (f p) (f q) at hc
      change 11 ≤ n (f p) ∧ nu (f p) (f q) = nu (f q) (f p) ∧
        7 ≤ nu (f p) (f q) ∧ s (f p) (f q) ≤ n (f p) - 7
      rcases comparison p q hc with heq | ho | ho | hm
      · exact (hne heq).elim
      · dsimp only [Oriented] at ho; omega
      · dsimp only [Oriented] at ho; omega
      · dsimp only [Mixed] at hm
        have hs := s_le (f p) (f q)
        have ht := s_symm (f p) (f q)
        simp only [nu] at hm ⊢
        omega
    · have hp : f (.mul (.of false) (.mul (.of true) (.of false))) =
          .mul C (.mul A C) := by rw [f_pair, f_pair, f_alpha, f_beta]
      have hq : f (.mul (.mul (.of true) (.of false)) (.of false)) =
          .mul (.mul A C) C := by rw [f_pair, f_pair, f_alpha, f_beta]
      refine ⟨.mul C (.mul A C), .mul (.mul A C) C, rfl, rfl, hp.symm, hq.symm,
        ⟨_, hp⟩, ⟨_, hq⟩, ?_⟩
      have hne : (.mul C (.mul A C) : Source) ≠ .mul (.mul A C) C := by decide
      refine ⟨hne, ?_⟩
      simp [NC, n, s, nu, leafAddresses, out, composition, A, C, E]
    · intro P Q hp hq hn hnp hnq hc
      rcases rigidity P Q hp hq hn hnp hnq hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact Finset.pair_comm _ _
    · have hp : f (.mul (.of true) (.mul (.of false) (.of true))) = .mul A B := by
        rw [f_pair, f_pair, f_alpha, f_beta]; rfl
      have hq : f (.mul (.mul (.of false) (.of true)) (.of true)) = .mul B A := by
        rw [f_pair, f_pair, f_alpha, f_beta]; rfl
      refine ⟨⟨_, hp⟩, ⟨_, hq⟩, ?_⟩
      have hne : (.mul A B : Source) ≠ .mul B A := by decide
      refine ⟨hne, ?_⟩
      simp [NC, n, leafAddresses, A, B, C, E]
    · intro F hF hNC
      by_cases hd : ∃ P ∈ F, ∃ Q ∈ F, P ≠ Q
      · obtain ⟨P, hp, Q, hq, hn⟩ := hd
        have fixed := rigidity P Q (hF P hp).1 (hF Q hq).1 hn
          (hF P hp).2 (hF Q hq).2 (hNC P hp Q hq hn)
        have cover : F ⊆ {.mul A B, .mul B A} := by
          intro R hr
          by_cases he : R = P
          · subst R
            rcases fixed with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
          · have hh := rigidity R P (hF R hr).1 (hF P hp).1 he
              (hF R hr).2 (hF P hp).2 (hNC R hr P hp he)
            rcases hh with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
        exact (Finset.card_le_card cover).trans Finset.card_le_two
      · have hs : F.card ≤ 1 := Finset.card_le_one.mpr fun P hp Q hq => by
          by_contra hn
          exact hd ⟨P, hp, Q, hq, hn⟩
        omega

  · intro S T hne he hc
    change f S ≠ f T at hne
    change n (f S) = n (f T) at he
    change NC (f S) (f T) at hc
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

end D5.S3.Arith.FibonacciAtomic.ActualImageSevenLeafSeparation
