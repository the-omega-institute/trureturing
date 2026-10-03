/- GID: D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Seven unshared leaves and the smallest nonconflicting actual image pair. -/

import D5.S3.Arith.FibonacciAtomic.ActualImageAddressCertificate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.ActualImageSevenLeafSeparation

open GenealogicalFiberTransport (Source substitution composition)
open ActualImageAddressCertificate (ActualImage leafAddresses out)
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

/-- Sharp separation for all actual three-step images, with the literal extremal
sources, the complete eleven-leaf classification, and the finite-family bound. -/
theorem result :
    (∀ P Q : Source, P ∈ ActualImage 3 → Q ∈ ActualImage 3 → P ≠ Q →
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
      (∀ P ∈ F, ∀ Q ∈ F, P ≠ Q → NC P Q) → F.card ≤ 2) := by
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
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
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

end D5.S3.Arith.FibonacciAtomic.ActualImageSevenLeafSeparation
