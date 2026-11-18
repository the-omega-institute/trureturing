/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointEightWord
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointEightWord
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Positive eight-cycle direction words in the actual Huang cube. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointPentagonSigns

/-! Classification of positive words of length eight in the original Huang signing. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointEightWord

open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q flip gamma IsBalanced IsSwitching)
open private switching_sq from D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
open private huangMatrix huangMatrix_symmetric from D5.S3.Combinatorics.Graph.HypercubeSubQuorum

private def separated {α : Type*} (w : Fin 8 → α) : Prop :=
  ∀ i, w i ≠ w (i + 1) ∧ w i ≠ w (i + 2)

private def positions {α : Type*} [DecidableEq α] (w : Fin 8 → α) (a : α) : Finset (Fin 8) :=
  Finset.univ.filter (fun i => w i = a)

private def parity (m : Fin 8 → Bool) : Bool :=
  m 0 ^^ m 1 ^^ m 2 ^^ m 3 ^^ m 4 ^^ m 5 ^^ m 6 ^^ m 7

private theorem separated_even_mask :
    ∀ a b c d e f g h : Bool,
      let m : Fin 8 → Bool := ![a,b,c,d,e,f,g,h]
      parity m = false →
      (∀ i, m i = true → m (i + 1) = false ∧ m (i + 2) = false) →
      (positions m true).card = 0 ∨ (positions m true).card = 2 := by
  decide +kernel

private theorem actual_separation {n : ℕ} {S : Finset (Q n)} (hbal : IsBalanced S)
    (v : Fin 8 → (S : Set (Q n))) (hv : Function.Injective v)
    (w : Fin 8 → Fin n) (step : ∀ i, (v (i + 1)).val = flip (v i).val (w i)) :
    separated w := by
  intro i
  have s₀ := step i
  have s₁ : (v (i + 2)).val = flip (v (i + 1)).val (w (i + 1)) := by
    simpa only [add_assoc, show (1 + 1 : Fin 8) = 2 by decide] using step (i + 1)
  have s₂ : (v (i + 3)).val = flip (v (i + 2)).val (w (i + 2)) := by
    simpa only [add_assoc, show (2 + 1 : Fin 8) = 3 by decide] using step (i + 2)
  have h₀ : w i ≠ w (i + 1) := by
    intro he
    rw [← he, s₀, BalancedCriticalSpectrum.flip_flip] at s₁
    exact (show ∀ j : Fin 8, j + 2 ≠ j by decide +kernel) i (hv (Subtype.ext s₁))
  have h₁ : w (i + 1) ≠ w (i + 2) := by
    intro he
    rw [← he, s₁, BalancedCriticalSpectrum.flip_flip] at s₂
    exact (show ∀ j : Fin 8, j + 3 ≠ j + 1 by decide +kernel) i (hv (Subtype.ext s₂))
  refine ⟨h₀, BalancedCubeGirth.three_directions_distinct hbal h₀ h₁ (v i).property ?_ ?_ ?_⟩
  · rw [← s₀]; exact (v (i + 1)).property
  · rw [← s₀, ← s₁]; exact (v (i + 2)).property
  · rw [← s₀, ← s₁, ← s₂]; exact (v (i + 3)).property

private theorem flip_at {n : ℕ} (x : Q n) (a b : Fin n) :
    flip x b a = (x a ^^ decide (b = a)) := by
  by_cases h : b = a
  · subst b
    cases hx : x a <;> simp [BalancedCriticalSpectrum.flip, hx]
  · simp [BalancedCriticalSpectrum.flip, h, Ne.symm h]

private theorem closed_even {n : ℕ} {S : Finset (Q n)}
    (v : Fin 8 → (S : Set (Q n))) (w : Fin 8 → Fin n)
    (step : ∀ i, (v (i + 1)).val = flip (v i).val (w i)) (a : Fin n) :
    parity (fun i => decide (w i = a)) = false := by
  have atStep (i : Fin 8) :=
    (congrFun (step i) a).trans (flip_at (v i).val a (w i))
  have h : (v 0).val a = ((v 7).val a ^^ decide (w 7 = a)) := atStep 7
  have h₀ : (v 1).val a = _ := atStep 0
  have h₁ : (v 2).val a = _ := atStep 1
  have h₂ : (v 3).val a = _ := atStep 2
  have h₃ : (v 4).val a = _ := atStep 3
  have h₄ : (v 5).val a = _ := atStep 4
  have h₅ : (v 6).val a = _ := atStep 5
  have h₆ : (v 7).val a = _ := atStep 6
  rw [h₆, h₅, h₄, h₃, h₂, h₁, h₀] at h
  apply (Bool.xor_right_inj (x := (v 0).val a)).mp
  simpa [parity, Bool.xor_assoc] using h.symm

private theorem position_count {n : ℕ} (w : Fin 8 → Fin n) (hs : separated w)
    (he : ∀ a, parity (fun i => decide (w i = a)) = false) (i : Fin 8) :
    (positions w (w i)).card = 2 := by
  let m : Fin 8 → Bool := fun j => decide (w j = w i)
  have hm : m = ![m 0,m 1,m 2,m 3,m 4,m 5,m 6,m 7] := by
    funext j; fin_cases j <;> rfl
  have hsep (j : Fin 8) (hj : m j = true) : m (j + 1) = false ∧ m (j + 2) = false := by
    have hh : w j = w i := of_decide_eq_true hj
    exact ⟨decide_eq_false (hh ▸ (hs j).1.symm), decide_eq_false (hh ▸ (hs j).2.symm)⟩
  have h := separated_even_mask (m 0) (m 1) (m 2) (m 3) (m 4) (m 5) (m 6) (m 7)
  rw [← hm] at h
  have hp : positions m true = positions w (w i) := by
    ext j; simp [positions, m]
  have hh := h (he _) hsep
  rw [hp] at hh
  have hi : i ∈ positions w (w i) := by simp [positions]
  have hpos := Finset.card_pos.mpr ⟨i, hi⟩
  exact hh.resolve_left (by omega)

private def pattern (p q r s t : Fin 4) : Fin 8 → Fin 4 := ![0,1,2,p,q,r,s,t]

private theorem fourth_bucket :
    ∀ p q r s t : Fin 4,
      let u := pattern p q r s t
      (∀ a : Fin 3, (positions u a.castSucc).card = 2) → (positions u 3).card = 2 := by
  decide +kernel

private theorem seven_patterns :
    ∀ p q r s t : Fin 4,
      let u := pattern p q r s t
      (∀ a : Fin 3, (positions u a.castSucc).card = 2) → separated u →
      [p,q,r,s,t] = [3,0,1,2,3] ∨ [p,q,r,s,t] = [0,3,2,1,3] ∨
      [p,q,r,s,t] = [3,1,0,3,2] ∨ [p,q,r,s,t] = [0,3,1,2,3] ∨
      [p,q,r,s,t] = [3,0,1,3,2] ∨ [p,q,r,s,t] = [3,0,2,1,3] ∨
      [p,q,r,s,t] = [3,1,0,2,3] := by
  simp only [separated]
  decide +kernel

private theorem normalize {n : ℕ} (w : Fin 8 → Fin n) (hs : separated w)
    (hc : ∀ i, (positions w (w i)).card = 2) :
    ∃ g : Fin 4 → Fin n, Function.Injective g ∧
      ∃ p q r s t, (∀ i, w i = g (pattern p q r s t i)) ∧
      (∀ a : Fin 3, (positions (pattern p q r s t) a.castSucc).card = 2) ∧
      separated (pattern p q r s t) := by
  have hab : w 0 ≠ w 1 := (hs 0).1
  have hac : w 0 ≠ w 2 := (hs 0).2
  have hbc : w 1 ≠ w 2 := (hs 1).1
  let code (a : Fin n) : Fin 4 := if a = w 0 then 0 else if a = w 1 then 1 else if a = w 2 then 2 else 3
  let u := pattern (code (w 3)) (code (w 4)) (code (w 5)) (code (w 6)) (code (w 7))
  have hu (i : Fin 8) : u i = code (w i) := by
    fin_cases i <;> simp [u, pattern, code, hab, hac, hbc, Ne.symm]
  have hcodes (i : Fin 8) :
      (u i = 0 ↔ w i = w 0) ∧ (u i = 1 ↔ w i = w 1) ∧
      (u i = 2 ↔ w i = w 2) ∧ (u i = 3 ↔ w i ≠ w 0 ∧ w i ≠ w 1 ∧ w i ≠ w 2) := by
    rw [hu]
    by_cases h₀ : w i = w 0
    · simp [code, h₀, hab, hac]
    by_cases h₁ : w i = w 1
    · simp [code, h₁, hbc, hab.symm]
    by_cases h₂ : w i = w 2
    · simp [code, h₂, hac.symm, hbc.symm]
    · simp [code, h₀, h₁, h₂]
  have hcount (a : Fin 3) : (positions u a.castSucc).card = 2 := by
    fin_cases a
    · change (positions u 0).card = 2
      rw [show positions u 0 = positions w (w 0) by ext i; simpa [positions] using (hcodes i).1]
      exact hc 0
    · change (positions u 1).card = 2
      rw [show positions u 1 = positions w (w 1) by ext i; simpa [positions] using (hcodes i).2.1]
      exact hc 1
    · change (positions u 2).card = 2
      rw [show positions u 2 = positions w (w 2) by ext i; simpa [positions] using (hcodes i).2.2.1]
      exact hc 2
  have h3 : (positions u 3).card = 2 := fourth_bucket _ _ _ _ _ hcount
  obtain ⟨k, hk⟩ := Finset.card_pos.mp (by rw [h3]; decide)
  have hk' : u k = 3 := by simpa [positions] using hk
  have hn := (hcodes k).2.2.2.mp hk'
  have he : positions w (w k) = positions u 3 := by
    apply Finset.eq_of_subset_of_card_le ?_ (by rw [h3, hc])
    intro i hi
    have hi' : w i = w k := by simpa [positions] using hi
    simp [positions, hu, code, hi', hn.1, hn.2.1, hn.2.2]
  let g : Fin 4 → Fin n := ![w 0,w 1,w 2,w k]
  have hg : Function.Injective g := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [g]
  have hgu (i : Fin 8) : w i = g (u i) := by
    have hh := (hcodes i).1
    have hh₁ := (hcodes i).2.1
    have hh₂ := (hcodes i).2.2.1
    have hh₃ : u i = 3 → w i = w k := by
      intro hi
      have hm : i ∈ positions w (w k) := by rw [he]; simp [positions, hi]
      simpa [positions] using hm
    generalize hval : u i = a
    fin_cases a <;> simp_all [g]
  refine ⟨g, hg, _, _, _, _, _, hgu, hcount, fun i => ⟨?_, ?_⟩⟩
  · intro hi
    exact (hs i).1 (by rw [hgu i, hgu (i + 1)]; exact congrArg g hi)
  · intro hi
    exact (hs i).2 (by rw [hgu i, hgu (i + 2)]; exact congrArg g hi)

private noncomputable def wordGamma {n : ℕ} (word : List (Fin n)) (z : Q n → ℝ) : Q n → ℝ :=
  word.foldr (fun a f => gamma a f) z

private theorem gamma_square {n : ℕ} (a : Fin n) (z : Q n → ℝ) :
    gamma a (gamma a z) = z := by
  funext x
  rw [BalancedCriticalSpectrum.gamma_apply, BalancedCriticalSpectrum.gamma_apply,
    BalancedCriticalSpectrum.flip_flip, huangMatrix_symmetric (flip x a) x, ← mul_assoc,
    ← pow_two, SupportedEigenSaturation.matrix_sq_of_adj (BalancedCriticalSpectrum.flip_adj x a),
    one_mul]

private theorem word_switching {n : ℕ} {S : Finset (Q n)} {sigma : Q n → ℝ}
    (hs : IsSwitching S sigma) (x : Q n) (word : List (Fin n))
    (hx : ∀ y ∈ word.scanl flip x, y ∈ S) :
    wordGamma word (fun _ => 1) x = sigma x * sigma (word.foldl flip x) := by
  induction word generalizing x with
  | nil =>
    have h := switching_sq hs (hx x (by simp))
    simpa [wordGamma, pow_two] using h.symm
  | cons a word ih =>
    have hx₀ := hx x (by simp)
    have hx₁ (y : Q n) (hy : y ∈ word.scanl flip (flip x a)) : y ∈ S :=
      hx y (by simp [List.scanl_cons, hy])
    have ha := hx₁ (flip x a) (by cases word <;> simp [List.scanl_cons])
    change gamma a (wordGamma word (fun _ => 1)) x = sigma x * sigma (word.foldl flip (flip x a))
    rw [BalancedCriticalSpectrum.gamma_apply, ih _ hx₁,
      hs.2 x hx₀ _ ha (BalancedCriticalSpectrum.flip_adj x a)]
    have h := switching_sq hs ha
    linear_combination (sigma x * sigma (word.foldl flip (flip x a))) * h

private theorem positive_word {n : ℕ} {S : Finset (Q n)} (hbal : IsBalanced S)
    (v : Fin 8 → (S : Set (Q n))) (w : Fin 8 → Fin n)
    (step : ∀ i, (v (i + 1)).val = flip (v i).val (w i)) :
    wordGamma [w 0,w 1,w 2,w 3,w 4,w 5,w 6,w 7] (fun _ => 1) (v 0).val = 1 := by
  obtain ⟨sigma, hs⟩ := hbal
  have h₀ : flip (v 0).val (w 0) = (v 1).val := (step 0).symm
  have h₁ : flip (v 1).val (w 1) = (v 2).val := (step 1).symm
  have h₂ : flip (v 2).val (w 2) = (v 3).val := (step 2).symm
  have h₃ : flip (v 3).val (w 3) = (v 4).val := (step 3).symm
  have h₄ : flip (v 4).val (w 4) = (v 5).val := (step 4).symm
  have h₅ : flip (v 5).val (w 5) = (v 6).val := (step 5).symm
  have h₆ : flip (v 6).val (w 6) = (v 7).val := (step 6).symm
  have h₇ : flip (v 7).val (w 7) = (v 0).val := (step 7).symm
  rw [word_switching hs]
  · simpa only [List.foldl_cons, List.foldl_nil, h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, ← pow_two] using
      switching_sq hs (v 0).property
  · intro y hy
    simp only [List.scanl_cons, List.scanl_nil, h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇,
      List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with h | h | h | h | h | h | h | h | h
    all_goals subst y; exact Subtype.property _

/-- The first three directions determine the three possible positive word types. -/
private theorem positive_eight_word {n : ℕ} {S : Finset (Q n)} (hbal : IsBalanced S)
    (v : Fin 8 → (S : Set (Q n))) (hv : Function.Injective v)
    (w : Fin 8 → Fin n) (step : ∀ i, (v (i + 1)).val = flip (v i).val (w i)) :
    ∃ g : Fin 4 → Fin n, Function.Injective g ∧
      w 0 = g 0 ∧ w 1 = g 1 ∧ w 2 = g 2 ∧
      ([w 7,w 6,w 5,w 4,w 3] = [g 3,g 2,g 1,g 0,g 3] ∨
       [w 7,w 6,w 5,w 4,w 3] = [g 3,g 1,g 2,g 3,g 0] ∨
       [w 7,w 6,w 5,w 4,w 3] = [g 2,g 3,g 0,g 1,g 3]) := by
  have hsep := actual_separation hbal v hv w step
  obtain ⟨g, hg, p, q, r, s, t, hw, hc, hsep'⟩ :=
    normalize w hsep (position_count w hsep (closed_even v w step))
  have hpos := positive_word hbal v w step
  have h₀ : w 0 = g 0 := hw 0
  have h₁ : w 1 = g 1 := hw 1
  have h₂ : w 2 = g 2 := hw 2
  have h₃ : w 3 = g p := hw 3
  have h₄ : w 4 = g q := hw 4
  have h₅ : w 5 = g r := hw 5
  have h₆ : w 6 = g s := hw 6
  have h₇ : w 7 = g t := hw 7
  refine ⟨g, hg, h₀, h₁, h₂, ?_⟩
  rw [h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇] at hpos
  rw [h₃, h₄, h₅, h₆, h₇]
  rcases seven_patterns p q r s t hc hsep' with h | h | h | h | h | h | h <;>
    simp only [List.cons.injEq, and_true] at h <;>
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · simp only [wordGamma, List.foldr_cons, List.foldr_nil] at hpos
    rw [BalancedCubeGirth.gamma_anticommute (hg.ne (show (2 : Fin 4) ≠ 0 by decide))
      (gamma (g 3) (gamma (g 1) (gamma (g 2) (gamma (g 3) (fun _ => 1)))))] at hpos
    simp only [map_neg, neg_neg] at hpos
    rw [BalancedCubeGirth.gamma_anticommute (hg.ne (show (1 : Fin 4) ≠ 0 by decide))
      (gamma (g 2) (gamma (g 3) (gamma (g 1) (gamma (g 2) (gamma (g 3) (fun _ => 1))))))] at hpos
    simp only [map_neg, neg_neg] at hpos
    rw [gamma_square (g 0) (gamma (g 1) (gamma (g 2) (gamma (g 3) (gamma (g 1) (gamma (g 2) (gamma (g 3) (fun _ => 1)))))))] at hpos
    rw [BalancedCubeGirth.gamma_anticommute (hg.ne (show (3 : Fin 4) ≠ 1 by decide))
      (gamma (g 2) (gamma (g 3) (fun _ => 1)))] at hpos
    simp only [map_neg, neg_neg] at hpos
    rw [BalancedCubeGirth.gamma_anticommute (hg.ne (show (2 : Fin 4) ≠ 1 by decide))
      (gamma (g 3) (gamma (g 2) (gamma (g 3) (fun _ => 1))))] at hpos
    simp only [map_neg, neg_neg] at hpos
    rw [gamma_square (g 1) (gamma (g 2) (gamma (g 3) (gamma (g 2) (gamma (g 3) (fun _ => 1)))))] at hpos
    rw [BalancedCubeGirth.gamma_anticommute (hg.ne (show (3 : Fin 4) ≠ 2 by decide))
      (gamma (g 3) (fun _ => 1))] at hpos
    simp only [map_neg, neg_neg] at hpos
    rw [gamma_square (g 2) (gamma (g 3) (gamma (g 3) (fun _ => 1)))] at hpos
    rw [gamma_square (g 3) (fun _ => 1)] at hpos
    norm_num at hpos
  · simp only [wordGamma, List.foldr_cons, List.foldr_nil] at hpos
    rw [BalancedCubeGirth.gamma_anticommute (hg.ne (show (3 : Fin 4) ≠ 0 by decide))
      (gamma (g 1) (gamma (g 3) (gamma (g 2) (fun _ => 1))))] at hpos
    simp only [map_neg, neg_neg] at hpos
    rw [BalancedCubeGirth.gamma_anticommute (hg.ne (show (2 : Fin 4) ≠ 0 by decide))
      (gamma (g 3) (gamma (g 1) (gamma (g 3) (gamma (g 2) (fun _ => 1)))))] at hpos
    simp only [map_neg, neg_neg] at hpos
    rw [BalancedCubeGirth.gamma_anticommute (hg.ne (show (1 : Fin 4) ≠ 0 by decide))
      (gamma (g 2) (gamma (g 3) (gamma (g 1) (gamma (g 3) (gamma (g 2) (fun _ => 1))))))] at hpos
    simp only [map_neg, neg_neg] at hpos
    rw [gamma_square (g 0) (gamma (g 1) (gamma (g 2) (gamma (g 3) (gamma (g 1) (gamma (g 3) (gamma (g 2) (fun _ => 1)))))))] at hpos
    rw [BalancedCubeGirth.gamma_anticommute (hg.ne (show (3 : Fin 4) ≠ 1 by decide))
      (gamma (g 3) (gamma (g 2) (fun _ => 1)))] at hpos
    simp only [map_neg, neg_neg] at hpos
    rw [BalancedCubeGirth.gamma_anticommute (hg.ne (show (2 : Fin 4) ≠ 1 by decide))
      (gamma (g 3) (gamma (g 3) (gamma (g 2) (fun _ => 1))))] at hpos
    simp only [map_neg, neg_neg] at hpos
    rw [gamma_square (g 1) (gamma (g 2) (gamma (g 3) (gamma (g 3) (gamma (g 2) (fun _ => 1)))))] at hpos
    rw [BalancedCubeGirth.gamma_anticommute (hg.ne (show (3 : Fin 4) ≠ 2 by decide))
      (fun _ => 1)] at hpos
    simp only [map_neg, neg_neg] at hpos
    rw [BalancedCubeGirth.gamma_anticommute (hg.ne (show (3 : Fin 4) ≠ 2 by decide))
      (gamma (g 3) (fun _ => 1))] at hpos
    simp only [map_neg, neg_neg] at hpos
    rw [gamma_square (g 2) (gamma (g 3) (gamma (g 3) (fun _ => 1)))] at hpos
    rw [gamma_square (g 3) (fun _ => 1)] at hpos
    norm_num at hpos
  · simp only [wordGamma, List.foldr_cons, List.foldr_nil] at hpos
    rw [BalancedCubeGirth.gamma_anticommute (hg.ne (show (3 : Fin 4) ≠ 0 by decide))
      (gamma (g 2) (gamma (g 1) (gamma (g 3) (fun _ => 1))))] at hpos
    simp only [map_neg, neg_neg] at hpos
    rw [BalancedCubeGirth.gamma_anticommute (hg.ne (show (2 : Fin 4) ≠ 0 by decide))
      (gamma (g 3) (gamma (g 2) (gamma (g 1) (gamma (g 3) (fun _ => 1)))))] at hpos
    simp only [map_neg, neg_neg] at hpos
    rw [BalancedCubeGirth.gamma_anticommute (hg.ne (show (1 : Fin 4) ≠ 0 by decide))
      (gamma (g 2) (gamma (g 3) (gamma (g 2) (gamma (g 1) (gamma (g 3) (fun _ => 1))))))] at hpos
    simp only [map_neg, neg_neg] at hpos
    rw [gamma_square (g 0) (gamma (g 1) (gamma (g 2) (gamma (g 3) (gamma (g 2) (gamma (g 1) (gamma (g 3) (fun _ => 1)))))))] at hpos
    rw [BalancedCubeGirth.gamma_anticommute (hg.ne (show (2 : Fin 4) ≠ 1 by decide))
      (gamma (g 3) (fun _ => 1))] at hpos
    simp only [map_neg, neg_neg] at hpos
    rw [BalancedCubeGirth.gamma_anticommute (hg.ne (show (3 : Fin 4) ≠ 1 by decide))
      (gamma (g 2) (gamma (g 3) (fun _ => 1)))] at hpos
    simp only [map_neg, neg_neg] at hpos
    rw [BalancedCubeGirth.gamma_anticommute (hg.ne (show (2 : Fin 4) ≠ 1 by decide))
      (gamma (g 3) (gamma (g 2) (gamma (g 3) (fun _ => 1))))] at hpos
    simp only [map_neg, neg_neg] at hpos
    rw [gamma_square (g 1) (gamma (g 2) (gamma (g 3) (gamma (g 2) (gamma (g 3) (fun _ => 1)))))] at hpos
    rw [BalancedCubeGirth.gamma_anticommute (hg.ne (show (3 : Fin 4) ≠ 2 by decide))
      (gamma (g 3) (fun _ => 1))] at hpos
    simp only [map_neg, neg_neg] at hpos
    rw [gamma_square (g 2) (gamma (g 3) (gamma (g 3) (fun _ => 1)))] at hpos
    rw [gamma_square (g 3) (fun _ => 1)] at hpos
    norm_num at hpos
  · simp only [wordGamma, List.foldr_cons, List.foldr_nil] at hpos
    rw [BalancedCubeGirth.gamma_anticommute (hg.ne (show (1 : Fin 4) ≠ 0 by decide))
      (gamma (g 2) (gamma (g 3) (fun _ => 1)))] at hpos
    simp only [map_neg, neg_neg] at hpos
    rw [BalancedCubeGirth.gamma_anticommute (hg.ne (show (3 : Fin 4) ≠ 0 by decide))
      (gamma (g 1) (gamma (g 2) (gamma (g 3) (fun _ => 1))))] at hpos
    simp only [map_neg, neg_neg] at hpos
    rw [BalancedCubeGirth.gamma_anticommute (hg.ne (show (2 : Fin 4) ≠ 0 by decide))
      (gamma (g 3) (gamma (g 1) (gamma (g 2) (gamma (g 3) (fun _ => 1)))))] at hpos
    simp only [map_neg, neg_neg] at hpos
    rw [BalancedCubeGirth.gamma_anticommute (hg.ne (show (1 : Fin 4) ≠ 0 by decide))
      (gamma (g 2) (gamma (g 3) (gamma (g 1) (gamma (g 2) (gamma (g 3) (fun _ => 1))))))] at hpos
    simp only [map_neg, neg_neg] at hpos
    rw [gamma_square (g 0) (gamma (g 1) (gamma (g 2) (gamma (g 3) (gamma (g 1) (gamma (g 2) (gamma (g 3) (fun _ => 1)))))))] at hpos
    rw [BalancedCubeGirth.gamma_anticommute (hg.ne (show (3 : Fin 4) ≠ 1 by decide))
      (gamma (g 2) (gamma (g 3) (fun _ => 1)))] at hpos
    simp only [map_neg, neg_neg] at hpos
    rw [BalancedCubeGirth.gamma_anticommute (hg.ne (show (2 : Fin 4) ≠ 1 by decide))
      (gamma (g 3) (gamma (g 2) (gamma (g 3) (fun _ => 1))))] at hpos
    simp only [map_neg, neg_neg] at hpos
    rw [gamma_square (g 1) (gamma (g 2) (gamma (g 3) (gamma (g 2) (gamma (g 3) (fun _ => 1)))))] at hpos
    rw [BalancedCubeGirth.gamma_anticommute (hg.ne (show (3 : Fin 4) ≠ 2 by decide))
      (gamma (g 3) (fun _ => 1))] at hpos
    simp only [map_neg, neg_neg] at hpos
    rw [gamma_square (g 2) (gamma (g 3) (gamma (g 3) (fun _ => 1)))] at hpos
    rw [gamma_square (g 3) (fun _ => 1)] at hpos
    norm_num at hpos

end D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointEightWord
