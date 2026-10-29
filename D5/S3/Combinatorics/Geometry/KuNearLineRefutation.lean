/- GID: D5/S3/Combinatorics/Geometry/KuNearLineRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Geometry/KuNearLineRefutation
   mirror-E: none(waiver:ordinary-board-refutation)
   anchors: [mathlib/module/Mathlib.Data.Finset.Max]
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Combinatorics/Geometry/KuNearLineRefutation.claim; result=D5/S3/Combinatorics/Geometry/KuNearLineRefutation.result; claim=D5/S3/Combinatorics/Geometry/KuNearLineRefutation.claim
   digest: The ordinary three-dimensional board has maximal saturated near-line-avoiding density below one third. -/

import D5.S3.Combinatorics.LatinEulerianDefs
import Mathlib.Tactic

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

open Finset
namespace KuGeometry

/-! Ku, Monochromatic k in a row, arXiv:2606.12880v1, Definitions 2.1, 2.2,
2.4, 2.6 and Conjecture 5.6. Coordinates are ordinary integers after adding one
 to each Fin value. Every nonzero signed direction is quantified; endpoints
must remain inside the board. The bound concerns the maximum density among
inclusion-maximal configurations, not the minimum or a toric board. -/

abbrev C := Fin 3
abbrev P := Fin 3 → C
def coord (a : P) (i : Fin 3) : ℤ := (a i).val + 1
def Valid (s v : Fin 3 → ℤ) : Prop :=
  (∃ i, v i ≠ 0) ∧ (∀ i, v i = -1 ∨ v i = 0 ∨ v i = 1) ∧
  ∀ t : Fin 3, ∀ i, 1 ≤ s i + t.val * v i ∧ s i + t.val * v i ≤ 3
def On (a : P) (s v : Fin 3 → ℤ) : Prop :=
  ∃ t : Fin 3, ∀ i, coord a i = s i + t.val * v i
def Common (a b : P) : Prop := ∃ s v, Valid s v ∧ On a s v ∧ On b s v
def Config (S : Finset P) : Prop := ∀ a ∈ S, ∀ b ∈ S, Common a b → a = b

theorem axis_common (a b : P) (j : Fin 3) (h : ∀ i, i ≠ j → a i = b i) : Common a b := by
  let s : Fin 3 → ℤ := fun i => if i = j then 1 else coord a i
  let v : Fin 3 → ℤ := fun i => if i = j then 1 else 0
  refine ⟨s, v, ?_, ?_, ?_⟩
  · refine ⟨⟨j, by simp [v]⟩, ?_, ?_⟩
    · intro i; dsimp [v]; split_ifs <;> simp
    · intro t i
      dsimp [s, v, coord]
      split_ifs
      · have := t.isLt; omega
      · have := (a i).isLt; omega
  · refine ⟨a j, ?_⟩
    intro i
    dsimp [s, v]
    split_ifs with e
    · subst i; simp [coord, add_comm]
    · simp
  · refine ⟨b j, ?_⟩
    intro i
    dsimp [s, v]
    split_ifs with e
    · subst i; simp [coord, add_comm]
    · simp [coord, h i e]

-- Every pair lying on a full face diagonal has a literal ordinary integer line.
theorem diag_common (a b : P) (hz : a 2 = b 2)
    (h : (a 0 = a 1 ∧ b 0 = b 1) ∨
      ((a 0).val + (a 1).val = 2 ∧ (b 0).val + (b 1).val = 2)) : Common a b := by
  rcases h with h | h
  · refine ⟨![1,1,coord a 2], ![1,1,0], ?_, ?_, ?_⟩
    · constructor
      · exact ⟨0, by norm_num⟩
      constructor
      · intro i; fin_cases i <;> simp
      · intro t i; fin_cases i <;> simp [coord, add_comm]
        all_goals have := t.isLt; have := (a 2).isLt; omega
    · refine ⟨a 0, ?_⟩
      intro i; fin_cases i <;> simp [coord, h.1, add_comm]
    · refine ⟨b 0, ?_⟩
      intro i; fin_cases i <;> simp [coord, h.2, hz, add_comm]
  · have ha : ((a 0).val : ℤ) + (a 1).val = 2 := by exact_mod_cast h.1
    have hb : ((b 0).val : ℤ) + (b 1).val = 2 := by exact_mod_cast h.2
    refine ⟨![1,3,coord a 2], ![1,-1,0], ?_, ?_, ?_⟩
    · constructor
      · exact ⟨0, by norm_num⟩
      constructor
      · intro i; fin_cases i <;> simp
      · intro t i; fin_cases i <;> simp [coord, add_comm]
        all_goals have := t.isLt; have := (a 2).isLt; omega
    · refine ⟨a 0, ?_⟩
      intro i; fin_cases i <;> simp [coord, add_comm]
      all_goals omega
    · refine ⟨b 0, ?_⟩
      intro i; fin_cases i <;> simp [coord, hz]
      all_goals omega

abbrev Latin := D5.S3.Combinatorics.LatinEulerianMultiples.IsLatin
theorem latin_diagonal (L : C → C → C) (hL : Latin 3 L) :
    ∃ i j : C, i ≠ j ∧ (L i i = L j j ∨ L i (2-i) = L j (2-j)) := by
  revert hL L
  unfold Latin D5.S3.Combinatorics.LatinEulerianMultiples.IsLatin Function.Bijective Function.Injective Function.Surjective
  decide +kernel


theorem config_bound (S : Finset P) (hs : Config S) : S.card ≤ 8 := by
  classical
  let proj : P → C × C := fun a => (a 0, a 1)
  have hinj : Set.InjOn proj S := by
    intro a ha b hb he
    apply hs a ha b hb
    apply axis_common a b 2
    intro i hi
    fin_cases i
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he
    · exact (hi rfl).elim
  have hc : S.card ≤ 9 := by
    have h := (S.image proj).card_le_univ
    rw [Finset.card_image_of_injOn hinj] at h
    simpa using h
  by_contra h8
  have h9 : S.card = 9 := by omega
  have hall : S.image proj = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinj, h9]
    decide
  have hfib : ∀ x y : C, ∃ z : C, ![x,y,z] ∈ S := by
    intro x y
    have hm : (x,y) ∈ S.image proj := by rw [hall]; simp
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hm
    refine ⟨a 2, ?_⟩
    have e : a = ![x,y,a 2] := by
      funext i
      fin_cases i
      · exact congrArg Prod.fst he
      · exact congrArg Prod.snd he
      · rfl
    rwa [← e]
  choose L hL using hfib
  have rowinj : ∀ i : C, Function.Injective (L i) := by
    intro i j j' he
    have h := hs _ (hL i j) _ (hL i j')
      (axis_common _ _ 1 (by intro c hc; fin_cases c <;> simp_all))
    simpa using congrFun h 1
  have colinj : ∀ j : C, Function.Injective (fun i => L i j) := by
    intro j i i' he
    have h := hs _ (hL i j) _ (hL i' j)
      (axis_common _ _ 0 (by intro c hc; fin_cases c <;> simp_all))
    simpa using congrFun h 0
  have hlatin : Latin 3 L :=
    ⟨fun i => ⟨rowinj i, Finite.surjective_of_injective (rowinj i)⟩,
      fun j => ⟨colinj j, Finite.surjective_of_injective (colinj j)⟩⟩
  obtain ⟨i,j,hij,he⟩ := latin_diagonal L hlatin
  rcases he with he | he
  · have h := hs _ (hL i i) _ (hL j j)
      (diag_common _ _ (by simpa using he) (Or.inl ⟨rfl,rfl⟩))
    exact hij (by simpa using congrFun h 0)
  · have hai : i.val + ((2-i : C).val) = 2 := by fin_cases i <;> decide
    have haj : j.val + ((2-j : C).val) = 2 := by fin_cases j <;> decide
    have h := hs _ (hL i (2-i)) _ (hL j (2-j))
      (diag_common _ _ (by simpa using he) (Or.inr ⟨hai,haj⟩))
    exact hij (by simpa using congrFun h 0)

def SourceConfig (S : Finset P) : Prop :=
  ∀ s v : Fin 3 → ℤ, Valid s v → ∀ N : Finset P, N.card = 2 →
  (∀ a ∈ N, On a s v) → ¬ N ⊆ S

theorem source_config_iff (S : Finset P) : SourceConfig S ↔ Config S := by
  classical
  constructor
  · intro hs a ha b hb hab
    by_contra hne
    obtain ⟨s,v,hv,haon,hbon⟩ := hab
    apply hs s v hv {a,b} (Finset.card_pair hne)
    · intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact haon
      · have ep := Finset.mem_singleton.mp hp
        subst p
        exact hbon
    · intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact ha
      · have ep := Finset.mem_singleton.mp hp
        subst p
        exact hb
  · intro hs s v hv N hN hon hsub
    obtain ⟨a,b,hne,rfl⟩ := Finset.card_eq_two.mp hN
    have ha : a ∈ ({a,b} : Finset P) := by simp
    have hb : b ∈ ({a,b} : Finset P) := by simp
    exact hne (hs a (hsub ha) b (hsub hb) ⟨s,v,hv,hon a ha,hon b hb⟩)


abbrev Board (k d : ℕ) := Fin d → Fin k
def GValid (k d : ℕ) (s v : Fin d → ℤ) : Prop :=
  (∃ i, v i ≠ 0) ∧ (∀ i, v i = -1 ∨ v i = 0 ∨ v i = 1) ∧
  ∀ t : Fin k, ∀ i, 1 ≤ s i + t.val * v i ∧ s i + t.val * v i ≤ k
def GOn {k d : ℕ} (a : Board k d) (s v : Fin d → ℤ) : Prop :=
  ∃ t : Fin k, ∀ i, (a i).val + (1 : ℤ) = s i + t.val * v i
noncomputable def GConfig {k d : ℕ} (S : Finset (Board k d)) : Prop := by
  classical
  exact ∀ s v, GValid k d s v → (S.filter (fun a => GOn a s v)).card ≤ k - 2

def GSourceConfig {k d : ℕ} (S : Finset (Board k d)) : Prop :=
  ∀ s v, GValid k d s v → ∀ N : Finset (Board k d), N.card = k - 1 →
    (∀ a ∈ N, GOn a s v) → ¬ N ⊆ S

theorem gsource_config_iff {k d : ℕ} (hk : 2 ≤ k) (S : Finset (Board k d)) :
    GSourceConfig S ↔ GConfig S := by
  classical
  constructor
  · intro h s v hv
    by_contra hn
    have hge : k - 1 ≤ (S.filter (fun a => GOn a s v)).card := by omega
    obtain ⟨N,hN,hcard⟩ := Finset.exists_subset_card_eq hge
    apply h s v hv N hcard
    · intro a ha; exact (Finset.mem_filter.mp (hN ha)).2
    · intro a ha; exact (Finset.mem_filter.mp (hN ha)).1
  · intro h s v hv N hcard hon hsub
    have hn : N ⊆ S.filter (fun a => GOn a s v) := by
      intro a ha; exact Finset.mem_filter.mpr ⟨hsub ha, hon a ha⟩
    have hle := Finset.card_le_card hn
    have hcap := h s v hv
    omega

theorem gconfig_33_iff (S : Finset P) : GConfig S ↔ Config S := by
  exact (gsource_config_iff (k := 3) (d := 3) (by decide) S).symm.trans
    (source_config_iff S)

def GSaturated {k d : ℕ} (S : Finset (Board k d)) : Prop :=
  GConfig S ∧ ∀ T : Finset (Board k d), GConfig T → S ⊆ T → T = S

theorem gexists_opt (k d : ℕ) : ∃ S : Finset (Board k d), GConfig S ∧
    ∀ T : Finset (Board k d), GConfig T → T.card ≤ S.card := by
  classical
  let F : Finset (Finset (Board k d)) := Finset.univ.filter GConfig
  have he : (∅ : Finset (Board k d)) ∈ F := by simp [F, GConfig]
  obtain ⟨S,hS,hmax⟩ := F.exists_max_image Finset.card ⟨∅,he⟩
  exact ⟨S, (Finset.mem_filter.mp hS).2,
    fun T hT => hmax T (by simp [F,hT])⟩
noncomputable def gopt (k d : ℕ) : Finset (Board k d) := Classical.choose (gexists_opt k d)
theorem gopt_spec (k d : ℕ) : GConfig (gopt k d) ∧
    ∀ T : Finset (Board k d), GConfig T → T.card ≤ (gopt k d).card := Classical.choose_spec (gexists_opt k d)
theorem gopt_saturated (k d : ℕ) : GSaturated (gopt k d) := by
  refine ⟨(gopt_spec k d).1, ?_⟩
  intro T hT hsub
  exact (Finset.eq_of_subset_of_card_le hsub ((gopt_spec k d).2 T hT)).symm
theorem density_maximum_attained (k d : ℕ) : ∃ S : Finset (Board k d),
    GSaturated S ∧ ∀ T : Finset (Board k d), GSaturated T → T.card ≤ S.card := by
  exact ⟨gopt k d, gopt_saturated k d, fun T hT => (gopt_spec k d).2 T hT.1⟩

/-- The chosen saturated cardinality maximum, divided by the board size. -/
noncomputable def density (k d : ℕ) : ℝ :=
  ((Classical.choose (density_maximum_attained k d)).card : ℝ) / (k : ℝ)^d

theorem exact_real_event : density 3 3 < (1 : ℝ) / 3 := by
  have hsat := (Classical.choose_spec (density_maximum_attained 3 3)).1
  have h := config_bound _ ((gconfig_33_iff _).mp hsat.1)
  have hr : ((Classical.choose (density_maximum_attained 3 3)).card : ℝ) ≤ 8 :=
    by exact_mod_cast h
  unfold density
  norm_num
  linarith

def claim : Prop := ∀ k : ℕ, 2 ≤ k → ∀ d : ℕ, density k d = 1 - 2 / (k : ℝ)
theorem result : ¬ claim := by
  intro h
  have he := h 3 (by norm_num) 3
  have hi := exact_real_event
  norm_num at he
  linarith
end KuGeometry
