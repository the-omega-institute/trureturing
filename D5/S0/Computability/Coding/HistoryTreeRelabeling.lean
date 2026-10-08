/- GID: D5/S0/Computability/Coding/HistoryTreeRelabeling
   generality: G
   mirror-B: D5/B/S0/Computability/Coding/HistoryTreeRelabeling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: History-indexed permutations transport prefix codes, budgets and path masses. -/

import D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality

open scoped BigOperators ENNReal

namespace D5.S0.Computability.Coding.HistoryTreeRelabeling

open DepthBudgetIidGreedyOptimality PrefixFreeCode

variable {α : Type*}

/-- Relabel a continuation, consulting the original history at each edge. -/
def relabel (π : List α → Equiv.Perm α) : List α → List α → List α
  | _, [] => []
  | h, a :: w => π h a :: relabel π (h ++ [a]) w

/-- Decode a continuation, recovering the original history before the next edge. -/
def decode (π : List α → Equiv.Perm α) : List α → List α → List α
  | _, [] => []
  | h, a :: w => (π h).symm a :: decode π (h ++ [(π h).symm a]) w

/-- The mass of a continuation is the product of the actual conditional rows. -/
def pathMass (q : List α → α → ℝ) : List α → List α → ℝ
  | _, [] => 1
  | h, a :: w => q h a * pathMass q (h ++ [a]) w

/-- Relabeling preserves length even when its permutation depends on history. -/
theorem relabel_length (π : List α → Equiv.Perm α) (h w : List α) :
    (relabel π h w).length = w.length := by
  induction w generalizing h with
  | nil => rfl
  | cons a w ih => simp only [relabel, List.length_cons, ih]

/-- Decoding and relabeling are inverse in the same recovered history. -/
theorem decode_relabel (π : List α → Equiv.Perm α) (h w : List α) :
    decode π h (relabel π h w) = w := by
  induction w generalizing h with
  | nil => rfl
  | cons a w ih => simp only [relabel, decode, Equiv.symm_apply_apply, ih]

/-- A family of local permutations defines a bijection of the whole word tree. -/
def treeEquiv (π : List α → Equiv.Perm α) : List α ≃ List α where
  toFun := relabel π []
  invFun := decode π []
  left_inv := decode_relabel π []
  right_inv := by
    intro w
    have inverse (h w : List α) : relabel π h (decode π h w) = w := by
      induction w generalizing h with
      | nil => rfl
      | cons a w ih => simp only [decode, relabel, Equiv.apply_symm_apply, ih]
    exact inverse [] w

/-- Relabeling an appended continuation consults the history before relabeling. -/
theorem relabel_append (π : List α → Equiv.Perm α) (h u v : List α) :
    relabel π h (u ++ v) = relabel π h u ++ relabel π (h ++ u) v := by
  induction u generalizing h with
  | nil => simp only [List.nil_append, List.append_nil, relabel]
  | cons a u ih =>
    simp only [List.cons_append, relabel, ih, List.cons_append]
    congr 2
    simp only [List.append_assoc, List.singleton_append]

/-- Both directions of the tree bijection preserve the ancestor relation. -/
theorem relabel_prefix_iff (π : List α → Equiv.Perm α) (h u v : List α) :
    relabel π h u <+: relabel π h v ↔ u <+: v := by
  constructor
  · induction u generalizing h v with
    | nil => intro _; exact List.nil_prefix
    | cons a u ih =>
      cases v with
      | nil => simp [relabel]
      | cons c v =>
        simp only [relabel, List.cons_prefix_cons]
        rintro ⟨hac, huv⟩
        have he := (π h).injective hac
        subst c
        exact ⟨rfl, ih (h ++ [a]) v huv⟩
  · rintro ⟨w, rfl⟩
    rw [relabel_append]
    exact List.prefix_append _ _

/-- Row transport gives pathwise transport, with no stationarity assumption. -/
theorem path_mass_relabel (π : List α → Equiv.Perm α) (p : α → ℝ)
    (q : List α → α → ℝ) (hq : ∀ h a, q h a = p (π h a)) (h w : List α) :
    pathMass q h w = wordMass p (relabel π h w) := by
  induction w generalizing h with
  | nil => simp [pathMass, relabel, wordMass]
  | cons a w ih => simp only [pathMass, relabel, wordMass, List.map_cons,
      List.prod_cons, hq, ih, wordMass]

/-- Constant conditional rows recover the existing iid word mass. -/
theorem path_mass_iid (p : α → ℝ) (h w : List α) :
    pathMass (fun _ => p) h w = wordMass p w := by
  induction w generalizing h with
  | nil => simp [pathMass, wordMass]
  | cons a w ih => simp only [pathMass, wordMass, List.map_cons, List.prod_cons, ih,
      wordMass]

/-- A finite sum of history-dependent codeword masses, using the canonical levels. -/
noncomputable def historyTruncatedMass [Fintype α] [DecidableEq α]
    (q : List α → α → ℝ) (F : Set (List α)) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), ∑ w ∈ level F n, pathMass q [] w

/-- The nonnegative countable mass of a history-dependent prefix code. -/
noncomputable def historyCodeMass (q : List α → α → ℝ) (F : Set (List α)) : ℝ≥0∞ :=
  ∑' w : F, ENNReal.ofReal (pathMass q [] w.1)

/-- Canonical levels are transported bijectively, including their cardinalities. -/
theorem level_relabel [Fintype α] [DecidableEq α]
    (π : List α → Equiv.Perm α) (F : Set (List α)) (n : ℕ) :
    level (relabel π [] '' F) n = (level F n).image (relabel π []) := by
  classical
  ext w
  rw [mem_level, Finset.mem_image]
  constructor
  · rintro ⟨hl, v, hv, rfl⟩
    exact ⟨v, (mem_level F v n).mpr ⟨(relabel_length π [] v) ▸ hl, hv⟩, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨hl, hm⟩ := (mem_level F v n).mp hv
    exact ⟨(relabel_length π [] v).trans hl, v, hm, rfl⟩

/-- The same tree bijection transports a legal code and every finite mass. -/
theorem result [Fintype α] [DecidableEq α]
    (π : List α → Equiv.Perm α) (p : α → ℝ) (q : List α → α → ℝ)
    (hq : ∀ h a, q h a = p (π h a)) (b : ℕ → ℕ) (F : Set (List α))
    (hF : Legal b F) :
    Legal b (relabel π [] '' F) ∧
    (∀ N, historyTruncatedMass q F N = truncatedMass p (relabel π [] '' F) N) ∧
    historyCodeMass q F = codeMass p (relabel π [] '' F) := by
  classical
  have inj : Function.Injective (relabel π []) := (treeEquiv π).injective
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ huv
    exact congrArg (relabel π []) (hF.1 hu hv ((relabel_prefix_iff π [] u v).mp huv))
  · rintro ⟨v, hv, he⟩
    have hv0 : v = [] := by
      apply List.length_eq_zero_iff.mp
      simpa only [he, List.length_nil] using (relabel_length π [] v).symm
    exact hF.2.1 (hv0 ▸ hv)
  · intro n
    rw [level_relabel, Finset.card_image_of_injective _ inj]
    exact hF.2.2 n
  · intro N
    apply Finset.sum_congr rfl
    intro n _
    rw [level_relabel, Finset.sum_image (fun _ _ _ _ h => inj h)]
    apply Finset.sum_congr rfl
    intro w _
    exact path_mass_relabel π p q hq [] w
  · let e : F ≃ (relabel π [] '' F) := Equiv.image (treeEquiv π) F
    change (∑' w : F, ENNReal.ofReal (pathMass q [] w.1)) =
      ∑' w : (relabel π [] '' F), ENNReal.ofReal (wordMass p w.1)
    rw [← e.tsum_eq]
    apply tsum_congr
    intro w
    exact congrArg ENNReal.ofReal (path_mass_relabel π p q hq [] w.1)

end D5.S0.Computability.Coding.HistoryTreeRelabeling
