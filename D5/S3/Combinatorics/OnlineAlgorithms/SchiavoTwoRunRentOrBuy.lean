/- GID: D5/S3/Combinatorics/OnlineAlgorithms/SchiavoTwoRunRentOrBuy
   generality: I
   mirror-B: D5/B/S3/Combinatorics/OnlineAlgorithms/SchiavoTwoRunRentOrBuy
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: One online rule with factor three and a two-run additive bound. -/

import D5.S3.Combinatorics.OnlineAlgorithms.GuardedRentOrBuyAdditive

set_option autoImplicit false

namespace GuardedRentOrBuy

noncomputable section

/-- At most two maximal constant consecutive runs, with empty blocks allowed. -/
def AtMostTwoRuns (xs : List ℝ) : Prop :=
  ∃ (a b : ℝ) (m n : ℕ), xs = List.replicate m a ++ List.replicate n b

/-- One first-call decision plus one decision on each visible increment. -/
def sessionCost (K : ℝ) (xs : List ℝ) (first : Bool) (rs : List Bool) : ℝ :=
  bill K 0 0 first + comparatorCost K 0 (xs.zip rs)

/-- Evaluate the deterministic prefix rule at each nonempty visible prefix. -/
def actions (rule : List ℝ → Bool) (xs : List ℝ) : List Bool :=
  List.ofFn fun i : Fin xs.length => rule (xs.take (i.val + 1))

private theorem scheduled_rates (K : ℝ) (s : State) (xs : List ℝ) :
    (scheduled K s xs).map Prod.fst = xs := by
  induction xs generalizing s with
  | nil => rfl
  | cons a xs ih => simp [scheduled, ih]

private theorem zip_actions (K : ℝ) (xs : List ℝ) :
    xs.zip (actions (prefixRule K) xs) = scheduled K initial xs := by
  let sc := scheduled K initial xs
  have hfst : sc.map Prod.fst = xs := scheduled_rates K initial xs
  have hlen : sc.length = xs.length := by simpa using congrArg List.length hfst
  have hacts : sc.map Prod.snd = actions (prefixRule K) xs := by
    apply List.ext_getElem
    · simp [actions, hlen]
    intro i h₁ h₂
    have h₃ : i < sc.length := by simpa using h₁
    have hg : sc[i]? = some sc[i] := List.getElem?_eq_getElem h₃
    have h₄ : (scheduled K ([].foldl (advance K) initial) xs)[i]? =
        some (sc[i].1, sc[i].2) := by
      change sc[i]? = some sc[i]
      exact hg
    have hr := scheduled_prefix K [] xs i sc[i].1 sc[i].2 h₄
    simpa [actions] using hr.symm
  exact (List.zip_of_prod hfst hacts).symm

private theorem zip_replicate (a : ℝ) (rs : List Bool) :
    (List.replicate rs.length a).zip rs = block a rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    change (a, r) :: (List.replicate rs.length a).zip rs = (a, r) :: block a rs
    rw [ih]

private theorem rates_nonneg_zip {xs : List ℝ} {rs : List Bool}
    (ha : ∀ a ∈ xs, 0 ≤ a) (h : rs.length = xs.length) :
    ∀ p ∈ xs.zip rs, 0 ≤ p.1 := by
  intro p hp
  apply ha
  rw [← List.map_fst_zip (l₁ := xs) (l₂ := rs) h.ge]
  exact List.mem_map_of_mem hp

private theorem additive_two_runs (K : ℝ) (hK : 0 < K) (xs : List ℝ) (ha : ∀ a ∈ xs, 0 ≤ a)
    (runs : AtMostTwoRuns xs) (first : Bool) (rs : List Bool) (hlen : rs.length = xs.length) :
    sessionCost K xs (prefixRule K []) (actions (prefixRule K) xs) ≤
      sessionCost K xs first rs + 2 * K := by
  obtain ⟨a, b, m, n, rfl⟩ := runs
  simp only [List.length_append, List.length_replicate] at hlen
  let left := rs.take m
  let right := rs.drop m
  have hl : left.length = m := by simp [left, List.length_take, hlen]
  have hr : right.length = n := by simp [right, List.length_drop, hlen]
  have hzip : (List.replicate m a ++ List.replicate n b).zip rs = block a left ++ block b right := by
    have happ : left ++ right = rs := List.take_append_drop m rs
    rw [← happ, List.zip_append (by simp [hl]), ← hl, ← hr, zip_replicate, zip_replicate]
  have hbound : policyCost K initial (List.replicate m a ++ List.replicate n b) ≤
        comparatorCost K 0 (block a left ++ block b right) + 2 * K := by
    by_cases hm : m = 0
    · have hzero : left = [] := List.length_eq_zero_iff.mp (hl.trans hm)
      rw [hm, hzero]
      change policyCost K initial (List.replicate n b) ≤ comparatorCost K 0 (block b right) + 2 * K
      by_cases hn : n = 0
      · have hrzero : right = [] := List.length_eq_zero_iff.mp (hr.trans hn)
        rw [hn, hrzero]
        simp [policyCost, block, comparatorCost, hK.le]
      · have hb : 0 ≤ b := ha b (by simp [List.mem_replicate, hn])
        have hcore := single_block_bound hK hb (o := 0) le_rfl initial rfl rfl
          (ordinary_initial K b) right
        rw [hr] at hcore
        linarith only [hcore, hK]
    · have hpa : 0 ≤ a := ha a (by simp [List.mem_replicate, hm])
      by_cases hn : n = 0
      · have hzero : right = [] := List.length_eq_zero_iff.mp (hr.trans hn)
        rw [hn, hzero]
        change policyCost K initial (List.replicate m a ++ []) ≤
          comparatorCost K 0 (block a left ++ []) + 2 * K
        rw [List.append_nil, List.append_nil]
        have hcore := single_block_bound hK hpa (o := 0) le_rfl initial rfl rfl
          (ordinary_initial K a) left
        rw [hl] at hcore
        linarith only [hcore, hK]
      · have hpb : 0 ≤ b := ha b (by simp [List.mem_replicate, hn])
        simpa only [hl, hr] using two_block_bound hK hpa hpb left right
  have he : comparatorCost K 0 (scheduled K initial (List.replicate m a ++ List.replicate n b)) =
      policyCost K initial (List.replicate m a ++ List.replicate n b) := scheduled_cost K initial _
  rw [sessionCost, zip_actions, he, sessionCost, hzip, prefixRule_nil]
  cases first <;> simp [bill] <;> linarith only [hbound, hK]

private theorem guarded_prefix_guarantees (K : ℝ) (hK : 0 < K) (xs : List ℝ)
    (ha : ∀ a ∈ xs, 0 ≤ a) (first : Bool) (rs : List Bool) (hlen : rs.length = xs.length) :
    let online := sessionCost K xs (prefixRule K []) (actions (prefixRule K) xs)
    let offline := sessionCost K xs first rs
    online ≤ 3 * offline ∧ (AtMostTwoRuns xs → online ≤ offline + 2 * K) := by
  refine ⟨?_, fun h => additive_two_runs K hK xs ha h first rs hlen⟩
  have h := factor_three K hK (xs.zip rs) (rates_nonneg_zip ha hlen) first
  rw [List.map_fst_zip hlen.ge] at h
  have hzero : bill K 0 0 false = 0 := by simp [bill]
  simpa [sessionCost, zip_actions, hzero, prefixRule_nil] using h

/-- Schiavo's third question in §5.B, with a universal factor of three. -/
theorem schiavo_section5b_third_question :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ K : ℝ, 0 < K →
      ∃ rule : List ℝ → Bool,
        ∀ (xs : List ℝ), (∀ a ∈ xs, 0 ≤ a) →
        ∀ (first : Bool) (rs : List Bool), rs.length = xs.length →
          let online := sessionCost K xs (rule []) (actions rule xs)
          let offline := sessionCost K xs first rs
          online ≤ c * offline ∧ (AtMostTwoRuns xs → online ≤ offline + 2 * K) := by
  exact ⟨3, by norm_num, fun K hK => ⟨prefixRule K, guarded_prefix_guarantees K hK⟩⟩

end

end GuardedRentOrBuy
