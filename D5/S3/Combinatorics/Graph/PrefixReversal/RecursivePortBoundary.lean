/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/RecursivePortBoundary
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/RecursivePortBoundary
   mirror-E: none(waiver:native-recursive-port-boundary)
   anchors: []
   utility: none
   digest: The complete even and odd boundary matchings with internal seams have explicit Hamilton paths and use each matching edge once. -/
/- Symbolic port template; actual native realization is a separate consumer obligation. -/
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Tactic
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace D5.S3.Combinatorics.Graph.PrefixReversal.RecursivePortBoundary
abbrev RawPort := ℕ × ℕ
abbrev Port (k : ℕ) := Fin (k + 1) × Fin 2
def code {k : ℕ} (p : Port k) : RawPort := (p.1.val, p.2.val)
private theorem code_injective (k : ℕ) : Function.Injective (@code k) := by
  intro p q h
  apply Prod.ext <;> apply Fin.ext
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h
def pair (p q x y : RawPort) : Prop := (p = x ∧ q = y) ∨ (p = y ∧ q = x)
def ladder (cutoff : ℕ) (p q : RawPort) : Prop :=
  p.2 = 0 ∧ q.2 = 1 ∧ p.1 ≤ cutoff ∧ q.1 = p.1 + 1
/-- E_k from (58.22), with an explicit guard for its empty ladder range. -/
def evenBoundary (k : ℕ) (p q : RawPort) : Prop :=
  (3 ≤ k ∧ (ladder (k - 3) p q ∨ ladder (k - 3) q p)) ∨
    pair p q (k - 2, 0) (k, 0) ∨
    pair p q (k - 1, 0) (k, 1) ∨
    pair p q (k - 1, 1) (0, 1)
/-- O_k from (58.23), including its empty k=3 ladder range. -/
def oddBoundary (k : ℕ) (p q : RawPort) : Prop :=
  (4 ≤ k ∧ (ladder (k - 4) p q ∨ ladder (k - 4) q p)) ∨
    pair p q (k - 2, 0) (k - 1, 0) ∨
    pair p q (k - 3, 0) (k, 0) ∨
    pair p q (k - 2, 1) (k, 1) ∨
    pair p q (k - 1, 1) (0, 1)
/-- Exactly the internal c links L_i--R_(i+1), 0≤i<k. -/
def internalSeam (k : ℕ) (p q : RawPort) : Prop :=
  (p.2 = 1 ∧ q.2 = 0 ∧ p.1 < k ∧ q.1 = p.1 + 1) ∨
    (q.2 = 1 ∧ p.2 = 0 ∧ q.1 < k ∧ p.1 = q.1 + 1)
def boundary (k : ℕ) (p q : RawPort) : Prop :=
  if k % 2 = 0 then evenBoundary k p q else oddBoundary k p q
private theorem pair_symm {p q x y : RawPort} (h : pair p q x y) : pair q p x y := by
  rcases h with ⟨hpx, hqy⟩ | ⟨hpy, hqx⟩
  · exact Or.inr ⟨hqy, hpx⟩
  · exact Or.inl ⟨hqx, hpy⟩
private theorem even_boundary_symm (k : ℕ) (p q : RawPort) :
    evenBoundary k p q → evenBoundary k q p := by
  intro h
  rcases h with h | h | h | h
  · exact Or.inl ⟨h.1, h.2.symm⟩
  · exact Or.inr (Or.inl (pair_symm h))
  · exact Or.inr (Or.inr (Or.inl (pair_symm h)))
  · exact Or.inr (Or.inr (Or.inr (pair_symm h)))
private theorem odd_boundary_symm (k : ℕ) (p q : RawPort) :
    oddBoundary k p q → oddBoundary k q p := by
  intro h
  rcases h with h | h | h | h | h
  · exact Or.inl ⟨h.1, h.2.symm⟩
  · exact Or.inr (Or.inl (pair_symm h))
  · exact Or.inr (Or.inr (Or.inl (pair_symm h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (pair_symm h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (pair_symm h))))
private theorem boundary_symm (k : ℕ) (p q : RawPort) :
    boundary k p q → boundary k q p := by
  unfold boundary
  split_ifs
  · exact even_boundary_symm k p q
  · exact odd_boundary_symm k p q
private theorem internalSeam_symm (k : ℕ) (p q : RawPort) :
    internalSeam k p q → internalSeam k q p := by
  exact Or.symm
/-- The graph contains just the independently specified boundary paths and
the internal c seams; loop exclusion is explicit for all parameter values. -/
def boundaryGraph (k : ℕ) : SimpleGraph (Port k) where
  Adj p q := p ≠ q ∧ (boundary k (code p) (code q) ∨ internalSeam k (code p) (code q))
  symm := by
    constructor
    intro p q h
    exact ⟨h.1.symm, h.2.elim
      (fun hb => Or.inl (boundary_symm k _ _ hb))
      (fun hc => Or.inr (internalSeam_symm k _ _ hc))⟩
  loopless := by constructor; intro p h; exact h.1 rfl
/-- For k=2s+2 this is the exact even trace described in §58.9.
Its ranges are even ladder, four middle ports, then odd ladder. -/
def evenRoute (s j : ℕ) : RawPort :=
  if j ≤ 2 * s then (j, j % 2)
  else if j = 2 * s + 1 then (2 * s + 2, 0)
  else if j = 2 * s + 2 then (2 * s + 1, 1)
  else if j = 2 * s + 3 then (0, 1)
  else (j - (2 * s + 3), j % 2)
def evenInverse (s : ℕ) (p : RawPort) : ℕ :=
  if p.2 = 0 then
    if p.1 = 2 * s + 2 then 2 * s + 1
    else if p.1 % 2 = 0 then p.1 else p.1 + 2 * s + 3
  else
    if p.1 = 0 then 2 * s + 3
    else if p.1 = 2 * s + 1 then 2 * s + 2
    else if p.1 % 2 = 1 then p.1 else p.1 + 2 * s + 3
def oddRoute (s j : ℕ) : RawPort :=
  if j ≤ 2 * s then (j, j % 2)
  else if j = 2 * s + 1 then (2 * s + 3, 0)
  else if j = 2 * s + 2 then (2 * s + 2, 1)
  else if j = 2 * s + 3 then (0, 1)
  else if j < 4 * s + 4 then (j - (2 * s + 3), j % 2)
  else if j = 4 * s + 4 then (2 * s + 1, 0)
  else if j = 4 * s + 5 then (2 * s + 2, 0)
  else if j = 4 * s + 6 then (2 * s + 1, 1)
  else (2 * s + 3, 1)
def oddInverse (s : ℕ) (p : RawPort) : ℕ :=
  if p.2 = 0 then
    if p.1 = 2 * s + 3 then 2 * s + 1
    else if p.1 = 2 * s + 2 then 4 * s + 5
    else if p.1 = 2 * s + 1 then 4 * s + 4
    else if p.1 % 2 = 0 then p.1 else p.1 + 2 * s + 3
  else
    if p.1 = 0 then 2 * s + 3
    else if p.1 = 2 * s + 3 then 4 * s + 7
    else if p.1 = 2 * s + 2 then 2 * s + 2
    else if p.1 = 2 * s + 1 then 4 * s + 6
    else if p.1 % 2 = 1 then p.1 else p.1 + 2 * s + 3
private theorem even_route_front_eq (s j : ℕ) (h : j ≤ 2 * s) :
    evenRoute s j = (j, j % 2) := by
  simp only [evenRoute, if_pos h]
private theorem even_route_tail_eq (s j : ℕ) (h : 2 * s + 3 < j) :
    evenRoute s j = (j - (2 * s + 3), j % 2) := by
  simp (disch := omega) only [evenRoute, if_pos, if_neg, if_true, if_false]
private theorem even_route_mid0_eq (s : ℕ) : evenRoute s (2 * s) = (2 * s, 0) := by
  rw [even_route_front_eq s (2 * s) (by omega)]
  exact Prod.ext rfl (by omega)
private theorem even_route_mid1_eq (s : ℕ) :
    evenRoute s (2 * s + 1) = (2 * s + 2, 0) := by
  simp (disch := omega) only [evenRoute, if_pos, if_neg, if_true, if_false]
private theorem even_route_mid2_eq (s : ℕ) :
    evenRoute s (2 * s + 2) = (2 * s + 1, 1) := by
  simp (disch := omega) only [evenRoute, if_pos, if_neg, if_true, if_false]
private theorem even_route_mid3_eq (s : ℕ) : evenRoute s (2 * s + 3) = (0, 1) := by
  simp (disch := omega) only [evenRoute, if_pos, if_neg, if_true, if_false]
private theorem even_route_mid4_eq (s : ℕ) : evenRoute s (2 * s + 4) = (1, 0) := by
  rw [even_route_tail_eq s (2 * s + 4) (by omega)]
  apply Prod.ext <;> omega
private theorem even_route_last0_eq (s : ℕ) :
    evenRoute s (4 * s + 4) = (2 * s + 1, 0) := by
  rw [even_route_tail_eq s (4 * s + 4) (by omega)]
  apply Prod.ext <;> omega
private theorem even_route_last1_eq (s : ℕ) :
    evenRoute s (4 * s + 5) = (2 * s + 2, 1) := by
  rw [even_route_tail_eq s (4 * s + 5) (by omega)]
  apply Prod.ext <;> omega
private theorem odd_route_front_eq (s j : ℕ) (h : j ≤ 2 * s) :
    oddRoute s j = (j, j % 2) := by
  simp only [oddRoute, if_pos h]
private theorem odd_route_body_eq (s j : ℕ)
    (h : 2 * s + 3 < j) (h' : j < 4 * s + 4) :
    oddRoute s j = (j - (2 * s + 3), j % 2) := by
  simp (disch := omega) only [oddRoute, if_pos, if_neg, if_true, if_false]
private theorem odd_route_mid0_eq (s : ℕ) : oddRoute s (2 * s) = (2 * s, 0) := by
  rw [odd_route_front_eq s (2 * s) (by omega)]
  exact Prod.ext rfl (by omega)
private theorem odd_route_mid1_eq (s : ℕ) :
    oddRoute s (2 * s + 1) = (2 * s + 3, 0) := by
  simp (disch := omega) only [oddRoute, if_pos, if_neg, if_true, if_false]
private theorem odd_route_mid2_eq (s : ℕ) :
    oddRoute s (2 * s + 2) = (2 * s + 2, 1) := by
  simp (disch := omega) only [oddRoute, if_pos, if_neg, if_true, if_false]
private theorem odd_route_mid3_eq (s : ℕ) : oddRoute s (2 * s + 3) = (0, 1) := by
  simp (disch := omega) only [oddRoute, if_pos, if_neg, if_true, if_false]
private theorem odd_route_mid4_eq (s : ℕ) : oddRoute s (2 * s + 4) = (1, 0) := by
  by_cases hs : s = 0
  · subst s
    rfl
  · rw [odd_route_body_eq s (2 * s + 4) (by omega) (by omega)]
    apply Prod.ext <;> omega
private theorem odd_route_pretail_eq (s : ℕ) :
    oddRoute s (4 * s + 3) = (2 * s, 1) := by
  by_cases hs : s = 0
  · subst s
    rfl
  · rw [odd_route_body_eq s (4 * s + 3) (by omega) (by omega)]
    apply Prod.ext <;> omega
private theorem odd_route_last0_eq (s : ℕ) :
    oddRoute s (4 * s + 4) = (2 * s + 1, 0) := by
  simp (disch := omega) only [oddRoute, if_pos, if_neg, if_true, if_false]
private theorem odd_route_last1_eq (s : ℕ) :
    oddRoute s (4 * s + 5) = (2 * s + 2, 0) := by
  simp (disch := omega) only [oddRoute, if_pos, if_neg, if_true, if_false]
private theorem odd_route_last2_eq (s : ℕ) :
    oddRoute s (4 * s + 6) = (2 * s + 1, 1) := by
  simp (disch := omega) only [oddRoute, if_pos, if_neg, if_true, if_false]
private theorem odd_route_last3_eq (s : ℕ) :
    oddRoute s (4 * s + 7) = (2 * s + 3, 1) := by
  simp (disch := omega) only [oddRoute, if_pos, if_neg, if_true, if_false]
private theorem even_route_bound (s j : ℕ) (hj : j < 4 * s + 6) :
    (evenRoute s j).1 ≤ 2 * s + 2 ∧ (evenRoute s j).2 < 2 := by
  have hmod := Nat.mod_lt j (by decide : 0 < 2)
  unfold evenRoute
  split_ifs <;> dsimp <;> omega
private theorem even_inverse_bound (s : ℕ) (p : RawPort)
    (hi : p.1 ≤ 2 * s + 2) (hb : p.2 < 2) : evenInverse s p < 4 * s + 6 := by
  rcases p with ⟨i, b⟩
  dsimp only at hi hb
  have hmod := Nat.mod_lt i (by decide : 0 < 2)
  unfold evenInverse
  split_ifs <;> dsimp at * <;> omega
set_option maxHeartbeats 800000 in
private theorem odd_route_bound (s j : ℕ) (hj : j < 4 * s + 8) :
    (oddRoute s j).1 ≤ 2 * s + 3 ∧ (oddRoute s j).2 < 2 := by
  have hmod := Nat.mod_lt j (by decide : 0 < 2)
  unfold oddRoute
  split_ifs <;> dsimp <;> omega
private theorem odd_inverse_bound (s : ℕ) (p : RawPort)
    (hi : p.1 ≤ 2 * s + 3) (hb : p.2 < 2) : oddInverse s p < 4 * s + 8 := by
  rcases p with ⟨i, b⟩
  dsimp only at hi hb
  have hmod := Nat.mod_lt i (by decide : 0 < 2)
  unfold oddInverse
  split_ifs <;> dsimp at * <;> omega
set_option maxHeartbeats 800000 in
private theorem even_inverse_route (s j : ℕ) (hj : j < 4 * s + 6) :
    evenInverse s (evenRoute s j) = j := by
  have hmod := Nat.mod_lt j (by decide : 0 < 2)
  by_cases hf : j ≤ 2 * s
  · rw [even_route_front_eq s j hf]
    have hp : j % 2 = 0 ∨ j % 2 = 1 := by omega
    rcases hp with hp | hp <;>
      simp (disch := omega) only [evenInverse, Prod.fst, Prod.snd, if_pos, if_neg, if_true, if_false]
  · by_cases hm : j ≤ 2 * s + 3
    · have hc : j = 2 * s + 1 ∨ j = 2 * s + 2 ∨ j = 2 * s + 3 := by omega
      rcases hc with rfl | rfl | rfl
      · rw [even_route_mid1_eq]
        simp (disch := omega) only [evenInverse, Prod.fst, Prod.snd, if_pos, if_neg, if_true, if_false]
      · rw [even_route_mid2_eq]
        simp (disch := omega) only [evenInverse, Prod.fst, Prod.snd, if_pos, if_neg, if_true, if_false]
      · rw [even_route_mid3_eq]
        simp (disch := omega) only [evenInverse, Prod.fst, Prod.snd, if_pos, if_neg, if_true, if_false]
    · rw [even_route_tail_eq s j (by omega)]
      have hsum : j - (2 * s + 3) + (2 * s + 3) = j := by omega
      have hp : j % 2 = 0 ∨ j % 2 = 1 := by omega
      rcases hp with hp | hp <;>
        simp (disch := omega) only [evenInverse, Prod.fst, Prod.snd, if_pos, if_neg, if_true, if_false]
          <;> omega
private theorem even_route_inverse (s : ℕ) (p : RawPort)
    (hi : p.1 ≤ 2 * s + 2) (hb : p.2 < 2) :
    evenRoute s (evenInverse s p) = p := by
  rcases p with ⟨i, b⟩
  dsimp only at hi hb
  have hm := Nat.mod_lt i (by decide : 0 < 2)
  have hside : b = 0 ∨ b = 1 := by omega
  rcases hside with rfl | rfl
  · by_cases ht : i = 2 * s + 2
    · subst i
      simp (disch := omega) only [evenInverse, Prod.fst, Prod.snd, if_pos, if_neg, if_true, if_false,
        even_route_mid1_eq]
    · by_cases hp : i % 2 = 0
      · have hinv : evenInverse s (i, 0) = i := by
          simp (disch := omega) only [evenInverse, Prod.fst, Prod.snd, if_pos, if_neg, if_true, if_false]
        rw [hinv, even_route_front_eq s i (by omega)]
        exact Prod.ext rfl hp
      · have hinv : evenInverse s (i, 0) = i + 2 * s + 3 := by
          simp (disch := omega) only [evenInverse, Prod.fst, Prod.snd, if_pos, if_neg, if_true, if_false]
        rw [hinv, even_route_tail_eq s (i + 2 * s + 3) (by omega)]
        apply Prod.ext <;> omega
  · by_cases hz : i = 0
    · subst i
      simp (disch := omega) only [evenInverse, Prod.fst, Prod.snd, if_pos, if_neg, if_true, if_false,
        even_route_mid3_eq]
    · by_cases ht : i = 2 * s + 1
      · subst i
        simp (disch := omega) only [evenInverse, Prod.fst, Prod.snd, if_pos, if_neg, if_true, if_false,
          even_route_mid2_eq]
      · by_cases hp : i % 2 = 1
        · have hinv : evenInverse s (i, 1) = i := by
            simp (disch := omega) only [evenInverse, Prod.fst, Prod.snd, if_pos, if_neg, if_true, if_false]
          rw [hinv, even_route_front_eq s i (by omega)]
          exact Prod.ext rfl hp
        · have hinv : evenInverse s (i, 1) = i + 2 * s + 3 := by
            simp (disch := omega) only [evenInverse, Prod.fst, Prod.snd, if_pos, if_neg, if_true, if_false]
          rw [hinv, even_route_tail_eq s (i + 2 * s + 3) (by omega)]
          apply Prod.ext <;> omega
private theorem odd_inverse_route (s j : ℕ) (hj : j < 4 * s + 8) :
    oddInverse s (oddRoute s j) = j := by
  have hmod := Nat.mod_lt j (by decide : 0 < 2)
  by_cases hf : j ≤ 2 * s
  · rw [odd_route_front_eq s j hf]
    have hp : j % 2 = 0 ∨ j % 2 = 1 := by omega
    rcases hp with hp | hp <;>
      simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg, if_true, if_false]
  · by_cases hm : j ≤ 2 * s + 3
    · have hc : j = 2 * s + 1 ∨ j = 2 * s + 2 ∨ j = 2 * s + 3 := by omega
      rcases hc with rfl | rfl | rfl
      · rw [odd_route_mid1_eq]
        simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg, if_true, if_false]
      · rw [odd_route_mid2_eq]
        simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg, if_true, if_false]
      · rw [odd_route_mid3_eq]
        simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg, if_true, if_false]
    · by_cases hb : j < 4 * s + 4
      · rw [odd_route_body_eq s j (by omega) hb]
        have hsum : j - (2 * s + 3) + (2 * s + 3) = j := by omega
        have hp : j % 2 = 0 ∨ j % 2 = 1 := by omega
        rcases hp with hp | hp <;>
          simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg, if_true, if_false]
            <;> omega
      · have hc : j = 4 * s + 4 ∨ j = 4 * s + 5 ∨ j = 4 * s + 6 ∨
            j = 4 * s + 7 := by omega
        rcases hc with rfl | rfl | rfl | rfl
        · rw [odd_route_last0_eq]
          simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg, if_true, if_false]
        · rw [odd_route_last1_eq]
          simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg, if_true, if_false]
        · rw [odd_route_last2_eq]
          simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg, if_true, if_false]
        · rw [odd_route_last3_eq]
          simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg, if_true, if_false]
private theorem odd_route_inverse (s : ℕ) (p : RawPort)
    (hi : p.1 ≤ 2 * s + 3) (hb : p.2 < 2) :
    oddRoute s (oddInverse s p) = p := by
  rcases p with ⟨i, b⟩
  dsimp only at hi hb
  have hm := Nat.mod_lt i (by decide : 0 < 2)
  have hside : b = 0 ∨ b = 1 := by omega
  rcases hside with rfl | rfl
  · by_cases ht : i = 2 * s + 3
    · subst i
      simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg, if_true, if_false,
        odd_route_mid1_eq]
    · by_cases ht' : i = 2 * s + 2
      · subst i
        simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg, if_true, if_false,
          odd_route_last1_eq]
      · by_cases ht'' : i = 2 * s + 1
        · subst i
          simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg, if_true, if_false,
            odd_route_last0_eq]
        · by_cases hp : i % 2 = 0
          · have hinv : oddInverse s (i, 0) = i := by
              simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg, if_true, if_false]
            rw [hinv, odd_route_front_eq s i (by omega)]
            exact Prod.ext rfl hp
          · have hinv : oddInverse s (i, 0) = i + 2 * s + 3 := by
              simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg, if_true, if_false]
            rw [hinv, odd_route_body_eq s (i + 2 * s + 3) (by omega) (by omega)]
            apply Prod.ext <;> omega
  · by_cases hz : i = 0
    · subst i
      simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg, if_true, if_false,
        odd_route_mid3_eq]
    · by_cases ht : i = 2 * s + 3
      · subst i
        simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg, if_true, if_false,
          odd_route_last3_eq]
      · by_cases ht' : i = 2 * s + 2
        · subst i
          simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg, if_true, if_false,
            odd_route_mid2_eq]
        · by_cases ht'' : i = 2 * s + 1
          · subst i
            simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg, if_true, if_false,
              odd_route_last2_eq]
          · by_cases hp : i % 2 = 1
            · have hinv : oddInverse s (i, 1) = i := by
                simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg, if_true, if_false]
              rw [hinv, odd_route_front_eq s i (by omega)]
              exact Prod.ext rfl hp
            · have hinv : oddInverse s (i, 1) = i + 2 * s + 3 := by
                simp (disch := omega) only [oddInverse, Prod.fst, Prod.snd, if_pos, if_neg, if_true, if_false]
              rw [hinv, odd_route_body_eq s (i + 2 * s + 3) (by omega) (by omega)]
              apply Prod.ext <;> omega
private theorem seam_forward (k i : ℕ) (h : i < k) :
    internalSeam k (i, 1) (i + 1, 0) := Or.inl ⟨rfl, rfl, h, rfl⟩
private theorem seam_reverse (k i : ℕ) (h : i < k) :
    internalSeam k (i + 1, 0) (i, 1) := Or.inr ⟨rfl, rfl, h, rfl⟩
private theorem even_ladder_forward (k i : ℕ) (hk : 3 ≤ k) (hi : i ≤ k - 3) :
    evenBoundary k (i, 0) (i + 1, 1) :=
  Or.inl ⟨hk, Or.inl ⟨rfl, rfl, hi, rfl⟩⟩
private theorem odd_ladder_forward (k i : ℕ) (hk : 4 ≤ k) (hi : i ≤ k - 4) :
    oddBoundary k (i, 0) (i + 1, 1) :=
  Or.inl ⟨hk, Or.inl ⟨rfl, rfl, hi, rfl⟩⟩
private theorem even_route_boundary_step (s j : ℕ)
    (hj : j + 1 < 4 * s + 6) (hp : j % 2 = 0) :
    evenBoundary (2 * s + 2) (evenRoute s j) (evenRoute s (j + 1)) := by
  have hp' : (j + 1) % 2 = 1 := by omega
  by_cases hf : j < 2 * s
  · rw [even_route_front_eq s j (by omega),
      even_route_front_eq s (j + 1) (by omega), hp, hp']
    exact even_ladder_forward _ _ (by omega) (by omega)
  · by_cases hm : j ≤ 2 * s + 3
    · have hc : j = 2 * s ∨ j = 2 * s + 1 ∨ j = 2 * s + 2 ∨
          j = 2 * s + 3 := by omega
      rcases hc with rfl | rfl | rfl | rfl
      · rw [even_route_mid0_eq, even_route_mid1_eq]
        exact Or.inr (Or.inl (Or.inl ⟨Prod.ext (by omega) rfl, rfl⟩))
      · omega
      · rw [even_route_mid2_eq,
          show 2 * s + 2 + 1 = 2 * s + 3 by omega, even_route_mid3_eq]
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Prod.ext (by omega) rfl, rfl⟩)))
      · omega
    · by_cases hl : j = 4 * s + 4
      · subst j
        rw [even_route_last0_eq,
          show 4 * s + 4 + 1 = 4 * s + 5 by omega, even_route_last1_eq]
        exact Or.inr (Or.inr (Or.inl (Or.inl ⟨Prod.ext (by omega) rfl, rfl⟩)))
      · have hn : j + 1 - (2 * s + 3) = (j - (2 * s + 3)) + 1 := by omega
        rw [even_route_tail_eq s j (by omega),
          even_route_tail_eq s (j + 1) (by omega), hp, hp', hn]
        exact even_ladder_forward _ _ (by omega) (by omega)
private theorem even_route_seam_step (s j : ℕ)
    (hj : j + 1 < 4 * s + 6) (hp : j % 2 = 1) :
    internalSeam (2 * s + 2) (evenRoute s j) (evenRoute s (j + 1)) := by
  have hp' : (j + 1) % 2 = 0 := by omega
  by_cases hf : j < 2 * s
  · rw [even_route_front_eq s j (by omega),
      even_route_front_eq s (j + 1) (by omega), hp, hp']
    exact seam_forward _ _ (by omega)
  · by_cases hm : j ≤ 2 * s + 3
    · have hc : j = 2 * s ∨ j = 2 * s + 1 ∨ j = 2 * s + 2 ∨
          j = 2 * s + 3 := by omega
      rcases hc with rfl | rfl | rfl | rfl
      · omega
      · rw [even_route_mid1_eq,
          show 2 * s + 1 + 1 = 2 * s + 2 by omega, even_route_mid2_eq]
        exact seam_reverse _ _ (by omega)
      · omega
      · rw [even_route_mid3_eq,
          show 2 * s + 3 + 1 = 2 * s + 4 by omega, even_route_mid4_eq]
        exact seam_forward _ _ (by omega)
    · have hn : j + 1 - (2 * s + 3) = (j - (2 * s + 3)) + 1 := by omega
      rw [even_route_tail_eq s j (by omega),
        even_route_tail_eq s (j + 1) (by omega), hp, hp', hn]
      exact seam_forward _ _ (by omega)
private theorem even_route_steps (s j : ℕ) (hj : j + 1 < 4 * s + 6) :
    (j % 2 = 0 → evenBoundary (2 * s + 2) (evenRoute s j) (evenRoute s (j + 1))) ∧
      (j % 2 = 1 → internalSeam (2 * s + 2) (evenRoute s j) (evenRoute s (j + 1))) :=
  ⟨even_route_boundary_step s j hj, even_route_seam_step s j hj⟩
private theorem odd_route_boundary_step (s j : ℕ)
    (hj : j + 1 < 4 * s + 8) (hp : j % 2 = 0) :
    oddBoundary (2 * s + 3) (oddRoute s j) (oddRoute s (j + 1)) := by
  have hp' : (j + 1) % 2 = 1 := by omega
  by_cases hf : j < 2 * s
  · rw [odd_route_front_eq s j (by omega),
      odd_route_front_eq s (j + 1) (by omega), hp, hp']
    exact odd_ladder_forward _ _ (by omega) (by omega)
  · by_cases hm : j ≤ 2 * s + 3
    · have hc : j = 2 * s ∨ j = 2 * s + 1 ∨ j = 2 * s + 2 ∨
          j = 2 * s + 3 := by omega
      rcases hc with rfl | rfl | rfl | rfl
      · rw [odd_route_mid0_eq, odd_route_mid1_eq]
        exact Or.inr (Or.inr (Or.inl (Or.inl ⟨Prod.ext (by omega) rfl, rfl⟩)))
      · omega
      · rw [odd_route_mid2_eq,
          show 2 * s + 2 + 1 = 2 * s + 3 by omega, odd_route_mid3_eq]
        exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨Prod.ext (by omega) rfl, rfl⟩))))
      · omega
    · by_cases hb : j < 4 * s + 3
      · have hn : j + 1 - (2 * s + 3) = (j - (2 * s + 3)) + 1 := by omega
        rw [odd_route_body_eq s j (by omega) (by omega),
          odd_route_body_eq s (j + 1) (by omega) (by omega), hp, hp', hn]
        exact odd_ladder_forward _ _ (by omega) (by omega)
      · have hc : j = 4 * s + 3 ∨ j = 4 * s + 4 ∨ j = 4 * s + 5 ∨
            j = 4 * s + 6 := by omega
        rcases hc with rfl | rfl | rfl | rfl
        · omega
        · rw [odd_route_last0_eq,
            show 4 * s + 4 + 1 = 4 * s + 5 by omega, odd_route_last1_eq]
          exact Or.inr (Or.inl (Or.inl
            ⟨Prod.ext (by omega) rfl, Prod.ext (by omega) rfl⟩))
        · omega
        · rw [odd_route_last2_eq,
            show 4 * s + 6 + 1 = 4 * s + 7 by omega, odd_route_last3_eq]
          exact Or.inr (Or.inr (Or.inr
            (Or.inl (Or.inl ⟨Prod.ext (by omega) rfl, rfl⟩))))
private theorem odd_route_seam_step (s j : ℕ)
    (hj : j + 1 < 4 * s + 8) (hp : j % 2 = 1) :
    internalSeam (2 * s + 3) (oddRoute s j) (oddRoute s (j + 1)) := by
  have hp' : (j + 1) % 2 = 0 := by omega
  by_cases hf : j < 2 * s
  · rw [odd_route_front_eq s j (by omega),
      odd_route_front_eq s (j + 1) (by omega), hp, hp']
    exact seam_forward _ _ (by omega)
  · by_cases hm : j ≤ 2 * s + 3
    · have hc : j = 2 * s ∨ j = 2 * s + 1 ∨ j = 2 * s + 2 ∨
          j = 2 * s + 3 := by omega
      rcases hc with rfl | rfl | rfl | rfl
      · omega
      · rw [odd_route_mid1_eq,
          show 2 * s + 1 + 1 = 2 * s + 2 by omega, odd_route_mid2_eq]
        exact seam_reverse _ _ (by omega)
      · omega
      · rw [odd_route_mid3_eq,
          show 2 * s + 3 + 1 = 2 * s + 4 by omega, odd_route_mid4_eq]
        exact seam_forward _ _ (by omega)
    · by_cases hb : j < 4 * s + 3
      · have hn : j + 1 - (2 * s + 3) = (j - (2 * s + 3)) + 1 := by omega
        rw [odd_route_body_eq s j (by omega) (by omega),
          odd_route_body_eq s (j + 1) (by omega) (by omega), hp, hp', hn]
        exact seam_forward _ _ (by omega)
      · have hc : j = 4 * s + 3 ∨ j = 4 * s + 4 ∨ j = 4 * s + 5 ∨
            j = 4 * s + 6 := by omega
        rcases hc with rfl | rfl | rfl | rfl
        · rw [odd_route_pretail_eq,
            show 4 * s + 3 + 1 = 4 * s + 4 by omega, odd_route_last0_eq]
          exact seam_forward _ _ (by omega)
        · omega
        · rw [odd_route_last1_eq,
            show 4 * s + 5 + 1 = 4 * s + 6 by omega, odd_route_last2_eq]
          exact seam_reverse _ _ (by omega)
        · omega
private theorem odd_route_steps (s j : ℕ) (hj : j + 1 < 4 * s + 8) :
    (j % 2 = 0 → oddBoundary (2 * s + 3) (oddRoute s j) (oddRoute s (j + 1))) ∧
      (j % 2 = 1 → internalSeam (2 * s + 3) (oddRoute s j) (oddRoute s (j + 1))) :=
  ⟨odd_route_boundary_step s j hj, odd_route_seam_step s j hj⟩
def evenEnumerate (s : ℕ) (j : Fin (4 * s + 6)) : Port (2 * s + 2) :=
  (⟨(evenRoute s j.val).1, Nat.lt_succ_of_le (even_route_bound s j.val j.isLt).1⟩,
    ⟨(evenRoute s j.val).2, (even_route_bound s j.val j.isLt).2⟩)
def oddEnumerate (s : ℕ) (j : Fin (4 * s + 8)) : Port (2 * s + 3) :=
  (⟨(oddRoute s j.val).1, Nat.lt_succ_of_le (odd_route_bound s j.val j.isLt).1⟩,
    ⟨(oddRoute s j.val).2, (odd_route_bound s j.val j.isLt).2⟩)
private theorem even_enumerate_injective (s : ℕ) : Function.Injective (evenEnumerate s) := by
  intro i j he
  have h := congrArg (fun p => evenInverse s (code p)) he
  change evenInverse s (evenRoute s i.val) = evenInverse s (evenRoute s j.val) at h
  rw [even_inverse_route s i.val i.isLt, even_inverse_route s j.val j.isLt] at h
  exact Fin.ext h
private theorem odd_enumerate_injective (s : ℕ) : Function.Injective (oddEnumerate s) := by
  intro i j he
  have h := congrArg (fun p => oddInverse s (code p)) he
  change oddInverse s (oddRoute s i.val) = oddInverse s (oddRoute s j.val) at h
  rw [odd_inverse_route s i.val i.isLt, odd_inverse_route s j.val j.isLt] at h
  exact Fin.ext h
private theorem even_enumerate_surjective (s : ℕ) : Function.Surjective (evenEnumerate s) := by
  intro p
  let j : Fin (4 * s + 6) := ⟨evenInverse s (code p),
    even_inverse_bound s (code p) (by change p.1.val ≤ _; have h := p.1.isLt; omega) p.2.isLt⟩
  refine ⟨j, code_injective _ ?_⟩
  exact even_route_inverse s (code p) (by change p.1.val ≤ _; have h := p.1.isLt; omega) p.2.isLt
private theorem odd_enumerate_surjective (s : ℕ) : Function.Surjective (oddEnumerate s) := by
  intro p
  let j : Fin (4 * s + 8) := ⟨oddInverse s (code p),
    odd_inverse_bound s (code p) (by change p.1.val ≤ _; have h := p.1.isLt; omega) p.2.isLt⟩
  refine ⟨j, code_injective _ ?_⟩
  exact odd_route_inverse s (code p) (by change p.1.val ≤ _; have h := p.1.isLt; omega) p.2.isLt
set_option maxHeartbeats 800000 in
private theorem even_mate_unique (s : ℕ) (p q r : Port (2 * s + 2))
    (hq : evenBoundary (2 * s + 2) (code p) (code q))
    (hr : evenBoundary (2 * s + 2) (code p) (code r)) : q = r := by
  have hp₀ := p.1.isLt
  have hp₁ := p.2.isLt
  have hq₀ := q.1.isLt
  have hq₁ := q.2.isLt
  have hr₀ := r.1.isLt
  have hr₁ := r.2.isLt
  apply code_injective
  simp only [evenBoundary, ladder, pair, code, Prod.mk.injEq] at hq hr ⊢
  omega
set_option maxHeartbeats 800000 in
private theorem odd_mate_unique (s : ℕ) (p q r : Port (2 * s + 3))
    (hq : oddBoundary (2 * s + 3) (code p) (code q))
    (hr : oddBoundary (2 * s + 3) (code p) (code r)) : q = r := by
  have hp₀ := p.1.isLt
  have hp₁ := p.2.isLt
  have hq₀ := q.1.isLt
  have hq₁ := q.2.isLt
  have hr₀ := r.1.isLt
  have hr₁ := r.2.isLt
  apply code_injective
  simp only [oddBoundary, ladder, pair, code, Prod.mk.injEq] at hq hr ⊢
  omega
/-- The B pieces, in the exact order and orientation used by the port trace. -/
def evenBEdge (s : ℕ) (i : Fin (2 * s + 3)) : Sym2 (Port (2 * s + 2)) :=
  s(evenEnumerate s ⟨2 * i.val, by have h := i.isLt; omega⟩,
    evenEnumerate s ⟨2 * i.val + 1, by have h := i.isLt; omega⟩)
def oddBEdge (s : ℕ) (i : Fin (2 * s + 4)) : Sym2 (Port (2 * s + 3)) :=
  s(oddEnumerate s ⟨2 * i.val, by have h := i.isLt; omega⟩,
    oddEnumerate s ⟨2 * i.val + 1, by have h := i.isLt; omega⟩)
private theorem even_bedge_injective (s : ℕ) : Function.Injective (evenBEdge s) := by
  intro i j he
  rcases Sym2.eq_iff.mp he with ⟨h, _⟩ | ⟨h, _⟩
  all_goals
    have hv := congrArg Fin.val (even_enumerate_injective s h)
    simp only [Fin.val_mk] at hv
  · exact Fin.ext (by omega)
  · omega
private theorem odd_bedge_injective (s : ℕ) : Function.Injective (oddBEdge s) := by
  intro i j he
  rcases Sym2.eq_iff.mp he with ⟨h, _⟩ | ⟨h, _⟩
  all_goals
    have hv := congrArg Fin.val (odd_enumerate_injective s h)
    simp only [Fin.val_mk] at hv
  · exact Fin.ext (by omega)
  · omega
/-- Every independently specified E edge is traversed as exactly one B
piece, not merely every endpoint. This is the actual reordering bridge for
expanding previously earned, disjoint path components. -/
theorem even_boundary_edges_once (s : ℕ) (p q : Port (2 * s + 2))
    (hB : evenBoundary (2 * s + 2) (code p) (code q)) :
    ∃! i : Fin (2 * s + 3), s(p, q) = evenBEdge s i := by
  obtain ⟨j, rfl⟩ := even_enumerate_surjective s p
  let i : Fin (2 * s + 3) := ⟨j.val / 2, by have h := j.isLt; omega⟩
  have hi := i.isLt
  have hb : evenBoundary (2 * s + 2)
      (code (evenEnumerate s ⟨2 * i.val, by omega⟩))
      (code (evenEnumerate s ⟨2 * i.val + 1, by omega⟩)) :=
    (even_route_steps s (2 * i.val) (by omega)).1 (by omega)
  have hm := Nat.mod_lt j.val (by decide : 0 < 2)
  have he : s(evenEnumerate s j, q) = evenBEdge s i := by
    by_cases hpar : j.val % 2 = 0
    · have hj : (⟨2 * i.val, by omega⟩ : Fin (4 * s + 6)) = j := by
        apply Fin.ext
        dsimp [i]
        omega
      rw [hj] at hb
      have hq := even_mate_unique s _ _ _ hB hb
      rw [hq]
      simp only [evenBEdge, hj]
    · have hj : (⟨2 * i.val + 1, by omega⟩ : Fin (4 * s + 6)) = j := by
        apply Fin.ext
        dsimp [i]
        omega
      rw [hj] at hb
      have hq := even_mate_unique s _ _ _ hB
        (even_boundary_symm _ _ _ hb)
      rw [hq]
      simp only [evenBEdge, hj]
      exact Sym2.eq_swap
  refine ⟨i, he, ?_⟩
  intro r hr
  exact even_bedge_injective s (hr.symm.trans he)
/-- Every O edge likewise occurs as exactly one whole B piece, including
the k=3 tail, so no genuine previous component can be omitted or repeated. -/
theorem odd_boundary_edges_once (s : ℕ) (p q : Port (2 * s + 3))
    (hB : oddBoundary (2 * s + 3) (code p) (code q)) :
    ∃! i : Fin (2 * s + 4), s(p, q) = oddBEdge s i := by
  obtain ⟨j, rfl⟩ := odd_enumerate_surjective s p
  let i : Fin (2 * s + 4) := ⟨j.val / 2, by have h := j.isLt; omega⟩
  have hi := i.isLt
  have hb : oddBoundary (2 * s + 3)
      (code (oddEnumerate s ⟨2 * i.val, by omega⟩))
      (code (oddEnumerate s ⟨2 * i.val + 1, by omega⟩)) :=
    (odd_route_steps s (2 * i.val) (by omega)).1 (by omega)
  have hm := Nat.mod_lt j.val (by decide : 0 < 2)
  have he : s(oddEnumerate s j, q) = oddBEdge s i := by
    by_cases hpar : j.val % 2 = 0
    · have hj : (⟨2 * i.val, by omega⟩ : Fin (4 * s + 8)) = j := by
        apply Fin.ext
        dsimp [i]
        omega
      rw [hj] at hb
      have hq := odd_mate_unique s _ _ _ hB hb
      rw [hq]
      simp only [oddBEdge, hj]
    · have hj : (⟨2 * i.val + 1, by omega⟩ : Fin (4 * s + 8)) = j := by
        apply Fin.ext
        dsimp [i]
        omega
      rw [hj] at hb
      have hq := odd_mate_unique s _ _ _ hB (odd_boundary_symm _ _ _ hb)
      rw [hq]
      simp only [oddBEdge, hj]
      exact Sym2.eq_swap
  refine ⟨i, he, ?_⟩
  intro r hr
  exact odd_bedge_injective s (hr.symm.trans he)
def evenTrace (s : ℕ) : List (Port (2 * s + 2)) := List.ofFn (evenEnumerate s)
def oddTrace (s : ℕ) : List (Port (2 * s + 3)) := List.ofFn (oddEnumerate s)
private theorem even_trace_chain (s : ℕ) : (evenTrace s).IsChain (boundaryGraph (2 * s + 2)).Adj := by
  rw [evenTrace, List.isChain_ofFn]
  intro i hi
  refine ⟨?_, ?_⟩
  · intro he
    have h := congrArg Fin.val (even_enumerate_injective s he)
    simp only [Fin.val_mk] at h
    omega
  · change boundary _ (evenRoute s i) (evenRoute s (i + 1)) ∨ _
    have hpar : (2 * s + 2) % 2 = 0 := by omega
    rw [boundary, if_pos hpar]
    have hm := Nat.mod_lt i (by decide : 0 < 2)
    by_cases h : i % 2 = 0
    · exact Or.inl ((even_route_steps s i hi).1 h)
    · exact Or.inr ((even_route_steps s i hi).2 (by omega))
private theorem odd_trace_chain (s : ℕ) : (oddTrace s).IsChain (boundaryGraph (2 * s + 3)).Adj := by
  rw [oddTrace, List.isChain_ofFn]
  intro i hi
  refine ⟨?_, ?_⟩
  · intro he
    have h := congrArg Fin.val (odd_enumerate_injective s he)
    simp only [Fin.val_mk] at h
    omega
  · change boundary _ (oddRoute s i) (oddRoute s (i + 1)) ∨ _
    have hpar : ¬ (2 * s + 3) % 2 = 0 := by omega
    rw [boundary, if_neg hpar]
    have hm := Nat.mod_lt i (by decide : 0 < 2)
    by_cases h : i % 2 = 0
    · exact Or.inl ((odd_route_steps s i hi).1 h)
    · exact Or.inr ((odd_route_steps s i hi).2 (by omega))
private theorem even_trace_start (s : ℕ) (hne : evenTrace s ≠ []) :
    (evenTrace s).head hne = (0, 0) := by
  unfold evenTrace at hne ⊢
  apply code_injective
  change code ((List.ofFn (evenEnumerate s)).head hne) = _
  rw [List.head_ofFn]
  change evenRoute s 0 = (0, 0)
  simp only [evenRoute, Nat.zero_le, ↓reduceIte, Nat.zero_mod]
private theorem odd_trace_start (s : ℕ) (hne : oddTrace s ≠ []) :
    (oddTrace s).head hne = (0, 0) := by
  unfold oddTrace at hne ⊢
  apply code_injective
  change code ((List.ofFn (oddEnumerate s)).head hne) = _
  rw [List.head_ofFn]
  change oddRoute s 0 = (0, 0)
  simp only [oddRoute, Nat.zero_le, ↓reduceIte, Nat.zero_mod]
private theorem even_trace_finish (s : ℕ) (hne : evenTrace s ≠ []) :
    (evenTrace s).getLast hne = (Fin.last (2 * s + 2), 1) := by
  unfold evenTrace at hne ⊢
  apply code_injective
  change code ((List.ofFn (evenEnumerate s)).getLast hne) = _
  rw [List.getLast_ofFn]
  change evenRoute s (4 * s + 6 - 1) = (2 * s + 2, 1)
  rw [show 4 * s + 6 - 1 = 4 * s + 5 by omega]
  exact even_route_last1_eq s
private theorem odd_trace_finish (s : ℕ) (hne : oddTrace s ≠ []) :
    (oddTrace s).getLast hne = (Fin.last (2 * s + 3), 1) := by
  unfold oddTrace at hne ⊢
  apply code_injective
  change code ((List.ofFn (oddEnumerate s)).getLast hne) = _
  rw [List.getLast_ofFn]
  change oddRoute s (4 * s + 8 - 1) = (2 * s + 3, 1)
  rw [show 4 * s + 8 - 1 = 4 * s + 7 by omega]
  exact odd_route_last3_eq s
/-- Every even boundary plus the actual internal seam pattern is a Hamilton
path from R0 to Lk. The literal trace is retained for later piece expansion. -/
theorem even_boundary_hamiltonian_path (s : ℕ) :
    ∃ w : (boundaryGraph (2 * s + 2)).Walk (0, 0) (Fin.last (2 * s + 2), 1),
      w.IsHamiltonian ∧ w.support = evenTrace s := by
  have hne : evenTrace s ≠ [] := by
    intro he
    have h := congrArg List.length he
    simp only [evenTrace, List.length_ofFn, List.length_nil] at h
    omega
  let w := SimpleGraph.Walk.ofSupport (evenTrace s) hne (even_trace_chain s)
  have hs : (w.copy (even_trace_start s hne) (even_trace_finish s hne)).support =
      evenTrace s :=
    (SimpleGraph.Walk.support_copy w _ _).trans
      (SimpleGraph.Walk.support_ofSupport hne (even_trace_chain s))
  refine ⟨w.copy (even_trace_start s hne) (even_trace_finish s hne), ?_, hs⟩
  apply SimpleGraph.Walk.IsPath.isHamiltonian_of_mem
  · apply SimpleGraph.Walk.IsPath.mk'
    rw [hs]
    exact List.nodup_ofFn_ofInjective (even_enumerate_injective s)
  · intro p
    rw [hs]
    obtain ⟨j, rfl⟩ := even_enumerate_surjective s p
    exact List.mem_ofFn.mpr ⟨j, rfl⟩
/-- Every odd boundary at k≥3 has the same full-path conclusion, including
the four-port tail and the k=3 empty-ladder case. -/
theorem odd_boundary_hamiltonian_path (s : ℕ) :
    ∃ w : (boundaryGraph (2 * s + 3)).Walk (0, 0) (Fin.last (2 * s + 3), 1),
      w.IsHamiltonian ∧ w.support = oddTrace s := by
  have hne : oddTrace s ≠ [] := by
    intro he
    have h := congrArg List.length he
    simp only [oddTrace, List.length_ofFn, List.length_nil] at h
    omega
  let w := SimpleGraph.Walk.ofSupport (oddTrace s) hne (odd_trace_chain s)
  have hs : (w.copy (odd_trace_start s hne) (odd_trace_finish s hne)).support =
      oddTrace s :=
    (SimpleGraph.Walk.support_copy w _ _).trans
      (SimpleGraph.Walk.support_ofSupport hne (odd_trace_chain s))
  refine ⟨w.copy (odd_trace_start s hne) (odd_trace_finish s hne), ?_, hs⟩
  apply SimpleGraph.Walk.IsPath.isHamiltonian_of_mem
  · apply SimpleGraph.Walk.IsPath.mk'
    rw [hs]
    exact List.nodup_ofFn_ofInjective (odd_enumerate_injective s)
  · intro p
    rw [hs]
    obtain ⟨j, rfl⟩ := odd_enumerate_surjective s p
    exact List.mem_ofFn.mpr ⟨j, rfl⟩
/- Native consumers must earn disjoint full-domain pieces, their E/O endpoints and real c seams. -/
#print axioms even_boundary_hamiltonian_path
#print axioms odd_boundary_hamiltonian_path
#print axioms even_boundary_edges_once
#print axioms odd_boundary_edges_once
end D5.S3.Combinatorics.Graph.PrefixReversal.RecursivePortBoundary
