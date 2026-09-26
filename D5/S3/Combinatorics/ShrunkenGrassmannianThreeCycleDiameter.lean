/- GID: D5/S3/Combinatorics/ShrunkenGrassmannianThreeCycleDiameter
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ShrunkenGrassmannianThreeCycleDiameter
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Proves the k = 3 clause of Conjecture 16 of Chervov et al., arXiv:2603.22195v1: with inverse-closed consecutive 3-cycle generators, the Schreier coset graph of S_N / (S_L x S_{N-L}) on binary words with L zeros has central eccentricity and diameter both equal to ceil(L(N-L)/2). -/

/-
proof_shape: result: content
escape_witness: form (2), the public conclusion `result` itself: the lower bound comes from the
  inversion potential (`inv_rot`, `step_inv`, `reach_inv`, `inv_reversal`: a rotation of three
  consecutive entries changes the inversion count by at most 2, through the frozen `inv_window`), and
  the upper bound from an induction on the length (`upper`): moving the last occurrence of the
  target's final letter to the end costs ceil(rho/2) moves (`peel`), which fits the parity budget
  (`budget_true`, `budget_false`) except in two parity cases, where the source ends in the other
  letter and the peeling runs from the target instead (`reach_symm`)
admission_basis: open-problem-resolution (issue #10230)
Direct frozen dependencies: D5/S3/ConceptDynamics/Completion/CommutingCompletionExchange: `normalWord`
  (the central state); D5/S1/Digit/Carry/ListInversions: `inv` (statement_id
  sha256:746f5581415a1e255341cd9dd423347ba85b2d2e1a58842f35a43f09f4f536e8) and `inv_window`
  (statement_id sha256:67f2816574b1b59c3e8bb25aa83e6ef6fdc230a4ffd0db75c77e5b0842659c50)
-/

import D5.S1.Digit.Carry.ListInversions
import D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange
import Mathlib.Data.Bool.Count
import Mathlib.Order.Lattice.Nat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter

open D5.S1.Digit.Carry.ListInversions (inv inv_window)
open D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange (normalWord)

/-!
Chervov et al., *CayleyPy-4: AI-Holography. Towards analogs of holographic string dualities for AI
tasks*, arXiv:2603.22195v1, subsection "Schreier coset graph: `S_n / (S_l × S_{n-l})` (`k`-shrunken
Grassmannian `Gr(l, n, k)`)". The vertices are the binary vectors with exactly `l` zeros and `n - l`
ones; the generators are the consecutive `k`-cycles `(i, i + 1, …, i + k - 1)`, `0 ≤ i ≤ n - k`, and
in the inverse-closed case also their inverses; CayleyPy's `central_state` is `[0]^l + [1]^(n - l)`.
Conjecture 16, `k = 3` clause: for `L ≥ 2`, the diameter is `⌈L (N - L) / 2⌉`. A word is a
`List Bool` with `false` for `0` and `true` for `1`. Both readings of "diameter" are covered: the
largest distance from the central state (CayleyPy's growth computation) and the largest distance
between two vertices.
-/

/-- The consecutive cycle on the window of length `k` starting at position `i`, acting on a word:
the window `[a₁, a₂, …, a_k]` becomes `[a₂, …, a_k, a₁]`. -/
def rotL (k i : ℕ) (x : List Bool) : List Bool :=
  x.take i ++ ((x.drop i).take k).rotate 1 ++ x.drop (i + k)

/-- The inverse cycle on the same window: `[a₁, …, a_{k-1}, a_k]` becomes `[a_k, a₁, …, a_{k-1}]`. -/
def rotR (k i : ℕ) (x : List Bool) : List Bool :=
  x.take i ++ ((x.drop i).take k).rotate (k - 1) ++ x.drop (i + k)

/-- One edge of the inverse-closed Schreier coset graph: some window of `k` consecutive positions
lies inside the word and `y` is obtained from `x` by the cycle or its inverse on that window. -/
def Step (k : ℕ) (x y : List Bool) : Prop :=
  ∃ i, i + k ≤ x.length ∧ (y = rotL k i x ∨ y = rotR k i x)

/-- `Reach k m x y`: `y` is reached from `x` in at most `m` steps. -/
def Reach (k : ℕ) : ℕ → List Bool → List Bool → Prop
  | 0, x, y => y = x
  | m + 1, x, y => Reach k m x y ∨ ∃ z, Reach k m x z ∧ Step k z y

/-- A vertex of the coset graph: a word of length `N` with exactly `L` zeros. -/
def IsVertex (L N : ℕ) (x : List Bool) : Prop := x.length = N ∧ x.count false = L

/-- The largest distance from the central state `[0]^L + [1]^(N - L)`, which is
`normalWord L (N - L)`: the least `m` within which every vertex is reached from it. -/
noncomputable def ecc (k L N : ℕ) : ℕ :=
  sInf {m | ∀ y, IsVertex L N y → Reach k m (normalWord L (N - L)) y}

/-- The diameter: the least `m` within which every vertex is reached from every vertex. -/
noncomputable def diam (k L N : ℕ) : ℕ :=
  sInf {m | ∀ x y, IsVertex L N x → IsVertex L N y → Reach k m x y}

/-- Conjecture 16 of arXiv:2603.22195v1, `k = 3` clause, for `L ≥ 2` and `N > 3` (the generators
require `n > k`), under both readings of the diameter. -/
def claim : Prop :=
  ∀ L N : ℕ, 2 ≤ L → L ≤ N → 3 < N →
    ecc 3 L N = (L * (N - L) + 1) / 2 ∧ diam 3 L N = (L * (N - L) + 1) / 2

/-- The `k = 3` clause of Conjecture 16 holds. -/
theorem result : claim := by
  have rotL_mid : ∀ (u v : List Bool) (a b c : Bool), rotL 3 u.length (u ++ a :: b :: c :: v) = u ++ b :: c :: a :: v := by
    intro u v a b c
    simp only [rotL, List.take_left, List.drop_append,
      List.drop_eq_nil_of_le (show u.length ≤ u.length + 3 by omega), List.nil_append]
    simp [List.rotate]
  have rotR_mid : ∀ (u v : List Bool) (a b c : Bool), rotR 3 u.length (u ++ a :: b :: c :: v) = u ++ c :: a :: b :: v := by
    intro u v a b c
    simp only [rotR, List.take_left, List.drop_append,
      List.drop_eq_nil_of_le (show u.length ≤ u.length + 3 by omega), List.nil_append]
    simp [List.rotate]
  have step_iff : ∀ (x y : List Bool), Step 3 x y ↔ ∃ u v : List Bool, ∃ a b c : Bool, x = u ++ a :: b :: c :: v ∧ (y = u ++ b :: c :: a :: v ∨ y = u ++ c :: a :: b :: v) := by
    intro x y
    constructor
    · rintro ⟨i, hi, hy⟩
      obtain ⟨a, b, c, v, hv⟩ : ∃ a b c : Bool, ∃ v, x.drop i = a :: b :: c :: v := by
        match h : x.drop i with
        | a :: b :: c :: v => exact ⟨a, b, c, v, rfl⟩
        | [] => simp at h; omega
        | [_] => have := congrArg List.length h; simp at this; omega
        | [_, _] => have := congrArg List.length h; simp at this; omega
      obtain ⟨u, hu, hx⟩ : ∃ u : List Bool, u.length = i ∧ x = u ++ a :: b :: c :: v :=
        ⟨x.take i, by simp; omega, by rw [← hv, List.take_append_drop]⟩
      subst hu hx
      refine ⟨u, v, a, b, c, rfl, ?_⟩
      rcases hy with hy | hy
      · left; rw [hy, rotL_mid]
      · right; rw [hy, rotR_mid]
    · rintro ⟨u, v, a, b, c, hx, hy | hy⟩
      · exact ⟨u.length, by simp [hx], Or.inl (by rw [hy, hx, rotL_mid])⟩
      · exact ⟨u.length, by simp [hx], Or.inr (by rw [hy, hx, rotR_mid])⟩
  have reach_succ : ∀ {m : ℕ} {x y : List Bool} (h : Reach 3 m x y), Reach 3 (m + 1) x y := by
    intro m x y h
    exact Or.inl h
  have reach_mono : ∀ {m n : ℕ} {x y : List Bool} (h : Reach 3 m x y) (hmn : m ≤ n), Reach 3 n x y := by
    intro m n x y h hmn
    induction hmn with
    | refl => exact h
    | step _ ih => exact reach_succ ih
  have reach_refl : ∀ (m : ℕ) (x : List Bool), Reach 3 m x x := by
    intro m x
    exact reach_mono (show Reach 3 0 x x from rfl) (Nat.zero_le m)
  have reach_trans : ∀ {a : ℕ} {x y : List Bool} (hxy : Reach 3 a x y), ∀ (b : ℕ) (z : List Bool), Reach 3 b y z → Reach 3 (a + b) x z := by
    intro a x y hxy b
    induction b with
    | zero => intro z hz; rw [show z = y from hz]; exact hxy
    | succ b ih =>
      intro z hz
      rcases hz with hz | ⟨w, hw, hwz⟩
      · exact reach_succ (ih z hz)
      · exact Or.inr ⟨w, ih w hw, hwz⟩
  have reach_of_step : ∀ {x y : List Bool} (h : Step 3 x y), Reach 3 1 x y := by
    intro x y h
    exact Or.inr ⟨x, rfl, h⟩
  have step_symm : ∀ {x y : List Bool} (h : Step 3 x y), Step 3 y x := by
    intro x y h
    obtain ⟨u, v, a, b, c, hx, hy | hy⟩ := (step_iff x y).1 h
    · exact (step_iff y x).2 ⟨u, v, b, c, a, hy, Or.inr hx⟩
    · exact (step_iff y x).2 ⟨u, v, c, a, b, hy, Or.inl hx⟩
  have reach_symm : ∀ (m : ℕ) (x y : List Bool), Reach 3 m x y → Reach 3 m y x := by
    intro m
    induction m with
    | zero => intro x y h; exact (show y = x from h).symm
    | succ m ih =>
      intro x y h
      rcases h with h | ⟨z, hz, hzy⟩
      · exact reach_succ (ih x y h)
      · have := reach_trans (reach_of_step (step_symm hzy)) m x (ih x z hz)
        rwa [Nat.add_comm] at this
  have step_append : ∀ {x y : List Bool} (w : List Bool) (h : Step 3 x y), Step 3 (x ++ w) (y ++ w) := by
    intro x y w h
    obtain ⟨u, v, a, b, c, hx, hy | hy⟩ := (step_iff x y).1 h
    · exact (step_iff _ _).2 ⟨u, v ++ w, a, b, c, by simp [hx], Or.inl (by simp [hy])⟩
    · exact (step_iff _ _).2 ⟨u, v ++ w, a, b, c, by simp [hx], Or.inr (by simp [hy])⟩
  have reach_append : ∀ (w : List Bool), ∀ (m : ℕ) (x y : List Bool), Reach 3 m x y → Reach 3 m (x ++ w) (y ++ w) := by
    intro w m
    induction m with
    | zero => intro x y h; rw [show y = x from h]; rfl
    | succ m ih =>
      intro x y h
      rcases h with h | ⟨z, hz, hzy⟩
      · exact reach_succ (ih x y h)
      · exact Or.inr ⟨z ++ w, ih x z hz, step_append w hzy⟩
  have step_perm : ∀ {x y : List Bool} (h : Step 3 x y), y.Perm x := by
    intro x y h
    have p1 : ∀ a b c : Bool, ([b, c, a] : List Bool).Perm [a, b, c] := by decide
    have p2 : ∀ a b c : Bool, ([c, a, b] : List Bool).Perm [a, b, c] := by decide
    obtain ⟨u, v, a, b, c, hx, hy | hy⟩ := (step_iff x y).1 h
    · subst hx hy
      exact List.Perm.append_left u (by
        simpa using (List.Perm.append_right v (p1 a b c)))
    · subst hx hy
      exact List.Perm.append_left u (by
        simpa using (List.Perm.append_right v (p2 a b c)))
  have reach_perm : ∀ (m : ℕ) (x y : List Bool), Reach 3 m x y → y.Perm x := by
    intro m
    induction m with
    | zero => intro x y h; rw [show y = x from h]
    | succ m ih =>
      intro x y h
      rcases h with h | ⟨z, hz, hzy⟩
      · exact ih x y h
      · exact (step_perm hzy).trans (ih x z hz)
  have inv_rot : ∀ (P S : List ℕ) (p q r : ℕ) (hp : p ≤ 1) (hq : q ≤ 1) (hr : r ≤ 1), inv (P ++ [q, r, p] ++ S) ≤ inv (P ++ [p, q, r] ++ S) + 2 ∧ inv (P ++ [r, p, q] ++ S) ≤ inv (P ++ [p, q, r] ++ S) + 2 := by
    intro P S p q r hp hq hr
    rw [inv_window, inv_window, inv_window]
    rcases (show p = 0 ∨ p = 1 by omega) with rfl | rfl <;>
    rcases (show q = 0 ∨ q = 1 by omega) with rfl | rfl <;>
    rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl <;>
    simp [inv] <;> omega
  have step_inv : ∀ {x y : List Bool} (h : Step 3 x y), inv (y.map Bool.toNat) ≤ inv (x.map Bool.toNat) + 2 := by
    intro x y h
    obtain ⟨u, v, a, b, c, hx, hy | hy⟩ := (step_iff x y).1 h
    · subst hx hy
      have := (inv_rot (u.map Bool.toNat) (v.map Bool.toNat) a.toNat b.toNat c.toNat
        (Bool.toNat_le a) (Bool.toNat_le b) (Bool.toNat_le c)).1
      simpa using this
    · subst hx hy
      have := (inv_rot (u.map Bool.toNat) (v.map Bool.toNat) a.toNat b.toNat c.toNat
        (Bool.toNat_le a) (Bool.toNat_le b) (Bool.toNat_le c)).2
      simpa using this
  have reach_inv : ∀ (m : ℕ) (x y : List Bool), Reach 3 m x y → inv (y.map Bool.toNat) ≤ inv (x.map Bool.toNat) + 2 * m := by
    intro m
    induction m with
    | zero => intro x y h; rw [show y = x from h]; omega
    | succ m ih =>
      intro x y h
      rcases h with h | ⟨z, hz, hzy⟩
      · have := ih x y h; omega
      · have h1 := ih x z hz; have h2 := step_inv hzy; omega
  have inv_central : ∀ (L M : ℕ), inv ((List.replicate L false ++ List.replicate M true).map Bool.toNat) = 0 := by
    intro L M
    have h1 : ∀ M : ℕ, inv (List.replicate M 1) = 0 := by
      intro M; induction M with
      | zero => rfl
      | succ M ih => simp [List.replicate_succ, inv, ih, List.countP_replicate]
    induction L with
    | zero => simpa [List.map_replicate] using h1 M
    | succ L ih => simpa [List.replicate_succ, inv, List.map_replicate] using ih
  have inv_reversal : ∀ (L M : ℕ), inv ((List.replicate M true ++ List.replicate L false).map Bool.toNat) = M * L := by
    intro L M
    have h0 : ∀ L : ℕ, inv (List.replicate L 0) = 0 := by
      intro L; induction L with
      | zero => rfl
      | succ L ih => simp [List.replicate_succ, inv, ih, List.countP_replicate]
    induction M with
    | zero => simpa [List.map_replicate] using h0 L
    | succ M ih =>
      simp only [List.map_replicate, List.map_append] at ih ⊢
      rw [List.replicate_succ, List.cons_append, inv, ih]
      simp [List.countP_replicate, List.countP_append]
      exact (Nat.succ_mul M L).symm
  have last_decomp : ∀ (b : Bool), ∀ x : List Bool, b ∈ x → ∃ u ρ, x = u ++ b :: List.replicate ρ (!b) := by
    intro b x
    induction x using List.reverseRecOn with
    | nil => intro h; simp at h
    | append_singleton x a ih =>
      intro h
      by_cases hab : a = b
      · exact ⟨x, 0, by simp [hab]⟩
      · have ha : a = !b := by cases a <;> cases b <;> simp_all
        have hbx : b ∈ x := by
          rcases List.mem_append.1 h with h | h
          · exact h
          · simp at h; exact absurd h.symm hab
        obtain ⟨u, ρ, rfl⟩ := ih hbx
        exact ⟨u, ρ + 1, by simp [ha, List.replicate_succ']⟩
  have peel : ∀ (b : Bool), ∀ (ρ : ℕ) (u : List Bool), 2 ≤ u.length + ρ → ∃ z, Reach 3 ((ρ + 1) / 2) (u ++ b :: List.replicate ρ (!b)) (z ++ [b]) := by
    intro b ρ
    induction ρ using Nat.strong_induction_on with
    | _ ρ ih =>
      intro u hu
      match ρ, ih with
      | 0, _ => exact ⟨u, by simpa using reach_refl 0 (u ++ [b])⟩
      | 1, _ =>
        rcases List.eq_nil_or_concat u with rfl | ⟨u', a, rfl⟩
        · simp at hu
        · refine ⟨u' ++ [!b, a], reach_of_step ((step_iff _ _).2
            ⟨u', [], a, b, !b, by simp, Or.inr (by simp)⟩)⟩
      | ρ + 2, ih =>
        obtain ⟨z, hz⟩ := ih ρ (by omega) (u ++ [!b, !b]) (by simp; omega)
        have hs : Step 3 (u ++ b :: List.replicate (ρ + 2) (!b))
            ((u ++ [!b, !b]) ++ b :: List.replicate ρ (!b)) :=
          (step_iff _ _).2 ⟨u, List.replicate ρ (!b), b, !b, !b,
            by simp [List.replicate_succ], Or.inl (by simp)⟩
        have := reach_trans (reach_of_step hs) _ _ hz
        refine ⟨z, ?_⟩
        rw [show (ρ + 2 + 1) / 2 = 1 + (ρ + 1) / 2 by omega]
        exact this
  have budget_true : ∀ (L M ρ : ℕ) (hρ : ρ ≤ L) (hM : 1 ≤ M)
    (hbad : ¬(L % 2 = 1 ∧ M % 2 = 0 ∧ ρ = L)), (ρ + 1) / 2 + (L * (M - 1) + 1) / 2 ≤ (L * M + 1) / 2 := by
    intro L M ρ hρ hM hbad
    have hLP : L ≤ L * M := Nat.le_mul_of_pos_right L hM
    have hpar : (L * M) % 2 = (L % 2) * (M % 2) % 2 := Nat.mul_mod L M 2
    rw [Nat.mul_sub_one]
    generalize L * M = P at *
    rcases Nat.mod_two_eq_zero_or_one L with hL | hL <;>
    rcases Nat.mod_two_eq_zero_or_one M with hM2 | hM2 <;>
    simp [hL, hM2] at hpar <;> omega
  have budget_false : ∀ (L M ρ : ℕ) (hρ : ρ ≤ M) (hL : 1 ≤ L)
    (hbad : ¬(M % 2 = 1 ∧ L % 2 = 0 ∧ ρ = M)), (ρ + 1) / 2 + ((L - 1) * M + 1) / 2 ≤ (L * M + 1) / 2 := by
    intro L M ρ hρ hL hbad
    have hMP : M ≤ L * M := Nat.le_mul_of_pos_left M hL
    have hpar : (L * M) % 2 = (L % 2) * (M % 2) % 2 := Nat.mul_mod L M 2
    rw [Nat.sub_one_mul]
    generalize L * M = P at *
    rcases Nat.mod_two_eq_zero_or_one L with hL2 | hL2 <;>
    rcases Nat.mod_two_eq_zero_or_one M with hM2 | hM2 <;>
    simp [hL2, hM2] at hpar <;> omega
  have upper : ∀ N, 3 ≤ N → ∀ x y : List Bool, x.length = N → y.length = N → y.count false = x.count false → Reach 3 ((x.count false * (N - x.count false) + 1) / 2) x y := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      intro x y hx hy hc
      match x, y, hx, hy with
      | [a1, a2, a3], [b1, b2, b3], _, _ =>
        have key : ∀ a1 a2 a3 b1 b2 b3 : Bool,
            [b1, b2, b3].count false = [a1, a2, a3].count false →
            [b1, b2, b3] = [a1, a2, a3] ∨
              (([b1, b2, b3] = [a2, a3, a1] ∨ [b1, b2, b3] = [a3, a1, a2]) ∧
                1 ≤ ([a1, a2, a3].count false * (3 - [a1, a2, a3].count false) + 1) / 2) := by
          decide
        rcases key a1 a2 a3 b1 b2 b3 hc with h | ⟨h, hf⟩
        · rw [h]; exact reach_refl _ _
        · exact reach_mono (reach_of_step ((step_iff _ _).2
            ⟨[], [], a1, a2, a3, rfl, by simpa using h⟩)) hf
    | succ N hN ih =>
      have side : ∀ (x y' : List Bool) (b : Bool), x.length = N + 1 → y'.length = N →
          (y' ++ [b]).count false = x.count false →
          ∃ ρ, ρ ≤ x.count (!b) ∧ (ρ = 0 ∨ ∃ x', x = x' ++ [!b]) ∧
            Reach 3 ((ρ + 1) / 2 + (y'.count false * (N - y'.count false) + 1) / 2)
              x (y' ++ [b]) := by
        intro x y' b hx hy' hc
        have hbx : b ∈ x := by
          have h1 := List.count_true_add_count_false x
          have h3 : y'.count false ≤ y'.length := List.count_le_length
          rw [hx] at h1
          have hpos : 0 < x.count b := by
            cases b
            · simp at hc; omega
            · simp at hc; omega
          exact List.count_pos_iff.1 hpos
        obtain ⟨u, ρ, rfl⟩ := last_decomp b x hbx
        obtain ⟨z, hz⟩ := peel b ρ u (by simp at hx; omega)
        have hperm := reach_perm _ _ _ hz
        have hzlen : z.length = N := by
          have := hperm.length_eq; simp at this hx; omega
        have hzc : z.count false = y'.count false := by
          have h1 := hperm.count_eq false
          rw [← hc] at h1
          simp only [List.count_append] at h1
          omega
        have hsub := ih z y' hzlen hy' hzc.symm
        rw [hzc] at hsub
        refine ⟨ρ, ?_, ?_, reach_trans hz _ _ (reach_append [b] _ _ _ hsub)⟩
        · simp [List.count_append]
        · rcases ρ with _ | ρ
          · left; rfl
          · right
            exact ⟨u ++ b :: List.replicate ρ (!b), by simp [List.replicate_succ']⟩
      intro x y hx hy hc
      obtain ⟨y', b, rfl⟩ : ∃ y' b, y = y' ++ [b] := by
        rcases List.eq_nil_or_concat y with h | ⟨y', b, h⟩
        · subst h; simp at hy
        · exact ⟨y', b, by simpa using h⟩
      have hy' : y'.length = N := by simp at hy; omega
      have hcx := List.count_true_add_count_false x
      have hcy := List.count_true_add_count_false y'
      have hcyl : y'.count false ≤ N := hy' ▸ List.count_le_length
      rw [hx] at hcx
      rw [hy'] at hcy
      obtain ⟨ρ, hρ, hend, hr⟩ := side x y' b hx hy' hc
      cases b with
      | true =>
        have hL : y'.count false = x.count false := by simpa using hc
        by_cases hbad : x.count false % 2 = 1 ∧ (N + 1 - x.count false) % 2 = 0 ∧
            ρ = x.count false
        · obtain ⟨x', rfl⟩ : ∃ x', x = x' ++ [false] := by
            rcases hend with h0 | h
            · omega
            · simpa using h
          have hx' : x'.length = N := by simp at hx; omega
          have hK : (x' ++ [false]).count false = x'.count false + 1 := by simp
          obtain ⟨ρ', hρ', -, hr'⟩ := side (y' ++ [true]) x' false (by simp; omega) hx' hc.symm
          have hyt : (y' ++ [true]).count true = N - x'.count false := by
            have := List.count_true_add_count_false (y' ++ [true])
            simp only [List.length_append, hy', List.length_singleton] at this
            have e : (y' ++ [true]).count false = x'.count false + 1 := by rw [hc, hK]
            omega
          have hb := budget_false (x'.count false + 1) (N - x'.count false) ρ'
            (by simpa [hyt] using hρ') (by omega) (by rw [hK] at hbad; omega)
          refine reach_symm _ _ _ (reach_mono hr' ?_)
          rw [hK, show N + 1 - (x'.count false + 1) = N - x'.count false by omega]
          simpa using hb
        · have hb := budget_true (x.count false) (N + 1 - x.count false) ρ
            (by simpa using hρ) (by omega) hbad
          refine reach_mono hr ?_
          rw [hL, show N - x.count false = N + 1 - x.count false - 1 by omega]
          exact hb
      | false =>
        have hL : y'.count false + 1 = x.count false := by simpa using hc
        by_cases hbad : (N + 1 - x.count false) % 2 = 1 ∧ x.count false % 2 = 0 ∧
            ρ = N + 1 - x.count false
        · obtain ⟨x', rfl⟩ : ∃ x', x = x' ++ [true] := by
            rcases hend with h0 | h
            · omega
            · simpa using h
          have hx' : x'.length = N := by simp at hx; omega
          have hK : (x' ++ [true]).count false = x'.count false := by simp
          obtain ⟨ρ', hρ', -, hr'⟩ := side (y' ++ [false]) x' true (by simp; omega) hx' hc.symm
          have hyf : (y' ++ [false]).count false = x'.count false := by rw [hc, hK]
          have hb := budget_true (x'.count false) (N + 1 - x'.count false) ρ'
            (by simpa [hyf] using hρ') (by rw [hK] at hbad; omega) (by rw [hK] at hbad; omega)
          refine reach_symm _ _ _ (reach_mono hr' ?_)
          rw [hK, show N - x'.count false = N + 1 - x'.count false - 1 by omega]
          exact hb
        · have hb := budget_false (x.count false) (N + 1 - x.count false) ρ
            (by simp at hρ; omega) (by omega) hbad
          refine reach_mono hr ?_
          rw [show y'.count false = x.count false - 1 by omega,
            show N - (x.count false - 1) = N + 1 - x.count false by omega]
          exact hb

  intro L N hL hLN hN
  have hc : IsVertex L N (normalWord L (N - L)) :=
    ⟨by simp [normalWord]; omega, by simp [normalWord, List.count_replicate]⟩
  have hr : IsVertex L N (List.replicate (N - L) true ++ List.replicate L false) :=
    ⟨by simp; omega, by simp [List.count_replicate]⟩
  have hup : ∀ x y, IsVertex L N x → IsVertex L N y →
      Reach 3 ((L * (N - L) + 1) / 2) x y := by
    intro x y hx hy
    have := upper N (by omega) x y hx.1 hy.1 (by rw [hx.2, hy.2])
    rwa [hx.2] at this
  have hlow : ∀ m, Reach 3 m (normalWord L (N - L))
      (List.replicate (N - L) true ++ List.replicate L false) → (L * (N - L) + 1) / 2 ≤ m := by
    intro m h
    have := reach_inv m _ _ h
    rw [inv_reversal, normalWord, inv_central, Nat.mul_comm] at this
    generalize L * (N - L) = P at *
    omega
  constructor
  · apply le_antisymm
    · exact Nat.sInf_le (fun y hy => hup _ _ hc hy)
    · exact le_csInf ⟨_, fun y hy => hup _ _ hc hy⟩ (fun m hm => hlow m (hm _ hr))
  · apply le_antisymm
    · exact Nat.sInf_le (fun x y hx hy => hup x y hx hy)
    · exact le_csInf ⟨_, fun x y hx hy => hup x y hx hy⟩ (fun m hm => hlow m (hm _ _ hc hr))

end D5.S3.Combinatorics.ShrunkenGrassmannianThreeCycleDiameter
