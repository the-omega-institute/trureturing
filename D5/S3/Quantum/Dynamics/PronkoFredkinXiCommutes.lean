/- GID: D5/S3/Quantum/Dynamics/PronkoFredkinXiCommutes
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/PronkoFredkinXiCommutes
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Pronko's Dyck-class operator Xi commutes with the periodic Fredkin Hamiltonian. -/

/-
proof_shape: result: content
escape_witness: form (2) — depth-parity invariance of balanced words under every periodic
  Fredkin exchange (the local `move_up` / `move_down` inside `result`) on the live path
admission_basis: escape-witness; open-problem-resolution requested (issue #9996)
Direct frozen dependencies: D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation
  (nUp, nDown, tensor, site, P, Pi, F, H)
-/

import D5.S3.Quantum.Dynamics.PronkoFredkinNonCyclicAnnihilation

open scoped BigOperators Matrix
open D5.S3.Quantum.Dynamics.PronkoFredkinNonCyclicAnnihilation
open D5.S3.Quantum.FiniteDimensional

namespace D5.S3.Quantum.Dynamics.PronkoFredkinXiCommutes

/-- The height after the first `i` letters of the word `ℓ`, with `↑ = 0` a step up
and `↓ = 1` a step down. -/
def pathHeight {N : ℕ} (ℓ : Fin N → Fin 2) (i : ℕ) : ℤ :=
  ∑ t ∈ Finset.univ.filter (fun t : Fin N => t.val < i), if ℓ t = 0 then 1 else -1

/-- `ℓ ∈ C_{a,b}(N)`: the path of `ℓ` started at height `a` stays at height `≥ 0`,
touches height `0`, and ends at height `b` (section 2.2). -/
def inClass (N a b : ℕ) (ℓ : Fin N → Fin 2) : Prop :=
  (∀ i ≤ N, 0 ≤ (a : ℤ) + pathHeight ℓ i) ∧ (∃ i ≤ N, (a : ℤ) + pathHeight ℓ i = 0) ∧
    (a : ℤ) + pathHeight ℓ N = b

open Classical in
/-- (4.1): `Ξ = Σ_{k=0}^{N/2} (-1)^k Σ_{ℓ ∈ C_{k,k}(N)} n_1^{ℓ_1} ⋯ n_N^{ℓ_N}`. -/
noncomputable def Xi (N : ℕ) : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  ∑ k ∈ Finset.range (N / 2 + 1), (-1 : ℂ) ^ k •
    ∑ ℓ ∈ Finset.univ.filter (inClass N k k),
      tensor N fun i => if ℓ i = 0 then nUp else nDown

/-- The relation `[Ξ, H] = 0` of section 4.1 (printed page 10), for every even `N ≥ 3`. -/
def claim : Prop := ∀ N : ℕ, 3 ≤ N → Even N → Xi N * H N = H N * Xi N

/-- One step of the path. -/
private def stepVal (l : Fin 2) : ℤ := if l = 0 then 1 else -1

/-- `D(ℓ) = max_{0 ≤ i ≤ N} (-height_i)`: the starting height of the class of `ℓ`. -/
private def depth {N : ℕ} (ℓ : Fin N → Fin 2) : ℤ :=
  (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one fun i => -pathHeight ℓ i

open Classical in
/-- The diagonal value of `Ξ` at a word. -/
private noncomputable def xiVal (N : ℕ) (w : Fin N → Fin 2) : ℂ :=
  ∑ k ∈ Finset.range (N / 2 + 1), if inClass N k k w then (-1 : ℂ) ^ k else 0

set_option maxHeartbeats 1000000 in
/-- `[Ξ, H] = 0` holds for every even `N ≥ 3`. The proof uses only `N ≥ 3`: the relation
holds for every `N ≥ 3`, even or odd. -/
theorem result : claim := by
  have pathHeight_eq {N : ℕ} (ℓ : Fin N → Fin 2) (i : ℕ) :
      pathHeight ℓ i = ∑ t ∈ Finset.univ.filter (fun t : Fin N => t.val < i), stepVal (ℓ t) :=
    rfl
  have pathHeight_zero {N : ℕ} (ℓ : Fin N → Fin 2) : pathHeight ℓ 0 = 0 := by
    simp [pathHeight]
  have pathHeight_succ {N : ℕ} (ℓ : Fin N → Fin 2) (i : ℕ) (hi : i < N) :
      pathHeight ℓ (i + 1) = pathHeight ℓ i + stepVal (ℓ ⟨i, hi⟩) := by
    rw [pathHeight_eq, pathHeight_eq]
    have hset : Finset.univ.filter (fun t : Fin N => t.val < i + 1) =
        insert ⟨i, hi⟩ (Finset.univ.filter (fun t : Fin N => t.val < i)) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      omega
    rw [hset, Finset.sum_insert (by simp), add_comm]
  have stepVal_bound (l : Fin 2) : stepVal l = 1 ∨ stepVal l = -1 := by
    unfold stepVal
    split_ifs <;> simp
  have neg_height_le_depth {N : ℕ} (ℓ : Fin N → Fin 2) {i : ℕ} (hi : i ≤ N) :
      -pathHeight ℓ i ≤ depth ℓ :=
    Finset.le_sup' (fun i => -pathHeight ℓ i) (Finset.mem_range.2 (by omega))
  have depth_le_iff {N : ℕ} (ℓ : Fin N → Fin 2) (c : ℤ) :
      depth ℓ ≤ c ↔ ∀ i ≤ N, -pathHeight ℓ i ≤ c := by
    unfold depth
    rw [Finset.sup'_le_iff]
    simp only [Finset.mem_range]
    constructor
    · intro h i hi
      exact h i (by omega)
    · intro h i hi
      exact h i (by omega)
  have depth_attained {N : ℕ} (ℓ : Fin N → Fin 2) :
      ∃ i ≤ N, depth ℓ = -pathHeight ℓ i := by
    obtain ⟨i, hi, h⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
      (fun i => -pathHeight ℓ i)
    exact ⟨i, by simpa [Nat.lt_succ_iff] using hi, h⟩
  have depth_nonneg {N : ℕ} (ℓ : Fin N → Fin 2) : 0 ≤ depth ℓ := by
    have := neg_height_le_depth ℓ (Nat.zero_le N)
    rwa [pathHeight_zero, neg_zero] at this
  have inClass_diag_iff {N : ℕ} (a : ℕ) (ℓ : Fin N → Fin 2) :
      inClass N a a ℓ ↔ pathHeight ℓ N = 0 ∧ (a : ℤ) = depth ℓ := by
    constructor
    · rintro ⟨hge, ⟨i, hi, hz⟩, hend⟩
      refine ⟨by linarith, le_antisymm ?_ ?_⟩
      · have := neg_height_le_depth ℓ hi
        linarith
      · rw [depth_le_iff]
        intro i hi
        have := hge i hi
        linarith
    · rintro ⟨hend, ha⟩
      refine ⟨fun i hi => ?_, ?_, by rw [hend]; ring⟩
      · have := neg_height_le_depth ℓ hi
        linarith
      · obtain ⟨i, hi, h⟩ := depth_attained ℓ
        exact ⟨i, hi, by linarith⟩
  have height_step_bound {N : ℕ} (ℓ : Fin N → Fin 2) {i j : ℕ} (hij : i ≤ j)
      (hj : j ≤ N) : |pathHeight ℓ j - pathHeight ℓ i| ≤ (j - i : ℕ) := by
    induction j, hij using Nat.le_induction with
    | base => simp
    | succ j hij ih =>
      have hjN : j < N := by omega
      rw [pathHeight_succ ℓ j hjN]
      have h1 := ih (by omega)
      rcases stepVal_bound (ℓ ⟨j, hjN⟩) with h | h <;> rw [h] <;>
        rw [show (j + 1 - i : ℕ) = (j - i : ℕ) + 1 by omega] <;> push_cast <;>
        rw [abs_le] at h1 ⊢ <;> constructor <;> linarith [h1.1, h1.2]
  have two_depth_le {N : ℕ} (ℓ : Fin N → Fin 2) (h0 : pathHeight ℓ N = 0) :
      2 * depth ℓ ≤ N := by
    obtain ⟨i, hi, hd⟩ := depth_attained ℓ
    have h1 := height_step_bound ℓ (Nat.zero_le i) hi
    have h2 := height_step_bound ℓ hi le_rfl
    rw [pathHeight_zero, sub_zero, abs_le] at h1
    rw [h0, zero_sub, abs_le] at h2
    push_cast [Nat.sub_zero, Nat.cast_sub hi] at h1 h2
    linarith [h1.1, h2.1]
  have height_diff_const {N : ℕ} (x y : Fin N → Fin 2) {i j : ℕ} (hij : i ≤ j)
      (hj : j ≤ N) (hagree : ∀ t : Fin N, i ≤ t.val → t.val < j → y t = x t) :
      pathHeight y j - pathHeight x j = pathHeight y i - pathHeight x i := by
    induction j, hij using Nat.le_induction with
    | base => rfl
    | succ j hij ih =>
      have hjN : j < N := by omega
      rw [pathHeight_succ y j hjN, pathHeight_succ x j hjN,
        hagree ⟨j, hjN⟩ hij (by simp)]
      have := ih (by omega) (fun t h1 h2 => hagree t h1 (by omega))
      linarith
  have depth_eq_of_local {N : ℕ} (x y : Fin N → Fin 2) (p q : ℕ) (hq : q ≤ N)
      (hqp : q ≠ p) (hsame : ∀ i ≤ N, i ≠ p → pathHeight y i = pathHeight x i)
      (hx : pathHeight x q ≤ pathHeight x p) (hy : pathHeight y q ≤ pathHeight y p) :
      depth y = depth x := by
    have hyq := hsame q hq hqp
    apply le_antisymm
    · rw [depth_le_iff]
      intro i hi
      by_cases hip : i = p
      · subst hip
        have := neg_height_le_depth x hq
        linarith
      · rw [hsame i hi hip]
        exact neg_height_le_depth x hi
    · rw [depth_le_iff]
      intro i hi
      by_cases hip : i = p
      · subst hip
        have := neg_height_le_depth y hq
        linarith
      · rw [← hsame i hi hip]
        exact neg_height_le_depth y hi
  have depth_eq_of_shift {N : ℕ} (x y : Fin N → Fin 2) (δ : ℤ) (q : ℕ)
      (hq0 : 0 < q) (hqN : q < N) (hxN : pathHeight x N = 0) (hyN : pathHeight y N = 0)
      (hshift : ∀ i, 0 < i → i < N → pathHeight y i = pathHeight x i + δ)
      (hx : pathHeight x q ≤ 0) (hy : pathHeight y q ≤ 0) :
      depth y = depth x - δ := by
    have hyq := hshift q hq0 hqN
    have hxq := neg_height_le_depth x hqN.le
    have hyq' := neg_height_le_depth y hqN.le
    apply le_antisymm
    · rw [depth_le_iff]
      intro i hi
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · subst h0
        rw [pathHeight_zero]
        linarith
      · rcases lt_or_eq_of_le hi with hlt | heq
        · rw [hshift i hpos hlt]
          have := neg_height_le_depth x hi
          linarith
        · subst heq
          linarith
    · have : depth x ≤ depth y + δ := by
        rw [depth_le_iff]
        intro i hi
        rcases Nat.eq_zero_or_pos i with h0 | hpos
        · subst h0
          rw [pathHeight_zero]
          linarith
        · rcases lt_or_eq_of_le hi with hlt | heq
          · have := hshift i hpos hlt
            have := neg_height_le_depth y hi
            linarith
          · subst heq
            linarith
      linarith
  have height_swap_adjacent {N : ℕ} (x : Fin N → Fin 2) (p : ℕ) (hp : p + 1 < N) :
      ∀ i ≤ N, i ≠ p + 1 →
        pathHeight (fun t => x (Equiv.swap (⟨p, by omega⟩ : Fin N) ⟨p + 1, hp⟩ t)) i =
          pathHeight x i := by
    set y : Fin N → Fin 2 := fun t => x (Equiv.swap (⟨p, by omega⟩ : Fin N) ⟨p + 1, hp⟩ t)
    have hfix : ∀ t : Fin N, t.val ≠ p → t.val ≠ p + 1 → y t = x t := by
      intro t h1 h2
      simp only [y]
      rw [Equiv.swap_apply_of_ne_of_ne (fun h => h1 (by rw [h])) (fun h => h2 (by rw [h]))]
    have hlow : ∀ i ≤ p, pathHeight y i = pathHeight x i := by
      intro i hi
      have := height_diff_const x y (Nat.zero_le i) (by omega)
        (fun t _ ht => hfix t (by omega) (by omega))
      rw [pathHeight_zero, pathHeight_zero] at this
      linarith
    have hmid : pathHeight y (p + 2) = pathHeight x (p + 2) := by
      rw [show p + 2 = p + 1 + 1 by ring, pathHeight_succ y (p + 1) hp,
        pathHeight_succ x (p + 1) hp, pathHeight_succ y p (by omega),
        pathHeight_succ x p (by omega), hlow p le_rfl]
      simp only [y]
      rw [Equiv.swap_apply_left, Equiv.swap_apply_right]
      ring
    intro i hi hne
    rcases Nat.lt_or_ge i (p + 1) with h | h
    · exact hlow i (by omega)
    · have hge : p + 2 ≤ i := by omega
      have := height_diff_const x y hge hi (fun t h1 _ => hfix t (by omega) (by omega))
      linarith
  have height_swap_ends {N : ℕ} (x : Fin N → Fin 2) (hN : 2 ≤ N) :
      (∀ i, 0 < i → i < N →
        pathHeight (fun t => x (Equiv.swap (⟨N - 1, by omega⟩ : Fin N) ⟨0, by omega⟩ t)) i =
          pathHeight x i + (stepVal (x ⟨N - 1, by omega⟩) - stepVal (x ⟨0, by omega⟩))) ∧
      pathHeight (fun t => x (Equiv.swap (⟨N - 1, by omega⟩ : Fin N) ⟨0, by omega⟩ t)) N =
        pathHeight x N := by
    set y : Fin N → Fin 2 := fun t => x (Equiv.swap (⟨N - 1, by omega⟩ : Fin N) ⟨0, by omega⟩ t)
    have hfix : ∀ t : Fin N, t.val ≠ N - 1 → t.val ≠ 0 → y t = x t := by
      intro t h1 h2
      simp only [y]
      rw [Equiv.swap_apply_of_ne_of_ne (fun h => h1 (by rw [h])) (fun h => h2 (by rw [h]))]
    have hone : pathHeight y 1 = pathHeight x 1 +
        (stepVal (x ⟨N - 1, by omega⟩) - stepVal (x ⟨0, by omega⟩)) := by
      have hy0 : y ⟨0, by omega⟩ = x ⟨N - 1, by omega⟩ := by
        simp only [y]
        rw [Equiv.swap_apply_right]
      have hy1 := pathHeight_succ y 0 (by omega)
      have hx1 := pathHeight_succ x 0 (by omega)
      rw [pathHeight_zero] at hy1 hx1
      simp only [zero_add] at hy1 hx1
      rw [hy1, hx1, hy0]
      ring
    have hinner : ∀ i, 0 < i → i < N → pathHeight y i = pathHeight x i +
        (stepVal (x ⟨N - 1, by omega⟩) - stepVal (x ⟨0, by omega⟩)) := by
      intro i hi0 hiN
      have := height_diff_const x y (show 1 ≤ i by omega) hiN.le
        (fun t h1 h2 => hfix t (by omega) (by omega))
      linarith
    refine ⟨hinner, ?_⟩
    have hlast := hinner (N - 1) (by omega) (by omega)
    have hN1 : N - 1 + 1 = N := by omega
    have hyN : pathHeight y N = pathHeight y (N - 1) + stepVal (y ⟨N - 1, by omega⟩) := by
      have := pathHeight_succ y (N - 1) (by omega)
      rwa [hN1] at this
    have hxN : pathHeight x N = pathHeight x (N - 1) + stepVal (x ⟨N - 1, by omega⟩) := by
      have := pathHeight_succ x (N - 1) (by omega)
      rwa [hN1] at this
    have hyl : y ⟨N - 1, by omega⟩ = x ⟨0, by omega⟩ := by
      simp only [y]
      rw [Equiv.swap_apply_left]
    rw [hyN, hxN, hlast, hyl]
    ring
  have neg_one_pow_depth_eq {N : ℕ} {x y : Fin N → Fin 2} (m : ℤ)
      (h : depth y = depth x + 2 * m) :
      (-1 : ℂ) ^ (depth y).toNat = (-1 : ℂ) ^ (depth x).toNat := by
    have hx := depth_nonneg x
    have hy := depth_nonneg y
    rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := (depth x).toNat)]
    congr 1
    omega
  have xiVal_eq (N : ℕ) (w : Fin N → Fin 2) :
      xiVal N w = if pathHeight w N = 0 then (-1 : ℂ) ^ (depth w).toNat else 0 := by
    unfold xiVal
    simp_rw [inClass_diag_iff]
    by_cases h0 : pathHeight w N = 0
    · rw [if_pos h0]
      have hd := depth_nonneg w
      have h2 := two_depth_le w h0
      have hiff : ∀ k : ℕ, (pathHeight w N = 0 ∧ (k : ℤ) = depth w) ↔ k = (depth w).toNat := by
        intro k
        constructor
        · rintro ⟨_, hk⟩
          omega
        · intro hk
          exact ⟨h0, by omega⟩
      simp_rw [hiff]
      rw [Finset.sum_ite_eq']
      rw [if_pos (Finset.mem_range.2 (by omega))]
    · rw [if_neg h0]
      exact Finset.sum_eq_zero fun k _ => by rw [if_neg (fun h => h0 h.1)]
  have xiVal_congr {N : ℕ} (x y : Fin N → Fin 2)
      (htot : pathHeight y N = pathHeight x N)
      (hpar : pathHeight x N = 0 → ∃ m : ℤ, depth y = depth x + 2 * m) :
      xiVal N y = xiVal N x := by
    rw [xiVal_eq, xiVal_eq, htot]
    by_cases h0 : pathHeight x N = 0
    · obtain ⟨m, hm⟩ := hpar h0
      rw [if_pos h0, if_pos h0, neg_one_pow_depth_eq m hm]
    · rw [if_neg h0, if_neg h0]
  have stepVal_ge (l : Fin 2) : -1 ≤ stepVal l := by
    unfold stepVal
    split_ifs <;> norm_num
  have stepVal_le (l : Fin 2) : stepVal l ≤ 1 := by
    unfold stepVal
    split_ifs <;> norm_num
  have stepVal_zero : stepVal 0 = 1 := by simp [stepVal]
  have stepVal_one : stepVal 1 = -1 := by simp [stepVal]
  have fin_ne {N a b : ℕ} (ha : a < N) (hb : b < N) (h : a ≠ b) :
      (⟨a, ha⟩ : Fin N) ≠ ⟨b, hb⟩ :=
    fun e => h (congrArg Fin.val e)
  have height_add_two {N : ℕ} (w : Fin N → Fin 2) (i : ℕ) (hi : i + 1 < N) :
      pathHeight w (i + 1 + 1) =
        pathHeight w i + stepVal (w ⟨i, by omega⟩) + stepVal (w ⟨i + 1, hi⟩) := by
    rw [pathHeight_succ w (i + 1) hi, pathHeight_succ w i (by omega)]
  have height_last {N : ℕ} (w : Fin N → Fin 2) (hN : 1 ≤ N) :
      pathHeight w N = pathHeight w (N - 1) + stepVal (w ⟨N - 1, by omega⟩) := by
    have h := pathHeight_succ w (N - 1) (by omega)
    rwa [show N - 1 + 1 = N by omega] at h
  have height_one {N : ℕ} (w : Fin N → Fin 2) (hN : 1 ≤ N) :
      pathHeight w 1 = stepVal (w ⟨0, by omega⟩) := by
    have h := pathHeight_succ w 0 (by omega)
    rw [pathHeight_zero] at h
    simpa only [zero_add] using h
  have finRotate_val {N : ℕ} (j : Fin N) :
      (finRotate N j).val = if j.val + 1 = N then 0 else j.val + 1 := by
    rcases N with _ | n
    · exact j.elim0
    · rw [coe_finRotate]
      by_cases h : j = Fin.last n
      · subst h
        simp
      · rw [if_neg h, if_neg]
        intro h'
        apply h
        ext
        simp only [Fin.val_last]
        omega
  have swapped_eq {N : ℕ} (a b : Fin N) (w : Fin N → Fin 2) :
      ((Equiv.swap a b).arrowCongr (Equiv.refl (Fin 2))) w = fun t => w (Equiv.swap a b t) := by
    funext t
    simp [Equiv.arrowCongr_apply, Equiv.symm_swap]
  have move_up {N : ℕ} (hN : 3 ≤ N) (j : Fin N) (w : Fin N → Fin 2) (hw : w j = 0) :
      xiVal N (fun t => w (Equiv.swap (finRotate N j) (finRotate N (finRotate N j)) t)) =
        xiVal N w := by
    have hjN := j.isLt
    have hwj : w ⟨j.val, hjN⟩ = 0 := hw
    rcases Nat.lt_or_ge (j.val + 1 + 1) N with h1 | h1
    · have hk1 : finRotate N j = ⟨j.val + 1, by omega⟩ :=
        Fin.ext (by rw [finRotate_val, if_neg (by omega)])
      have hk2 : finRotate N (finRotate N j) = ⟨j.val + 1 + 1, h1⟩ :=
        Fin.ext (by rw [finRotate_val, hk1]; simp only; rw [if_neg (by omega)])
      rw [hk2, hk1]
      have hsame := height_swap_adjacent w (j.val + 1) h1
      apply xiVal_congr
      · exact hsame N le_rfl (by omega)
      · intro _
        refine ⟨0, ?_⟩
        rw [mul_zero, add_zero]
        have hyj : w (Equiv.swap (⟨j.val + 1, by omega⟩ : Fin N) ⟨j.val + 1 + 1, h1⟩
            ⟨j.val, hjN⟩) = 0 := by
          rw [Equiv.swap_apply_of_ne_of_ne (fin_ne _ _ (by omega)) (fin_ne _ _ (by omega))]
          exact hwj
        apply depth_eq_of_local w _ (j.val + 1 + 1) j.val (by omega) (by omega) hsame
        · rw [height_add_two w j.val (by omega), hwj, stepVal_zero]
          linarith [stepVal_ge (w ⟨j.val + 1, by omega⟩)]
        · rw [height_add_two _ j.val (by omega), hyj, stepVal_zero]
          linarith [stepVal_ge (w (Equiv.swap (⟨j.val + 1, by omega⟩ : Fin N)
            ⟨j.val + 1 + 1, h1⟩ ⟨j.val + 1, by omega⟩))]
    · rcases Nat.lt_or_ge (j.val + 1) N with h2 | h2
      · -- `j = N - 2`: the exchanged letters are the last and the first
        have hjv : j.val = N - 2 := by omega
        have hk1 : finRotate N j = ⟨N - 1, by omega⟩ :=
          Fin.ext (by rw [finRotate_val, if_neg (by omega)]; simp only; omega)
        have hk2 : finRotate N (finRotate N j) = ⟨0, by omega⟩ :=
          Fin.ext (by rw [finRotate_val, hk1]; simp only; rw [if_pos (by omega)])
        rw [hk2, hk1]
        obtain ⟨hshift, htot⟩ := height_swap_ends w (by omega)
        apply xiVal_congr
        · exact htot
        · intro h0
          have hyN : pathHeight (fun t => w (Equiv.swap (⟨N - 1, by omega⟩ : Fin N)
              ⟨0, by omega⟩ t)) N = 0 := by rw [htot, h0]
          have hyj : w (Equiv.swap (⟨N - 1, by omega⟩ : Fin N) ⟨0, by omega⟩
              ⟨N - 2, by omega⟩) = 0 := by
            rw [Equiv.swap_apply_of_ne_of_ne (fin_ne _ _ (by omega)) (fin_ne _ _ (by omega))]
            rw [← hwj]
            congr 1
            ext
            simp only
            omega
          have hwj' : w ⟨N - 2, by omega⟩ = 0 := by
            rw [← hwj]
            congr 1
            ext
            simp only
            omega
          have hxq : pathHeight w (N - 2) ≤ 0 := by
            have hl := height_last w (by omega)
            have hl2 := pathHeight_succ w (N - 2) (by omega)
            rw [show N - 2 + 1 = N - 1 by omega] at hl2
            rw [hwj', stepVal_zero] at hl2
            linarith [stepVal_ge (w ⟨N - 1, by omega⟩)]
          have hyq : pathHeight (fun t => w (Equiv.swap (⟨N - 1, by omega⟩ : Fin N)
              ⟨0, by omega⟩ t)) (N - 2) ≤ 0 := by
            have hl := height_last (fun t => w (Equiv.swap (⟨N - 1, by omega⟩ : Fin N)
              ⟨0, by omega⟩ t)) (by omega)
            have hl2 := pathHeight_succ (fun t => w (Equiv.swap (⟨N - 1, by omega⟩ : Fin N)
              ⟨0, by omega⟩ t)) (N - 2) (by omega)
            rw [show N - 2 + 1 = N - 1 by omega] at hl2
            rw [hyj, stepVal_zero] at hl2
            linarith [stepVal_ge (w (Equiv.swap (⟨N - 1, by omega⟩ : Fin N) ⟨0, by omega⟩
              ⟨N - 1, by omega⟩))]
          have hd := depth_eq_of_shift w _ _ (N - 2) (by omega) (by omega) h0 hyN hshift hxq hyq
          rcases stepVal_bound (w ⟨N - 1, by omega⟩) with ha | ha <;>
            rcases stepVal_bound (w ⟨0, by omega⟩) with hb | hb <;>
            rw [ha, hb] at hd
          · exact ⟨0, by linarith⟩
          · exact ⟨-1, by linarith⟩
          · exact ⟨1, by linarith⟩
          · exact ⟨0, by linarith⟩
      · -- `j = N - 1`: the exchanged letters are the first two
        have hjv : j.val = N - 1 := by omega
        have hk1 : finRotate N j = ⟨0, by omega⟩ :=
          Fin.ext (by rw [finRotate_val, if_pos (by omega)])
        have hk2 : finRotate N (finRotate N j) = ⟨0 + 1, by omega⟩ :=
          Fin.ext (by rw [finRotate_val, hk1]; simp only; rw [if_neg (by omega)])
        rw [hk2, hk1]
        have hsame := height_swap_adjacent w 0 (by omega)
        apply xiVal_congr
        · exact hsame N le_rfl (by omega)
        · intro h0
          refine ⟨0, ?_⟩
          rw [mul_zero, add_zero]
          have hwl : w ⟨N - 1, by omega⟩ = 0 := by
            rw [← hwj]
            congr 1
            ext
            simp only
            omega
          have hyl : w (Equiv.swap (⟨0, by omega⟩ : Fin N) ⟨0 + 1, by omega⟩ ⟨N - 1, by omega⟩) =
              0 := by
            rw [Equiv.swap_apply_of_ne_of_ne (fin_ne _ _ (by omega)) (fin_ne _ _ (by omega))]
            exact hwl
          have hyN : pathHeight (fun t => w (Equiv.swap (⟨0, by omega⟩ : Fin N)
              ⟨0 + 1, by omega⟩ t)) N = 0 := by rw [hsame N le_rfl (by omega), h0]
          apply depth_eq_of_local w _ (0 + 1) (N - 1) (by omega) (by omega) hsame
          · have hl := height_last w (by omega)
            rw [hwl, stepVal_zero, h0] at hl
            rw [height_one w (by omega)]
            linarith [stepVal_ge (w ⟨0, by omega⟩)]
          · have hl := height_last (fun t => w (Equiv.swap (⟨0, by omega⟩ : Fin N)
              ⟨0 + 1, by omega⟩ t)) (by omega)
            rw [hyl, stepVal_zero, hyN] at hl
            rw [height_one _ (by omega)]
            linarith [stepVal_ge (w (Equiv.swap (⟨0, by omega⟩ : Fin N) ⟨0 + 1, by omega⟩
              ⟨0, by omega⟩))]
  have move_down {N : ℕ} (hN : 3 ≤ N) (j : Fin N) (w : Fin N → Fin 2)
      (hw : w (finRotate N (finRotate N j)) = 1) :
      xiVal N (fun t => w (Equiv.swap j (finRotate N j) t)) = xiVal N w := by
    obtain ⟨jv, hjN⟩ := j
    rcases Nat.lt_or_ge (jv + 1 + 1) N with h1 | h1
    · have hk1 : finRotate N ⟨jv, hjN⟩ = ⟨jv + 1, by omega⟩ :=
        Fin.ext (by rw [finRotate_val, if_neg (by simp only; omega)])
      have hk2 : finRotate N (finRotate N ⟨jv, hjN⟩) = ⟨jv + 1 + 1, h1⟩ :=
        Fin.ext (by rw [finRotate_val, hk1]; rw [if_neg (by simp only; omega)])
      rw [hk2] at hw
      rw [hk1]
      have hsame := height_swap_adjacent w jv (by omega)
      apply xiVal_congr
      · exact hsame N le_rfl (by omega)
      · intro _
        refine ⟨0, ?_⟩
        rw [mul_zero, add_zero]
        have hyc : w (Equiv.swap (⟨jv, hjN⟩ : Fin N) ⟨jv + 1, by omega⟩ ⟨jv + 1 + 1, h1⟩) = 1 := by
          rw [Equiv.swap_apply_of_ne_of_ne (fin_ne _ _ (by omega)) (fin_ne _ _ (by omega))]
          exact hw
        apply depth_eq_of_local w _ (jv + 1) (jv + 1 + 1 + 1) (by omega) (by omega) hsame
        · have := pathHeight_succ w (jv + 1 + 1) h1
          rw [hw, stepVal_one, pathHeight_succ w (jv + 1) (by omega)] at this
          linarith [stepVal_le (w ⟨jv + 1, by omega⟩)]
        · have := pathHeight_succ (fun t => w (Equiv.swap (⟨jv, hjN⟩ : Fin N)
            ⟨jv + 1, by omega⟩ t)) (jv + 1 + 1) h1
          rw [hyc, stepVal_one, pathHeight_succ _ (jv + 1) (by omega)] at this
          linarith [stepVal_le (w (Equiv.swap (⟨jv, hjN⟩ : Fin N) ⟨jv + 1, by omega⟩
            ⟨jv + 1, by omega⟩))]
    · rcases Nat.lt_or_ge (jv + 1) N with h2 | h2
      · -- `j = N - 2`: exchange the letters `N - 2, N - 1`; the control letter is the first
        have hk1 : finRotate N ⟨jv, hjN⟩ = ⟨jv + 1, h2⟩ :=
          Fin.ext (by rw [finRotate_val, if_neg (by simp only; omega)])
        have hk2 : finRotate N (finRotate N ⟨jv, hjN⟩) = ⟨0, by omega⟩ :=
          Fin.ext (by rw [finRotate_val, hk1]; rw [if_pos (by simp only; omega)])
        rw [hk2] at hw
        rw [hk1]
        have hsame := height_swap_adjacent w jv h2
        apply xiVal_congr
        · exact hsame N le_rfl (by omega)
        · intro h0
          refine ⟨0, ?_⟩
          rw [mul_zero, add_zero]
          have hyc : w (Equiv.swap (⟨jv, hjN⟩ : Fin N) ⟨jv + 1, h2⟩ ⟨0, by omega⟩) = 1 := by
            rw [Equiv.swap_apply_of_ne_of_ne (fin_ne _ _ (by omega)) (fin_ne _ _ (by omega))]
            exact hw
          have hyN : pathHeight (fun t => w (Equiv.swap (⟨jv, hjN⟩ : Fin N)
              ⟨jv + 1, h2⟩ t)) N = 0 := by rw [hsame N le_rfl (by omega), h0]
          apply depth_eq_of_local w _ (jv + 1) 1 (by omega) (by omega) hsame
          · rw [height_one w (by omega), hw, stepVal_one]
            have hl' : pathHeight w N = pathHeight w (jv + 1) + stepVal (w ⟨jv + 1, h2⟩) := by
              have := pathHeight_succ w (jv + 1) h2
              rwa [show jv + 1 + 1 = N by omega] at this
            rw [h0] at hl'
            linarith [stepVal_le (w ⟨jv + 1, h2⟩)]
          · rw [height_one _ (by omega), hyc, stepVal_one]
            have hl' : pathHeight (fun t => w (Equiv.swap (⟨jv, hjN⟩ : Fin N) ⟨jv + 1, h2⟩ t)) N =
                pathHeight (fun t => w (Equiv.swap (⟨jv, hjN⟩ : Fin N) ⟨jv + 1, h2⟩ t)) (jv + 1) +
                stepVal (w (Equiv.swap (⟨jv, hjN⟩ : Fin N) ⟨jv + 1, h2⟩ ⟨jv + 1, h2⟩)) := by
              have := pathHeight_succ (fun t => w (Equiv.swap (⟨jv, hjN⟩ : Fin N)
                ⟨jv + 1, h2⟩ t)) (jv + 1) h2
              rwa [show jv + 1 + 1 = N by omega] at this
            rw [hyN] at hl'
            linarith [stepVal_le (w (Equiv.swap (⟨jv, hjN⟩ : Fin N) ⟨jv + 1, h2⟩ ⟨jv + 1, h2⟩))]
      · -- `j = N - 1`: exchange the last and the first letter; the control letter is the second
        have hjv : jv = N - 1 := by omega
        subst hjv
        have hk1 : finRotate N ⟨N - 1, hjN⟩ = ⟨0, by omega⟩ :=
          Fin.ext (by rw [finRotate_val, if_pos (by simp only; omega)])
        have hk2 : finRotate N (finRotate N ⟨N - 1, hjN⟩) = ⟨0 + 1, by omega⟩ :=
          Fin.ext (by rw [finRotate_val, hk1]; rw [if_neg (by simp only; omega)])
        rw [hk2] at hw
        rw [hk1]
        obtain ⟨hshift, htot⟩ := height_swap_ends w (by omega)
        apply xiVal_congr
        · exact htot
        · intro h0
          have hyN : pathHeight (fun t => w (Equiv.swap (⟨N - 1, by omega⟩ : Fin N)
              ⟨0, by omega⟩ t)) N = 0 := by rw [htot, h0]
          have hyc : w (Equiv.swap (⟨N - 1, by omega⟩ : Fin N) ⟨0, by omega⟩ ⟨0 + 1, by omega⟩) =
              1 := by
            rw [Equiv.swap_apply_of_ne_of_ne (fin_ne _ _ (by omega)) (fin_ne _ _ (by omega))]
            exact hw
          have hxq : pathHeight w (0 + 1 + 1) ≤ 0 := by
            rw [height_add_two w 0 (by omega), pathHeight_zero, hw, stepVal_one]
            linarith [stepVal_le (w ⟨0, by omega⟩)]
          have hyq : pathHeight (fun t => w (Equiv.swap (⟨N - 1, by omega⟩ : Fin N)
              ⟨0, by omega⟩ t)) (0 + 1 + 1) ≤ 0 := by
            rw [height_add_two _ 0 (by omega), pathHeight_zero, hyc, stepVal_one]
            linarith [stepVal_le (w (Equiv.swap (⟨N - 1, by omega⟩ : Fin N) ⟨0, by omega⟩
              ⟨0, by omega⟩))]
          have hd := depth_eq_of_shift w _ _ (0 + 1 + 1) (by omega) (by omega) h0 hyN hshift
            hxq hyq
          rcases stepVal_bound (w ⟨N - 1, by omega⟩) with ha | ha <;>
            rcases stepVal_bound (w ⟨0, by omega⟩) with hb | hb <;>
            rw [ha, hb] at hd
          · exact ⟨0, by linarith⟩
          · exact ⟨-1, by linarith⟩
          · exact ⟨1, by linarith⟩
          · exact ⟨0, by linarith⟩
  have tensor_diagonal {N : ℕ} (d : Fin N → Fin 2 → ℂ) :
      tensor N (fun i => Matrix.diagonal (d i)) = Matrix.diagonal (fun w => ∏ i, d i (w i)) := by
    ext y x
    simp only [tensor, Matrix.diagonal_apply]
    by_cases h : y = x
    · subst h
      simp
    · rw [if_neg h]
      obtain ⟨i, hi⟩ : ∃ i, y i ≠ x i := by
        by_contra hc
        push Not at hc
        exact h (funext hc)
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_neg hi])
  have nUp_diag : nUp = Matrix.diagonal (fun v : Fin 2 => if v = 0 then 1 else 0) := by
    ext a b
    fin_cases a <;> fin_cases b <;> norm_num [nUp, qubitZ, Matrix.one_apply, Matrix.diagonal_apply]
  have nDown_diag : nDown = Matrix.diagonal (fun v : Fin 2 => if v = 0 then 0 else 1) := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [nDown, qubitZ, Matrix.one_apply, Matrix.diagonal_apply]
  have site_diagonal {N : ℕ} (j : Fin N) (d : Fin 2 → ℂ) :
      site N j (Matrix.diagonal d) = Matrix.diagonal (fun w => d (w j)) := by
    unfold site
    have h : (fun i => if i = j then Matrix.diagonal d else (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
        fun i => Matrix.diagonal (fun v => if i = j then d v else 1) := by
      funext i
      split_ifs <;> simp [Matrix.diagonal_one]
    rw [h, tensor_diagonal]
    congr 1
    funext w
    rw [Finset.prod_eq_single j (fun i _ hij => by simp [hij]) (by simp)]
    simp
  have Xi_eq (N : ℕ) : Xi N = Matrix.diagonal (xiVal N) := by
    classical
    have hproj : ∀ ℓ : Fin N → Fin 2, (tensor N fun i => if ℓ i = 0 then nUp else nDown) =
        Matrix.diagonal (fun w => if w = ℓ then 1 else 0) := by
      intro ℓ
      have h : (fun i => if ℓ i = 0 then nUp else nDown) =
          fun i => Matrix.diagonal (fun v : Fin 2 => if v = ℓ i then (1 : ℂ) else 0) := by
        funext i
        rw [nUp_diag, nDown_diag]
        generalize ℓ i = u
        fin_cases u <;> ext a b <;> fin_cases a <;> fin_cases b <;> simp
      rw [h, tensor_diagonal]
      congr 1
      funext w
      by_cases hw : w = ℓ
      · subst hw
        simp
      · rw [if_neg hw]
        obtain ⟨i, hi⟩ : ∃ i, w i ≠ ℓ i := by
          by_contra hc
          push Not at hc
          exact hw (funext hc)
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_neg hi])
    unfold Xi
    simp_rw [hproj]
    ext y x
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
    unfold xiVal
    by_cases hyx : y = x
    · subst hyx
      simp only [if_true]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs <;> simp
    · simp [hyx]
  have P_apply {N : ℕ} (j : Fin N) (y x : Fin N → Fin 2) :
      P N j y x = if (fun t => y (Equiv.swap j (finRotate N j) t)) = x then 1 else 0 := by
    unfold P Equiv.Perm.permMatrix
    rw [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, swapped_eq]
    simp only [Option.mem_def, Option.some.injEq]
  have swap_swap_word {N : ℕ} (a b : Fin N) (y : Fin N → Fin 2) :
      (fun t => (fun s => y (Equiv.swap a b s)) (Equiv.swap a b t)) = y := by
    funext t
    simp
  have Xi_comm_F {N : ℕ} (hN : 3 ≤ N) (j : Fin N) : Xi N * F N j = F N j * Xi N := by
    rw [Xi_eq]
    ext y x
    simp only [F, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply]
    rw [nUp_diag, nDown_diag, site_diagonal, site_diagonal]
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Pi, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.one_apply, P_apply, smul_eq_mul]
    set k := finRotate N j
    set k2 := finRotate N k
    by_cases hyx : y = x
    · subst hyx
      ring
    · rw [if_neg hyx]
      have e1 : (if y j = 0 then (1 : ℂ) else 0) *
          (if (fun t => y (Equiv.swap k k2 t)) = x then 1 else 0) *
            (xiVal N y - xiVal N x) = 0 := by
        by_cases hc : y j = 0 ∧ (fun t => y (Equiv.swap k k2 t)) = x
        · rw [← hc.2, move_up hN j y hc.1]
          ring
        · rcases not_and_or.mp hc with h | h <;> simp [h]
      have e2 : (if (fun t => y (Equiv.swap j k t)) = x then (1 : ℂ) else 0) *
          (if x k2 = 0 then 0 else 1) * (xiVal N y - xiVal N x) = 0 := by
        by_cases hc : (fun t => y (Equiv.swap j k t)) = x ∧ x k2 = 1
        · have hback : (fun t => x (Equiv.swap j k t)) = y := by
            rw [← hc.1]
            exact swap_swap_word j k y
          have hmv := move_down hN j x hc.2
          rw [hback] at hmv
          rw [hmv]
          ring
        · rcases not_and_or.mp hc with h | h
          · simp [h]
          · have : x k2 = 0 := by
              generalize x k2 = u at h ⊢
              revert h
              fin_cases u <;> decide
            simp [this]
      linear_combination (-(1 : ℂ) / 2) * e1 + (-(1 : ℂ) / 2) * e2
  intro N hN _
  unfold H
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => Xi_comm_F hN j

#print axioms result

end D5.S3.Quantum.Dynamics.PronkoFredkinXiCommutes
