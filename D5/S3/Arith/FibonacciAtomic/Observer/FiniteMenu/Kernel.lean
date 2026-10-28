/- GID: D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/Kernel
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Original all-menu ranks classify complete synchronized native trajectories. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuObstruction
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.Kernel

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualLeafHistoryRigidity (subtree)
open NativeFiniteMenuCode
open NativeRankedNavigationCompiler (pathCost pathThreshold atomic_navigation)

/-- Equality at each selected literal address and each common supplied count. -/
def Same (S : Menu) (u v : Source) : Prop :=
  ∀ q ∈ S, ∀ k : Nat,
    readout q (substitution^[k] u) = readout q (substitution^[k] v)

private theorem same_symm {S : Menu} {u v : Source} (h : Same S u v) : Same S v u :=
  fun q hq k => (h q hq k).symm

private theorem same_trans {S : Menu} {u v w : Source}
    (h : Same S u v) (g : Same S v w) : Same S u w :=
  fun q hq k => (h q hq k).trans (g q hq k)

private theorem iter_mul (k : Nat) (x y : Source) :
    substitution^[k] (.mul x y) = .mul (substitution^[k] x) (substitution^[k] y) :=
  Function.Semiconj₂.iterate (fun s t => substitution.map_mul s t) k x y

private theorem beta_shift (k : Nat) :
    substitution^[k] (.of false) = substitution^[k+1] (.of true) := by
  rw [Function.iterate_succ_apply]
  rfl

private theorem read_at (a r : Address) (u : Source) :
    readout (a ++ r) u = match subtree a u with
      | none => .absent
      | some t => readout r t :=
  ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1 a r u

private theorem atomic_threshold (q : Address) : pathThreshold q ≤ pathCost q + 1 := by
  have sep := NativeFiniteMenuObstruction.atomic_separator q
  have hAt := read_at q [] (substitution^[pathCost q+1] (.of true))
  simp only [List.append_nil] at hAt
  cases hs : subtree q (substitution^[pathCost q+1] (.of true)) with
  | none => rw [hs] at hAt; rw [hAt] at sep; cases sep.1
  | some t =>
    obtain ⟨r, bound, _, _⟩ := (atomic_navigation q (pathCost q+1) t).mp hs
    exact bound

private theorem atomic_branch_after (q : Address) (k : Nat)
    (hk : pathCost q + 2 ≤ k) :
    readout q (substitution^[k] (.of true)) = .branch := by
  obtain ⟨m, hm⟩ : ∃ m, k = m + pathCost q + 2 := ⟨k-pathCost q-2, by omega⟩
  subst k
  have nav := (atomic_navigation q (m+pathCost q+2)
    (.mul (substitution^[m+1] (.of true)) (substitution^[m] (.of true)))).mpr
    ⟨m+2, by have := atomic_threshold q; omega, by omega,
      NativeRankedEqualityCompiler.atomic_pair m⟩
  have hAt := read_at q [] (substitution^[m+pathCost q+2] (.of true))
  simpa only [List.append_nil, nav, readout] using hAt

theorem atomic_not_branch_before (q : Address) (k : Nat)
    (hk : k < pathCost q + 2) :
    readout q (substitution^[k] (.of true)) ≠ .branch := by
  have hAt := read_at q [] (substitution^[k] (.of true))
  simp only [List.append_nil] at hAt
  cases hs : subtree q (substitution^[k] (.of true)) with
  | none => rw [hs] at hAt; rw [hAt]; decide
  | some t =>
    obtain ⟨r, _, he, ht⟩ := (atomic_navigation q k t).mp hs
    have hr : r = 0 ∨ r = 1 := by omega
    rcases hr with rfl | rfl
    · rw [hs, ← ht] at hAt
      change readout q (substitution^[k] (.of true)) = .alpha at hAt
      rw [hAt]; decide
    · rw [hs, ← ht] at hAt
      change readout q (substitution^[k] (.of true)) = .beta at hAt
      rw [hAt]; decide

/-- Every source has become a branch at q by its atomic branch bound. -/
theorem branch_after (q : Address) (u : Source) (k : Nat)
    (hk : pathCost q + 2 ≤ k) : readout q (substitution^[k] u) = .branch := by
  induction q generalizing u k with
  | nil =>
    have hk : 2 ≤ k := by simpa [pathCost] using hk
    cases u with
    | of b =>
      cases b with
      | false =>
        rw [beta_shift]
        exact atomic_branch_after [] (k+1) (by simp [pathCost]; omega)
      | true => exact atomic_branch_after [] k (by simpa [pathCost] using hk)
    | mul l r => rw [iter_mul]; rfl
  | cons b q ih =>
    cases u with
    | of c =>
      cases c with
      | false =>
        rw [beta_shift]
        exact atomic_branch_after (b :: q) (k+1) (by omega)
      | true => exact atomic_branch_after (b :: q) k hk
    | mul l r =>
      rw [iter_mul]
      have hq : pathCost q + 2 ≤ k := by cases b <;> simp [pathCost] at hk <;> omega
      cases b
      · exact ih l k hq
      · exact ih r k hq

private theorem same_pair_iff (S : Menu) (x y x' y' : Source) :
    Same S (.mul x y) (.mul x' y') ↔
      Same (child false S) x x' ∧ Same (child true S) y y' := by
  constructor
  · intro h
    constructor <;> intro q hq k
    · have ht := h (false :: q) ((mem_child false S q).mp hq) k
      simpa only [iter_mul, readout] using ht
    · have ht := h (true :: q) ((mem_child true S q).mp hq) k
      simpa only [iter_mul, readout] using ht
  · rintro ⟨hl, hr⟩ q hq k
    rw [iter_mul, iter_mul]
    cases q with
    | nil => rfl
    | cons b q =>
      cases b with
      | false => exact hl q ((mem_child false S q).mpr hq) k
      | true => exact hr q ((mem_child true S q).mpr hq) k

private theorem alpha_not_pair (S : Menu) (hS : S ≠ []) (x y : Source) :
    ¬ Same S (.of true) (.mul x y) := by
  intro h
  obtain ⟨q, hq⟩ : ∃ q, q ∈ S := by cases S with
    | nil => contradiction
    | cons q S => exact ⟨q, by simp⟩
  cases q with
  | nil => have he := h [] hq 0; cases he
  | cons b r =>
    have he := h (b :: r) hq (pathCost r+2)
    have hb : readout (b :: r) (substitution^[pathCost r+2] (.mul x y)) = .branch := by
      rw [iter_mul]
      cases b <;> exact branch_after r _ (pathCost r+2) (by omega)
    apply atomic_not_branch_before (b :: r) (pathCost r+2)
      (by cases b <;> simp [pathCost])
    exact he.trans hb

private theorem leaves_distinct (S : Menu) (hS : S ≠ []) :
    ¬ Same S (.of true) (.of false) := by
  intro h
  obtain ⟨q, hq⟩ : ∃ q, q ∈ S := by cases S with
    | nil => contradiction
    | cons q S => exact ⟨q, by simp⟩
  have hs := NativeFiniteMenuObstruction.atomic_separator q
  have he := h q hq (pathCost q+1)
  rw [hs.1, hs.2] at he
  cases he

private theorem overlap_same (S : Menu) (he : eta S = false) :
    Same S (.of false) (.mul (.of true) (.of true)) := by
  intro q hq k
  unfold eta at he
  have ha := List.all_eq_true.mp (Bool.eq_true_of_not_eq_false' he) q hq
  have shape : ∃ c r, q = false :: c :: r := by
    cases q with
    | nil => simp at ha
    | cons b r =>
      cases b with
      | false =>
        cases r with
        | nil => simp at ha
        | cons c r => exact ⟨c, r, rfl⟩
      | true => simp at ha
  obtain ⟨c, r, rfl⟩ := shape
  cases k with
  | zero => rfl
  | succ k =>
    have hb : substitution^[k+1] (.of false) =
        .mul (substitution^[k+1] (.of true)) (substitution^[k] (.of true)) := by
      rw [beta_shift, show k+1+1 = k+2 by omega, NativeRankedEqualityCompiler.atomic_pair]
    rw [hb, iter_mul]
    rfl

private theorem beta_pair_guard (S : Menu) (x y : Source)
    (h : Same S (.of false) (.mul x y)) : eta S = false := by
  change (!S.all _) = false
  simp only [Bool.not_eq_eq_eq_not, Bool.not_false]
  apply List.all_eq_true.mpr
  intro q hq
  cases q with
  | nil => have he := h [] hq 0; cases he
  | cons b r =>
    cases b with
    | false =>
      cases r with
      | nil =>
        have he := h [false] hq 0
        cases x with
        | of b => cases b <;> cases he
        | mul l r => cases he
      | cons c r => rfl
    | true =>
      have he := h (true :: r) hq (pathCost r+2)
      have hb : readout (true :: r) (substitution^[pathCost r+2] (.mul x y)) = .branch := by
        rw [iter_mul]; exact branch_after r y _ (by omega)
      rw [beta_shift] at he
      apply False.elim
      apply atomic_not_branch_before (true :: r) (pathCost r+2+1) (by simp [pathCost]; omega)
      exact he.trans hb

private theorem beta_pair_iff (S : Menu) (x y : Source) :
    Same S (.of false) (.mul x y) ↔
      S = [] ∨ eta S = false ∧
        Same (child false S) (.of true) x ∧ Same (child true S) (.of true) y := by
  constructor
  · intro h
    right
    have he := beta_pair_guard S x y h
    exact ⟨he, (same_pair_iff S _ _ _ _).mp (same_trans (same_symm (overlap_same S he)) h)⟩
  · rintro (rfl | ⟨he, hl, hr⟩)
    · intro q hq; simp at hq
    · exact same_trans (overlap_same S he) ((same_pair_iff S _ _ _ _).mpr ⟨hl,hr⟩)

private theorem pair_code_lt (S : Menu) (x y : Source) :
    code (child false S) x * N (child true S) + code (child true S) y <
      N (child false S) * N (child true S) := by
  have hl := (original_code_grammar (child false S)).2.2.2 x
  have hr := (original_code_grammar (child true S)).2.2.2 y
  have hm := Nat.mul_le_mul_right (N (child true S)) (Nat.succ_le_of_lt hl)
  simp only [Nat.succ_eq_add_one, Nat.add_mul, one_mul] at hm
  omega

private theorem pair_code_iff (S : Menu) (hS : S ≠ []) (x y x' y' : Source) :
    code S (.mul x y) = code S (.mul x' y') ↔
      code (child false S) x = code (child false S) x' ∧
      code (child true S) y = code (child true S) y' := by
  have gs := (original_code_grammar S).2.1 hS
  rw [gs.2.1, gs.2.1]
  constructor
  · intro he
    let a : Fin (N (child false S)) × Fin (N (child true S)) :=
      (⟨code (child false S) x, (original_code_grammar _).2.2.2 x⟩,
       ⟨code (child true S) y, (original_code_grammar _).2.2.2 y⟩)
    let b : Fin (N (child false S)) × Fin (N (child true S)) :=
      (⟨code (child false S) x', (original_code_grammar _).2.2.2 x'⟩,
       ⟨code (child true S) y', (original_code_grammar _).2.2.2 y'⟩)
    have hp : a = b := finProdFinEquiv.injective (Fin.ext (by
      simpa only [finProdFinEquiv_apply_val, a, b, Nat.mul_comm, Nat.add_comm] using he))
    exact ⟨congrArg (fun p => p.1.val) hp, congrArg (fun p => p.2.val) hp⟩
  · rintro ⟨hl,hr⟩; rw [hl,hr]

private theorem code_alpha_not_pair (S : Menu) (hS : S ≠ []) (x y : Source) :
    code S (.of true) ≠ code S (.mul x y) := by
  have gs := (original_code_grammar S).2.1 hS
  rw [gs.2.2.1, gs.2.1]
  exact (Nat.ne_of_lt (pair_code_lt S x y)).symm

private theorem code_leaves_distinct (S : Menu) (hS : S ≠ []) :
    code S (.of true) ≠ code S (.of false) := by
  obtain ⟨q, hq⟩ : ∃ q, q ∈ S := by cases S with
    | nil => contradiction
    | cons q S => exact ⟨q, by simp⟩
  exact original_code_context_separation S [] q hq

private theorem code_beta_pair_iff (S : Menu) (hS : S ≠ []) (x y : Source) :
    code S (.of false) = code S (.mul x y) ↔
      eta S = false ∧ code (child false S) (.of true) = code (child false S) x ∧
        code (child true S) (.of true) = code (child true S) y := by
  have gs := (original_code_grammar S).2.1 hS
  cases he : eta S
  · rw [gs.2.2.2, he]
    simp only [Bool.false_eq_true, ↓reduceIte, true_and]
    rw [← gs.2.1 (.of true) (.of true), pair_code_iff S hS]
  · have hb := pair_code_lt S x y
    rw [gs.2.2.2, gs.2.1, he]
    simp only [↓reduceIte, Bool.true_eq_false, false_and, iff_false]
    omega

private theorem kernel_aux (h : Nat) (S : Menu)
    (depth : ∀ q ∈ S, q.length < h) (u v : Source) :
    code S u = code S v ↔ Same S u v := by
  induction h generalizing S u v with
  | zero =>
    have hs : S = [] := List.eq_nil_iff_forall_not_mem.mpr (by
      intro q hq; have := depth q hq; omega)
    subst S
    simp [Same, (original_code_grammar []).1 rfl |>.2]
  | succ h ih =>
    by_cases hs : S = []
    · subst S; simp [Same, (original_code_grammar []).1 rfl |>.2]
    · have dc (b : Bool) : ∀ q ∈ child b S, q.length < h := by
        intro q hq
        have hd := depth (b :: q) ((mem_child b S q).mp hq)
        simp only [List.length_cons] at hd; omega
      have betaPair (x y : Source) :
          code S (.of false) = code S (.mul x y) ↔ Same S (.of false) (.mul x y) := by
        rw [code_beta_pair_iff S hs, beta_pair_iff]
        simp only [hs, false_or]
        rw [ih _ (dc false), ih _ (dc true)]
      cases u with
      | of b =>
        cases v with
        | of c =>
          cases b <;> cases c
          · exact ⟨fun _ q hq k => rfl, fun _ => rfl⟩
          · exact iff_of_false ((code_leaves_distinct S hs).symm)
              (fun he => leaves_distinct S hs (same_symm he))
          · exact iff_of_false (code_leaves_distinct S hs) (leaves_distinct S hs)
          · exact ⟨fun _ q hq k => rfl, fun _ => rfl⟩
        | mul x y =>
          cases b with
          | false => exact betaPair x y
          | true => exact iff_of_false (code_alpha_not_pair S hs x y) (alpha_not_pair S hs x y)
      | mul x y =>
        cases v with
        | of b =>
          cases b with
          | false => exact ⟨fun he => same_symm ((betaPair x y).mp he.symm),
              fun he => ((betaPair x y).mpr (same_symm he)).symm⟩
          | true =>
            exact iff_of_false ((code_alpha_not_pair S hs x y).symm)
              (fun he => alpha_not_pair S hs x y (same_symm he))
        | mul x' y' =>
          rw [pair_code_iff S hs, same_pair_iff, ih _ (dc false), ih _ (dc true)]

/-- The original rank has precisely the kernel of the full selected native trajectory. -/
theorem original_menu_kernel (S : Menu) (u v : Source) :
    code S u = code S v ↔
      ∀ q ∈ S, ∀ k : Nat,
        readout q (substitution^[k] u) = readout q (substitution^[k] v) := by
  apply kernel_aux (S.toFinset.sup List.length + 1) S _ u v
  intro q hq
  exact Nat.lt_succ_of_le (Finset.le_sup (List.mem_toFinset.mpr hq))

end D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.Kernel
