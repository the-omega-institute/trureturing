/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedSwapNormalForm
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedSwapNormalForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: A balanced nine-cube support invariant under the leading swap has a paired mask. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9PairBoundaryKernel

/-! The pure leading swap gives a normal form for a balanced source support.
Using the boundary-kernel reduction also requires an image mask in the same orientation. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedSwapNormalForm

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum
  (Q flip flip_adj flip_apply_same gamma gamma_apply IsBalanced IsSwitching switching_sq)
open BalancedCubeGirth (adjacent_exists_flip)
open HuangCubeCovariance (exists_signed_covariance)
open Q9IsotropicHuang (flipSign weightedAction weightedAction_real)
open Q9PairBoundaryKernel (pairVertex cubeMask)

private abbrev second (n : ℕ) : Fin (n + 2) := (0 : Fin (n + 1)).succ

private abbrev swapAxes (n : ℕ) : Equiv.Perm (Fin (n + 2)) := Equiv.swap 0 (second n)

private theorem swapAxes_tail {n : ℕ} (i : Fin n) :
    swapAxes n i.succ.succ = i.succ.succ :=
  Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _)
    (fun h => Fin.succ_ne_zero i (Fin.succ_inj.mp h))

/-- The ordinary transposition of coordinates `0` and `1`. -/
def leadingSwap {n : ℕ} : Q (n + 2) ≃ Q (n + 2) where
  toFun x i := x (swapAxes n i)
  invFun x i := x (swapAxes n i)
  left_inv x := funext fun i => congrArg x (Equiv.swap_apply_self _ _ i)
  right_inv x := funext fun i => congrArg x (Equiv.swap_apply_self _ _ i)

private theorem leadingSwap_cons {n : ℕ} (u v : Bool) (t : Q n) :
    leadingSwap (Fin.cons u (Fin.cons v t)) = Fin.cons v (Fin.cons u t) := by
  funext i
  induction i using Fin.cases with
  | zero => simp only [leadingSwap, Equiv.coe_fn_mk, Equiv.swap_apply_left,
      Fin.cons_zero, Fin.cons_succ]
  | succ i =>
      induction i using Fin.cases with
      | zero => simp only [leadingSwap, Equiv.coe_fn_mk, Equiv.swap_apply_right,
          Fin.cons_zero, Fin.cons_succ]
      | succ i => simp only [leadingSwap, Equiv.coe_fn_mk, swapAxes_tail, Fin.cons_succ]

private theorem leadingSwap_pairVertex {n : ℕ} (u v : Bool) (t : Q n) :
    leadingSwap (pairVertex (u, v, t)) = pairVertex (v, u, t) :=
  leadingSwap_cons u v t

private theorem leadingSwap_flip {n : ℕ} (x : Q (n + 2)) (i : Fin (n + 2)) :
    leadingSwap (flip x i) = flip (leadingSwap x) (swapAxes n i) := by
  funext j
  by_cases hj : j = swapAxes n i
  · subst j
    simp only [leadingSwap, Equiv.coe_fn_mk, Equiv.swap_apply_self, flip_apply_same]
  · have hi : swapAxes n j ≠ i := by
      intro h
      exact hj (by simpa only [Equiv.swap_apply_self] using congrArg (swapAxes n) h)
    simp [leadingSwap, BalancedCriticalSpectrum.flip, hj, hi]

/-- The false-prefix gauge is negative at `00` and positive on the other fibres. -/
private def leadingSwapSign {n : ℕ} (x : Q (n + 2)) : ℝ :=
  if x 0 = false ∧ x (second n) = false then -1 else 1

private theorem leadingSwapSign_sq {n : ℕ} (x : Q (n + 2)) : leadingSwapSign x ^ 2 = 1 := by
  unfold leadingSwapSign
  split <;> norm_num

private theorem leadingSwapSign_pairVertex {n : ℕ} (u v : Bool) (t : Q n) :
    leadingSwapSign (pairVertex (u, v, t)) = if u = false ∧ v = false then -1 else 1 := by
  change leadingSwapSign (Fin.cons u (Fin.cons v t)) = _
  simp only [leadingSwapSign, Fin.cons_zero, Fin.cons_succ]

-- The two endpoint gauges account for the change of the Q9 flip coefficient.
private theorem leadingSwap_edge (x : Q 9) (i : Fin 9) :
    (flipSign (swapAxes 7 i) (leadingSwap x) : ℝ) =
      leadingSwapSign x * (flipSign i x : ℝ) * leadingSwapSign (flip x i) := by
  have sign_zero {n : ℕ} (z : Q (n + 1)) : (flipSign 0 z : ℝ) = 1 := Int.cast_one
  have sign_succ {n : ℕ} (a : Bool) (z : Q n) (j : Fin n) :
      (flipSign j.succ (Fin.cons a z) : ℝ) =
        (if a then 1 else -1) * (flipSign j z : ℝ) := by
    change (↑((if (Fin.cons a z : Q (n + 1)) 0 then 1 else -1) *
      flipSign j (Sensitivity.π (Fin.cons a z))) : ℝ) = _
    have htail : Sensitivity.π (Fin.cons a z) = z :=
      Fin.tail_cons (α := fun _ : Fin (n + 1) => Bool) a z
    rw [Fin.cons_zero, htail, Int.cast_mul]
    cases a <;> simp
  obtain ⟨⟨u, v, t⟩, rfl⟩ := (pairVertex (n := 7)).surjective x
  have hvertex : pairVertex (u, v, t) = Fin.cons u (Fin.cons v t) := rfl
  rw [hvertex]
  simp only [leadingSwap_cons]
  induction i using Fin.cases with
  | zero =>
      simp only [swapAxes, Equiv.swap_apply_left, sign_succ, sign_zero,
        BalancedCriticalSpectrum.flip, Fin.cons_zero, Fin.update_cons_zero]
      cases u <;> cases v <;> simp [leadingSwapSign]
  | succ i =>
      induction i using Fin.cases with
      | zero =>
          change (flipSign (swapAxes 7 (second 7)) _ : ℝ) = _
          simp only [swapAxes, Equiv.swap_apply_right, sign_succ, sign_zero,
            BalancedCriticalSpectrum.flip, Fin.cons_succ, Fin.cons_zero,
            ← Fin.cons_update, Fin.update_cons_zero]
          cases u <;> cases v <;> simp [leadingSwapSign]
      | succ i =>
          simp only [swapAxes_tail, sign_succ, BalancedCriticalSpectrum.flip,
            Fin.cons_succ, ← Fin.cons_update]
          cases u <;> cases v <;> simp [leadingSwapSign, (Fin.succ_ne_zero i).symm]

private theorem switching_flipSign {C : Finset (Q 9)} {sigma : Q 9 → ℝ}
    (hs : IsSwitching C sigma) (x : Q 9) (i : Fin 9) (hx : x ∈ C) (hy : flip x i ∈ C) :
    (flipSign i x : ℝ) = sigma x * sigma (flip x i) := by
  let t : Fin 9 → ℤ := fun j => if j = i then 1 else 0
  have hsum : (∑ j : Fin 9, (t j : ℝ) • gamma j) = gamma i := by
    rw [Finset.sum_eq_single i]
    · simp [t]
    · intro j _ hj
      simp [t, hj]
    · simp
  have hgamma : (flipSign i x : ℝ) = gamma i (fun _ => 1) x := by
    have h := congrFun (weightedAction_real t (fun _ => 1)) x
    rw [hsum] at h
    unfold weightedAction at h
    rw [Finset.sum_eq_single i] at h
    · simpa [t] using h
    · intro j _ hj
      simp [t, hj]
    · simp
  rw [hgamma, gamma_apply, mul_one]
  exact hs.2 x hx _ hy (flip_adj x i)

/-- The gauge times the two switching signs is constant along induced walks. -/
private theorem leadingSwap_ratio_eq_of_reachable {C : Finset (Q 9)}
    {sigma : Q 9 → ℝ} (hs : IsSwitching C sigma)
    (hS : ∀ x ∈ C, leadingSwap x ∈ C) {x y : (C : Set (Q 9))}
    (hxy : ((hypercube 9).induce (C : Set (Q 9))).Reachable x y) :
    leadingSwapSign x.val * sigma x.val * sigma (leadingSwap x.val) =
      leadingSwapSign y.val * sigma y.val * sigma (leadingSwap y.val) := by
  let ratio (z : Q 9) := leadingSwapSign z * sigma z * sigma (leadingSwap z)
  have ratio_sq {z : Q 9} (hz : z ∈ C) : ratio z ^ 2 = 1 := by
    simp only [ratio, mul_pow, leadingSwapSign_sq, switching_sq hs hz,
      switching_sq hs (hS z hz), mul_one]
  have edge_ratio {u v : Q 9} (hu : u ∈ C) (hv : v ∈ C)
      (h : (hypercube 9).Adj u v) : ratio u = ratio v := by
    obtain ⟨i, rfl⟩ := adjacent_exists_flip h
    have hflip := leadingSwap_flip (n := 7) u i
    have hswap := switching_flipSign hs (leadingSwap u) (swapAxes 7 i) (hS u hu)
      (by
        rw [← hflip]
        exact hS _ hv)
    rw [← hflip] at hswap
    have he := leadingSwap_edge u i
    rw [switching_flipSign hs u i hu hv, hswap] at he
    have hp : ratio u * ratio (flip u i) = 1 := by
      calc
        _ = (leadingSwapSign u * (sigma u * sigma (flip u i)) * leadingSwapSign (flip u i)) *
            (sigma (leadingSwap u) * sigma (leadingSwap (flip u i))) := by
          dsimp only [ratio]
          ring
        _ = (sigma (leadingSwap u) * sigma (leadingSwap (flip u i))) ^ 2 := by
          rw [← he, pow_two]
        _ = 1 := by rw [mul_pow, switching_sq hs (hS u hu), switching_sq hs (hS _ hv), mul_one]
    calc
      ratio u = ratio u * ratio (flip u i) ^ 2 := by rw [ratio_sq hv, mul_one]
      _ = ratio (flip u i) := by rw [pow_two, ← mul_assoc, hp, one_mul]
  let G := (hypercube 9).induce (C : Set (Q 9))
  have walk_ratio {u v : C} (p : G.Walk u v) : ratio u.val = ratio v.val := by
    induction p with
    | nil => rfl
    | @cons u v _ h _ ih => exact (edge_ratio u.property v.property h).trans ih
  obtain ⟨p⟩ := hxy
  exact walk_ratio p

/-- The two fixed corner fibres cannot meet the same induced component. -/
private theorem not_reachable_of_leadingSwap_opposite_corners {C : Finset (Q 9)}
    (hC : IsBalanced C) (hS : ∀ x ∈ C, leadingSwap x ∈ C) {u v : Q 7}
    (hu : pairVertex (false, false, u) ∈ C) (hv : pairVertex (true, true, v) ∈ C) :
    ¬ ((hypercube 9).induce (C : Set (Q 9))).Reachable
      ⟨pairVertex (false, false, u), hu⟩ ⟨pairVertex (true, true, v), hv⟩ := by
  intro hp
  obtain ⟨sigma, hs⟩ := hC
  have h : (-1 : ℝ) * sigma (pairVertex (false, false, u)) *
        sigma (pairVertex (false, false, u)) =
      1 * sigma (pairVertex (true, true, v)) * sigma (pairVertex (true, true, v)) := by
    simpa [leadingSwap_pairVertex, leadingSwapSign_pairVertex] using
      leadingSwap_ratio_eq_of_reachable hs hS hp
  nlinarith only [h, switching_sq hs hu, switching_sq hs hv]

/-- When `b` is true, complement both leading bits. The tail stays fixed. -/
def complementLeadingPair {n : ℕ} (b : Bool) : Q (n + 2) ≃ Q (n + 2) where
  toFun x i := if b = true ∧ (i = 0 ∨ i = second n) then !(x i) else x i
  invFun x i := if b = true ∧ (i = 0 ∨ i = second n) then !(x i) else x i
  left_inv x := by
    funext i
    by_cases h : b = true ∧ (i = 0 ∨ i = second n)
    · simp only [ite_eq_left h, Bool.not_not]
    · simp only [ite_eq_right h]
  right_inv x := by
    funext i
    by_cases h : b = true ∧ (i = 0 ∨ i = second n)
    · simp only [ite_eq_left h, Bool.not_not]
    · simp only [ite_eq_right h]

private theorem complementLeadingPair_twice {n : ℕ} (b : Bool) (x : Q (n + 2)) :
    complementLeadingPair b (complementLeadingPair b x) = x :=
  (complementLeadingPair b).left_inv x

private theorem complementLeadingPair_flip {n : ℕ} (b : Bool) (x : Q (n + 2)) (i : Fin (n + 2)) :
    complementLeadingPair b (flip x i) = flip (complementLeadingPair b x) i := by
  funext j
  by_cases hj : j = i
  · subst j
    simp only [complementLeadingPair, Equiv.coe_fn_mk, flip_apply_same]
    by_cases h : b = true ∧ (i = 0 ∨ i = second n)
    · simp only [ite_eq_left h, Bool.not_not]
    · simp only [ite_eq_right h]
  · simp only [complementLeadingPair, Equiv.coe_fn_mk, BalancedCriticalSpectrum.flip,
      Function.update_of_ne hj]

private theorem complementLeadingPair_pairVertex {n : ℕ} (b u v : Bool) (t : Q n) :
    complementLeadingPair b (pairVertex (u, v, t)) =
      pairVertex ((if b then !u else u), (if b then !v else v), t) := by
  change complementLeadingPair b (Fin.cons u (Fin.cons v t)) =
    Fin.cons (if b then !u else u) (Fin.cons (if b then !v else v) t)
  funext i
  induction i using Fin.cases with
  | zero => simp [complementLeadingPair]
  | succ i =>
      induction i using Fin.cases with
      | zero => simp [complementLeadingPair]
      | succ i =>
          have hn : i.succ.succ ≠ second n := fun h => Fin.succ_ne_zero i (Fin.succ_inj.mp h)
          simp only [complementLeadingPair, Equiv.coe_fn_mk, Fin.succ_ne_zero, hn,
            or_false, and_false, ite_false, Fin.cons_succ]

/-- Complementing both swapped axes preserves the ordinary transposition. -/
private theorem complementLeadingPair_commute_swap {n : ℕ} (b : Bool) (x : Q (n + 2)) :
    complementLeadingPair b (leadingSwap x) = leadingSwap (complementLeadingPair b x) := by
  obtain ⟨⟨u, v, t⟩, rfl⟩ := (pairVertex (n := n)).surjective x
  simp only [leadingSwap_pairVertex, complementLeadingPair_pairVertex]

private theorem mem_image_complementLeadingPair {n : ℕ} {C : Finset (Q (n + 2))}
    (b : Bool) (x : Q (n + 2)) :
    x ∈ C.image (complementLeadingPair b) ↔ complementLeadingPair b x ∈ C := by
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simpa only [complementLeadingPair_twice] using hy
  · intro hx
    exact Finset.mem_image.mpr ⟨_, hx, complementLeadingPair_twice b x⟩

private theorem balanced_image_complementLeadingPair {n : ℕ} {C : Finset (Q (n + 2))}
    (b : Bool) (hC : IsBalanced C) : IsBalanced (C.image (complementLeadingPair b)) := by
  let g := complementLeadingPair (n := n) b
  obtain ⟨theta, ht, he, _⟩ :=
    exists_signed_covariance g (Equiv.refl _) (complementLeadingPair_flip b)
  obtain ⟨sigma, hs⟩ := hC
  refine ⟨fun x => theta (g x) * sigma (g x), ?_, ?_⟩
  · intro x hx
    have hsx := switching_sq hs ((mem_image_complementLeadingPair b x).mp hx)
    change sigma (g x) ^ 2 = 1 at hsx
    exact sq_eq_one_iff.mp (by rw [mul_pow, (sq_eq_one_iff.mpr (ht (g x))), hsx, mul_one])
  · intro x hx y hy hxy
    obtain ⟨i, rfl⟩ := adjacent_exists_flip hxy
    have hflip : g (flip x i) = flip (g x) i := complementLeadingPair_flip b x i
    have hAdj : (hypercube (n + 2)).Adj (g x) (g (flip x i)) := by
      rw [hflip]
      exact flip_adj _ _
    have hcov := he (g x) i
    rw [← hflip,
      show g (g x) = x from complementLeadingPair_twice b x,
      show g (g (flip x i)) = flip x i from complementLeadingPair_twice b (flip x i)] at hcov
    rw [hcov, hs.2 _ ((mem_image_complementLeadingPair b x).mp hx) _
      ((mem_image_complementLeadingPair b (flip x i)).mp hy) hAdj]
    ring

/-- A preconnected balanced support invariant under the leading swap omits an entire
fixed corner fibre. Complementing both leading bits when needed gives a balanced pair mask. -/
theorem exists_cubeMask_of_leadingSwap {C : Finset (Q 9)} (hC : IsBalanced C)
    (hS : ∀ x ∈ C, leadingSwap x ∈ C)
    (hconn : ((hypercube 9).induce (C : Set (Q 9))).Preconnected) :
    ∃ (b : Bool) (M S : Set (Q 7)),
      (∀ t : Q 7, pairVertex (!b, !b, t) ∉ C) ∧
      (C.image (complementLeadingPair b) : Set (Q 9)) = cubeMask M S ∧
        IsBalanced (C.image (complementLeadingPair b)) := by
  classical
  have hEmpty : ∃ b : Bool, ∀ t : Q 7, pairVertex (!b, !b, t) ∉ C := by
    by_cases h00 : ∃ u : Q 7, pairVertex (false, false, u) ∈ C
    · obtain ⟨u, hu⟩ := h00
      exact ⟨false, fun v hv =>
        not_reachable_of_leadingSwap_opposite_corners hC hS hu hv (hconn _ _)⟩
    · exact ⟨true, fun t ht => h00 ⟨t, ht⟩⟩
  obtain ⟨b, hb⟩ := hEmpty
  let M : Set (Q 7) := {t | complementLeadingPair b (pairVertex (false, false, t)) ∈ C}
  let S : Set (Q 7) := {t | complementLeadingPair b (pairVertex (true, false, t)) ∈ C}
  refine ⟨b, M, S, hb, ?_, balanced_image_complementLeadingPair b hC⟩
  apply Set.ext
  intro x
  obtain ⟨⟨u, v, t⟩, rfl⟩ := (pairVertex (n := 7)).surjective x
  simp only [Finset.mem_coe, mem_image_complementLeadingPair, cubeMask,
    Set.mem_preimage, Equiv.symm_apply_apply]
  cases u <;> cases v
  · rfl
  · change complementLeadingPair b (pairVertex (false, true, t)) ∈ C ↔
      complementLeadingPair b (pairVertex (true, false, t)) ∈ C
    constructor <;> intro ht <;>
      simpa only [← complementLeadingPair_commute_swap, leadingSwap_pairVertex] using hS _ ht
  · rfl
  · change complementLeadingPair b (pairVertex (true, true, t)) ∈ C ↔ False
    rw [complementLeadingPair_pairVertex]
    exact iff_false_intro (by cases b <;> exact hb t)

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedSwapNormalForm
