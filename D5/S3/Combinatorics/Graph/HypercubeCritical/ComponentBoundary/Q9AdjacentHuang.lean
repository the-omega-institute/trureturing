/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9AdjacentHuang
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9AdjacentHuang
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Every adjacent Hamming cut intertwines the full signed Huang action. -/

import Archive.Sensitivity
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang
import D5.S3.Combinatorics.Graph.HypercubeCritical.SixtySixPointSupport.WeightLayerParity
import Batteries.Tactic.OpenPrivate

/-! Two-step cancellation between distinct Hamming ranks isolates each adjacent cut.
For Hong–Wu–Xia Problem 2, this gives a solution of the eigenvalue equation on
each cut of a switched cubic support, including the zero vector. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9AdjacentHuang

open BalancedCriticalSpectrum (Q flip)
open scoped Matrix
open Q9IsotropicHuang
  (weightedLinear weightedAction flipSign weightedLinear_apply weightedLinear_square)
open private flipSign_cast from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang
open private weight_flip trueDirections from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixtySixPointSupport.WeightLayerParity
open private huangMatrix_symmetric from D5.S3.Combinatorics.Graph.HypercubeSubQuorum

private abbrev rank (x : Q 9) : ℤ := booleanWeight x

private theorem flip_rank_eq (x : Q 9) (i : Fin 9) :
    rank (flip x i) = if x i = true then rank x - 1 else rank x + 1 := by
  change (↑(booleanWeight (flip x i)) : ℤ) =
    if x i = true then (↑(booleanWeight x) : ℤ) - 1 else (↑(booleanWeight x) : ℤ) + 1
  rw [weight_flip]
  by_cases hi : x i = true
  · have hm : i ∈ trueDirections x := by simp [trueDirections, hi]
    have hp : 0 < booleanWeight x := Finset.card_pos.mpr ⟨i, hm⟩
    simp only [hi, ite_true]
    omega
  · simp [hi]

private theorem flip_rank (x : Q 9) (i : Fin 9) :
    rank (flip x i) = rank x - 1 ∨ rank (flip x i) = rank x + 1 := by
  rw [flip_rank_eq]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Retain the coordinates of a cube function on a single Hamming rank.
Integer indices make the projection at any negative rank the zero map. -/
def rankProjection {R : Type*} [CommRing R] (k : ℤ) : Module.End R (Q 9 → R) :=
  LinearMap.pi fun x => if rank x = k then LinearMap.proj x else 0

private theorem rankProjection_apply {R : Type*} [CommRing R]
    (k : ℤ) (f : Q 9 → R) (x : Q 9) :
    rankProjection k f x = if rank x = k then f x else 0 := by
  change (if rank x = k then LinearMap.proj x else 0) f = _
  split <;> rfl

local notation "P" => rankProjection

private theorem rankProjection_mul_ne {R : Type*} [CommRing R] {a c : ℤ}
    (hac : a ≠ c) : P a * P c = (0 : Module.End R (Q 9 → R)) := by
  apply LinearMap.ext
  intro f
  funext x
  change P a (P c f) x = 0
  by_cases hx : rank x = a
  · simp [rankProjection_apply, hx, hac]
  · simp [rankProjection_apply, hx]

private theorem action_to_adjacent {R : Type*} [CommRing R]
    (w : Fin 9 → R) (c : ℤ) :
    weightedLinear w * P c = (P (c - 1) + P (c + 1)) * (weightedLinear w * P c) := by
  apply LinearMap.ext
  intro f
  funext x
  change weightedLinear w (P c f) x =
    P (c - 1) (weightedLinear w (P c f)) x + P (c + 1) (weightedLinear w (P c f)) x
  simp only [rankProjection_apply]
  by_cases hlo : rank x = c - 1
  · simp [hlo, show c - 1 ≠ c + 1 by omega]
  by_cases hhi : rank x = c + 1
  · simp [hhi, show c + 1 ≠ c - 1 by omega]
  simp only [hlo, hhi, ite_false, add_zero, weightedLinear_apply, weightedAction]
  apply Finset.sum_eq_zero
  intro i _
  have hne : rank (flip x i) ≠ c := by
    have := flip_rank x i
    omega
  simp [rankProjection_apply, hne]

private theorem action_from_adjacent {R : Type*} [CommRing R]
    (w : Fin 9 → R) (a : ℤ) :
    P a * weightedLinear w = (P a * weightedLinear w) * (P (a - 1) + P (a + 1)) := by
  apply LinearMap.ext
  intro f
  funext x
  change P a (weightedLinear w f) x =
    P a (weightedLinear w (P (a - 1) f + P (a + 1) f)) x
  by_cases hx : rank x = a
  · simp only [rankProjection_apply, hx, ite_true, weightedLinear_apply, weightedAction,
      Pi.add_apply]
    apply Finset.sum_congr rfl
    intro i _
    rcases flip_rank x i with hi | hi
    · simp [hi, hx, show a - 1 ≠ a + 1 by omega]
    · simp [hi, hx, show a + 1 ≠ a - 1 by omega]
  · simp [rankProjection_apply, hx]

private theorem action_off_adjacent {R : Type*} [CommRing R]
    (w : Fin 9 → R) {a c : ℤ} (hlo : a ≠ c - 1) (hhi : a ≠ c + 1) :
    P a * (weightedLinear w * P c) = 0 := by
  rw [action_to_adjacent w c, ← mul_assoc, mul_add,
    rankProjection_mul_ne hlo, rankProjection_mul_ne hhi, add_zero, zero_mul]

private theorem action_two_step_cancel {R : Type*} [CommRing R] (w : Fin 9 → R)
    {a b c : ℤ} (hab : a = b - 1 ∨ a = b + 1) (hbc : b = c - 1 ∨ b = c + 1)
    (hac : a ≠ c) :
    P a * (weightedLinear w * (P b * (weightedLinear w * P c))) = 0 := by
  let H := weightedLinear w
  change P a * (H * (P b * (H * P c))) = 0
  have hs : P a * (H * (H * P c)) = 0 := by
    rw [← mul_assoc H H, weightedLinear_square, smul_mul_assoc, one_mul,
      mul_smul_comm, rankProjection_mul_ne hac, smul_zero]
  have hd := action_to_adjacent w c
  change H * P c = (P (c - 1) + P (c + 1)) * (H * P c) at hd
  conv at hs => lhs; arg 2; arg 2; rw [hd]
  rw [add_mul, mul_add, mul_add] at hs
  rcases hbc with rfl | rfl
  · have hz : P a * (H * (P (c + 1) * (H * P c))) = 0 := by
      have hoff := action_off_adjacent w (a := a) (c := c + 1) (by omega) (by omega)
      calc
        _ = (P a * (weightedLinear w * P (c + 1))) * (H * P c) := by
          simp only [mul_assoc, H]
        _ = 0 := by rw [hoff, zero_mul]
    rwa [hz, add_zero] at hs
  · have hz : P a * (H * (P (c - 1) * (H * P c))) = 0 := by
      have hoff := action_off_adjacent w (a := a) (c := c - 1) (by omega) (by omega)
      calc
        _ = (P a * (weightedLinear w * P (c - 1))) * (H * P c) := by
          simp only [mul_assoc, H]
        _ = 0 := by rw [hoff, zero_mul]
    rwa [hz, zero_add] at hs

/-- The part of the weighted Huang operator using the edges from rank k
to rank k+1 and back. -/
def cutAction {R : Type*} [CommRing R] (w : Fin 9 → R) (k : ℤ) :
    Module.End R (Q 9 → R) :=
  P k * weightedLinear w * P (k + 1) + P (k + 1) * weightedLinear w * P k

private theorem action_cut_block_commute {R : Type*} [CommRing R] (w : Fin 9 → R)
    {b c : ℤ} (hbc : b = c - 1 ∨ b = c + 1) :
    weightedLinear w * (P b * (weightedLinear w * P c)) =
    P c * (weightedLinear w * (P b * weightedLinear w)) := by
  let H := weightedLinear w
  change H * (P b * (H * P c)) = P c * (H * (P b * H))
  have hto : H * P b = (P (b - 1) + P (b + 1)) * (H * P b) := action_to_adjacent w b
  have hfrom : P b * H = (P b * H) * (P (b - 1) + P (b + 1)) := action_from_adjacent w b
  have hl : H * (P b * (H * P c)) = P c * (H * (P b * (H * P c))) := by
    calc
      _ = (H * P b) * (H * P c) := (mul_assoc H (P b) (H * P c)).symm
      _ = P (b - 1) * (H * (P b * (H * P c))) +
          P (b + 1) * (H * (P b * (H * P c))) := by
        rw [hto]
        simp only [add_mul, mul_assoc]
      _ = _ := by
        rcases hbc with hbc | hbc
        · rw [action_two_step_cancel w (Or.inl rfl) (Or.inl hbc) (by omega),
            zero_add, show b + 1 = c by omega]
        · rw [action_two_step_cancel w (Or.inr rfl) (Or.inr hbc) (by omega),
            add_zero, show b - 1 = c by omega]
  have hr : P c * (H * (P b * H)) = P c * (H * (P b * (H * P c))) := by
    conv_lhs => arg 2; arg 2; rw [hfrom]
    rw [mul_add, mul_add, mul_add, mul_assoc (P b), mul_assoc (P b)]
    rcases hbc with hbc | hbc
    · rw [action_two_step_cancel w (Or.inr (by omega)) (Or.inr (by omega))
        (show c ≠ b - 1 by omega), zero_add, show b + 1 = c by omega]
    · rw [action_two_step_cancel w (Or.inl (by omega)) (Or.inl (by omega))
        (show c ≠ b + 1 by omega), add_zero, show b - 1 = c by omega]
  exact hl.trans hr.symm

/-- Each adjacent cut operator commutes with the full weighted Huang operator.
The only terms leaving the two ranks cancel through the square of the full action. -/
theorem cutAction_commutes {R : Type*} [CommRing R] (w : Fin 9 → R) (k : ℤ) :
    weightedLinear w * cutAction w k = cutAction w k * weightedLinear w := by
  simp only [cutAction, mul_add, add_mul, mul_assoc]
  rw [action_cut_block_commute w (b := k) (c := k + 1) (Or.inl (by omega)),
    action_cut_block_commute w (b := k + 1) (c := k) (Or.inr rfl), add_comm]

/-- Applying a single adjacent cut to an eigenvector preserves its eigenvalue
and produces a vector supported on the two ranks of that cut. -/
theorem cutAction_eigenvector {R : Type*} [CommRing R] (w : Fin 9 → R)
    (k : ℤ) (f : Q 9 → R) (s : R) (hf : weightedLinear w f = s • f) :
    weightedLinear w (cutAction w k f) = s • cutAction w k f ∧
      ∀ x, (booleanWeight x : ℤ) ≠ k → (booleanWeight x : ℤ) ≠ k + 1 →
        cutAction w k f x = 0 := by
  constructor
  · have h := congrArg (fun A : Module.End R (Q 9 → R) => A f) (cutAction_commutes w k)
    change weightedLinear w (cutAction w k f) = cutAction w k (weightedLinear w f) at h
    rw [h, hf, map_smul]
  · intro x hlo hhi
    change P k (weightedLinear w (P (k + 1) f)) x + P (k + 1) (weightedLinear w (P k f)) x = 0
    simp [rankProjection_apply, hlo, hhi]

private theorem action_dot {R : Type*} [CommRing R] (w : Fin 9 → R) (f g : Q 9 → R) :
    f ⬝ᵥ weightedLinear w g = weightedLinear w f ⬝ᵥ g := by
  simp only [dotProduct, weightedLinear_apply, weightedAction, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  let flipEquiv : Q 9 ≃ Q 9 :=
    ⟨(flip · i), (flip · i), fun x => BalancedCriticalSpectrum.flip_flip x i,
      fun x => BalancedCriticalSpectrum.flip_flip x i⟩
  conv_rhs => rw [← flipEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  have hsign : flipSign i (flip x i) = flipSign i x := by
    apply Int.cast_injective (α := ℝ)
    rw [flipSign_cast, flipSign_cast, BalancedCriticalSpectrum.flip_flip, huangMatrix_symmetric]
  change f x * (w i * (flipSign i x : R) * g (flip x i)) =
    w i * (flipSign i (flip x i) : R) * f (flip (flip x i) i) * g (flip x i)
  rw [hsign, BalancedCriticalSpectrum.flip_flip]
  ac_rfl

private theorem rankProjection_dot {R : Type*} [CommRing R]
    (k : ℤ) (f g : Q 9 → R) : P k f ⬝ᵥ g = f ⬝ᵥ P k g := by
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : rank x = k <;> simp [rankProjection_apply, hx]

private theorem rankProjection_idem_apply {R : Type*} [CommRing R]
    (k : ℤ) (f : Q 9 → R) : P k (P k f) = P k f := by
  funext x
  by_cases hx : rank x = k <;> simp [rankProjection_apply, hx]

/-- Count each supported edge across the cut once at its rank-`k` endpoint. -/
def cutEdgeCount (S : Finset (Q 9)) (k : ℤ) : ℕ :=
  ∑ x ∈ S, ∑ i : Fin 9,
    if rank x = k ∧ rank (flip x i) = k + 1 ∧ flip x i ∈ S then 1 else 0

private theorem cut_dot_eq_card (k : ℤ) (S : Finset (Q 9)) (f : Q 9 → ℤ)
    (hzero : ∀ x ∉ S, f x = 0)
    (hcohere : ∀ x ∈ S, ∀ i, flip x i ∈ S →
      f x * flipSign i x * f (flip x i) = 1) :
    f ⬝ᵥ P k (weightedLinear (fun _ => 1) (P (k + 1) f)) = (cutEdgeCount S k : ℤ) := by
  simp only [dotProduct, rankProjection_apply, weightedLinear_apply, weightedAction, one_mul,
    cutEdgeCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have hrestrict (p : Q 9 → ℤ) :
      (∑ x, f x * p x) = ∑ x ∈ S, f x * p x :=
    (Finset.sum_subset (Finset.subset_univ S) fun x _ hx => by simp [hzero x hx]).symm
  rw [hrestrict]
  apply Finset.sum_congr rfl
  intro x hxS
  by_cases hx : rank x = k
  · simp only [hx, ite_true, true_and, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hy : rank (flip x i) = k + 1
    · by_cases hm : flip x i ∈ S
      · simpa only [hy, hm, and_self, ite_true, mul_assoc, Int.cast_id] using hcohere x hxS i hm
      · simp [hy, hm, hzero _ hm]
    · simp [hy]
  · simp [hx]

/-- Each rank of the cut vector has energy three times the number of induced
edges in the cut of a coherent integral switching with eigenvalue three. -/
theorem cutAction_edge_energy (k : ℤ) (S : Finset (Q 9)) (f : Q 9 → ℤ)
    (hzero : ∀ x ∉ S, f x = 0)
    (hcohere : ∀ x ∈ S, ∀ i, flip x i ∈ S →
      f x * flipSign i x * f (flip x i) = 1)
    (hf : weightedLinear (fun _ => 1) f = (3 : ℤ) • f) :
    let g := cutAction (fun _ => 1) k f
    (P k g ⬝ᵥ P k g) = 3 * (cutEdgeCount S k : ℤ) ∧
      (P (k + 1) g ⬝ᵥ P (k + 1) g) = 3 * (cutEdgeCount S k : ℤ) := by
  let H := weightedLinear (fun _ => (1 : ℤ))
  let part (a b : ℤ) := P a (H (P b f))
  have hproject (a b : ℤ) : P a (part a b) = part a b :=
    rankProjection_idem_apply a _
  have hswap {a b : ℤ} (hab : a = b - 1 ∨ a = b + 1) :
      H (part a b) = (3 : ℤ) • part b a := by
    have h := congrArg (fun A : Module.End ℤ (Q 9 → ℤ) => A f)
      (action_cut_block_commute (fun _ => 1) hab)
    change H (part a b) = P b (H (P a (H f))) at h
    rw [h, show H f = _ from hf, map_smul, map_smul, map_smul]
  have hdot (a b : ℤ) : f ⬝ᵥ part a b = f ⬝ᵥ part b a := by
    change f ⬝ᵥ P a (H (P b f)) = f ⬝ᵥ P b (H (P a f))
    rw [← rankProjection_dot, ← rankProjection_dot, action_dot, dotProduct_comm]
  have henergy {a b : ℤ} (hab : a = b - 1 ∨ a = b + 1) :
      part a b ⬝ᵥ part a b = 3 * (f ⬝ᵥ part a b) := by
    calc
      _ = P a (part a b) ⬝ᵥ H (P b f) := (rankProjection_dot a _ _).symm
      _ = H (part a b) ⬝ᵥ P b f := by rw [hproject, action_dot]
      _ = 3 * (f ⬝ᵥ part b a) := by
        rw [hswap hab, smul_dotProduct, ← rankProjection_dot b (part b a) f,
          hproject, dotProduct_comm (part b a) f]
        rfl
      _ = _ := by rw [hdot b a]
  have hpart {a b : ℤ} (hab : a ≠ b) :
      P a (part a b + part b a) = part a b := by
    rw [map_add, hproject]
    have hzeroPart := congrArg (fun A : Module.End ℤ (Q 9 → ℤ) => A (H (P a f)))
      (rankProjection_mul_ne hab)
    change P a (part b a) = 0 at hzeroPart
    rw [hzeroPart, add_zero]
  change P k (part k (k + 1) + part (k + 1) k) ⬝ᵥ
      P k (part k (k + 1) + part (k + 1) k) = _ ∧
    P (k + 1) (part k (k + 1) + part (k + 1) k) ⬝ᵥ
      P (k + 1) (part k (k + 1) + part (k + 1) k) = _
  have hm : f ⬝ᵥ part k (k + 1) = (cutEdgeCount S k : ℤ) :=
    cut_dot_eq_card k S f hzero hcohere
  constructor
  · rw [hpart (show k ≠ k + 1 by omega), henergy (Or.inl (by omega)), hm]
  · rw [add_comm (part k (k + 1)), hpart (show k + 1 ≠ k by omega),
      henergy (Or.inr rfl), hdot (k + 1) k, hm]

private theorem flipSign_mod_two {n : ℕ} (i : Fin n) (x : Q n) :
    (flipSign i x : ZMod 2) = 1 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero => simp [flipSign]
    | succ i =>
      change (((if x 0 then 1 else -1) * flipSign i (Sensitivity.π x) : ℤ) : ZMod 2) = 1
      rw [Int.cast_mul, ih, mul_one]
      cases x 0 <;> decide

private theorem action_lower_rank_ones_mod_two {k : ℤ} {x : Q 9} (hx : rank x = k) :
    ((weightedLinear (fun _ => (1 : ℤ)) (P (k - 1) (fun _ => 1)) x : ℤ) : ZMod 2) =
      (k : ZMod 2) := by
  rw [weightedLinear_apply]
  have hselect (i : Fin 9) : rank (flip x i) = k - 1 ↔ x i = true := by
    rw [flip_rank_eq, hx]
    by_cases hi : x i = true
    · simp [hi]
    · simp [hi, show k + 1 ≠ k - 1 by omega]
  simp only [weightedAction, one_mul, rankProjection_apply, Int.cast_sum, Int.cast_mul,
    Int.cast_id, flipSign_mod_two, hselect, Int.cast_ite, Int.cast_zero, Int.cast_one]
  rw [← Finset.sum_filter]
  change (∑ _i ∈ trueDirections x, (1 : ZMod 2)) = (k : ZMod 2)
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, ← hx]
  simp [booleanWeight]

private theorem odd_rank_energy_even (k : ℤ) (hk : Odd k) (v : Q 9 → ℤ)
    (hv : P k v = v)
    (hboundary : P (k - 1) (weightedLinear (fun _ => (1 : ℤ)) v) = 0) :
    Even (v ⬝ᵥ v) := by
  let H := weightedLinear (fun _ => (1 : ℤ))
  let lowerOnes : Q 9 → ℤ := P (k - 1) (fun _ => 1)
  have hdot : H lowerOnes ⬝ᵥ v = 0 := by
    rw [← action_dot]
    change P (k - 1) (fun _ => 1) ⬝ᵥ H v = 0
    rw [rankProjection_dot, hboundary, dotProduct_zero]
  have hreduce := congrArg (fun n : ℤ => (n : ZMod 2)) hdot
  apply ZMod.intCast_eq_zero_iff_even.mp
  change (↑(v ⬝ᵥ v) : ZMod 2) = 0
  change (↑(H lowerOnes ⬝ᵥ v) : ZMod 2) = 0 at hreduce
  simp only [dotProduct, Int.cast_sum, Int.cast_mul] at hreduce ⊢
  calc
    _ = ∑ x, (↑(H lowerOnes x) : ZMod 2) * (v x : ZMod 2) := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : rank x = k
      · rw [action_lower_rank_ones_mod_two hx, hk.intCast_zmod_two, one_mul]
        generalize (v x : ZMod 2) = t
        fin_cases t
        · exact zero_mul (0 : ZMod 2)
        · exact one_mul (1 : ZMod 2)
      · have hval := congrFun hv x
        simp only [rankProjection_apply, hx, ite_false] at hval
        simp [← hval]
    _ = 0 := hreduce

/-- Every odd lower rank has an even number of induced cut edges in a coherent
integral Huang switching with eigenvalue three. Summing the exterior equations
modulo two counts each lower-rank vertex once per occupied coordinate. -/
theorem cutAction_odd_cut_even_edges (k : ℤ) (hk : Odd k) (S : Finset (Q 9))
    (f : Q 9 → ℤ) (hzero : ∀ x ∉ S, f x = 0)
    (hcohere : ∀ x ∈ S, ∀ i, flip x i ∈ S →
      f x * flipSign i x * f (flip x i) = 1)
    (hf : weightedLinear (fun _ => 1) f = (3 : ℤ) • f) :
    Even (cutEdgeCount S k) := by
  let H := weightedLinear (fun _ => (1 : ℤ))
  let v := P k (cutAction (fun _ => (1 : ℤ)) k f)
  have hpart : v = P k (H (P (k + 1) f)) := by
    change P k (P k (H (P (k + 1) f)) + P (k + 1) (H (P k f))) = _
    rw [map_add, rankProjection_idem_apply]
    have hz := congrArg (fun A : Module.End ℤ (Q 9 → ℤ) => A (H (P k f)))
      (rankProjection_mul_ne (show k ≠ k + 1 by omega))
    change P k (P (k + 1) (H (P k f))) = 0 at hz
    rw [hz, add_zero]
  have hboundary : P (k - 1) (H v) = 0 := by
    rw [hpart]
    exact congrArg (fun A : Module.End ℤ (Q 9 → ℤ) => A f)
      (action_two_step_cancel (fun _ => 1) (Or.inl rfl)
        (Or.inl (show k = k + 1 - 1 by omega)) (show k - 1 ≠ k + 1 by omega))
  have heven := odd_rank_energy_even k hk v (rankProjection_idem_apply k _) hboundary
  have henergy : v ⬝ᵥ v = 3 * (cutEdgeCount S k : ℤ) :=
    (cutAction_edge_energy k S f hzero hcohere hf).1
  rw [henergy] at heven
  apply ZMod.natCast_eq_zero_iff_even.mp
  simpa only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
    show (3 : ZMod 2) = 1 by decide, one_mul] using heven.intCast_zmod_two

/--
info: 'D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9AdjacentHuang.cutAction_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms cutAction_commutes

/--
info: 'D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9AdjacentHuang.cutAction_eigenvector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms cutAction_eigenvector

/--
info: 'D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9AdjacentHuang.cutAction_edge_energy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms cutAction_edge_energy

/--
info: 'D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9AdjacentHuang.cutAction_odd_cut_even_edges' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms cutAction_odd_cut_even_edges

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9AdjacentHuang
