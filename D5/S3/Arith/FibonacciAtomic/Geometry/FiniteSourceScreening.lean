/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.Positive]
   utility: none
   digest: The counting resolvent is identified with the centered Gram screening formula once the actual finite tree energy bridge is supplied. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceCovariance
import Mathlib.Analysis.InnerProductSpace.Positive

/-! The exact finite counting-screening identity is reduced to the actual source edge bridge. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceScreening

open ActualTreeReadoutAcquisition (Address)
open FiniteSourceHardy (H NodeL2)
open FiniteSourceMass (N)
open FiniteSourceCovariance (one v B Sigma)
open InnerProductSpace
open FiniteSourceMass (Node vertices μ)
open FiniteSourceHardy (Edge edges path value)
open MeasureTheory
open scoped BigOperators ENNReal

/-- Concrete potentials on every original occurrence, including the root. -/
abbrev Potential (n : ℕ) := Node n → ℝ

/-- The original root occurrence. -/
def rootNode (n : ℕ) : Node n := ⟨[], FiniteSourceMass.root_mem n⟩

/-- Concrete functions in the actual uniform node Hilbert space. -/
def nodeLp (n : ℕ) (f : Potential n) : NodeL2 n :=
  (MemLp.of_discrete : MemLp f 2 (μ n)).toLp f

private theorem edge_vertex (n : ℕ) (p : Edge) (hp : p ∈ edges n) :
    p.val ∈ vertices n := by
  simpa [edges] using hp

/-- The reached child of an original unit-conductance edge. -/
def child (n : ℕ) (p : Edge) (hp : p ∈ edges n) : Node n :=
  ⟨p.val, edge_vertex n p hp⟩

/-- The reached parent, with no additional edge incident to the root. -/
def parent (n : ℕ) (p : Edge) (hp : p ∈ edges n) : Node n :=
  ⟨p.val.dropLast, FiniteSourceCovariance.prefix_vertex n _ (child n p hp)
    p.val.dropLast_prefix⟩

/-- Parent-minus-child increments, zero on every absent common coordinate. -/
def gradient (n : ℕ) (f : Potential n) : H :=
  ∑ p ∈ edges n, lp.single 2 p
    (if hp : p ∈ edges n then f (parent n p hp) - f (child n p hp) else 0)

/-- Actual finite support in the fixed common edge space. -/
def Supported (n : ℕ) (z : H) : Prop := ∀ p, p ∉ edges n → z p = 0

private theorem gradient_apply (n : ℕ) (f : Potential n) (p : Edge) :
    gradient n f p =
      if hp : p ∈ edges n then f (parent n p hp) - f (child n p hp) else 0 := by
  classical
  simp [gradient, lp.coeFn_sum, lp.coeFn_single, Pi.single_apply, eq_comm]

private theorem gradient_supported (n : ℕ) (f : Potential n) :
    Supported n (gradient n f) := by
  intro p hp
  simp [gradient_apply, hp]

private theorem prefix_snoc (q s : Address) (b : Bool) :
    q.IsPrefix (s ++ [b]) ↔ q = s ++ [b] ∨ q.IsPrefix s := by
  constructor
  · intro h
    by_cases hlen : q.length ≤ s.length
    · right
      rw [List.prefix_iff_eq_take] at h ⊢
      simpa [List.take_append_of_le_length hlen] using h
    · left
      have he : q.length = (s ++ [b]).length := by
        have := h.length_le
        simp only [List.length_append, List.length_singleton] at *
        omega
      have ht := List.prefix_iff_eq_take.mp h
      simpa [he] using ht
  · rintro (rfl | h)
    · exact List.IsPrefix.refl _
    · exact h.trans (List.prefix_append _ _)

private theorem path_snoc (n : ℕ) (s : Address) (b : Bool)
    (hx : s ++ [b] ∈ vertices n) :
    path n 0 ⟨s ++ [b], hx⟩ =
      insert (⟨s ++ [b], by simp⟩ : Edge)
        (path n 0 ⟨s, FiniteSourceCovariance.prefix_vertex n s
          ⟨s ++ [b], hx⟩ (List.prefix_append _ _)⟩) := by
  classical
  ext q
  have hq : 0 < q.val.length := List.length_pos_of_ne_nil q.property
  simp only [path, Finset.mem_filter, Finset.mem_insert, hq, true_and,
    prefix_snoc, Subtype.ext_iff]
  constructor
  · rintro ⟨hqE, h | h⟩
    · exact Or.inl h
    · exact Or.inr ⟨hqE, h⟩
  · rintro (h | ⟨hqE, h⟩)
    · subst h
      exact ⟨by simpa [edges] using hx, Or.inl rfl⟩
    · exact ⟨hqE, Or.inr h⟩

private theorem value_snoc (n : ℕ) (s : Address) (b : Bool)
    (hx : s ++ [b] ∈ vertices n) (z : H) :
    value n 0 z ⟨s ++ [b], hx⟩ =
      value n 0 z ⟨s, FiniteSourceCovariance.prefix_vertex n s
        ⟨s ++ [b], hx⟩ (List.prefix_append _ _)⟩ + z ⟨s ++ [b], by simp⟩ := by
  classical
  have hnot : (⟨s ++ [b], by simp⟩ : Edge) ∉ path n 0
      ⟨s, FiniteSourceCovariance.prefix_vertex n s
        ⟨s ++ [b], hx⟩ (List.prefix_append _ _)⟩ := by
    intro h
    have hlen := (Finset.mem_filter.mp h).2.2.length_le
    simp at hlen
  unfold value
  rw [path_snoc, Finset.sum_insert hnot, add_comm]

private theorem value_root (n : ℕ) (z : H) : value n 0 z (rootNode n) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro p hp
  have h := (Finset.mem_filter.mp hp).2.2
  have : p.val = [] := List.prefix_nil.mp h
  exact False.elim (p.property this)

private theorem value_parent (n : ℕ) (p : Edge) (hp : p ∈ edges n) (z : H) :
    value n 0 z (child n p hp) = value n 0 z (parent n p hp) + z p := by
  obtain ⟨s, b, he⟩ : ∃ s b, p.val = s ++ [b] := by
    exact ⟨p.val.dropLast, p.val.getLast p.property,
      (List.dropLast_append_getLast p.property).symm⟩
  have hv := value_snoc n s b (he ▸ edge_vertex n p hp) z
  simpa [child, parent, he] using hv

private theorem path_gradient (n : ℕ) (f : Potential n) (x : Node n) :
    value n 0 (gradient n f) x = f (rootNode n) - f x := by
  obtain ⟨x, hx⟩ := x
  induction x using List.reverseRecOn with
  | nil => simpa [rootNode] using value_root n (gradient n f)
  | append_singleton s b ih =>
    have hs := FiniteSourceCovariance.prefix_vertex n s ⟨s ++ [b], hx⟩
      (List.prefix_append _ _)
    have hp : (⟨s ++ [b], by simp⟩ : Edge) ∈ edges n := by simpa [edges] using hx
    rw [value_snoc, ih hs, gradient_apply, dif_pos hp]
    simp only [parent, child, List.dropLast_concat]
    ring

/-- The root value minus the actual root-to-node path sum. -/
def reconstruct (n : ℕ) (c : ℝ) (z : H) : Potential n :=
  fun x => c - value n 0 z x

private theorem gradient_reconstruct (n : ℕ) (c : ℝ) (z : H)
    (hz : Supported n z) : gradient n (reconstruct n c z) = z := by
  ext p
  rw [gradient_apply]
  split_ifs with hp
  · dsimp [reconstruct]
    rw [value_parent]
    ring
  · exact (hz p hp).symm

private theorem inner_gradient (n : ℕ) (f : Potential n) (z : H) :
    inner ℝ (gradient n f) z =
      ∑ p ∈ edges n,
        (if hp : p ∈ edges n then f (parent n p hp) - f (child n p hp) else 0) * z p := by
  classical
  simp [gradient, sum_inner, lp.inner_single_left, real_inner_comm]

/-- The original counting Laplacian: each reached parent-child edge occurs once. -/
def countingLaplacian (n : ℕ) (f : Potential n) : Potential n := fun x =>
  ∑ p ∈ edges n, if hp : p ∈ edges n then
    (f (parent n p hp) - f (child n p hp)) *
      ((if x = parent n p hp then 1 else 0) - (if x = child n p hp then 1 else 0))
    else 0

private theorem counting_energy (n : ℕ) (f g : Potential n) :
    (∑ x, f x * countingLaplacian n g x) =
      inner ℝ (gradient n f) (gradient n g) := by
  classical
  simp only [countingLaplacian, Finset.mul_sum]
  rw [Finset.sum_comm, inner_gradient]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [dif_pos hp, gradient_apply]
  rw [dif_pos hp]
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

private theorem nodeLp_inner (n : ℕ) (f g : Potential n) :
    inner ℝ (nodeLp n f) (nodeLp n g) =
      (N n : ℝ)⁻¹ * ∑ x, f x * g x := by
  rw [L2.inner_def]
  have he : (fun x => inner ℝ (nodeLp n f x) (nodeLp n g x)) =ᵐ[μ n]
      (fun x => f x * g x) := by
    filter_upwards [(MemLp.of_discrete : MemLp f 2 (μ n)).coeFn_toLp,
      (MemLp.of_discrete : MemLp g 2 (μ n)).coeFn_toLp] with x hf hg
    change nodeLp n f x * nodeLp n g x = _
    rw [hf, hg]
  rw [integral_congr_ae he, integral_fintype Integrable.of_finite]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [measureReal_def, FiniteSourceMass.finite_source_masses.2.2.2.2.2.1]
  simp

private theorem nodeLp_reconstruct (n : ℕ) (c : ℝ) (z : H) :
    nodeLp n (reconstruct n c z) = c • one n - FiniteSourceHardy.J n z := by
  unfold nodeLp
  change _ = c • one n - FiniteSourceHardy.trace n 0 z
  unfold one FiniteSourceHardy.trace
  rw [← MemLp.toLp_const_smul, ← MemLp.toLp_sub]
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall fun x => by simp [reconstruct]

/-- Actual path reconstruction and unit-edge energy with the uniform/counting factor.
This applies to every source index, including both edge-free singleton sources. -/
theorem actual_reconstruction_energy (n : ℕ) :
    (∀ f : Potential n,
      reconstruct n (f (rootNode n)) (gradient n f) = f) ∧
    (∀ (c : ℝ) (z : H), Supported n z →
      gradient n (reconstruct n c z) = z) ∧
    (∀ f g : Potential n,
      (N n : ℝ) * inner ℝ (nodeLp n f) (nodeLp n (countingLaplacian n g)) =
        inner ℝ (gradient n f) (gradient n g)) ∧
    (∀ (c : ℝ) (z : H),
      nodeLp n (reconstruct n c z) = c • one n - FiniteSourceHardy.J n z) := by
  refine ⟨?_, gradient_reconstruct n, ?_, nodeLp_reconstruct n⟩
  · intro f
    funext x
    dsimp [reconstruct]
    rw [path_gradient]
    ring
  · intro f g
    rw [nodeLp_inner, ← mul_assoc, mul_inv_cancel₀ (by
      exact_mod_cast (FiniteSourceMass.N_pos n).ne'), one_mul, counting_energy]

/-! `unitInverse` keeps the inverse attached to the compiled `IsUnit` witness. -/
noncomputable def unitInverse {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →L[ℝ] E) (hA : IsUnit A) : E →L[ℝ] E := by
  letI := hA.invertible
  exact ⅟A

structure ActualBridge (n : ℕ) where
  /-- The closed counting-measure Laplacian on the actual occurrence nodes. -/
  L : NodeL2 n →L[ℝ] NodeL2 n
  /-- The counting-normalized root source vector. -/
  source : NodeL2 n
  /-- Root evaluation on actual node potentials. -/
  root : NodeL2 n →L[ℝ] ℝ
  /-- Every actual potential is its root value plus its supported edge increments. -/
  decompose : ∀ f : NodeL2 n, ∃ c : ℝ, ∃ z : H,
    f = c • one n - FiniteSourceHardy.J n z
  /-- The edge energy is the counting Laplacian form on the actual source. -/
  weak_energy : ∀ (c d : ℝ) (z w : H),
    inner ℝ (c • one n - FiniteSourceHardy.J n z)
      (L (d • one n - FiniteSourceHardy.J n w)) =
      inner ℝ z w
  /-- The actual counting Laplacian is symmetric. -/
  symmetric : ∀ f g : NodeL2 n, inner ℝ (L f) g = inner ℝ f (L g)
  /-- The counting Laplacian energy is nonnegative. -/
  positive : ∀ f : NodeL2 n, 0 ≤ inner ℝ (L f) f
  /-- Root evaluation of a reconstructed potential is its constant mode. -/
  root_decompose : ∀ (c : ℝ) (z : H),
    root (c • one n - FiniteSourceHardy.J n z) = c
  /-- The normalized counting source pairs with a reconstructed potential by its root value/N. -/
  source_pair : ∀ (c : ℝ) (z : H),
    inner ℝ source (c • one n - FiniteSourceHardy.J n z) = c / (N n : ℝ)
  /-- The positive screening operator is invertible on the full common edge space. -/
  screened_unit : ∀ (lam : ℝ), 0 < lam →
    IsUnit (ContinuousLinearMap.id ℝ H + ((N n : ℝ) * lam) • FiniteSourceCovariance.Sigma n)
  /-- Positive screening makes the actual node resolvent invertible. -/
  laplacian_unit : ∀ (lam : ℝ), 0 < lam →
    IsUnit (L + lam • (1 : NodeL2 n →L[ℝ] NodeL2 n))
  /-- The centered Gram operator has its covariance bilinear form. -/
  covariance_pair : ∀ (z w : H),
    inner ℝ z (FiniteSourceCovariance.Sigma n w) =
      inner ℝ (FiniteSourceHardy.J n z) (FiniteSourceHardy.J n w) -
        inner ℝ z (v n) * inner ℝ (v n) w

def root_response (n : ℕ) (D : ActualBridge n) (lam : ℝ) (hlam : 0 < lam) : ℝ :=
  D.root (unitInverse (D.L + lam • (1 : NodeL2 n →L[ℝ] NodeL2 n))
    (D.laplacian_unit lam hlam) D.source)

def screened_inverse (n : ℕ) (D : ActualBridge n) (lam : ℝ) (hlam : 0 < lam) : H →L[ℝ] H :=
  unitInverse (ContinuousLinearMap.id ℝ H + ((N n : ℝ) * lam) • FiniteSourceCovariance.Sigma n)
    (D.screened_unit lam hlam)

end D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceScreening
