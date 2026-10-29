/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceScreening
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.Positive]
   utility: none
   digest: Actual address gradients, counting energy and uniform node normalization. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceCovariance
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Topology.Algebra.Module.FiniteDimension

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
open scoped BigOperators ENNReal NNReal

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
  change (lp.evalCLM ℝ (fun _ : Edge => ℝ) 2 p)
    (∑ q ∈ edges n, lp.single 2 q
      (if hq : q ∈ edges n then f (parent n q hq) - f (child n q hq) else 0)) = _
  rw [map_sum]
  change (∑ q ∈ edges n, (lp.single 2 q
    (if hq : q ∈ edges n then f (parent n q hq) - f (child n q hq) else 0)) p) = _
  by_cases hp : p ∈ edges n <;> simp [Pi.single_apply, eq_comm, hp]

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
      rw [he, List.take_length] at ht
      exact ht
  · rintro (rfl | h)
    · exact List.prefix_refl _
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
    · exact ⟨by simpa [edges, h] using hx, Or.inl h⟩
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
  have ep : (⟨s ++ [b], by simp⟩ : Edge) = p := Subtype.ext he.symm
  simpa [child, parent, he, ep] using hv

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
  simp [gradient, sum_inner, lp.inner_single_left, mul_comm]

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
    have hf' : nodeLp n f x = f x := hf
    have hg' : nodeLp n g x = g x := hg
    simp [hf', hg', mul_comm]
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

private def nodeLinear (n : ℕ) : Potential n →ₗ[ℝ] NodeL2 n where
  toFun := nodeLp n
  map_add' f g := by
    unfold nodeLp
    rw [← MemLp.toLp_add]
  map_smul' c f := by
    unfold nodeLp
    rw [← MemLp.toLp_const_smul]
    rfl

private theorem nodeLinear_bijective (n : ℕ) : Function.Bijective (nodeLinear n) := by
  classical
  constructor
  · intro f g h
    funext x
    have he := congrArg (fun u : NodeL2 n =>
      inner ℝ u (nodeLp n (fun y => if y = x then 1 else 0))) h
    change inner ℝ (nodeLp n f) _ = inner ℝ (nodeLp n g) _ at he
    simp only [nodeLp_inner] at he
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true] at he
    exact mul_left_cancel₀ (inv_ne_zero (by exact_mod_cast (FiniteSourceMass.N_pos n).ne')) he
  · intro f
    refine ⟨fun x => f x, ?_⟩
    exact Lp.toLp_coeFn f MemLp.of_discrete

/-- The faithful uniform L2 representation of all concrete node functions. -/
def nodeEquiv (n : ℕ) : Potential n ≃L[ℝ] NodeL2 n :=
  (LinearEquiv.ofBijective (nodeLinear n) (nodeLinear_bijective n)).toContinuousLinearEquiv

private def laplacianLinear (n : ℕ) : Potential n →ₗ[ℝ] Potential n where
  toFun := countingLaplacian n
  map_add' f g := by
    classical
    funext x
    simp only [countingLaplacian, Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [dif_pos hp, RingHom.id_apply]
    ring
  map_smul' c f := by
    classical
    funext x
    simp only [countingLaplacian, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [dif_pos hp, RingHom.id_apply]
    ring

/-- The actual counting Laplacian transported to the uniform node Hilbert space. -/
def L (n : ℕ) : NodeL2 n →L[ℝ] NodeL2 n :=
  (nodeEquiv n).toContinuousLinearMap.comp
    ((laplacianLinear n).toContinuousLinearMap.comp (nodeEquiv n).symm.toContinuousLinearMap)

/-- Actual root evaluation, without killing or a boundary condition at the root. -/
def root (n : ℕ) : NodeL2 n →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (rootNode n)).comp (nodeEquiv n).symm.toContinuousLinearMap

/-- The counting root delta, represented in the uniform node space. -/
def source (n : ℕ) : NodeL2 n :=
  nodeLp n (fun x => if x = rootNode n then 1 else 0)

private theorem L_nodeLp (n : ℕ) (f : Potential n) :
    L n (nodeLp n f) = nodeLp n (countingLaplacian n f) := by
  change nodeEquiv n (laplacianLinear n ((nodeEquiv n).symm (nodeEquiv n f))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rfl

private theorem root_nodeLp (n : ℕ) (f : Potential n) :
    root n (nodeLp n f) = f (rootNode n) := by
  change ((nodeEquiv n).symm (nodeEquiv n f)) (rootNode n) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]

/-- The actual source has supported path coordinates and exact counting normalization. -/
theorem actual_screening_bridge (n : ℕ) :
    (∀ f : NodeL2 n, ∃ (c : ℝ) (z : H), Supported n z ∧
      f = c • one n - FiniteSourceHardy.J n z) ∧
    (∀ (c d : ℝ) (z w : H), Supported n z → Supported n w →
      (N n : ℝ) * inner ℝ (c • one n - FiniteSourceHardy.J n z)
        (L n (d • one n - FiniteSourceHardy.J n w)) = inner ℝ z w) ∧
    (∀ (c : ℝ) (z : H), root n (c • one n - FiniteSourceHardy.J n z) = c) ∧
    (∀ (c : ℝ) (z : H),
      inner ℝ (source n) (c • one n - FiniteSourceHardy.J n z) = c / (N n : ℝ)) := by
  have hr := actual_reconstruction_energy n
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f
    let g := (nodeEquiv n).symm f
    refine ⟨g (rootNode n), gradient n g, gradient_supported n g, ?_⟩
    rw [← hr.2.2.2, hr.1]
    exact (nodeEquiv n).apply_symm_apply f |>.symm
  · intro c d z w hz hw
    rw [← hr.2.2.2 c z, ← hr.2.2.2 d w, L_nodeLp, hr.2.2.1,
      hr.2.1 c z hz, hr.2.1 d w hw]
  · intro c z
    rw [← hr.2.2.2 c z, root_nodeLp]
    simp [reconstruct, value_root]
  · intro c z
    rw [← hr.2.2.2 c z]
    unfold source
    rw [nodeLp_inner]
    simp [ite_mul, reconstruct, value_root, div_eq_mul_inv, mul_comm]

/-! `unitInverse` keeps the inverse attached to the compiled `IsUnit` witness. -/
noncomputable def unitInverse {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →L[ℝ] E) (hA : IsUnit A) : E →L[ℝ] E := by
  letI := hA.invertible
  exact ⅟A

private theorem L_positive (n : ℕ) (f : NodeL2 n) :
    0 ≤ inner ℝ (L n f) f := by
  let g := (nodeEquiv n).symm f
  have hg : nodeLp n g = f := (nodeEquiv n).apply_symm_apply f
  have he := (actual_reconstruction_energy n).2.2.1 g g
  rw [← L_nodeLp, hg] at he
  rw [← real_inner_comm (L n f) f]
  have hn : 0 < (N n : ℝ) := by exact_mod_cast FiniteSourceMass.N_pos n
  have hp : 0 ≤ (N n : ℝ) * inner ℝ f (L n f) := by
    rw [he]
    exact real_inner_self_nonneg
  exact nonneg_of_mul_nonneg_left (by simpa only [mul_comm] using hp) hn

private theorem laplacian_unit (n : ℕ) (lam : ℝ) (hlam : 0 < lam) :
    IsUnit (L n + lam • (1 : NodeL2 n →L[ℝ] NodeL2 n)) := by
  apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map
    (𝕜 := ℝ) (L n + lam • (1 : NodeL2 n →L[ℝ] NodeL2 n))
    (c := ⟨lam, hlam.le⟩) (by exact hlam)
  intro f
  have hp := L_positive n f
  calc
    ‖f‖ ^ 2 * lam ≤
        inner ℝ ((L n + lam • (1 : NodeL2 n →L[ℝ] NodeL2 n)) f) f := by
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply, inner_add_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq]
      nlinarith
    _ ≤ ‖inner ℝ ((L n + lam • (1 : NodeL2 n →L[ℝ] NodeL2 n)) f) f‖ := le_abs_self _

private theorem covariance_pair (n : ℕ) (z w : H) :
    inner ℝ z (Sigma n w) =
      inner ℝ (FiniteSourceHardy.J n z) (FiniteSourceHardy.J n w) -
        inner ℝ z (v n) * inner ℝ (v n) w := by
  simp only [FiniteSourceCovariance.Sigma, B, ContinuousLinearMap.sub_apply, inner_sub_right,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    rankOne_apply, real_inner_smul_right]
  ring

private theorem Sigma_positive (n : ℕ) (z : H) :
    0 ≤ inner ℝ (Sigma n z) z := by
  rw [real_inner_comm, covariance_pair, real_inner_self_eq_norm_sq]
  have hc : ‖inner ℝ (one n) (FiniteSourceHardy.J n z)‖ ≤
      ‖one n‖ * ‖FiniteSourceHardy.J n z‖ := norm_inner_le_norm _ _
  rw [FiniteSourceCovariance.one_norm, one_mul] at hc
  have hv : inner ℝ (v n) z = inner ℝ (one n) (FiniteSourceHardy.J n z) := by
    exact ContinuousLinearMap.adjoint_inner_left _ _ _
  simp only [← real_inner_comm z (v n), hv]
  have hab : |inner ℝ (one n) (FiniteSourceHardy.J n z)| ≤ ‖FiniteSourceHardy.J n z‖ := hc
  have hs := (sq_le_sq₀ (abs_nonneg (inner ℝ (one n) (FiniteSourceHardy.J n z)))
    (norm_nonneg (FiniteSourceHardy.J n z))).2 hab
  rw [sq_abs] at hs
  nlinarith

private theorem screened_unit (n : ℕ) (lam : ℝ) (hlam : 0 < lam) :
    IsUnit (ContinuousLinearMap.id ℝ H + ((N n : ℝ) * lam) • Sigma n) := by
  apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map
    (𝕜 := ℝ) (ContinuousLinearMap.id ℝ H + ((N n : ℝ) * lam) • Sigma n)
    (c := 1) (by norm_num)
  intro z
  have hp := Sigma_positive n z
  have ht : 0 ≤ (N n : ℝ) * lam := mul_nonneg (Nat.cast_nonneg _) hlam.le
  calc
    ‖z‖ ^ 2 * (1 : ℝ≥0) ≤
        inner ℝ ((ContinuousLinearMap.id ℝ H + ((N n : ℝ) * lam) • Sigma n) z) z := by
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply, inner_add_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq, NNReal.coe_one, mul_one]
      exact le_add_of_nonneg_right (mul_nonneg ht hp)
    _ ≤ ‖inner ℝ ((ContinuousLinearMap.id ℝ H + ((N n : ℝ) * lam) • Sigma n) z) z‖ :=
      le_abs_self _

/-- Original counting root response, using the proved positive resolvent inverse. -/
def root_response (n : ℕ) (lam : ℝ) (hlam : 0 < lam) : ℝ :=
  root n (unitInverse (L n + lam • (1 : NodeL2 n →L[ℝ] NodeL2 n))
    (laplacian_unit n lam hlam) (source n))

/-- The genuine screening inverse on the full common edge Hilbert space. -/
def screened_inverse (n : ℕ) (lam : ℝ) (hlam : 0 < lam) : H →L[ℝ] H :=
  unitInverse (ContinuousLinearMap.id ℝ H + ((N n : ℝ) * lam) • Sigma n)
    (screened_unit n lam hlam)

private theorem inverse_apply (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →L[ℝ] E) (hA : IsUnit A) (x : E) :
    A (unitInverse A hA x) = x := by
  letI := hA.invertible
  change (A * ⅟A) x = x
  rw [mul_invOf_self]
  rfl

private theorem inverse_cancel (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →L[ℝ] E) (hA : IsUnit A) (x : E) :
    unitInverse A hA (A x) = x := by
  letI := hA.invertible
  change (⅟A * A) x = x
  rw [invOf_mul_self]
  rfl

private theorem reconstruction_energy (n : ℕ) (c : ℝ) (z : H) (g : Potential n) :
    (N n : ℝ) * inner ℝ (c • one n - FiniteSourceHardy.J n z)
      (L n (nodeLp n g)) = inner ℝ z (gradient n g) := by
  rw [← nodeLp_reconstruct, L_nodeLp, (actual_reconstruction_energy n).2.2.1]
  calc
    inner ℝ (gradient n (reconstruct n c z)) (gradient n g) =
        inner ℝ (gradient n g) (gradient n (reconstruct n c z)) := real_inner_comm _ _
    _ = inner ℝ (gradient n g) z := by
      rw [inner_gradient, inner_gradient]
      apply Finset.sum_congr rfl
      intro p hp
      simp only [gradient_apply, dite_eq_left hp, reconstruct]
      rw [value_parent n p hp z]
      ring
    _ = inner ℝ z (gradient n g) := real_inner_comm _ _

private theorem L_symmetric (n : ℕ) (f g : NodeL2 n) :
    inner ℝ (L n f) g = inner ℝ f (L n g) := by
  let a := (nodeEquiv n).symm f
  let b := (nodeEquiv n).symm g
  have ha : nodeLp n a = f := (nodeEquiv n).apply_symm_apply f
  have hb : nodeLp n b = g := (nodeEquiv n).apply_symm_apply g
  have he := (actual_reconstruction_energy n).2.2.1 a b
  have he' := (actual_reconstruction_energy n).2.2.1 b a
  rw [← L_nodeLp, ha, hb] at he he'
  apply mul_left_cancel₀ (show (N n : ℝ) ≠ 0 by
    exact_mod_cast (FiniteSourceMass.N_pos n).ne')
  calc
    (N n : ℝ) * inner ℝ (L n f) g =
        (N n : ℝ) * inner ℝ g (L n f) := by rw [real_inner_comm]
    _ = inner ℝ (gradient n b) (gradient n a) := he'
    _ = inner ℝ (gradient n a) (gradient n b) := real_inner_comm _ _
    _ = (N n : ℝ) * inner ℝ f (L n g) := he.symm

/-- The exact centered counting response for every original finite source. -/
theorem finite_source_screening (n : ℕ) (lam : ℝ) (hlam : 0 < lam) :
    root_response n lam hlam - 1 / ((N n : ℝ) * lam) =
      inner ℝ (v n) (screened_inverse n lam hlam (v n)) := by
  let τ : ℝ := (N n : ℝ) * lam
  have hτ : τ ≠ 0 := mul_ne_zero (by exact_mod_cast (FiniteSourceMass.N_pos n).ne') hlam.ne'
  let z : H := screened_inverse n lam hlam (v n)
  let c : ℝ := τ⁻¹ + inner ℝ (v n) z
  let f : NodeL2 n := c • one n - FiniteSourceHardy.J n z
  have hAz : z + τ • Sigma n z = v n := by
    exact inverse_apply H _ (screened_unit n lam hlam) (v n)
  have hτc : τ * c = 1 + τ * inner ℝ (v n) z := by
    dsimp [c]
    rw [mul_add, mul_inv_cancel₀ hτ]
  have hz : z = τ • (FiniteSourceHardy.J n).adjoint f := by
    calc
      z = v n - τ • Sigma n z := eq_sub_of_add_eq hAz
      _ = τ • (FiniteSourceHardy.J n).adjoint f := by
        dsimp [f]
        simp only [map_sub, map_smul, FiniteSourceCovariance.Sigma,
          ContinuousLinearMap.sub_apply, rankOne_apply, smul_sub, smul_smul]
        change v n - (τ • B n z - (τ * inner ℝ (v n) z) • v n) =
          (τ * c) • v n - τ • B n z
        rw [hτc, add_smul, one_smul]
        abel
  have ho : inner ℝ (one n) (one n) = 1 := by
    rw [real_inner_self_eq_norm_sq, FiniteSourceCovariance.one_norm]
    norm_num
  have hmean : inner ℝ f (one n) = τ⁻¹ := by
    rw [real_inner_comm]
    dsimp [f]
    rw [inner_sub_right, real_inner_smul_right, ho, mul_one]
    have hv : inner ℝ (one n) (FiniteSourceHardy.J n z) = inner ℝ (v n) z :=
      (ContinuousLinearMap.adjoint_inner_left _ _ _).symm
    rw [hv]
    dsimp [c]
    ring
  have hweak (g : Potential n) :
      (N n : ℝ) * inner ℝ f (L n (nodeLp n g)) +
        τ * inner ℝ f (nodeLp n g) = g (rootNode n) := by
    have hrec := (actual_reconstruction_energy n).1 g
    have hdec : nodeLp n g =
        g (rootNode n) • one n - FiniteSourceHardy.J n (gradient n g) := by
      exact (congrArg (nodeLp n) hrec).symm.trans (nodeLp_reconstruct n _ _)
    have he := reconstruction_energy n c z g
    change (N n : ℝ) * inner ℝ f (L n (nodeLp n g)) = _ at he
    have hedge : inner ℝ z (gradient n g) =
        τ * inner ℝ f (FiniteSourceHardy.J n (gradient n g)) := by
      rw [hz, real_inner_smul_left, ContinuousLinearMap.adjoint_inner_left]
    rw [he, hdec, inner_sub_right, real_inner_smul_right, hmean, hedge]
    field_simp [hτ]
    <;> ring
  have hsol : (L n + lam • (1 : NodeL2 n →L[ℝ] NodeL2 n)) f = source n := by
    apply ext_inner_right ℝ
    intro u
    let g := (nodeEquiv n).symm u
    have hg : nodeLp n g = u := (nodeEquiv n).apply_symm_apply u
    have hw := hweak g
    rw [hg] at hw
    have hs : (N n : ℝ) * inner ℝ (source n) u = g (rootNode n) := by
      rw [← hg]
      unfold source
      rw [nodeLp_inner]
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
      rw [← mul_assoc, mul_inv_cancel₀ (by
        exact_mod_cast (FiniteSourceMass.N_pos n).ne'), one_mul]
    apply mul_left_cancel₀ (show (N n : ℝ) ≠ 0 by
      exact_mod_cast (FiniteSourceMass.N_pos n).ne')
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, inner_add_left, real_inner_smul_left,
      L_symmetric]
    dsimp [τ] at hw
    nlinarith [hs]
  have hfinv : unitInverse (L n + lam • (1 : NodeL2 n →L[ℝ] NodeL2 n))
      (laplacian_unit n lam hlam) (source n) = f := by
    rw [← hsol]
    exact inverse_cancel _ _ _ _
  unfold root_response
  rw [hfinv]
  change root n (c • one n - FiniteSourceHardy.J n z) - 1 / τ = inner ℝ (v n) z
  rw [(actual_screening_bridge n).2.2.1 c z]
  dsimp [c]
  rw [one_div]
  ring

end D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceScreening
