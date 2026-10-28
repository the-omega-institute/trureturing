/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderEnergy
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderEnergy
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Constant-trace variational minimization on the original biased binary boundary. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryFreeRootForm

/-! Variational splitting in the original square-summable edge space. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderEnergy

open ActualTreeReadoutAcquisition (Address)
open FiniteSourceHardy (H Edge)
open BiasedBoundaryTrace (G J M Omega cylinder indicator J_single)
open BiasedBoundaryPathSplit (S descendant constG prefixSum prefixes boundary_path_split)
open BiasedBoundaryConditionalLaw (pullback)
open BiasedBoundaryCentering (mean Pi C centered_suffix_residual pullback_const)
open BiasedBoundaryFreeRootForm (D K Sigma lift form energy free_root_least_energy)
open MeasureTheory InnerProductSpace
open D5.S0.Computability.Coding.PrefixFreeCode (IsPrefixFree)
open scoped BigOperators

private def edge (c : Bool) : Edge := ⟨[c], by simp⟩
private def E (c : Bool) : H →L[ℝ] H := (S [c]).adjoint

private theorem suffix_root (c d : Bool) (a : ℝ) :
    S [c] (lp.single 2 (edge d) a) = 0 := by
  by_cases h : c = d
  · subst d
    exact BiasedBoundaryPathSplit.suffix_single_prefix [c] (edge c) a (by rfl)
  · exact BiasedBoundaryPathSplit.suffix_single_of_not_prefix [c] (edge d) a (by
      simpa [edge] using h)

private theorem suffix_branch (c d : Bool) (u : Edge) (a : ℝ) :
    S [c] (lp.single 2 (descendant [d] u) a) =
      if c = d then lp.single 2 u a else 0 := by
  by_cases h : c = d
  · subst d
    simpa using BiasedBoundaryPathSplit.suffix_single_descendant [c] u a
  · rw [if_neg h]
    exact BiasedBoundaryPathSplit.suffix_single_of_not_prefix [c] (descendant [d] u) a
      (by simpa [descendant] using h)

private theorem E_root (c d : Bool) (z : H) : E c z (edge d) = 0 := by
  classical
  have h := (S [c]).adjoint_inner_right (lp.single 2 (edge d) (1 : ℝ)) z
  rw [suffix_root, inner_zero_left, lp.inner_single_left] at h
  simpa [E, Real.inner_apply] using h

private theorem E_branch (c d : Bool) (z : H) (u : Edge) :
    E c z (descendant [d] u) = if c = d then z u else 0 := by
  classical
  have h := (S [c]).adjoint_inner_right
    (lp.single 2 (descendant [d] u) (1 : ℝ)) z
  rw [suffix_branch, lp.inner_single_left] at h
  by_cases he : c = d
  · simpa [E, he, lp.inner_single_left, Real.inner_apply] using h
  · simpa [E, he, Real.inner_apply] using h

private def graft (x y : ℝ) (z w : H) : H :=
  lp.single 2 (edge false) x + lp.single 2 (edge true) y + E false z + E true w

private theorem graft_root (x y : ℝ) (z w : H) (c : Bool) :
    graft x y z w (edge c) = if c then y else x := by
  classical
  simp only [graft, lp.coeFn_add, Pi.add_apply, E_root, add_zero]
  cases c <;> simp [edge, Pi.single_apply]

private theorem suffix_graft (x y : ℝ) (z w : H) (c : Bool) :
    S [c] (graft x y z w) = if c then w else z := by
  classical
  ext u
  rw [boundary_path_split.1]
  change (lp.single 2 (edge false) x : H) (descendant [c] u) +
    (lp.single 2 (edge true) y : H) (descendant [c] u) +
    E false z (descendant [c] u) + E true w (descendant [c] u) = _
  have hn (d : Bool) : descendant [c] u ≠ edge d := by
    intro h
    have he : 1 + u.val.length = 1 := by
      simpa only [descendant, edge, List.length_append, List.length_singleton] using
        congrArg (fun p : Edge => p.val.length) h
    have hu := List.length_pos_of_ne_nil u.property
    omega
  simp only [lp.coeFn_single, Pi.single_apply, hn, ite_false, E_branch]
  cases c <;> simp

private theorem graft_pair (x y : ℝ) (z w v : H) :
    inner ℝ (graft x y z w) v = x * v (edge false) + y * v (edge true) +
      inner ℝ z (S [false] v) + inner ℝ w (S [true] v) := by
  classical
  simp only [graft, inner_add_left, lp.inner_single_left, Real.inner_apply]
  rw [show inner ℝ (E false z) v = inner ℝ z (S [false] v) from
      (S [false]).adjoint_inner_left v z,
    show inner ℝ (E true w) v = inner ℝ w (S [true] v) from
      (S [true]).adjoint_inner_left v w]
  ring

private theorem graft_norm (x y : ℝ) (z w : H) :
    ‖graft x y z w‖^2 = x^2 + y^2 + ‖z‖^2 + ‖w‖^2 := by
  rw [← real_inner_self_eq_norm_sq, graft_pair, graft_root, graft_root,
    suffix_graft, suffix_graft]
  simp only [Bool.false_eq_true, if_false, if_true, real_inner_self_eq_norm_sq]
  ring

private theorem graft_split (z : H) :
    graft (z (edge false)) (z (edge true)) (S [false] z) (S [true] z) = z := by
  classical
  ext p
  obtain ⟨p,hp⟩ := p
  cases p with
  | nil => exact (hp rfl).elim
  | cons c u =>
    cases u with
    | nil => exact graft_root _ _ _ _ c |>.trans (by cases c <;> rfl)
    | cons d v =>
      let q : Edge := ⟨d::v, by simp⟩
      change (lp.single 2 (edge false) (z (edge false)) : H) (descendant [c] q) +
        (lp.single 2 (edge true) (z (edge true)) : H) (descendant [c] q) +
        E false (S [false] z) (descendant [c] q) +
        E true (S [true] z) (descendant [c] q) = _
      simp only [lp.coeFn_single, Pi.single_apply, E_branch]
      have hn (b : Bool) : descendant [c] q ≠ edge b := by
        intro he
        have hh := congrArg (fun p : Edge => p.val.length) he
        simp [descendant, edge, q] at hh
      simp only [hn, if_false, zero_add]
      cases c <;> simp [boundary_path_split.1, descendant, q]

private theorem norm_split (z : H) :
    ‖z‖^2 = (z (edge false))^2 + (z (edge true))^2 +
      ‖S [false] z‖^2 + ‖S [true] z‖^2 := by
  conv_lhs => rw [← graft_split z]
  exact graft_norm _ _ _ _

private theorem prefix_one (c : Bool) (z : H) : prefixSum [c] z = z (edge c) := by
  classical
  have hp : prefixes [c] = {edge c} := by
    ext q
    simp [prefixes, List.inits, edge, q.property, Subtype.ext_iff]
  simp [prefixSum, hp]

private theorem pullback_graft (x y : ℝ) (z w : H) (c : Bool) :
    pullback [c] (J (graft x y z w)) =
      constG (if c then y else x) + J (if c then w else z) := by
  rw [boundary_path_split.2.2.2.2, prefix_one, graft_root, suffix_graft]


private def firstLevel : Finset Edge := {edge false, edge true}

private theorem firstLevel_prefixfree :
    IsPrefixFree (Subtype.val '' (firstLevel : Set Edge)) := by
  intro p hp q hq hpq
  obtain ⟨p,hp,rfl⟩ := hp
  obtain ⟨q,hq,rfl⟩ := hq
  simp only [firstLevel, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;>
    simp_all [edge]

private theorem firstLevel_cover (ω : Omega) :
    ∃ p ∈ firstLevel, ω ∈ cylinder p.val := by
  refine ⟨edge (ω 0), ?_, ?_⟩
  · cases h : ω 0 <;> simp [firstLevel, h]
  · rw [BiasedBoundaryCylinderProjection.cylinder_ray]
    simp [edge, D5.S0.Computability.Coding.BiasedMassFrontier.rayPrefix]

private theorem pullback_ext {F T : G}
    (h : ∀ c : Bool, pullback [c] F = pullback [c] T) : F = T := by
  have hn := (BiasedBoundaryCylinderProjection.partition_centered_residual
    firstLevel firstLevel_prefixfree firstLevel_cover).2.2.1 (F-T)
  have hp (c : Bool) : pullback [c] (F-T) = 0 := by rw [map_sub,h c,sub_self]
  have hz : ‖F-T‖^2 = 0 := by
    simpa [firstLevel, edge, hp] using hn
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

private theorem graft_constant {x y a b : ℝ} {z w : H}
    (hz : J z = constG a) (hw : J w = constG b) (h : x+a = y+b) :
    J (graft x y z w) = constG (x+a) := by
  apply pullback_ext
  intro c
  rw [pullback_graft, pullback_const]
  cases c
  · simp only [Bool.false_eq_true, if_false]
    rw [hz, ← map_add]
  · simp only [if_true]
    rw [hw, ← map_add, ← h]

private def seed : H := graft 1 1 0 0
private def fixedLift : H := J.kerᗮ.starProjection seed

private theorem seed_trace : J seed = constG 1 := by
  simpa [seed] using (graft_constant (x := 1) (y := 1)
    (a := 0) (b := 0) (by simp) (by simp) (by ring))

private theorem fixed_trace : J fixedLift = constG 1 := by
  unfold fixedLift
  rw [Submodule.starProjection_orthogonal_val, map_sub]
  have hk : J (J.ker.starProjection seed) = 0 :=
    Submodule.starProjection_apply_mem J.ker seed
  rw [hk,sub_zero,seed_trace]

private theorem scalar_trace (t : ℝ) : J (t • fixedLift) = constG t := by
  rw [map_smul,fixed_trace]
  simpa only [smul_eq_mul,mul_one] using (constG.map_smul t (1:ℝ)).symm

private theorem fixed_pair (c : ℝ) (z : H) (hz : J z = constG c) :
    inner ℝ fixedLift z = c * ‖fixedLift‖^2 := by
  have hk : z-c • fixedLift ∈ J.ker := by
    change J (z-c • fixedLift) = 0
    rw [map_sub,hz,scalar_trace,sub_self]
  have hm : fixedLift ∈ J.kerᗮ := Submodule.starProjection_apply_mem _ _
  have ho := hm (z-c • fixedLift) hk
  rw [inner_sub_left,inner_smul_left,real_inner_self_eq_norm_sq,
    real_inner_comm z fixedLift] at ho
  linarith

private theorem fixed_bound (c : ℝ) (z : H) (hz : J z = constG c) :
    c^2 * ‖fixedLift‖^2 ≤ ‖z‖^2 := by
  have hn := sq_nonneg ‖z-c • fixedLift‖
  rw [norm_sub_sq_real,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,
    inner_smul_right,real_inner_comm z fixedLift,fixed_pair c z hz] at hn
  nlinarith

private theorem suffix_constant (c : Bool) (a : ℝ) (z : H)
    (hz : J z = constG a) : J (S [c] z) = constG (a-z (edge c)) := by
  have hh := congrArg (fun F : G => pullback [c] F) hz
  rw [boundary_path_split.2.2.2.2,prefix_one,pullback_const] at hh
  rw [map_sub]
  calc
    J (S [c] z) = (constG (z (edge c))+J (S [c] z))-constG (z (edge c)) := by abel
    _ = constG a-constG (z (edge c)) := by rw [hh]

private theorem fixed_norm : ‖fixedLift‖^2 = 1 := by
  let m : ℝ := ‖fixedLift‖^2
  have hm : 0 < m := by
    apply sq_pos_of_ne_zero
    intro h
    have hz : fixedLift = 0 := norm_eq_zero.mp h
    have hh := congrArg mean fixed_trace
    rw [hz,map_zero,map_zero,centered_suffix_residual.2.1] at hh
    norm_num at hh
  have hg : J (graft (1/2) (1/2) ((1/2:ℝ) • fixedLift)
      ((1/2:ℝ) • fixedLift)) = constG 1 := by
    convert graft_constant (scalar_trace (1/2)) (scalar_trace (1/2)) (by ring) using 1 <;>
      norm_num
  have hu := fixed_bound 1 _ hg
  rw [graft_norm,norm_smul,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs] at hu
  have hupper : m ≤ 1 := by dsimp [m]; nlinarith
  let x := fixedLift (edge false)
  let y := fixedLift (edge true)
  have hl := fixed_bound (1-x) (S [false] fixedLift)
    (suffix_constant false 1 fixedLift fixed_trace)
  have hr := fixed_bound (1-y) (S [true] fixedLift)
    (suffix_constant true 1 fixedLift fixed_trace)
  have hn := norm_split fixedLift
  change m = x^2+y^2+‖S [false] fixedLift‖^2+‖S [true] fixedLift‖^2 at hn
  change (1-x)^2*m ≤ _ at hl
  change (1-y)^2*m ≤ _ at hr
  have hlow : x^2+y^2+(1-x)^2*m+(1-y)^2*m ≤ m := by linarith
  have hh := mul_le_mul_of_nonneg_left hlow (show 0 ≤ 1+m by linarith)
  have hsqx := sq_nonneg ((1+m)*x-m)
  have hsqy := sq_nonneg ((1+m)*y-m)
  have hprod : m*(m-1) ≥ 0 := by nlinarith
  have hlow' : 1 ≤ m := by nlinarith
  exact le_antisymm hupper hlow'

private theorem fixed_recursion :
    fixedLift = graft (1/2) (1/2) ((1/2:ℝ) • fixedLift) ((1/2:ℝ) • fixedLift) := by
  let r := graft (1/2) (1/2) ((1/2:ℝ) • fixedLift) ((1/2:ℝ) • fixedLift)
  have ht : J r = constG 1 := by
    convert graft_constant (scalar_trace (1/2)) (scalar_trace (1/2)) (by ring) using 1 <;>
      norm_num
  have hn : ‖r‖^2 = 1 := by
    dsimp [r]
    rw [graft_norm,norm_smul,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,fixed_norm]
    norm_num
  have hp := fixed_pair 1 r ht
  have hz : ‖fixedLift-r‖^2 = 0 := by
    rw [norm_sub_sq_real,fixed_norm,hn,hp,fixed_norm]
    norm_num
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

/-- Constant traces on the original biased boundary have the unit fixed-root
minimum, and its minimizer splits equally into the original two subtrees. -/
theorem constant_trace_minimum : ∃ q : H,
    J q = constG 1 ∧ ‖q‖^2 = 1 ∧
    (∀ (c : ℝ) (z : H), J z = constG c → inner ℝ q z = c) ∧
    (∀ c : Bool, q (edge c) = 1/2 ∧ S [c] q = (1/2:ℝ) • q) := by
  refine ⟨fixedLift,fixed_trace,fixed_norm,?_,?_⟩
  · intro c z hz
    rw [fixed_pair c z hz,fixed_norm,mul_one]
  · intro c
    constructor
    · conv_lhs => rw [fixed_recursion]
      rw [graft_root]
      cases c <;> rfl
    · conv_lhs => rw [fixed_recursion]
      rw [suffix_graft]
      cases c <;> rfl

end D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCylinderEnergy
