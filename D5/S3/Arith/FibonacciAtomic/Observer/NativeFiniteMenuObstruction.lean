/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteMenuObstruction
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Every missing proper prefix has one original height-bounded whole-vector obstruction. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuReconstruction
import D5.S3.Arith.FibonacciAtomic.Observer.NativeAlphaSpineObservation
import D5.S3.Arith.FibonacciAtomic.Observer.NativeRankedNavigationCompiler
import D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuObstruction

open GenealogicalFiberTransport (Source substitution decompose)
open ActualTreeReadoutAcquisition (Address Reply readout leaves flip)
open ActualLeafHistoryRigidity (subtree)
open ActualImageAddressCertificate (height)
open NativeFiniteMenuCode NativeFiniteMenuReconstruction
open NativeRankedNavigationCompiler (pathCost pathThreshold atomic_navigation)

def outer (v : Source) : Source := .mul (.of true) v

def publicMenu (S : Menu) : Menu := S.map (true :: ·)

def Family (D : Nat) (t : Source) : Prop := ∃ v : Source, height v ≤ D ∧ t = outer v

private theorem outer_vector (S : Menu) (v : Source) (k : Nat) :
    future (publicMenu S) (outer v) k = future S v k := by
  have iter := Function.Semiconj₂.iterate
    (show Function.Semiconj₂ substitution FreeMagma.mul FreeMagma.mul from
      fun x y => substitution.map_mul x y) k (.of true) v
  simp only [future, initial, publicMenu, List.map_map, Function.comp_def, outer, iter, readout]

private theorem spine_height (a : Address) (b : Bool) : height (spine a (.of b)) = a.length := by
  induction a with
  | nil => rfl
  | cons c a ih =>
    cases c <;> simp [spine, height, decompose, BinaryTree.height] at * <;> omega

private theorem spine_leaf (a : Address) : a ∈ leaves (spine a (.of true)) := by
  induction a with
  | nil => simp [spine, leaves]
  | cons b a ih =>
    cases b
    · simp only [spine, List.foldr, Bool.false_eq_true, ↓reduceIte, leaves]
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨a, ih, rfl⟩
    · simp only [spine, List.foldr, ↓reduceIte, leaves]
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨a, ih, rfl⟩

private theorem spine_flip (a : Address) : flip (spine a (.of true)) a = spine a (.of false) := by
  induction a with
  | nil => rfl
  | cons b a ih =>
    cases b
    · exact congrArg (fun t : Source => t.mul (.of true)) ih
    · exact congrArg (fun t : Source => (FreeMagma.of true).mul t) ih

theorem path_bounds (r : Address) :
    pathCost r ≤ 2 * r.length ∧ pathThreshold r ≤ pathCost r + 1 := by
  induction r with
  | nil => simp [pathCost, pathThreshold]
  | cons b r ih =>
    cases b <;> simp only [pathCost, pathThreshold, List.length_cons, Bool.false_eq_true,
      ↓reduceIte, max_le_iff] <;> omega

theorem atomic_separator (r : Address) :
    readout r (substitution^[pathCost r + 1] (.of true)) = .beta ∧
    readout r (substitution^[pathCost r + 1] (.of false)) = .branch := by
  have nav := atomic_navigation r (pathCost r + 1) (.of false)
  have reached : subtree r (substitution^[pathCost r + 1] (.of true)) = some (.of false) :=
    nav.mpr ⟨1, (path_bounds r).2, by omega, rfl⟩
  have reached' : subtree r (substitution^[pathCost r + 2] (.of true)) =
      some (.mul (.of false) (.of true)) :=
    (atomic_navigation r (pathCost r + 2) (.mul (.of false) (.of true))).mpr
      ⟨2, by have := (path_bounds r).2; omega, by omega, rfl⟩
  have beta : substitution^[pathCost r + 1] (.of false) =
      substitution^[pathCost r + 2] (.of true) := by
    rw [show pathCost r + 2 = (pathCost r + 1) + 1 by omega,
      Function.iterate_succ_apply]
    rfl
  have app := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ha := app r [] (substitution^[pathCost r + 1] (.of true))
  have hb := app r [] (substitution^[pathCost r + 2] (.of true))
  rw [reached] at ha
  rw [reached'] at hb
  exact ⟨by simpa [readout] using ha, by rw [beta]; simpa [readout] using hb⟩

private theorem spine_transport (a r : Address) (b : Bool) (k : Nat) :
    readout (a ++ r) (substitution^[k] (spine a (.of b))) =
      readout r (substitution^[k] (.of b)) := by
  have ht := NativeDepthPatterns.original_present_transport k a (spine a (.of b)) (.of b)
    (NativeAlphaSpineObservation.native_alpha_spine_at a (.of b))
  have app := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    a r (substitution^[k] (spine a (.of b)))
  rw [ht] at app
  exact app

/-- One prescribed pair simultaneously hides its whole initial vector, separates
its original ranks and yields beta/branch at the same legal supplied count. -/
theorem every_missing_prefix_obstruction (D : Nat) (S : Menu)
    (bounded : ∀ q ∈ S, q.length + 1 ≤ D) (a r : Address)
    (proper : r ≠ []) (selected : a ++ r ∈ S) (missing : a ∉ S) :
    let v := spine a (.of true)
    let v' := spine a (.of false)
    let k := pathCost r + 1
    2 ≤ D ∧ height v = a.length ∧ height v' = a.length ∧ a.length ≤ D - 2 ∧
      Family D (outer v) ∧ Family D (outer v') ∧
      initial S v = initial S v' ∧ initial (publicMenu S) (outer v) = initial (publicMenu S) (outer v') ∧
      code S v ≠ code S v' ∧ k < 2 * D ∧
      readout (true :: (a ++ r)) (substitution^[k] (outer v)) = .beta ∧
      readout (true :: (a ++ r)) (substitution^[k] (outer v')) = .branch ∧
      future S v k ≠ future S v' k ∧
      future (publicMenu S) (outer v) k ≠ future (publicMenu S) (outer v') k := by
  dsimp only
  have hd := bounded (a ++ r) selected
  have hr : 0 < r.length := by
    by_contra hh
    exact proper (List.length_eq_zero_iff.mp (by omega))
  simp only [List.length_append] at hd
  have hs : initial S (spine a (.of true)) = initial S (spine a (.of false)) := by
    apply List.map_congr_left
    intro q hq
    have ne : q ≠ a := by rintro rfl; exact missing hq
    have hf := ActualTreeReadoutAcquisition.source_foundation.2.2.2.1
      (spine a (.of true)) a (spine_leaf a) q ne
    rw [spine_flip] at hf
    exact hf.symm
  have hp : initial (publicMenu S) (outer (spine a (.of true))) =
      initial (publicMenu S) (outer (spine a (.of false))) := by
    change future (publicMenu S) (outer (spine a (.of true))) 0 =
      future (publicMenu S) (outer (spine a (.of false))) 0
    rw [outer_vector, outer_vector]
    exact hs
  have sep := atomic_separator r
  have ha : readout (a ++ r) (substitution^[pathCost r + 1] (spine a (.of true))) = .beta := by
    rw [spine_transport]; exact sep.1
  have hb : readout (a ++ r) (substitution^[pathCost r + 1] (spine a (.of false))) = .branch := by
    rw [spine_transport]; exact sep.2
  have diff : future S (spine a (.of true)) (pathCost r + 1) ≠
      future S (spine a (.of false)) (pathCost r + 1) := by
    intro he
    have hq := List.map_inj_left.mp he (a ++ r) selected
    rw [ha, hb] at hq
    cases hq
  have iter (v : Source) : substitution^[pathCost r + 1] (outer v) =
      .mul (substitution^[pathCost r + 1] (.of true)) (substitution^[pathCost r + 1] v) :=
    Function.Semiconj₂.iterate (fun x y => substitution.map_mul x y) (pathCost r + 1) (.of true) v
  refine ⟨by omega, spine_height a true, spine_height a false, by omega,
    ⟨_, by rw [spine_height]; omega, rfl⟩, ⟨_, by rw [spine_height]; omega, rfl⟩,
    hs, hp, original_code_context_separation S a r selected, ?_, ?_, ?_, diff, ?_⟩
  · have := (path_bounds r).1; omega
  · rw [iter]; exact ha
  · rw [iter]; exact hb
  · rw [outer_vector, outer_vector]; exact diff

end D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuObstruction
