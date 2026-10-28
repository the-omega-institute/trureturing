/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/NativeFreshSensorSector
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Ambient antisymmetric beta-cherry sectors on native fresh-sensor material. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorGrowth

/-! Native beta-cherry pair actions, including all ambient material coordinates. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorSector

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address readout)
open ActualLeafHistoryRigidity (OutputContext subtree)
open NativeMaterialRootRecognition (material terminals neighbors children)
open NativeGuardedLeafRepair (Value)
open NativeFreshSensorGrowth (cone grown update lift embed sensors)

/-- A material coordinate vector; addresses are mathematical coordinates, not Read ports. -/
def basis (p : Address) : Value := fun q => if q = p then 1 else 0

/-- Antisymmetric sibling coordinates at the same literal offset. -/
def pair (p : Address) : Value := basis (false :: p) - basis (true :: p)

private theorem embed_root (p : Address) (x : Value) (hx : x [] = 0) :
    embed p x [] = 0 := by cases p <;> simp [embed, lift, hx]

/-- The complete ambient update has no exterior charge for a zero-root field. -/
private theorem update_context (J : OutputContext) (t : Source) (x : Value) (hx : x [] = 0) :
    update (J.plug t) (embed J.holeAddress x) = embed J.holeAddress (update t x) := by
  induction J with
  | hole => rfl
  | left J sibling ih =>
      change update (.mul (J.plug t) sibling) (lift false (embed J.holeAddress x)) =
        lift false (embed J.holeAddress (update t x))
      rw [NativeFreshSensorGrowth.update_lift _ _ false _ (embed_root _ _ hx)]
      exact congrArg (lift false) ih
  | right sibling J ih =>
      change update (.mul sibling (J.plug t)) (lift true (embed J.holeAddress x)) =
        lift true (embed J.holeAddress (update t x))
      rw [NativeFreshSensorGrowth.update_lift _ _ true _ (embed_root _ _ hx)]
      exact congrArg (lift true) ih

private theorem embed_add (p : Address) (x y : Value) :
    embed p (x + y) = embed p x + embed p y := by
  induction p with
  | nil => rfl
  | cons b p ih =>
      funext q
      cases q with
      | nil => simp [embed, lift]
      | cons c q => by_cases hc : c = b <;> simp [embed, lift, ih, hc]

private theorem embed_basis (p q : Address) : embed p (basis q) = basis (p ++ q) := by
  induction p with
  | nil => rfl
  | cons b p ih =>
      funext r
      cases r with
      | nil => simp [embed, lift, basis]
      | cons c r => by_cases hc : c = b <;> simp [embed, lift, ih, basis, hc]

/-- A beta cherry after the exact two-split growth at both original leaves. -/
def localTree : Source := .mul (cone false) (cone false)

/-- All six native pair actions, including the common-parent and exterior coordinates. -/
private theorem local_actions :
    update localTree (pair []) = pair [false] + pair [true] ∧
    update localTree (pair [false]) = pair [] + pair [false, false] + pair [false, true] ∧
    update localTree (pair [false, false]) = pair [false] + pair [false, false, false] ∧
    update localTree (pair [false, false, false]) = pair [false, false] ∧
    update localTree (pair [true]) = pair [] ∧
    update localTree (pair [false, true]) = pair [false] := by
  repeat' constructor
  all_goals
    funext p
    rcases p with _ | ⟨b,p⟩
    · norm_num [update, localTree, cone, material, neighbors, children, readout, pair, basis]
    · cases b <;>
        rcases p with _ | ⟨c,p⟩ <;>
        first | norm_num [update, localTree, cone, material, neighbors, children, readout,
          pair, basis]
      all_goals cases c <;>
        rcases p with _ | ⟨d,p⟩ <;>
        first | norm_num [update, localTree, cone, material, neighbors, children, readout,
          pair, basis]
      all_goals cases d <;>
        rcases p with _ | ⟨e,p⟩ <;>
        first | norm_num [update, localTree, cone, material, neighbors, children, readout,
          pair, basis]
      all_goals cases e <;>
        rcases p with _ | ⟨f,p⟩ <;>
        norm_num [update, localTree, cone, material, neighbors, children, readout,
          pair, basis]

private theorem embed_sub (p : Address) (x y : Value) :
    embed p (x - y) = embed p x - embed p y := by
  induction p with
  | nil => rfl
  | cons b p ih =>
      funext q
      cases q with
      | nil => simp [embed, lift]
      | cons c q => by_cases hc : c = b <;> simp [embed, lift, ih, hc]

/-- Each pair is interpreted on the same ambient material, at an arbitrary cherry address. -/
def vector (p q : Address) : Value :=
  basis (p ++ false :: q) - basis (p ++ true :: q)

private theorem vector_eq (p q : Address) : vector p q = embed p (pair q) := by
  simp [vector, pair, embed_sub, embed_basis]

/-- The six local equations transport to every ambient material coordinate. -/
private theorem ambient_actions (J : OutputContext) :
    update (J.plug localTree) (vector J.holeAddress []) =
      vector J.holeAddress [false] + vector J.holeAddress [true] ∧
    update (J.plug localTree) (vector J.holeAddress [false]) =
      vector J.holeAddress [] + vector J.holeAddress [false, false] +
        vector J.holeAddress [false, true] ∧
    update (J.plug localTree) (vector J.holeAddress [false, false]) =
      vector J.holeAddress [false] + vector J.holeAddress [false, false, false] ∧
    update (J.plug localTree) (vector J.holeAddress [false, false, false]) =
      vector J.holeAddress [false, false] ∧
    update (J.plug localTree) (vector J.holeAddress [true]) = vector J.holeAddress [] ∧
    update (J.plug localTree) (vector J.holeAddress [false, true]) =
      vector J.holeAddress [false] := by
  have hz (p : Address) : pair p [] = 0 := by simp [pair, basis]
  simp only [vector_eq, update_context J localTree _ (hz _), local_actions.1,
    local_actions.2.1, local_actions.2.2.1, local_actions.2.2.2.1,
    local_actions.2.2.2.2.1, local_actions.2.2.2.2.2, embed_add,
    and_self]

private theorem subtree_grown {p : Address} {t s : Source}
    (h : subtree p t = some s) : subtree p (grown t) = some (grown s) := by
  induction p generalizing t with
  | nil => have he : t = s := by simpa [subtree] using h
           subst t; rfl
  | cons b p ih =>
      cases t with
      | of c => simp [subtree] at h
      | mul l r =>
          cases b
          · exact ih (by simpa [subtree] using h)
          · exact ih (by simpa [subtree] using h)

/-- All ambient pair identities on the actual attained graph of any original beta cherry. -/
theorem attained_actions (t : Source) (p : Address)
    (hp : subtree p t = some (.mul (.of false) (.of false))) :
    update (grown t) (vector p []) = vector p [false] + vector p [true] ∧
    update (grown t) (vector p [false]) =
      vector p [] + vector p [false, false] + vector p [false, true] ∧
    update (grown t) (vector p [false, false]) =
      vector p [false] + vector p [false, false, false] ∧
    update (grown t) (vector p [false, false, false]) = vector p [false, false] ∧
    update (grown t) (vector p [true]) = vector p [] ∧
    update (grown t) (vector p [false, true]) = vector p [false] := by
  have hs := subtree_grown hp
  obtain ⟨_, _, _, _, _, _, _, _, _, hctx, _⟩ :=
    ActualLeafHistoryRigidity.actual_address_geometry
  obtain ⟨J, hJ, he, _⟩ := hctx p (grown t) localTree hs
  simpa only [hJ, he] using ambient_actions J

/-- The actual complete-material adjacency as a rational linear operator. -/
def adjacency (t : Source) : Value →ₗ[ℚ] Value where
  toFun := update t
  map_add' x y := by
    funext p
    change (if p ∈ material t then ((neighbors t p).map (x + y)).sum else 0) =
      (if p ∈ material t then ((neighbors t p).map x).sum else 0) +
        (if p ∈ material t then ((neighbors t p).map y).sum else 0)
    split_ifs with hm
    · change ((neighbors t p).map (fun q => x q + y q)).sum = _
      exact List.sum_map_add
    · simp
  map_smul' r x := by
    funext p
    simp only [update, Pi.smul_apply, smul_eq_mul]
    split_ifs
    · induction neighbors t p with
      | nil => simp
      | cons q qs ih => simp [ih, mul_add]
    · simp

/-- The half-difference at the original sibling owners and their second left descendants. -/
def half (p : Address) : Value := (1 / 2 : ℚ) • (vector p [] - vector p [false, false])

private theorem update_half (t : Source) (p : Address)
    (hp : subtree p t = some (.mul (.of false) (.of false))) :
    adjacency (grown t) (half p) =
      (1 / 2 : ℚ) • (vector p [true] - vector p [false, false, false]) := by
  have ha := attained_actions t p hp
  change adjacency (grown t) ((1 / 2 : ℚ) • (_ - _)) = _
  rw [map_smul, map_sub]
  change (1 / 2 : ℚ) • (update (grown t) _ - update (grown t) _) = _
  rw [ha.1, ha.2.2.1]
  funext q
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
  ring

/-- Period two and the exact displayed second and fourth powers on attained native material. -/
theorem attained_powers (t : Source) (p : Address)
    (hp : subtree p t = some (.mul (.of false) (.of false))) :
    adjacency (grown t) (half p) =
      (1 / 2 : ℚ) • (vector p [true] - vector p [false, false, false]) ∧
    adjacency (grown t) (adjacency (grown t) (half p)) = half p ∧
    (adjacency (grown t))^[2] (vector p []) =
      (2 : ℚ) • vector p [] + vector p [false, false] + vector p [false, true] ∧
    (adjacency (grown t))^[2] (vector p [false, true]) =
      vector p [] + vector p [false, false] + vector p [false, true] ∧
    (adjacency (grown t))^[4] (vector p []) =
      (6 : ℚ) • vector p [] + (5 : ℚ) • vector p [false, false] +
        (4 : ℚ) • vector p [false, true] := by
  have ha := attained_actions t p hp
  have h0 : adjacency (grown t) (vector p []) = _ := ha.1
  have h1 : adjacency (grown t) (vector p [false]) = _ := ha.2.1
  have h2 : adjacency (grown t) (vector p [false, false]) = _ := ha.2.2.1
  have h3 : adjacency (grown t) (vector p [false, false, false]) = _ := ha.2.2.2.1
  have h4 : adjacency (grown t) (vector p [true]) = _ := ha.2.2.2.2.1
  have h5 : adjacency (grown t) (vector p [false, true]) = _ := ha.2.2.2.2.2
  refine ⟨update_half t p hp, ?_, ?_, ?_, ?_⟩
  · rw [update_half t p hp, map_smul, map_sub, h4, h3]
    rfl
  all_goals
    simp only [show (2 : ℕ) = 1 + 1 from rfl, show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl,
      Function.iterate_succ_apply', Function.iterate_zero_apply,
      Function.iterate_one, map_add, map_smul, h0, h1, h2, h3, h4, h5]
  all_goals
    funext q
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring

end D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorSector
