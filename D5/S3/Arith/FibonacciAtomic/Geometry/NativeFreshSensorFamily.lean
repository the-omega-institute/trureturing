/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/NativeFreshSensorFamily
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Independent persistent rational sectors behind actual designated native sensors. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorSector

/-! Full rational cherry families and unbounded designated observation times. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorFamily

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address)
open ActualLeafHistoryRigidity (OutputContext subtree)
open NativeMaterialRootRecognition (D material terminals)
open NativeGuardedLeafRepair (Value RawMap nativeRun)
open NativeFreshSensorGrowth (cone grown calls history update embed lift sensors)
open NativeFreshSensorSector (basis vector half adjacency)
open scoped BigOperators

private def growContext : OutputContext → OutputContext
  | .hole => .hole
  | .left J r => .left (growContext J) (grown r)
  | .right l J => .right (grown l) (growContext J)

private theorem grow_plug (J : OutputContext) (t : Source) :
    grown (J.plug t) = (growContext J).plug (grown t) := by
  induction J <;> simp_all [growContext, grown, OutputContext.plug]

private theorem grow_hole (J : OutputContext) :
    (growContext J).holeAddress = J.holeAddress := by
  induction J <;> simp_all [growContext, OutputContext.holeAddress]

private theorem embed_terminal (J : OutputContext) (t : Source) (x : Value)
    (hx : ∀ p ∈ terminals t, x p = 0) :
    ∀ p ∈ terminals (J.plug t), embed J.holeAddress x p = 0 := by
  induction J with
  | hole => exact hx
  | left J r ih =>
      intro p hp
      simp only [OutputContext.plug, terminals, List.mem_append, List.mem_map] at hp
      rcases hp with ⟨q,hq,rfl⟩ | ⟨q,hq,rfl⟩
      · simpa [OutputContext.holeAddress, embed, lift] using ih q hq
      · simp [OutputContext.holeAddress, embed, lift]
  | right l J ih =>
      intro p hp
      simp only [OutputContext.plug, terminals, List.mem_append, List.mem_map] at hp
      rcases hp with ⟨q,hq,rfl⟩ | ⟨q,hq,rfl⟩
      · simp [OutputContext.holeAddress, embed, lift]
      · simpa [OutputContext.holeAddress, embed, lift] using ih q hq

private theorem embed_sensor (J : OutputContext) (t : Source) (x : Value)
    (hx : ∀ p ∈ sensors t, x p = 0) :
    ∀ p ∈ sensors (J.plug t), embed J.holeAddress x p = 0 := by
  induction J with
  | hole => exact hx
  | left J r ih =>
      intro p hp
      simp only [OutputContext.plug, sensors, List.mem_append, List.mem_map] at hp
      rcases hp with ⟨q,hq,rfl⟩ | ⟨q,hq,rfl⟩
      · simpa [OutputContext.holeAddress, embed, lift] using ih q hq
      · simp [OutputContext.holeAddress, embed, lift]
  | right l J ih =>
      intro p hp
      simp only [OutputContext.plug, sensors, List.mem_append, List.mem_map] at hp
      rcases hp with ⟨q,hq,rfl⟩ | ⟨q,hq,rfl⟩
      · simp [OutputContext.holeAddress, embed, lift]
      · simpa [OutputContext.holeAddress, embed, lift] using ih q hq

private theorem half_embed (p : Address) :
    half p = embed p (half []) := by
  funext q
  induction p generalizing q with
  | nil => rfl
  | cons b p ih =>
      cases q with
      | nil => simp [half, vector, basis, embed, lift]
      | cons c q =>
          cases b <;> cases c <;>
            simp_all [half, vector, basis, embed, lift]

private theorem tail_embed (p : Address) :
    (1 / 2 : ℚ) • (vector p [true] - vector p [false,false,false]) =
      embed p ((1 / 2 : ℚ) • (vector [] [true] - vector [] [false,false,false])) := by
  funext q
  induction p generalizing q with
  | nil => rfl
  | cons b p ih =>
      cases q with
      | nil => simp [vector, basis, embed, lift]
      | cons c q => cases b <;> cases c <;> simp_all [vector, basis, embed, lift]

theorem designated_support (t : Source) (p : Address)
    (hp : subtree p t = some (.mul (.of false) (.of false))) :
    (∀ q ∈ terminals (grown t), half p q = 0) ∧
    (∀ q ∈ sensors t, half p q = 0) ∧
    (∀ q ∈ sensors t, adjacency (grown t) (half p) q = 0) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hctx, _⟩ :=
    ActualLeafHistoryRigidity.actual_address_geometry
  obtain ⟨J,hJ,he,_⟩ := hctx p t (.mul (.of false) (.of false)) hp
  have ht : ∀ q ∈ terminals (grown (.mul (.of false) (.of false))), half [] q = 0 := by
    intro q hq
    simp [grown, cone, terminals] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [half, vector, basis]
  have hs : ∀ q ∈ sensors (.mul (.of false) (.of false)), half [] q = 0 := by
    intro q hq
    simp [sensors] at hq
    rcases hq with rfl | rfl <;> norm_num [half, vector, basis]
  have hb : ∀ q ∈ sensors (.mul (.of false) (.of false)),
      ((1 / 2 : ℚ) • (vector [] [true] - vector [] [false,false,false])) q = 0 := by
    intro q hq
    simp [sensors] at hq
    rcases hq with rfl | rfl <;> norm_num [vector, basis]
  refine ⟨?_, ?_, ?_⟩
  · have hh := embed_terminal (growContext J) _ _ ht
    rw [grow_hole, hJ] at hh
    rw [← grow_plug, he] at hh
    intro q hq
    rw [half_embed p]
    exact hh q hq
  · have hh := embed_sensor J _ _ hs
    rw [hJ, he] at hh
    intro q hq
    rw [half_embed p]
    exact hh q hq
  · rw [(NativeFreshSensorSector.attained_powers t p hp).1, tail_embed]
    have hh := embed_sensor J _ _ hb
    simpa only [hJ, he] using hh

/-- Disjoint literal cones of the original logical beta cherries. -/
structure Cherries (t : Source) (k : ℕ) where
  root : Fin k → Address
  native : ∀ i, subtree (root i) t = some (.mul (.of false) (.of false))
  disjoint : ∀ i j, i ≠ j → ∀ p q : Address, root i ++ p ≠ root j ++ q

/-- The sector map on all independent rational parameters. -/
def H {t : Source} {k : ℕ} (ch : Cherries t k) (theta : Fin k → ℚ) : Value :=
  ∑ i, theta i • half (ch.root i)

private theorem half_owner (p : Address) : half p (p ++ [false]) = 1 / 2 := by
  norm_num [half, vector, basis]

private theorem half_other {t : Source} {k : ℕ} (ch : Cherries t k)
    (i j : Fin k) (hij : i ≠ j) : half (ch.root j) (ch.root i ++ [false]) = 0 := by
  have h0 := ch.disjoint i j hij [false] [false]
  have h1 := ch.disjoint i j hij [false] [true]
  have h2 := ch.disjoint i j hij [false] [false,false,false]
  have h3 := ch.disjoint i j hij [false] [true,false,false]
  simp [half, vector, basis, h0, h1, h2, h3]

private theorem H_owner {t : Source} {k : ℕ} (ch : Cherries t k)
    (theta : Fin k → ℚ) (i : Fin k) : H ch theta (ch.root i ++ [false]) = theta i / 2 := by
  change (∑ j : Fin k, theta j • half (ch.root j)) _ = _
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · simp [half_owner, div_eq_mul_inv]
  · intro j _ hji
    simp [half_other ch i j hji.symm]
  · simp

/-- Independent rational sectors on the actual grown source, with every natural observation time. -/
theorem persistent_family {t : Source} {k : ℕ} (ch : Cherries t k) :
    Function.Injective (H ch) ∧
    (∀ theta, adjacency (grown t) (adjacency (grown t) (H ch theta)) = H ch theta) ∧
    (∀ theta (j : ℕ) q, q ∈ sensors t → (adjacency (grown t))^[j] (H ch theta) q = 0) ∧
    (∀ theta q, q ∈ terminals (grown t) → H ch theta q = 0) := by
  have hperiod (theta : Fin k → ℚ) :
      adjacency (grown t) (adjacency (grown t) (H ch theta)) = H ch theta := by
    simp only [H, map_sum, map_smul,
      (NativeFreshSensorSector.attained_powers t _ (ch.native _)).2.1]
  have hz (theta : Fin k → ℚ) : ∀ q ∈ sensors t, H ch theta q = 0 := by
    intro q hq
    simp only [H, Finset.sum_apply, Pi.smul_apply]
    exact Finset.sum_eq_zero (fun i _ => by rw [(designated_support t _ (ch.native i)).2.1 q hq]; simp)
  have hb (theta : Fin k → ℚ) : ∀ q ∈ sensors t, adjacency (grown t) (H ch theta) q = 0 := by
    intro q hq
    simp only [H, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]
    exact Finset.sum_eq_zero (fun i _ => by rw [(designated_support t _ (ch.native i)).2.2 q hq]; simp)
  refine ⟨?_, hperiod, ?_, ?_⟩
  · intro theta eta he
    funext i
    have hi := congrFun he (ch.root i ++ [false])
    rw [H_owner, H_owner] at hi
    linarith
  · intro theta j
    induction j using Nat.twoStepInduction with
    | zero => simpa using hz theta
    | one => simpa using hb theta
    | more n ih _ =>
        rw [Function.iterate_add_apply]
        have htwo : (adjacency (grown t))^[2] (H ch theta) = H ch theta := by
          simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using hperiod theta
        rw [htwo]
        exact ih
  · intro theta q hq
    simp only [H, Finset.sum_apply, Pi.smul_apply]
    exact Finset.sum_eq_zero (fun i _ => by rw [(designated_support t _ (ch.native i)).1 q hq]; simp)

end D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorFamily
