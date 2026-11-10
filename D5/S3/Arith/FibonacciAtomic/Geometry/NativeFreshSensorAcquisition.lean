/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/NativeFreshSensorAcquisition
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Same-execution native rational sector with actual raw designated sensors. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorFamily
import D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorBindings

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorAcquisition

open GenealogicalFiberTransport (Source composition)
open ActualTreeReadoutAcquisition (Address leaves)
open ActualLeafHistoryRigidity (subtree)
open NativeMaterialRootRecognition (D material terminals)
open NativeGuardedLeafRepair (Value RawMap nativeRun zeroExtend)
open NativeFreshSensorGrowth (grown calls sensors update)
open NativeFreshSensorSector (vector half adjacency)
open NativeFreshSensorFamily (Cherries H)
open NativeFreshSensorBindings (fresh inherited)
open scoped BigOperators

/-- The prepared old owner-pair field, distinct from the persistent half-sector. -/
def oldField {t : Source} {k : ℕ} (ch : Cherries t k) (theta : Fin k → ℚ) : Value :=
  ∑ i, theta i • vector (ch.root i) []

/-- Restriction to exactly one designated sensor per original leaf, in roster order. -/
def observation (t : Source) : Value →ₗ[ℚ] (Fin (sensors t).length → ℚ) where
  toFun x i := x (sensors t)[i]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem sensor_fresh (t : Source) (p : Address) (hp : p ∈ sensors t) :
    p ∈ fresh t := by
  induction t generalizing p with
  | of b => cases b <;> simp_all [sensors, fresh]
  | mul l r il ir =>
      simp only [sensors, List.mem_append, List.mem_map] at hp
      rcases hp with ⟨q,hq,rfl⟩ | ⟨q,hq,rfl⟩
      · exact List.mem_append_left _ (List.mem_map.mpr ⟨q,il q hq,rfl⟩)
      · exact List.mem_append_right _ (List.mem_map.mpr ⟨q,ir q hq,rfl⟩)

/-- Full native execution entrance and sector, with the same attained graph in every clause. -/
theorem complete_native_sector (t : Source) (ht : D t) {k : ℕ} (ch : Cherries t k)
    (labels : RawMap) (next : ℤ) (theta : Fin k → ℚ) :
    ∃ labels' next' y,
      nativeRun t labels next (oldField ch theta) (calls t) =
        some (grown t, labels', next', y) ∧
      D (grown t) ∧
      (∀ p ∈ material t, p ∈ material (grown t)) ∧
      (∀ p ∈ material (grown t), y p = zeroExtend t (oldField ch theta) p) ∧
      next' = next + (fresh t).length ∧
      (∀ i, i < next → labels i ∈ terminals t → labels' i = inherited t (labels i)) ∧
      (∀ j (hj : j < (fresh t).length), labels' (next + j) = (fresh t)[j]) ∧
      (∀ p ∈ sensors t, ∃ i, next ≤ i ∧ labels' i = p) ∧
      (material (grown t)).length + 1 = 5 * (composition t).1 + 7 * (composition t).2 ∧
      (terminals (grown t)).length = 2 * (composition t).1 + 3 * (composition t).2 ∧
      (sensors t).length = (leaves t).length ∧
      (∀ p ∈ sensors t, p ∈ terminals (grown t)) ∧
      (∀ i, update (grown t) (vector (ch.root i) []) =
          vector (ch.root i) [false] + vector (ch.root i) [true] ∧
        update (grown t) (vector (ch.root i) [false]) =
          vector (ch.root i) [] + vector (ch.root i) [false,false] + vector (ch.root i) [false,true] ∧
        update (grown t) (vector (ch.root i) [false,false]) =
          vector (ch.root i) [false] + vector (ch.root i) [false,false,false] ∧
        update (grown t) (vector (ch.root i) [false,false,false]) = vector (ch.root i) [false,false] ∧
        update (grown t) (vector (ch.root i) [true]) = vector (ch.root i) [] ∧
        update (grown t) (vector (ch.root i) [false,true]) = vector (ch.root i) [false]) ∧
      (∀ i, adjacency (grown t) (half (ch.root i)) =
          (1 / 2 : ℚ) • (vector (ch.root i) [true] - vector (ch.root i) [false,false,false]) ∧
        adjacency (grown t) (adjacency (grown t) (half (ch.root i))) = half (ch.root i) ∧
        (adjacency (grown t))^[2] (vector (ch.root i) []) =
          (2 : ℚ) • vector (ch.root i) [] + vector (ch.root i) [false,false] + vector (ch.root i) [false,true] ∧
        (adjacency (grown t))^[2] (vector (ch.root i) [false,true]) =
          vector (ch.root i) [] + vector (ch.root i) [false,false] + vector (ch.root i) [false,true] ∧
        (adjacency (grown t))^[4] (vector (ch.root i) []) =
          (6 : ℚ) • vector (ch.root i) [] + (5 : ℚ) • vector (ch.root i) [false,false] +
            (4 : ℚ) • vector (ch.root i) [false,true]) ∧
      (∀ i, observation t (half (ch.root i)) = 0 ∧
        observation t (adjacency (grown t) (half (ch.root i))) = 0) ∧
      Function.Injective (H ch) ∧
      (∀ eta, adjacency (grown t) (adjacency (grown t) (H ch eta)) = H ch eta) ∧
      (∀ eta (j : ℕ), observation t ((adjacency (grown t))^[j] (H ch eta)) = 0) ∧
      (∀ eta p, p ∈ terminals (grown t) → H ch eta p = 0) := by
  obtain ⟨labels',next',y,hr,hold,hzero⟩ :=
    NativeFreshSensorGrowth.actual_values t ht labels next (oldField ch theta)
  have raw := NativeFreshSensorBindings.raw_bindings hr
  have inv := NativeFreshSensorGrowth.inventory t
  have fam := NativeFreshSensorFamily.persistent_family ch
  refine ⟨labels',next',y,hr,(NativeFreshSensorGrowth.history t ht).domain,
    NativeGuardedLeafRepair.history_preserves_material (NativeFreshSensorGrowth.history t ht),
    ?_,raw.1,raw.2.1,raw.2.2,?_,inv.1,inv.2.1,
    inv.2.2.1,inv.2.2.2,?_,?_,?_,fam.1,fam.2.1,?_,fam.2.2.2⟩
  · intro p hp
    by_cases hm : p ∈ material t
    · simpa [zeroExtend,hm] using hold p hm
    · simpa [zeroExtend,hm] using hzero p hp hm
  · intro p hp
    obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp (sensor_fresh t p hp)
    refine ⟨next+j,by omega,?_⟩
    exact (raw.2.2 j hj).trans he
  · intro i
    exact NativeFreshSensorSector.attained_actions t _ (ch.native i)
  · intro i
    exact NativeFreshSensorSector.attained_powers t _ (ch.native i)
  · intro n
    have hs := NativeFreshSensorFamily.designated_support t _ (ch.native n)
    constructor
    · funext i; exact hs.2.1 _ (List.getElem_mem i.isLt)
    · funext i; exact hs.2.2 _ (List.getElem_mem i.isLt)
  · intro eta j
    funext i
    exact fam.2.2.1 eta j _ (List.getElem_mem i.isLt)

end D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorAcquisition
