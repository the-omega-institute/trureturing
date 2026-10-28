/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/NativeFreshSensorGrowth
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Guarded fresh-sensor growth on every original native leaf. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.NativeGuardedLeafRepair

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorGrowth

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address readout leaves)
open ActualLeafHistoryRigidity (OutputContext subtree)
open NativeMaterialRootRecognition (D material terminals neighbors)
open NativeGuardedLeafRepair (Call run nativeRun History Value RawMap)

/-- The two-step alpha cone and the two-split beta cone. -/
def cone (b : Bool) : Source :=
  if b then .mul (.of false) (.of true)
  else .mul (.mul (.of false) (.of true)) (.of true)

/-- Replace each original leaf by its designated-sensor cone. -/
def grown : Source → Source
  | .of b => cone b
  | .mul l r => .mul (grown l) (grown r)

/-- Depth-first fixed original-leaf order; no numerical operations occur. -/
def calls : Source → List Call
  | .of true => [.promote [], .split []]
  | .of false => [.split [], .split [false]]
  | .mul l r => (calls l).map (Call.shift [false]) ++
      (calls r).map (Call.shift [true])

private theorem run_append {t u v : Source} {w z : List Call}
    (hw : run t w = some u) (hz : run u z = some v) :
    run t (w ++ z) = some v := by
  induction w generalizing t with
  | nil =>
      have he : t = u := by simpa [run] using hw
      subst t
      exact hz
  | cons c w ih =>
      cases c with
      | promote p =>
          unfold run at hw
          split at hw <;> try contradiction
          next h => simpa [run, h] using ih hw
      | split p =>
          unfold run at hw
          split at hw <;> try contradiction
          next h => simpa [run, h] using ih hw

/-- Every original leaf's requested growth executes on the original guarded runner. -/
theorem executes (t : Source) : run t (calls t) = some (grown t) := by
  induction t with
  | of b => cases b <;> rfl
  | mul l r il ir =>
      have hl := NativeGuardedLeafRepair.context_run (.left .hole r) il
      have hr := NativeGuardedLeafRepair.context_run (.right (grown l) .hole) ir
      exact run_append hl hr

/-- The complete actual guarded history, retaining the original birth domain. -/
def history (t : Source) (ht : D t) : History t :=
  ⟨grown t, calls t, executes t, NativeGuardedLeafRepair.run_preserves_D ht (executes t)⟩

/-- Fresh-only growth carries arbitrary original rational values on the same material. -/
theorem actual_values (t : Source) (ht : D t) (labels : RawMap) (next : ℤ) (x : Value) :
    ∃ labels' next' y,
      nativeRun t labels next x (calls t) = some (grown t, labels', next', y) ∧
      (∀ p ∈ material t, y p = x p) ∧
      (∀ p ∈ material (grown t), p ∉ material t → y p = 0) :=
  NativeGuardedLeafRepair.history_preserves_values (history t ht) labels next x

/-- Designated addresses indexed by the fixed original-leaf roster. -/
def sensors : Source → List Address
  | .of true => [[true]]
  | .of false => [[false, true]]
  | .mul l r => (sensors l).map (false :: ·) ++ (sensors r).map (true :: ·)

private theorem sensor_terminal (t : Source) (p : Address) (hp : p ∈ sensors t) :
    p ∈ terminals (grown t) := by
  induction t generalizing p with
  | of b => cases b <;> simpa [sensors, grown, cone, terminals] using hp
  | mul l r il ir =>
      simp only [sensors, List.mem_append, List.mem_map] at hp
      rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · simp [grown, terminals, List.mem_map, il q hq]
      · simp [grown, terminals, List.mem_map, ir q hq]

/-- Native neighbor-sum on the complete material, extended by zero off the material. -/
def update (t : Source) (x : Value) : Value :=
  fun p => if p ∈ material t then ((neighbors t p).map x).sum else 0

/-- Prefix a field by one native edge, assigning zero to all exterior addresses. -/
def lift (b : Bool) (x : Value) : Value
  | [] => 0
  | c :: p => if c = b then x p else 0

/-- Prefix a field by an arbitrary literal native address. -/
def embed : Address → Value → Value
  | [], x => x
  | b :: p, x => lift b (embed p x)

private theorem material_cons (l r : Source) (b : Bool) (p : Address) :
    b :: p ∈ material (.mul l r) ↔ p ∈ material (if b then r else l) := by
  cases b <;> simp [material, List.mem_map]

private theorem sum_lift (b : Bool) (x : Value) (ps : List Address) :
    ((ps.map (b :: ·)).map (lift b x)).sum = (ps.map x).sum := by
  simp [List.map_map, lift]

private theorem sum_other (b : Bool) (x : Value) (ps : List Address) :
    ((ps.map ((!b) :: ·)).map (lift b x)).sum = 0 := by
  cases b <;> simp [List.map_map, lift]

/-- Zero at the attached root is exactly what removes the exterior parent charge. -/
theorem update_lift (l r : Source) (b : Bool) (x : Value) (hx : x [] = 0) :
    update (.mul l r) (lift b x) = lift b (update (if b then r else l) x) := by
  funext p
  cases p with
  | nil => cases b <;> simp [update, material, neighbors, NativeMaterialRootRecognition.children,
      readout, lift, hx]
  | cons c p =>
      by_cases hcb : c = b
      · subst c
        rw [update, if_congr (propext (material_cons l r b p)) rfl rfl]
        rw [NativeMaterialRootRecognition.neighbors_cons]
        by_cases hm : p ∈ material (if b then r else l)
        · simp [hm, List.map_append, List.sum_append, sum_lift, lift, update]
        · simp [hm, lift, update]
      · cases b <;> cases c <;> try contradiction
        all_goals
          simp [update, lift, NativeMaterialRootRecognition.neighbors_cons,
            List.map_append, List.sum_append, List.map_map]

end D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorGrowth
