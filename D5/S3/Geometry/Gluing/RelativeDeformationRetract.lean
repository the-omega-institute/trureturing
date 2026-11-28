/- GID: D5/S3/Geometry/Gluing/RelativeDeformationRetract
   generality: G
   mirror-B: D5/B/S3/Geometry/Gluing/RelativeDeformationRetract
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A homotopy-equivalent subcomplex inclusion is a strong deformation retraction. -/

import D5.S3.Geometry.FiniteSubcomplexCylinder
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Homotopy.Equiv

noncomputable section

open scoped ContinuousMap unitInterval
open ContinuousMap
open D5.S3.Geometry.FiniteConeCollapse
open D5.S3.Geometry.FiniteConeUnionWedge (realizationInclusion)

namespace D5.S3.Geometry.RelativeDeformationRetract

open FiniteSubcomplexCylinder (Space Subspace homotopy_extension)

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {K L : PreAbstractSimplicialComplex V}

private def reducedTime (u t : I) : I :=
  ⟨(σ u : ℝ) * (t : ℝ), unitInterval.mul_mem (σ u).property t.property⟩

private theorem continuous_reducedTime :
    Continuous (fun z : I × I => reducedTime z.1 z.2) :=
  ((continuous_subtype_val.comp (unitInterval.continuous_symm.comp continuous_fst)).mul
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

private theorem reducedTime_start (t : I) : reducedTime 0 t = t :=
  Subtype.ext (by simp [reducedTime])

private theorem reducedTime_end (t : I) : reducedTime 1 t = 0 :=
  Subtype.ext (by simp [reducedTime])

private theorem reducedTime_zero (u : I) : reducedTime u 0 = 0 :=
  Subtype.ext (by simp [reducedTime])

private theorem reducedTime_one (u : I) : reducedTime u 1 = σ u :=
  Subtype.ext (by simp [reducedTime])

/-- Make a homotopy to an idempotent map relative to the subcomplex it fixes. -/
private theorem relativeHomotopy (hLK : L ≤ K) {p : C(Space K, Space K)}
    (hp : ∀ a : Subspace K L, p a.val = a.val) (hpp : p.comp p = p)
    (H : Homotopy (ContinuousMap.id (Space K)) p) :
    (ContinuousMap.id (Space K)).HomotopicRel p (Subspace K L) := by
  let repeated : Homotopy p p :=
    (H.compContinuousMap p).cast (ContinuousMap.id_comp p) hpp
  have repeated_apply (t : I) (x : Space K) : repeated (t, x) = H (t, p x) := rfl
  let initial := H.trans repeated.symm
  let paths : C(Space K, C(I, Space K)) :=
    (initial.toContinuousMap.comp ContinuousMap.prodSwap).curry

  -- Carry u with a to express joint continuity of the family of homotopies.
  let base : C(I × Subspace K L, Space K) :=
    ⟨fun z => z.2.val, continuous_subtype_val.comp continuous_snd⟩
  let turn : C(I × Subspace K L, Space K) :=
    ⟨fun z => H (σ z.1, z.2.val), (map_continuous H).comp
      ((unitInterval.continuous_symm.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))⟩
  let clock : C(I × (I × Subspace K L), I × Space K) :=
    ⟨fun z => (reducedTime z.2.1 z.1, z.2.2.val),
      (continuous_reducedTime.comp (continuous_snd.fst.prodMk continuous_fst)).prodMk
        (continuous_subtype_val.comp continuous_snd.snd)⟩
  let shortened : Homotopy base turn := {
    toContinuousMap := H.toContinuousMap.comp clock
    map_zero_left := by
      rintro ⟨u, a⟩
      change H (reducedTime u 0, a.val) = a.val
      simp only [reducedTime_zero, Homotopy.apply_zero, ContinuousMap.id_apply]
    map_one_left := by
      rintro ⟨u, a⟩
      change H (reducedTime u 1, a.val) = H (σ u, a.val)
      rw [reducedTime_one] }
  have shortened_apply (t u : I) (a : Subspace K L) :
      shortened (t, (u, a)) = H (reducedTime u t, a.val) := rfl
  let backtrack := shortened.trans shortened.symm
  let side : C(I × Subspace K L, C(I, Space K)) :=
    (backtrack.toContinuousMap.comp ContinuousMap.prodSwap).curry
  have side_zero (a : Subspace K L) : side (0, a) = paths a.val := by
    apply ContinuousMap.ext
    intro t
    change (shortened.trans shortened.symm) (t, (0, a)) =
      (H.trans repeated.symm) (t, a.val)
    simp only [Homotopy.trans_apply]
    split_ifs <;>
      simp only [Homotopy.symm_apply, shortened_apply, repeated_apply, reducedTime_start, hp]
  have side_one (t : I) (a : Subspace K L) : side (1, a) t = a.val := by
    change (shortened.trans shortened.symm) (t, (1, a)) = a.val
    rw [Homotopy.trans_apply]
    split_ifs <;>
      simp only [Homotopy.symm_apply, shortened_apply, reducedTime_end, Homotopy.apply_zero,
        ContinuousMap.id_apply]

  obtain ⟨E, E_zero, E_side⟩ := homotopy_extension K L paths side hLK side_zero
  let evalTime (s : I) : C(I × Space K, Space K) :=
    E.uncurry.comp ((ContinuousMap.id (I × Space K)).prodMk (ContinuousMap.const _ s))
  let atTop : C(I × Space K, Space K) :=
    E.uncurry.comp
      (((ContinuousMap.const (I × Space K) (1 : I)).prodMk ContinuousMap.snd).prodMk
        ContinuousMap.fst)
  let top (s : I) : C(Space K, Space K) :=
    (evalTime s).comp ((ContinuousMap.const (Space K) (1 : I)).prodMk (ContinuousMap.id _))

  -- Follow the left endpoint, the final path, and the right endpoint in reverse.
  let firstLeg : HomotopyRel (ContinuousMap.id (Space K)) (top 0) (Subspace K L) := {
    toHomotopy :=
      { toContinuousMap := evalTime 0
        map_zero_left := fun x => by
          change E (0, x) 0 = x
          calc
            E (0, x) 0 = paths x 0 := DFunLike.congr_fun (E_zero x) 0
            _ = x := initial.apply_zero x
        map_one_left := fun _ => rfl }
    prop' := fun u x hx => by
      let a : Subspace K L := ⟨x, hx⟩
      change E (u, a.val) 0 = a.val
      calc
        E (u, a.val) 0 = side (u, a) 0 := DFunLike.congr_fun (E_side u a) 0
        _ = a.val := backtrack.apply_zero (u, a) }
  let middleLeg : HomotopyRel (top 0) (top 1) (Subspace K L) := {
    toHomotopy :=
      { toContinuousMap := atTop
        map_zero_left := fun _ => rfl
        map_one_left := fun _ => rfl }
    prop' := fun t x hx => by
      let a : Subspace K L := ⟨x, hx⟩
      change E (1, a.val) t = E (1, a.val) 0
      rw [E_side 1 a, side_one t a, side_one 0 a] }
  let lastLeg : HomotopyRel p (top 1) (Subspace K L) := {
    toHomotopy :=
      { toContinuousMap := evalTime 1
        map_zero_left := fun x => by
          change E (0, x) 1 = p x
          calc
            E (0, x) 1 = paths x 1 := DFunLike.congr_fun (E_zero x) 1
            _ = p x := initial.apply_one x
        map_one_left := fun _ => rfl }
    prop' := fun u x hx => by
      let a : Subspace K L := ⟨x, hx⟩
      change E (u, a.val) 1 = p a.val
      calc
        E (u, a.val) 1 = side (u, a) 1 := DFunLike.congr_fun (E_side u a) 1
        _ = a.val := backtrack.apply_one (u, a)
        _ = p a.val := (hp a).symm }
  exact ⟨(firstLeg.trans middleLeg).trans lastLeg.symm⟩

/-- A finite subcomplex whose realization inclusion is a homotopy equivalence is a
strong deformation retract of the ambient realization. -/
theorem strongDeformationRetract_of_homotopyEquiv (hLK : L ≤ K)
    (e : Space L ≃ₕ Space K) (he : e.toFun = realizationInclusion hLK) :
    ∃ r : C(Space K, Space L),
      r.comp (realizationInclusion hLK) = ContinuousMap.id (Space L) ∧
      (ContinuousMap.id (Space K)).HomotopicRel ((realizationInclusion hLK).comp r)
        (Subspace K L) := by
  let i := realizationInclusion hLK
  let g := e.invFun
  obtain ⟨leftHomotopy⟩ : (g.comp i).Homotopic (ContinuousMap.id (Space L)) := by
    simpa only [i, g, ← he] using e.left_inv
  obtain ⟨rightHomotopy⟩ : (i.comp g).Homotopic (ContinuousMap.id (Space K)) := by
    simpa only [i, g, ← he] using e.right_inv
  let j : C(Subspace K L, Space L) :=
    ⟨fun a => ⟨a.val.val, a.property⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  have hj (a : Subspace K L) : i (j a) = a.val := Subtype.ext rfl
  let side : C(I × Subspace K L, Space L) :=
    leftHomotopy.toContinuousMap.comp ((ContinuousMap.id I).prodMap j)
  have side_zero (a : Subspace K L) : side (0, a) = g a.val := by
    change leftHomotopy (0, j a) = g a.val
    calc
      leftHomotopy (0, j a) = g (i (j a)) := leftHomotopy.apply_zero (j a)
      _ = g a.val := congrArg (fun y => g y) (hj a)
  obtain ⟨F, F_zero, F_side⟩ := homotopy_extension K L g side hLK side_zero
  let r := F.curry 1
  have hri (a : Space L) : r (i a) = a := by
    let a' : Subspace K L := ⟨i a, a.property⟩
    calc
      r (i a) = side (1, a') := F_side 1 a'
      _ = leftHomotopy (1, a) := rfl
      _ = a := leftHomotopy.apply_one a
  let p := i.comp r
  have hp (a : Subspace K L) : p a.val = a.val := by
    calc
      p a.val = p (i (j a)) := congrArg (fun x => p x) (hj a).symm
      _ = i (j a) := congrArg (fun y => i y) (hri (j a))
      _ = a.val := hj a
  have hpp : p.comp p = p := ContinuousMap.ext fun x =>
    congrArg (fun y => i y) (hri (r x))
  let stage : Homotopy g r :=
    ⟨F, F_zero, fun _ => rfl⟩
  let H : Homotopy (ContinuousMap.id (Space K)) p :=
    rightHomotopy.symm.trans ((Homotopy.refl i).comp stage)
  exact ⟨r, ContinuousMap.ext hri, relativeHomotopy hLK hp hpp H⟩

end D5.S3.Geometry.RelativeDeformationRetract
