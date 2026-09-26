/- GID: D5/S3/ConceptDynamics/DagSemantics/DepthFirst/DefaultDictionary
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DagSemantics/DepthFirst/DefaultDictionary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original default dictionary interface and finite vector instance -/

/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/

import D5.S3.ConceptDynamics.DagSemantics.DepthFirst.ElementAccess
import D5.S3.ConceptDynamics.DagSemantics.DepthFirst.FiniteSupport
import Mathlib.Data.Fintype.Basic

/-!
Faithful excerpt port of `Algorithm/Data/Classes/DefaultDict.lean` from
astrainfinita/Algorithm at ce7dc1da842c7c5b8096a886d803acfb24d71a67.
Unused declarations are omitted; live thin proofs are inlined and imports normalized.
Apache-2.0 license: Library/ConceptDynamics/zhao2023algorithm.md.
Retire this port when equivalent declarations are available in this repository's
actual pinned Mathlib revision, replacing uses by direct imports and applications.
-/

namespace Vector
variable {α : Type*} {n : ℕ}

set_option linter.unusedVariables false in -- TODO: generalize
@[nolint unusedArguments]
protected abbrev WithDefault (α : Type*) (n : Nat) (f : Fin n → α) := Vector α n

end Vector

class DefaultDict.ReadOnly (C : Type*) (ι : outParam Type*)
    (α : outParam Type*) (d : outParam <| ι → α) extends
    GetElemAllValid C ι α where
  toDFinsupp' : C → Π₀' i, [α, d i]
  coe_toDFinsupp'_eq_getElem : ∀ a, ⇑(toDFinsupp' a) = (fun i ↦ a[i]'all_valid)
export DefaultDict.ReadOnly (toDFinsupp' coe_toDFinsupp'_eq_getElem)

/-- `DefaultDict C ι α d` is a data structure that acts like a finitely supported function
  `Π₀' i, [α, d i]` with single point update operation. -/
class DefaultDict (C : Type*) [Inhabited C] (ι : outParam Type*)
    (α : outParam Type*) (d : outParam <| ι → α) extends
    DefaultDict.ReadOnly C ι α d, GetSetElemAllValid C ι α where
  getElem_default i : (default : C)[i]'all_valid = d i

attribute [simp] DefaultDict.getElem_default coe_toDFinsupp'_eq_getElem

namespace Vector.WithDefault
variable {α : Type*} {n : ℕ} {f : Fin n → α}

instance {α n f} : Inhabited (Vector.WithDefault α n f) where
  default := .ofFn f

instance : DefaultDict (Vector.WithDefault α n f) (Fin n) α f where
  getElem a i _ := a.get i
  setElem a i := a.set i
  getElem_setElem_self a i v := a.getElem_set_self i.2
  getElem_setElem_of_ne a i v j hij := a.getElem_set_ne i.2 j.2 (by omega)
  getElem_default i := congrFun (by
    ext j
    exact getElem_ofFn j.2) i
  toDFinsupp' a := DFinsupp'.equivFunOnFintype.symm (get a)
  coe_toDFinsupp'_eq_getElem _ := (DFinsupp'.equivFunOnFintype (d := f)).apply_symm_apply _

end Vector.WithDefault
