/- GID: D5/S3/ConceptDynamics/DagSemantics/DepthFirst/ElementAccess
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DagSemantics/DepthFirst/ElementAccess
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original lookup and update interfaces for default dictionaries -/

/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/

import Mathlib.Data.Nat.Notation
import Mathlib.Logic.Function.Basic

/-!
Faithful excerpt port of `Algorithm/Data/Classes/GetElem.lean` from
astrainfinita/Algorithm at ce7dc1da842c7c5b8096a886d803acfb24d71a67.
Unused declarations are omitted; live thin proofs are inlined and imports normalized.
Apache-2.0 license: Library/ConceptDynamics/zhao2023algorithm.md.
Retire this port when equivalent declarations are available in this repository's
actual pinned Mathlib revision, replacing uses by direct imports and applications.
-/

variable {C ι α : Type*} {Valid : C → ι → Prop}

class SetElem (C : Type*) (ι : Type*) (α : outParam Type*) where
  protected setElem : C → ι → α → C

macro:max c:term noWs "[" i:term " => " v:term "]" : term => `(SetElem.setElem $c $i $v)
macro:max c:term noWs "[" i:term " ↦ " v:term "]" : term => `(SetElem.setElem $c $i $v)

class GetSetElem (C : Type*) (ι : Type*) (α : outParam Type*)
    (Valid : outParam (C → ι → Prop)) extends GetElem C ι α Valid, SetElem C ι α where
  valid_setElem {c} {i : ι} {x j} : Valid c[i ↦ x] j ↔ i = j ∨ Valid c j := by get_elem_tactic
  getElem_setElem_self c i x :
    c[i ↦ x][i]'(valid_setElem.mpr <| .inl rfl) = x
  getElem_setElem_of_ne c {i} x {j} (hij : i ≠ j)
    (hs : Valid c[i ↦ x] j := by get_elem_tactic) (h : Valid c j := by get_elem_tactic) :
    c[i ↦ x][j]'hs = c[j]'h
export GetSetElem (valid_setElem getElem_setElem_self getElem_setElem_of_ne)

attribute [simp] getElem_setElem_self getElem_setElem_of_ne

class HasValid (C : Type*) (ι : Type*) where
  Valid : C → ι → Prop

class GetElemAllValid (C : Type*) (ι : Type*) (α : outParam Type*) extends
    HasValid C ι, GetElem C ι α Valid where
  Valid := fun _ _ ↦ True
  all_valid {c i} : Valid c i := by get_elem_tactic
export GetElemAllValid (all_valid)

attribute [simp] all_valid

/-- Extending `get_elem_tactic` with `all_valid` still abstracts its proof in public statements,
hiding compound collection/index expressions from `rw`. Keep `all_valid` unabstracted;
the fallback retains normal proof abstraction, allowing private helper lemmas. -/
macro_rules
  | `($c[$i]) => `(getElem $c $i (set_option backward.proofsInPublic true in by first
    | done
    | exact GetElemAllValid.all_valid
    | exact set_option backward.proofsInPublic false in by get_elem_tactic))

class GetSetElemAllValid (C : Type*) (ι : Type*) (α : outParam Type*) extends
    GetElemAllValid C ι α, SetElem C ι α where
  getElem_setElem_self (c : C) (i : ι) v : c[i ↦ v][i]'all_valid = v
  getElem_setElem_of_ne (c : C) {i : ι} v {j} (hij : i ≠ j) :
    c[i ↦ v][j]'all_valid = c[j]'all_valid

instance GetSetElemAllValid.toGetSetElem (C ι α : Type*) [GetSetElemAllValid C ι α] :
    GetSetElem C ι α HasValid.Valid where
  valid_setElem := by simp
  getElem_setElem_self := getElem_setElem_self
  getElem_setElem_of_ne _ _ _ _ hij _ _ := getElem_setElem_of_ne _ _ hij
