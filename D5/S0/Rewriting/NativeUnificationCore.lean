/- GID: D5/S0/Rewriting/NativeUnificationCore
   generality: G
   mirror-B: D5/B/S0/Rewriting/NativeUnificationCore
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Native finite term encoding and consumed finite-map primitives. -/

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Upstream: strata-org/Strata commit a74043b69b98d4197dfd7d59df1b4427dcfc3f37.
Retirement: replace this port by direct imports when this repository pinned
dependency contains equivalent usable declarations for this consumed closure.

LICENSE-APACHE

                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

LICENSE-MIT
Copyright (c) Strata Contributors

Permission is hereby granted, free of charge, to any
person obtaining a copy of this software and associated
documentation files (the "Software"), to deal in the
Software without restriction, including without
limitation the rights to use, copy, modify, merge,
publish, distribute, sublicense, and/or sell copies of
the Software, and to permit persons to whom the Software
is furnished to do so, subject to the following
conditions:

The above copyright notice and this permission notice
shall be included in all copies or substantial portions
of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF
ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED
TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A
PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT
SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR
IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
DEALINGS IN THE SOFTWARE.
NOTICE
Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.

-/

import Mathlib.Tactic
import Mathlib.Algebra.Free
import Mathlib.Data.Fintype.EquivFin
import Std.Data.HashMap.Lemmas
import Std.Tactic.BVDecide

set_option autoImplicit false
set_option relaxedAutoImplicit false


namespace Lambda
section
set_option autoImplicit true
set_option relaxedAutoImplicit true
open Std (ToFormat Format format)
set_option relaxedAutoImplicit true
abbrev TyIdentifier := String
inductive LMonoTy : Type where
  | ftvar (name : TyIdentifier)
  | tcons (name : String) (args : List LMonoTy)
  | bitvec (size : Nat)
abbrev LMonoTys := List LMonoTy
@[induction_eliminator]
theorem LMonoTy.induct {P : LMonoTy → Prop}
  (ftvar : ∀f, P (.ftvar f))
  (bitvec : ∀n, P (.bitvec n))
  (tcons : ∀name args, (∀ ty ∈ args, P ty) → P (.tcons name args)) :
  ∀ ty, P ty := by
  intro n
  apply LMonoTy.rec <;> try assumption
  case nil => simp
  case cons =>
    intro head tail h_head h_tail
    simp_all
  done
mutual
@[simp]
def LMonoTy.size (ty : LMonoTy) : Nat :=
  match ty with
  | .ftvar _ => 1
  | .tcons _ args => 1 + LMonoTys.size args
  | .bitvec _ => 1
@[simp]
def LMonoTys.size (args : LMonoTys) : Nat :=
    match args with
    | [] => 0
    | t :: rest => LMonoTy.size t + LMonoTys.size rest
end
def LMonoTy.BEq (x y : LMonoTy) : Bool :=
  match x, y with
  | .ftvar i, .ftvar j => i == j
  | .bitvec i, .bitvec j => i == j
  | .tcons i1 j1, .tcons i2 j2 =>
    i1 == i2 && j1.length == j2.length && go j1 j2
  | _, _ => false
  where go j1 j2 :=
  match j1, j2 with
  | [], _ => true
  | _, [] => true
  | x :: xrest, y :: yrest =>
    LMonoTy.BEq x y && go xrest yrest
@[simp]
theorem LMonoTy.BEq_refl : LMonoTy.BEq ty ty := by
  induction ty <;> simp_all [LMonoTy.BEq]
  rename_i name args ih
  induction args
  case tcons.nil => simp [LMonoTy.BEq.go]
  case tcons.cons =>
    rename_i head tail ih'
    simp_all [LMonoTy.BEq.go]
  done
instance : DecidableEq LMonoTy :=
  fun x y =>
    if h: LMonoTy.BEq x y then
      isTrue (by
                induction x generalizing y
                case ftvar =>
                  unfold LMonoTy.BEq at h <;> split at h <;> try simp_all
                case bitvec =>
                  unfold LMonoTy.BEq at h <;> split at h <;> try simp_all
                case tcons =>
                  rename_i name args ih
                  cases y <;> try simp_all [LMonoTy.BEq]
                  rename_i name' args'
                  obtain ⟨⟨h1, h2⟩, h3⟩ := h
                  induction args generalizing args'
                  case nil => unfold List.length at h2; split at h2 <;> simp_all
                  case cons head' tail' ih' =>
                    unfold LMonoTy.BEq.go at h3 <;> split at h3 <;> try simp_all
                    rename_i j1 j2 x xrest y yrest heq
                    obtain ⟨h3_1, h3_2⟩ := h3
                    obtain ⟨ih1, ih2⟩ := ih
                    exact ⟨ih1 y h3_1, ih' ih2 yrest h3_2 rfl⟩)
    else
      isFalse (by induction x generalizing y
                  case ftvar =>
                    cases y <;> try simp_all [LMonoTy.BEq]
                  case bitvec n =>
                    cases y <;> try simp_all [LMonoTy.BEq]
                  case tcons name args ih =>
                    cases y <;> try simp_all [LMonoTy.BEq]
                    rename_i name' args'
                    intro hname; simp [hname] at h
                    induction args generalizing args'
                    case tcons.nil =>
                      simp [LMonoTy.BEq.go] at h
                      unfold List.length at h; split at h <;> simp_all
                    case tcons.cons head tail ih' =>
                      cases args' <;> try simp_all
                      rename_i head' tail'; intro _
                      have ih'' := @ih' tail'
                      unfold LMonoTy.BEq.go at h
                      simp_all)
mutual
def LMonoTy.freeVars (mty : LMonoTy) : List TyIdentifier :=
  match mty with
  | .ftvar x => [x]
  | .bitvec _ => []
  | .tcons _ ltys => LMonoTys.freeVars ltys
def LMonoTys.freeVars (mtys : LMonoTys) : List TyIdentifier :=
    match mtys with
    | [] => [] | ty :: rest => LMonoTy.freeVars ty ++ LMonoTys.freeVars rest
end
@[simp]
theorem LMonoTys.freeVars_of_cons :
  LMonoTys.freeVars (x :: xs) = LMonoTy.freeVars x ++ LMonoTys.freeVars xs := by
  simp_all [LMonoTys.freeVars]
open Std (ToFormat Format format)
theorem LMonoTy.size_gt_zero :
  0 < LMonoTy.size ty := by
  induction ty <;>  simp_all [LMonoTy.size]
  all_goals (unfold LMonoTys.size; split; simp_all; omega)
theorem LMonoTy.size_lt_of_mem {ty: LMonoTy} {tys: LMonoTys} (h: ty ∈ tys):
  ty.size <= tys.size := by
  induction tys <;> simp only[LMonoTys.size]<;> grind
theorem LMonoTys.freeVars_mem_subset
    {ty : LMonoTy} {tys : List LMonoTy}
    (ht : ty ∈ tys)
    : LMonoTy.freeVars ty ⊆ LMonoTys.freeVars tys := by
  induction tys with
  | nil => contradiction
  | cons x rest ih =>
    simp only [LMonoTys.freeVars_of_cons]
    grind
theorem LMonoTys.freeVars_exists
    {v : TyIdentifier} {tys : List LMonoTy}
    (hv : v ∈ LMonoTys.freeVars tys)
    : ∃ ty, ty ∈ tys ∧ v ∈ LMonoTy.freeVars ty := by
  induction tys with
  | nil => simp [LMonoTys.freeVars] at hv
  | cons ty rest ih =>
    simp only [LMonoTys.freeVars_of_cons, List.mem_append] at hv
    cases hv with
    | inl h => exact ⟨ty, .head _, h⟩
    | inr h => obtain ⟨t, ht, htv⟩ := ih h; exact ⟨t, .tail _ ht, htv⟩
end
end Lambda

namespace Strata.Util
section
set_option autoImplicit true
set_option relaxedAutoImplicit true
structure HMap (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  private mk ::
  private rep : Std.HashMap α β
namespace HMap
variable {α : Type u} {β : Type v} {γ : Type w} [BEq α] [Hashable α]
def empty : HMap α β := ⟨Std.HashMap.emptyWithCapacity⟩
def insert (m : HMap α β) (a : α) (b : β) : HMap α β :=
  ⟨m.rep.insert a b⟩
def find? (m : HMap α β) (a : α) : Option β :=
  m.rep.get? a
def isEmpty (m : HMap α β) : Bool :=
  m.rep.isEmpty
def keys (m : HMap α β) : List α :=
  m.rep.keys
def toList (m : HMap α β) : List (α × β) :=
  m.rep.toList
def values (m : HMap α β) : List β :=
  m.toList.map Prod.snd
def ofList (l : List (α × β)) : HMap α β :=
  ⟨Std.HashMap.ofList l⟩
def single (a : α) (b : β) : HMap α β :=
  (empty : HMap α β).insert a b
def mapValues (f : β → γ) (m : HMap α β) : HMap α γ :=
  ⟨m.rep.map (fun _ v => f v)⟩
@[simp]
theorem find?_empty (a : α) : (empty : HMap α β).find? a = none := by
  simp [find?, empty]
@[simp]
theorem find?_insert_self [EquivBEq α] [LawfulHashable α]
    (m : HMap α β) (a : α) (b : β) :
    (m.insert a b).find? a = some b := by
  unfold find? insert
  simp
theorem find?_insert_ne [EquivBEq α] [LawfulHashable α]
    (m : HMap α β) (a x : α) (b : β) (h : x != a) :
    (m.insert a b).find? x = m.find? x := by
  unfold find? insert
  simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  have hx : (x == a) = false := by simpa [bne] using h
  have h' : (a == x) = false := by rw [BEq.comm]; exact hx
  simp [h']
theorem find?_of_isEmpty [EquivBEq α] [LawfulHashable α]
    (m : HMap α β) (a : α) (h : m.isEmpty) : m.find? a = none := by
  simp only [find?, Std.HashMap.get?_eq_getElem?]
  exact Std.HashMap.getElem?_of_isEmpty h
theorem mem_values_iff_find? [LawfulBEq α] [LawfulHashable α]
    (m : HMap α β) (v : β) :
    v ∈ m.values ↔ ∃ k, m.find? k = some v := by
  simp only [values, find?, List.mem_map, toList]
  constructor
  · rintro ⟨⟨k, v'⟩, h_mem, rfl⟩
    exact ⟨k, (Std.HashMap.mem_toList_iff_getElem?_eq_some.mp h_mem)⟩
  · rintro ⟨k, hk⟩
    exact ⟨(k, v), Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hk, rfl⟩
theorem mem_keys_iff_find? [LawfulBEq α] [LawfulHashable α]
    (m : HMap α β) (k : α) :
    k ∈ m.keys ↔ ∃ v, m.find? k = some v := by
  simp only [keys, find?, Std.HashMap.mem_keys, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.mem_iff_isSome_getElem?, Option.isSome_iff_exists]
theorem find?_mem_keys [LawfulBEq α] [LawfulHashable α]
    (m : HMap α β) (h : m.find? k = some v) : k ∈ m.keys :=
  (mem_keys_iff_find? m k).mpr ⟨v, h⟩
theorem find?_mem_values [LawfulBEq α] [LawfulHashable α]
    (m : HMap α β) (h : m.find? k = some v) : v ∈ m.values :=
  (mem_values_iff_find? m v).mpr ⟨k, h⟩
theorem mem_keys_ofList [LawfulBEq α] [LawfulHashable α]
    (l : List (α × β)) (k : α) (hk : k ∈ (HMap.ofList l).keys) :
    k ∈ l.map Prod.fst := by
  simp only [keys, ofList, Std.HashMap.mem_keys] at hk
  rw [Std.HashMap.mem_ofList] at hk
  exact List.contains_iff_mem.mp hk
theorem find?_ofList_self_map [LawfulBEq α] [LawfulHashable α]
    (l : List α) (g : α → β) (k : α) (hk : k ∈ l) :
    HMap.find? (HMap.ofList (l.map (fun a => (a, g a)))) k = some (g k) := by
  have hfs : ∀ (L : List α), k ∈ L →
      List.findSome? (fun x => if (x.fst == k) = true then some x.snd else none)
        (L.map (fun a => (a, g a))) = some (g k) := by
    intro L hL
    induction L with
    | nil => simp at hL
    | cons a rest ih =>
      simp only [List.map_cons, List.findSome?_cons]
      by_cases h : (a == k) = true
      · simp only [h, if_true]; rw [beq_iff_eq] at h; rw [h]
      · simp only [h, Bool.false_eq_true, if_false]
        apply ih; simp only [List.mem_cons] at hL
        rcases hL with h' | h'
        · rw [h'] at h; simp at h
        · exact h'
  simp only [find?, ofList, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.ofList_eq_insertMany_empty, Std.HashMap.getElem?_insertMany_list,
    Std.HashMap.getElem?_empty, Option.or_none]
  rw [List.findSomeRev?_eq_findSome?_reverse, ← List.map_reverse]
  exact hfs l.reverse (by rw [List.mem_reverse]; exact hk)
theorem find?_of_not_mem_keys [LawfulBEq α] [LawfulHashable α]
    (m : HMap α β) (h : m.find? k = none) : k ∉ m.keys := by
  intro hk
  obtain ⟨v, hv⟩ := (mem_keys_iff_find? m k).mp hk
  rw [hv] at h; exact absurd h (by simp)
theorem not_mem_keys_find?_none [LawfulBEq α] [LawfulHashable α]
    (m : HMap α β) (k : α) (h : k ∉ m.keys) : m.find? k = none := by
  cases hf : m.find? k with
  | none => rfl
  | some v => exact absurd (find?_mem_keys m hf) h
theorem insert_keys_subset [LawfulBEq α] [LawfulHashable α]
    (m : HMap α β) (key : α) (val : β) :
    ∀ k, k ∈ (m.insert key val).keys → k ∈ key :: m.keys := by
  intro k hk
  simp only [keys, insert] at hk
  rw [Std.HashMap.mem_keys] at hk
  rw [Std.HashMap.mem_insert] at hk
  rcases hk with h | h
  · rw [LawfulBEq.eq_of_beq h]; exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (by rw [mem_keys_iff_find?]; rw [Std.HashMap.mem_iff_isSome_getElem?, Option.isSome_iff_exists] at h; simpa [find?, Std.HashMap.get?_eq_getElem?] using h)
theorem insert_values_subset [LawfulBEq α] [LawfulHashable α]
    (m : HMap α β) (key : α) (val : β) :
    ∀ v, v ∈ (m.insert key val).values → v ∈ val :: m.values := by
  intro v hv
  rw [mem_values_iff_find?] at hv
  obtain ⟨k, hk⟩ := hv
  by_cases h : k = key
  · subst h; rw [find?_insert_self] at hk; injection hk with hk; subst hk; exact List.mem_cons_self
  · refine List.mem_cons_of_mem _ ?_
    rw [mem_values_iff_find?]
    exact ⟨k, by rw [← hk, find?_insert_ne m key k val (by simp [bne, h])]⟩
@[simp]
theorem find?_mapValues [LawfulBEq α] [LawfulHashable α]
    (f : β → γ) (m : HMap α β) (k : α) :
    (m.mapValues f).find? k = (m.find? k).map f := by
  simp only [find?, mapValues, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_map]
theorem mem_keys_mapValues_iff [LawfulBEq α] [LawfulHashable α]
    (f : β → γ) (m : HMap α β) (k : α) :
    k ∈ (m.mapValues f).keys ↔ k ∈ m.keys := by
  rw [mem_keys_iff_find?, mem_keys_iff_find?]
  constructor
  · rintro ⟨v, hv⟩; rw [find?_mapValues] at hv
    exact (Option.map_eq_some_iff.mp hv).imp (fun _ h => h.1)
  · rintro ⟨v, hv⟩; exact ⟨f v, by rw [find?_mapValues, hv]; rfl⟩
@[simp]
theorem find?_single_self [EquivBEq α] [LawfulHashable α]
    (a : α) (b : β) : (single a b).find? a = some b := by
  simp [single, find?_insert_self]
theorem find?_single_ne [EquivBEq α] [LawfulHashable α]
    (a x : α) (b : β) (h : x != a) : (single a b).find? x = none := by
  simp only [single]
  rw [find?_insert_ne _ a x b h, find?_empty]
theorem mem_keys_single_iff [LawfulBEq α] [LawfulHashable α]
    (a x : α) (b : β) : x ∈ (single a b).keys ↔ x = a := by
  rw [mem_keys_iff_find?]
  constructor
  · rintro ⟨v, hv⟩
    by_cases h : x = a
    · exact h
    · rw [find?_single_ne a x b (by simp [bne, h])] at hv; exact absurd hv (by simp)
  · rintro rfl; exact ⟨b, find?_single_self x b⟩
theorem mem_values_single_iff [LawfulBEq α] [LawfulHashable α]
    (a : α) (b v : β) : v ∈ (single a b).values ↔ v = b := by
  rw [mem_values_iff_find?]
  constructor
  · rintro ⟨k, hk⟩
    by_cases h : k = a
    · subst h; rw [find?_single_self] at hk; injection hk with hk; exact hk.symm
    · rw [find?_single_ne a k b (by simp [bne, h])] at hk; exact absurd hk (by simp)
  · rintro rfl; exact ⟨a, find?_single_self a v⟩
theorem mem_values_mapValues [LawfulBEq α] [LawfulHashable α]
    (f : β → γ) (m : HMap α β) (w : γ) :
    w ∈ (m.mapValues f).values ↔ ∃ v, v ∈ m.values ∧ w = f v := by
  rw [mem_values_iff_find?]
  constructor
  · rintro ⟨k, hk⟩
    rw [find?_mapValues] at hk
    obtain ⟨v, hv, hwv⟩ := Option.map_eq_some_iff.mp hk
    exact ⟨v, find?_mem_values m hv, hwv.symm⟩
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨k, hk⟩ := (mem_values_iff_find? m v).mp hv
    exact ⟨k, by rw [find?_mapValues, hk]; rfl⟩
end HMap
end
end Strata.Util

namespace List
section
set_option autoImplicit true
set_option relaxedAutoImplicit true
def uniq {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | a :: as =>
    let as := as.uniq
    if a ∈ as then as else a :: as
end
end List

namespace NativeTermUnification
open Lambda Strata.Util
abbrev Source := FreeMagma Bool
abbrev Term (X : Type) := FreeMagma (Bool ⊕ X)
structure Presentation (X : Type) where
  enumeration : List X
  complete : ∀ x, x ∈ enumeration
  code : X → String
  decode : String → Option X
  decode_code : ∀ x, decode (code x) = some x
  code_decode : ∀ s x, decode s = some x → code x = s
variable {X : Type}
def leaf (b : Bool) : LMonoTy := .tcons (if b then "native.true" else "native.false") []
def pair (a b : LMonoTy) : LMonoTy := .tcons "native.pair" [a,b]
def encode (p : Presentation X) : Term X → LMonoTy
  | .of (.inl b) => leaf b
  | .of (.inr x) => .ftvar (p.code x)
  | .mul a b => pair (encode p a) (encode p b)
def encodeGround : Source → LMonoTy
  | .of b => leaf b
  | .mul a b => pair (encodeGround a) (encodeGround b)
def evaluate (v : X → Source) : Term X → Source :=
  FreeMagma.lift (Sum.elim FreeMagma.of v)
inductive Shape : LMonoTy → Prop
  | var (s : String) : Shape (.ftvar s)
  | bool (b : Bool) : Shape (leaf b)
  | mul {a b} : Shape a → Shape b → Shape (pair a b)
def nativeDecode (p : Presentation X) : LMonoTy → Option (Term X)
  | .ftvar s => (p.decode s).map (fun x => .of (.inr x))
  | .tcons "native.false" [] => some (.of (.inl false))
  | .tcons "native.true" [] => some (.of (.inl true))
  | .tcons "native.pair" [a,b] => do
    let a' ← nativeDecode p a
    let b' ← nativeDecode p b
    pure (.mul a' b')
  | _ => none
  termination_by t => sizeOf t
def Supported (p : Presentation X) (t : LMonoTy) : Prop :=
  ∀ s ∈ t.freeVars, ∃ x, p.code x = s
theorem decode_encode (p : Presentation X) (t : Term X) : nativeDecode p (encode p t) = some t := by
  induction t with
  | of a => cases a with
    | inl b => cases b <;> simp [encode, leaf, nativeDecode]
    | inr x => simp [encode, nativeDecode, p.decode_code]
  | mul a b ha hb => simp [encode, pair, nativeDecode, ha, hb]
theorem encode_injective (p : Presentation X) : Function.Injective (encode p) := by
  intro a b h
  have := congrArg (nativeDecode p) h
  simpa only [decode_encode, Option.some.injEq] using this
theorem encode_shape (p : Presentation X) (t : Term X) : Shape (encode p t) := by
  induction t with
  | of a => cases a with
    | inl b => exact Shape.bool b
    | inr x => exact Shape.var _
  | mul a b ha hb => exact Shape.mul ha hb
theorem encode_supported (p : Presentation X) (t : Term X) : Supported p (encode p t) := by
  induction t with
  | of a => cases a with
    | inl b => cases b <;> simp [encode, leaf, Supported, LMonoTy.freeVars, LMonoTys.freeVars]
    | inr x => intro s hs; simp [encode, LMonoTy.freeVars] at hs; exact ⟨x, hs.symm⟩
  | mul a b ha hb =>
    intro s hs
    simp [encode, pair, LMonoTy.freeVars, LMonoTys.freeVars] at hs
    exact hs.elim (ha s) (hb s)
theorem decode_exact (p : Presentation X) (t : LMonoTy) (ht : Shape t) (hs : Supported p t) :
    ∃ a, nativeDecode p t = some a ∧ encode p a = t := by
  induction ht with
  | var s =>
    obtain ⟨x, hx⟩ := hs s (by simp [LMonoTy.freeVars])
    exact ⟨.of (.inr x), by simp [nativeDecode, ← hx, p.decode_code], by simp [encode, hx]⟩
  | bool b => cases b <;> refine ⟨.of (.inl _), ?_, rfl⟩ <;> simp [nativeDecode, leaf]
  | @mul a b ha hb iha ihb =>
    have hs' : Supported p a ∧ Supported p b := by
      constructor <;> intro s h
      · exact hs s (by simp [pair, LMonoTy.freeVars, LMonoTys.freeVars, h])
      · exact hs s (by simp [pair, LMonoTy.freeVars, LMonoTys.freeVars, h])
    obtain ⟨a', hda, hea⟩ := iha hs'.1
    obtain ⟨b', hdb, heb⟩ := ihb hs'.2
    exact ⟨.mul a' b', by simp [pair, nativeDecode, hda, hdb], by simp [encode, hea, heb]⟩
def finName (n : Nat) : String := String.ofList (List.replicate n 'v')
def finPresentation (n : Nat) : Presentation (Fin n) where
  enumeration := List.finRange n
  complete x := by simp
  code x := finName x.val
  decode s := if h : s.toList.length < n then
    if finName s.toList.length == s then some ⟨s.toList.length, h⟩ else none
    else none
  decode_code x := by simp [finName, x.isLt]
  code_decode s x h := by
    split at h
    · split at h
      · rename_i he
        cases h
        exact eq_of_beq he
      · simp at h
    · simp at h
def Presentation.transport {X Z : Type} (p : Presentation Z) (e : X ≃ Z) : Presentation X where
  enumeration := p.enumeration.map e.symm
  complete x := List.mem_map.mpr ⟨e x, p.complete (e x), e.symm_apply_apply x⟩
  code x := p.code (e x)
  decode s := (p.decode s).map e.symm
  decode_code x := by simp [p.decode_code]
  code_decode s x h := by
    obtain ⟨z, hz, he⟩ := Option.map_eq_some_iff.mp h
    rw [← he, e.apply_symm_apply]
    exact p.code_decode s z hz
noncomputable def finitePresentation (X : Type) [Finite X] : Presentation X := by
  letI := Fintype.ofFinite X
  exact (finPresentation (Fintype.card X)).transport (Fintype.equivFin X)
end NativeTermUnification
namespace NativeTermUnification
open Lambda
variable {X : Type}
theorem encode_decode (p : Presentation X) (t : LMonoTy) (a : Term X)
    (h : nativeDecode p t = some a) : encode p a = t := by
  revert a
  apply nativeDecode.induct (motive := fun t => ∀ a, nativeDecode p t = some a → encode p a = t)
  · intro s a h
    simp only [nativeDecode, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, rfl⟩ := h
    exact congrArg LMonoTy.ftvar (p.code_decode s x hx)
  · intro a h
    simp only [nativeDecode, Option.some.injEq] at h
    cases h; rfl
  · intro a h
    simp only [nativeDecode, Option.some.injEq] at h
    cases h; rfl
  · intro l r hl hr a h
    simp only [nativeDecode, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨l', hdl, r', hdr, he⟩ := h
    cases he
    exact congrArg₂ pair (hl l' hdl) (hr r' hdr)
  · intro t hv hf ht hp a h
    rw [nativeDecode.eq_def] at h
    split at h
    · exact (hv _ rfl).elim
    · exact (hf rfl).elim
    · exact (ht rfl).elim
    · exact (hp _ _ rfl).elim
    · contradiction
theorem decode_domain (p : Presentation X) (t : LMonoTy) :
    (∃ a, nativeDecode p t = some a) ↔ Shape t ∧ Supported p t := by
  constructor
  · rintro ⟨a, ha⟩
    rw [← encode_decode p t a ha]
    exact ⟨encode_shape p a, encode_supported p a⟩
  · rintro ⟨ht, hs⟩
    obtain ⟨a, ha, _⟩ := decode_exact p t ht hs
    exact ⟨a, ha⟩
end NativeTermUnification
