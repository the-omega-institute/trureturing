/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module
prelude
public import OmegaInit.Data.List.Control
import all OmegaInit.Data.Nat.Bitwise.Basic

port_definition List.zipWithM'._sparseCasesOn_1
port_definition List.zipWithM'.match_1
port_definition List.zipWithM'._f
port_definition List.zipWithM'
port_proof List.zipWithM'_nil_left by_reflexivity
port_proof List.zipWithM'_cons_cons by_reflexivity
port_proof List.zipWithM_nil_left by_reflexivity

namespace Omega.List

public theorem zipWithM'_nil_right {m : Type u → Type v} {α : Type w} {β : Type x} {γ : Type u}
    {l : List α} [mon : Monad m] {f : α → β → m γ} :
    Eq (zipWithM' f l List.nil) (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m mon)) (List γ) List.nil) :=
  List.casesOn l rfl (fun _ _ => rfl)

public theorem zipWithM_nil_right {m : Type u → Type v} {α : Type w} {β : Type x} {γ : Type u}
    {l : List α} [mon : Monad m] {f : α → β → m γ} :
    Eq (zipWithM f l List.nil) (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m mon)) (List γ) List.nil) :=
  List.casesOn l rfl (fun _ _ => rfl)

end Omega.List
