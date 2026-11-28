/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module
prelude
public import OmegaInit.Data.List.Control
import all OmegaInit.Data.Nat.Bitwise.Basic

port_definition List.mapM'.match_1 with_native_code
port_definition List.mapM'._f
port_definition List.mapM'
port_structural_code List.mapM' on_arg 6
port_proof List.mapM'_nil by_reflexivity
port_proof List.mapM'_cons by_reflexivity
port_proof List.mapM_nil by_reflexivity

port_definition List.zipWithM'._sparseCasesOn_1
port_definition List.zipWithM'.match_1 with_native_code
port_definition List.zipWithM'._f
port_definition List.zipWithM'
port_structural_code List.zipWithM' on_arg 7
port_proof List.zipWithM'_nil_left by_reflexivity
port_proof List.zipWithM'_cons_cons by_reflexivity
port_proof List.zipWithM_nil_left by_reflexivity

namespace Omega.List

private theorem zipWithM'_nil_rightImpl {m : Type u → Type v} {α : Type w} {β : Type x} {γ : Type u}
    {l : List α} [inst : Monad m] {f : α → β → m γ} :
    Eq (zipWithM' f l List.nil) (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) (List γ) List.nil) :=
  List.casesOn l rfl (fun _ _ => rfl)

private theorem zipWithM_nil_rightImpl {m : Type u → Type v} {α : Type w} {β : Type x} {γ : Type u}
    {l : List α} [inst : Monad m] {f : α → β → m γ} :
    Eq (zipWithM f l List.nil) (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) (List γ) List.nil) :=
  List.casesOn l rfl (fun _ _ => rfl)

end Omega.List

port_proof List.zipWithM'_nil_right using Omega.List.zipWithM'_nil_rightImpl
port_proof List.zipWithM_nil_right using Omega.List.zipWithM_nil_rightImpl
