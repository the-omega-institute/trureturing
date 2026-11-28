/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Chad Sharp
-/
module
prelude
public import OmegaInit.Data.List.Basic
public import OmegaInit.Control.Id

port_structural_code private List.scanAuxM.go on_arg 6

namespace Omega.List

@[inline, irreducible] public def scanlM [Monad m] (f : β → α → m β) (init : β) (l : List α) : m (List β) :=
  @Functor.map m (show Monad m from inferInstance).toApplicative.toFunctor _ _ List.reverse (scanAuxM.go f l init .nil)

@[inline, irreducible] public def scanrM [Monad m] (f : α → β → m β) (init : β) (xs : List α) : m (List β) :=
  scanAuxM.go (flip f) xs.reverse init .nil

end Omega.List

port_definition List.scanl with_native_code
port_definition List.scanr with_native_code
