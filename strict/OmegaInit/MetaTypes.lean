/-
Copyright (c) Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude

noncomputable section

public section

namespace Omega

inductive Lean.Meta.EtaStructMode where
  | «all»
  | notClasses
  | «none»

inductive Lean.Meta.TransparencyMode where
  | «all»
  | «default»
  | reducible
  | instances
  | «none»
  | «implicit»

end Omega
