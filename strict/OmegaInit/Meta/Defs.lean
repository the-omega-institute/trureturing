/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura and Sebastian Ullrich

Additional goodies for writing macros
-/
module
prelude

noncomputable section

public section

namespace Omega

inductive Lean.Meta.ApplyNewGoals where
  | nonDependentFirst
  | nonDependentOnly
  | «all»

end Omega
