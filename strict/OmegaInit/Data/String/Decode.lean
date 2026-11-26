/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module
prelude

noncomputable section

public section

namespace Omega

inductive ByteArray.utf8DecodeChar?.FirstByte where
  | invalid
  | «done»
  | oneMore
  | twoMore
  | threeMore

end Omega
