/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module
prelude
public import OmegaInit.Data.Range.Polymorphic.Nat

port_proof Std.PRange.Nat.succ?_eq by_reflexivity
port_proof Std.PRange.Nat.succMany?_eq by_reflexivity
port_proof Std.PRange.Nat.succ_eq by_reflexivity
port_proof Std.PRange.Nat.succMany_eq by_reflexivity

/- The pinned lookup flags are coerced to propositions. For each open equation below,
the first specialization forces (true = true) = Nat.le 1 1 and the second forces
(false = true) = Nat.le 2 1. In each case the two propositions have different
inductive heads. A proof by reflexivity fails at both inputs. RangeIndex proves
the exact reflection condition next to each name. Arguments follow the pinned binder order.

Nat.isSome_getElem?_toList_rco_eq  (0 1 0), (0 1 1)  LTReflection
Nat.isSome_getElem?_toList_roc_eq  (0 1 0), (0 1 1)  LTReflection
Nat.isSome_getElem?_toList_roo_eq  (0 2 0), (0 2 1)  LTReflection
Nat.isSome_getElem?_toList_rcc_eq  (0 0 0), (0 0 1)  LTReflection
Nat.isSome_getElem?_toList_rio_eq  (1 0), (1 1)  LTReflection
Nat.isSome_getElem?_toList_ric_eq  (1 1), (1 2)  LEReflection
Nat.isNone_getElem?_toList_rco_eq  (0 1 1), (0 2 1)  LEReflection
Nat.isNone_getElem?_toList_roc_eq  (0 1 1), (0 2 1)  LEReflection
Nat.isNone_getElem?_toList_roo_eq  (0 1 0), (0 2 0)  LEPositiveRight
Nat.isNone_getElem?_toList_rcc_eq  (0 0 1), (0 1 1)  LTReflection
Nat.isNone_getElem?_toList_rio_eq  (1 1), (2 1)  LEReflection
Nat.isNone_getElem?_toList_ric_eq  (0 1), (1 1)  LTReflection
Nat.isSome_getElem?_toArray_rco_eq  (0 1 0), (0 1 1)  LTReflection
Nat.isSome_getElem?_toArray_roc_eq  (0 1 0), (0 1 1)  LTReflection
Nat.isSome_getElem?_toArray_roo_eq  (0 2 0), (0 2 1)  LTReflection
Nat.isSome_getElem?_toArray_rcc_eq  (0 0 0), (0 0 1)  LTReflection
Nat.isSome_getElem?_toArray_rio_eq  (1 0), (1 1)  LTReflection
Nat.isSome_getElem?_toArray_ric_eq  (1 1), (1 2)  LEReflection
Nat.isNone_getElem?_toArray_rco_eq  (0 1 1), (0 2 1)  LEReflection
Nat.isNone_getElem?_toArray_roc_eq  (0 1 1), (0 2 1)  LEReflection
Nat.isNone_getElem?_toArray_roo_eq  (0 1 0), (0 2 0)  LEPositiveRight
Nat.isNone_getElem?_toArray_rcc_eq  (0 0 1), (0 1 1)  LTReflection
Nat.isNone_getElem?_toArray_rio_eq  (1 1), (2 1)  LEReflection
Nat.isNone_getElem?_toArray_ric_eq  (0 1), (1 1)  LTReflection
-/
