/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
module
prelude
public import OmegaInit.Core

port_proof Classical.exists_true_of_nonempty

/- Classical.epsilon_singleton selects from the predicate y = x. Its strict specialization
returns x. The pinned type refers directly to Classical.epsilon, whose full type gives
Classical.choice by applying it to the constantly true predicate. -/
