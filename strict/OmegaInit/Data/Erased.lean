/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Sebastian Graf
-/
module
prelude
public import OmegaInit.Classical
public import OmegaInit.Ext

port_definition Erased
port_proof Erased.mk._proof_1
port_definition Erased.mk with_native_code
port_alternative_proof Erased.mk_inj from OmegaChecks.InitPort.Alternatives.Logic

/- Erased.out, Erased.out_mk, Erased.mk_out, Erased.out_inj and Erased.out_inj_iff
remain open at the original polymorphic signatures. A selector for the singleton
predicates represented by Erased gives one extractor satisfying all four laws.
For carriers in Prop the extractor is constructive. For carriers in Type v,
choice from nonempty subsingletons suffices. Conversely, given extensional equality
of predicates, the bare extractor selects from every nonempty subsingleton of that
universe. On Bool, recovering each constructor is equivalent to deciding e.val false
for every e. See OmegaChecks.InitBoundaries.ErasedSelection. -/
