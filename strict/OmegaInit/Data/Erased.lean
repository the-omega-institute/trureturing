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

/- The original out_mk, mk_out, out_inj and out_inj_iff refer to Erased.out.
Recovering a value at every universe with its constructor equation is equivalent
to selection for the singleton predicates represented by Erased. The constructive
extractor for a carrier in Prop and the equivalence of inverse laws are in
OmegaChecks.InitBoundaries.ErasedSelection. The unrestricted extractor is open. -/
