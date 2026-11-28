/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module
prelude
public import OmegaInit.System.IO
public import OmegaInit.Core

port_native_records Lean.Order.PartialOrder
port_proof Lean.Order.PartialOrder.rel_of_eq
port_definition Lean.Order.chain
port_definition Lean.Order.is_sup
port_proof Lean.Order.is_sup_unique
port_definition Lean.Order.is_meet
port_native_records Lean.Order.CCPO, Lean.Order.CompleteLattice
port_definition Lean.Order.empty_chain
port_proof Lean.Order.chain_empty
port_definition Lean.Order.monotone
port_proof Lean.Order.monotone_id
port_proof Lean.Order.monotone_const
port_proof Lean.Order.monotone_compose
port_definition Lean.Order.PartialOrder.noConfusionType
port_definition Lean.Order.PartialOrder.noConfusion
port_definition Lean.Order.PartialOrder.mk.noConfusion
port_definition Lean.Order.PartialOrder.ctorIdx with_native_code
port_definition Lean.Order.CCPO.noConfusionType
port_definition Lean.Order.CCPO.noConfusion
port_definition Lean.Order.CCPO.mk.noConfusion
port_definition Lean.Order.CCPO.ctorIdx with_native_code
port_definition Lean.Order.CompleteLattice.noConfusionType
port_definition Lean.Order.CompleteLattice.noConfusion
port_definition Lean.Order.CompleteLattice.mk.noConfusion
port_definition Lean.Order.CompleteLattice.ctorIdx with_native_code

attribute [instance] Omega.Lean.Order.CCPO.toPartialOrder
attribute [instance] Omega.Lean.Order.CompleteLattice.toPartialOrder
port_proof Lean.Order.chain_conj
port_definition Lean.Order.instPartialOrderUnit with_native_code
attribute [instance] Omega.Lean.Order.instPartialOrderUnit
port_proof Lean.Order.Unit.unit_le
port_proof Lean.Order.instCCPOUnit._proof_1
port_definition Lean.Order.instCCPOUnit with_native_code
attribute [instance] Omega.Lean.Order.instCCPOUnit
port_proof Lean.Order.instCompleteLatticeUnit._proof_1
port_definition Lean.Order.instCompleteLatticeUnit with_native_code
attribute [instance] Omega.Lean.Order.instCompleteLatticeUnit

port_definition Lean.Order.FlatOrder
port_definition Lean.Order.FlatOrder.mk with_native_code
port_definition Lean.Order.FlatOrder.inner with_native_code
port_proof Lean.Order.FlatOrder.mk_inner by_reflexivity
port_proof Lean.Order.FlatOrder.inner_mk by_reflexivity
port_proof Lean.Order.FlatOrder.mk_inj
port_inductive Lean.Order.FlatOrder.rel
port_proof Lean.Order.FlatOrder.instOrder._proof_1
port_proof Lean.Order.FlatOrder.instOrder._proof_2
port_definition Lean.Order.FlatOrder.instOrder with_native_code
attribute [instance] Omega.Lean.Order.FlatOrder.instOrder

/- CCPO.csup and CompleteLattice.sup have to return a value from a mere
existence proof. Each full selector yields selection from every inhabited
subsingleton by taking the empty chain or set (InternalOrder.uniqueChoiceOfChainSup
and uniqueChoiceOfSup). CCPO.csup_spec, csup_le, le_csup, CompleteLattice.sup_spec,
sup_le and le_sup refer to these selectors in their types.

Lean.Order.iterates.sup uses CCPO.csup as the result index. Lean.Order.iterates
and its step, sup, casesOn, rec, recOn, below, below.step, below.sup, below.rec,
below.casesOn and brecOn therefore require a selector in the inductive family.
InternalOrder.ChainIteration.Generated uses any value satisfying is_sup.
Its relation to the pinned predicate is officialIff. Reconstructing the
unrestricted selector and the original family is open. -/

/- The public flat_csup_eq and flat_csup_is_sup use flat_csup. Its specified
behavior selects a nonbottom point even when the predicate is not a chain.
InternalOrder.choiceFromFlatPresence recovers Classical.choice from that behavior.
On chains, FlatSelection.smallChainSelections characterizes the small-universe
supremum law, and eqIffChainLaw characterizes agreement with a certified supremum. -/
