/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
module
prelude
public import OmegaInit.Core

port_proof Classical.exists_true_of_nonempty
port_definition Classical.indefiniteDescription.match_1
port_definition Classical.propDecidable.match_1
port_definition Classical.typeDecidable.match_1

/- An implementation of any of Classical.choose, Exists.choose, Classical.epsilon,
Classical.indefiniteDescription, Classical.strongIndefiniteDescription,
Classical.inhabited_of_nonempty or Classical.inhabited_of_exists would select a
value of an arbitrary nonempty type. In the predicate-based interfaces, take the
predicate to be constantly true. For Classical.typeDecidable, its positive
branch supplies the value and its negative branch contradicts nonemptiness.
The type reductions are checked in OmegaChecks.InitBoundaries.reductions.

Classical.choose_spec, Exists.choose_spec, Classical.epsilon_spec,
Classical.epsilon_spec_aux and Classical.choose.congr_simp refer to those
selectors in their statements. ChoiceOperands.certifyEndpoints checks their
specialized occurrences against the pinned statements.

Classical.propComplete identifies each proposition with True or False.
Applying this classification to two equivalent propositions yields propext,
as proved by OmegaChecks.InitBoundaries.propextFromPropComplete. -/

/- Classical.epsilon_singleton selects from the predicate y = x. Its strict specialization
returns x. The pinned type refers directly to Classical.epsilon, whose full type gives
Classical.choice by applying it to the constantly true predicate. -/
