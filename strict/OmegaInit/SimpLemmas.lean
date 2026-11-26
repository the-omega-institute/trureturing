/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

notation, basic datatypes and type classes
-/
module
prelude
public import OmegaInit.Core

namespace Omega

public theorem iff_congr {p₁ p₂ q₁ q₂ : Prop} (h₁ : Iff p₁ p₂) (h₂ : Iff q₁ q₂) :
    Iff (Iff p₁ q₁) (Iff p₂ q₂) :=
  Iff.intro (fun h => h₁.symm.trans (h.trans h₂))
    (fun h => h₁.trans (h.trans h₂.symm))

end Omega

port_proof and_assoc
port_proof and_congr_right
port_proof and_congr_left
port_proof and_iff_left_of_imp
port_proof and_iff_left_iff_imp
port_proof and_iff_right_of_imp
port_proof and_iff_right_iff_imp
port_proof and_imp
port_proof and_not_self
port_proof forall_prop_congr_dom
port_proof of_eq_true
port_proof have_body_congr'
port_proof have_body_congr_dep'
port_proof have_unused' by_reflexivity
port_proof have_unused_dep'
port_proof have_val_congr'
port_proof or_iff_left_of_imp
port_proof or_iff_left_iff_imp
port_proof implies_congr
port_proof implies_congr_left
port_proof implies_congr_right
port_proof let_val_congr
port_proof ne_eq by_reflexivity
port_proof not_and
port_proof not_and_self
port_proof not_iff_self
port_proof of_eq_false
port_proof Or.imp
port_proof Or.imp_right
port_proof Or.imp_left
port_proof or_assoc
port_proof or_iff_right_of_imp
port_proof Bool.false_and by_reflexivity
port_proof Bool.false_or by_reflexivity
port_proof Bool.not_false by_reflexivity
port_proof Bool.not_true by_reflexivity
port_proof Bool.true_and by_reflexivity
port_proof Bool.true_or by_reflexivity
port_proof Eq.mpr_not
port_proof Eq.mpr_prop
