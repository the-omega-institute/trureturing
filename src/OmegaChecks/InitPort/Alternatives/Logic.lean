module
public import Init.SimpLemmas
public import Init.Sym.Lemmas
public import Init.Data.Sum.Lemmas

namespace OmegaChecks.InitPort.Alternatives

public theorem let_congr : type_of% @_root_.let_congr :=
  fun {_ _ a _ _ _} ha hb => ha ▸ hb a

public theorem let_body_congr : type_of% @_root_.let_body_congr :=
  fun {_ _ _ _} a h => h a

public theorem have_congr' : type_of% @_root_.have_congr' :=
  @_root_.OmegaChecks.InitPort.Alternatives.let_congr

public theorem Lean.Sym.ite_of_decide_eq_true_congr :
    type_of% @_root_.Lean.Sym.ite_of_decide_eq_true_congr :=
  fun {_} _ {_} _ _ _ h {_ ht} => ite_eq_left (h.mpr (of_decide_eq_true ht))

public theorem Lean.Sym.ite_of_decide_eq_false_congr :
    type_of% @_root_.Lean.Sym.ite_of_decide_eq_false_congr :=
  fun {_} _ {_} _ _ _ h {_ ht} => ite_eq_right (fun hc => of_decide_eq_false ht (h.mp hc))

public theorem Sum.elim_eq_iff : type_of% @_root_.Sum.elim_eq_iff := by
  intro α β γ u u' v v'
  constructor
  · intro e
    exact ⟨congrArg (fun f => f ∘ Sum.inl) e, congrArg (fun f => f ∘ Sum.inr) e⟩
  · rintro ⟨rfl, rfl⟩
    rfl

end OmegaChecks.InitPort.Alternatives
