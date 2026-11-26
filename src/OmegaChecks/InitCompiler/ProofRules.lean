module
public import Init.Core

namespace OmegaChecks.InitCompiler.ProofRules

/-- Conditional congruence consumes just the two implications between the guards. -/
public theorem iteCongr {α : Sort u} {b c : Prop} {x y s t : α} [Decidable b] [Decidable c]
    (h : b ↔ c) (yes : c → x = s) (no : ¬c → y = t) :
    (if b then x else y) = (if c then s else t) :=
  Decidable.byCases (p := c)
    (fun hc => (ite_eq_left (h.mpr hc)).trans ((yes hc).trans (ite_eq_left hc).symm))
    (fun hc => (ite_eq_right (fun hb => hc (h.mp hb))).trans ((no hc).trans (ite_eq_right hc).symm))

public theorem diteCongr {b c : Prop} {α : Sort u} [Decidable b] [Decidable c]
    {x : b → α} {s : c → α} {y : ¬b → α} {t : ¬c → α}
    (h : b ↔ c) (yes : ∀ hc, x (h.mpr hc) = s hc)
    (no : ∀ hc, y (fun hb => hc (h.mp hb)) = t hc) : dite b x y = dite c s t :=
  Decidable.byCases (p := c)
    (fun hc => (dite_eq_left (h.mpr hc)).trans ((yes hc).trans (dite_eq_left hc).symm))
    (fun hc => (dite_eq_right (fun hb => hc (h.mp hb))).trans ((no hc).trans (dite_eq_right hc).symm))

/-- Change a propositional binder while retaining the dependency on its proof. -/
public theorem forallDomain {a c : Prop} {b : a → Prop} {d : c → Prop}
    (ac : a ↔ c) (step : ∀ hc, b (ac.mpr hc) ↔ d hc) : (∀ ha, b ha) ↔ ∀ hc, d hc :=
  ⟨fun f hc => (step hc).mp (f (ac.mpr hc)), fun g ha => (step (ac.mp ha)).mpr (g (ac.mp ha))⟩

/-- Equivalent guards compute the same Boolean for every pair of decision instances. -/
public theorem decideCongr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) :
    decide p = decide q :=
  Decidable.byCases (p := p)
    (fun hp => (decide_eq_true hp).trans (decide_eq_true (h.mp hp)).symm)
    (fun hp => (decide_eq_false hp).trans (decide_eq_false (fun hq => hp (h.mpr hq))).symm)

end OmegaChecks.InitCompiler.ProofRules
