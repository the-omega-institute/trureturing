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

end OmegaChecks.InitCompiler.ProofRules
