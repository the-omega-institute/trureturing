module
public import Init.Core
import all Init.Data.Int.Linear

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

public theorem natBEq (a b : Nat) : a.beq b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl _⟩

public theorem intBEq (a b : Int) : a.beq' b = true ↔ a = b := by
  rw [Int.beq'_eq_beq]
  exact beq_iff_eq

public theorem intBNe (a b : Int) : a.beq' b = false ↔ a ≠ b := by
  rw [Int.beq'_eq_beq]
  exact beq_eq_false_iff_ne

public theorem polyBEq (p q : Int.Internal.Linear.Poly) : p.beq' q = true ↔ p = q := by
  induction p generalizing q with
  | num k =>
    cases q with
    | num l => exact ⟨fun h => congrArg _ ((intBEq ..).mp h), fun h => (intBEq ..).mpr (by cases h; rfl)⟩
    | add => exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | add k x p ih =>
    cases q with
    | num => exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
    | add l y q =>
      constructor
      · intro h
        obtain ⟨hk,tail⟩ := Bool.and_eq_true_iff.mp h
        obtain ⟨hv,hp⟩ := Bool.and_eq_true_iff.mp tail
        cases (intBEq ..).mp hk
        cases Nat.eq_of_beq_eq_true hv
        exact congrArg (Int.Internal.Linear.Poly.add k x) ((ih q).mp hp)
      · intro h
        cases h
        exact Bool.and_eq_true_iff.mpr ⟨(intBEq ..).mpr rfl, Bool.and_eq_true_iff.mpr ⟨Nat.beq_refl _, (ih p).mpr rfl⟩⟩
end OmegaChecks.InitCompiler.ProofRules
