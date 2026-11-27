module
public import Init.Core
import all Init.Data.Int.Linear
import all Init.Grind.Ring.CommSolver

namespace OmegaChecks.InitCompiler.ProofRules

/-- A decision on the reverse comparison suffices at a call to the total-order law. -/
public theorem notLtDecidable {α : Type u} [LT α] [LE α] [Std.Total (α := α) (· ≤ ·)]
    [Std.LawfulOrderLT α] {a b : α} [Decidable (b ≤ a)] : ¬ a < b ↔ b ≤ a := by
  refine ⟨fun hn => ?_, Std.not_lt_of_ge⟩
  by_cases reverse : b ≤ a
  · exact reverse
  · exact (hn (Std.lt_iff_le_and_not_ge.mpr ⟨Std.le_of_not_ge reverse, reverse⟩)).elim

/-- A decidable reverse comparison also splits the strict-order law without totality. -/
public theorem notLtOrDecidable {α : Type u} [LT α] [LE α] [Std.LawfulOrderLT α]
    {a b : α} [Decidable (b ≤ a)] : ¬ a < b ↔ ¬ a ≤ b ∨ b ≤ a := by
  constructor
  · intro hn
    by_cases reverse : b ≤ a
    · exact .inr reverse
    · exact .inl (fun forward => hn (Std.lt_iff_le_and_not_ge.mpr ⟨forward, reverse⟩))
  · rintro (no | reverse) lt
    · exact no (Std.lt_iff_le_and_not_ge.mp lt).1
    · exact (Std.lt_iff_le_and_not_ge.mp lt).2 reverse

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

private theorem negNatLe {a b : Nat} : Int.negSucc a ≤ Int.negSucc b ↔ b ≤ a :=
  Int.neg_le_neg_iff.trans Int.ofNat_le |>.trans Nat.succ_le_succ_iff
private theorem negNatLt {a b : Nat} : Int.negSucc a < Int.negSucc b ↔ b < a :=
  Int.neg_lt_neg_iff.trans Int.ofNat_lt |>.trans Nat.succ_lt_succ_iff

public theorem intBLt (a b : Int) : a.blt' b = true ↔ a < b := by
  cases a with
  | ofNat n =>
    cases b with
    | ofNat m => exact (Iff.intro Nat.le_of_ble_eq_true Nat.ble_eq_true_of_le).trans Int.ofNat_lt.symm
    | negSucc m =>
      exact ⟨(fun h => nomatch h), fun h => False.elim (Int.not_lt_of_ge (Int.le_trans (Int.negSucc_le_zero m) (Int.natCast_nonneg n)) h)⟩
  | negSucc n =>
    cases b with
    | ofNat m => exact ⟨fun _ => Int.lt_of_lt_of_le (Int.negSucc_lt_zero n) (Int.natCast_nonneg m), fun _ => rfl⟩
    | negSucc m => exact (Iff.intro Nat.le_of_ble_eq_true Nat.ble_eq_true_of_le).trans negNatLt.symm

public theorem intBLe (a b : Int) : a.ble' b = true ↔ a ≤ b := by
  cases a with
  | ofNat n =>
    cases b with
    | ofNat m => exact (Iff.intro Nat.le_of_ble_eq_true Nat.ble_eq_true_of_le).trans Int.ofNat_le.symm
    | negSucc m =>
      exact ⟨(fun h => nomatch h), fun h => False.elim (Int.not_le_of_gt (Int.lt_of_lt_of_le (Int.negSucc_lt_zero m) (Int.natCast_nonneg n)) h)⟩
  | negSucc n =>
    cases b with
    | ofNat m => exact ⟨fun _ => Int.le_trans (Int.negSucc_le_zero n) (Int.natCast_nonneg m), fun _ => rfl⟩
    | negSucc m => exact (Iff.intro Nat.le_of_ble_eq_true Nat.ble_eq_true_of_le).trans negNatLe.symm

open Lean.Grind.CommRing

private theorem powerBeqSame (p q : Power) : p.beq' q = (p == q) := by
  cases p; cases q; rfl

private theorem monBeqSame (m n : Mon) : m.beq' n = (m == n) := by
  induction m generalizing n with
  | unit => cases n <;> rfl
  | mult p m ih =>
    cases n with
    | unit => rfl
    | mult q n =>
      change (p.beq' q && m.beq' n) = ((p == q) && (m == n))
      rw [powerBeqSame, ih]

private theorem ringPolyBeqSame (p q : Poly) : p.beq' q = (p == q) := by
  induction p generalizing q with
  | num k =>
    cases q with
    | num l => exact Int.beq'_eq_beq k l
    | add => rfl
  | add k m p ih =>
    cases q with
    | num => rfl
    | add l n q =>
      change (Int.beq' k l && (m.beq' n && p.beq' q)) = _
      rw [Int.beq'_eq_beq, monBeqSame, ih]
      rfl

public theorem ringPowerBEq (p q : Power) : p.beq' q = true ↔ p = q := by
  rw [powerBeqSame]; exact beq_iff_eq

public theorem ringMonBEq (m n : Mon) : m.beq' n = true ↔ m = n := by
  rw [monBeqSame]; exact beq_iff_eq

public theorem ringPolyBEq (p q : Poly) : p.beq' q = true ↔ p = q := by
  rw [ringPolyBeqSame]; exact beq_iff_eq

end OmegaChecks.InitCompiler.ProofRules
