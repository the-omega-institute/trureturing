module
public import Init.Grind.Module.OfNatModule
import all Init.Grind.Module.Envelope
import Lean

public section
namespace OmegaChecks.InitBoundaries.ModuleEnvelopeExact
open Lean.Grind IntModule.OfNatModule
universe u

/-- The two embedding equalities in the pinned interface transport disequality
to arbitrary quotient variables. On the images themselves, the exact condition
is double-negated injectivity. -/
abbrev ReflectsDisequality : Prop := ∀ {α : Type u} [NatModule α] [AddRightCancel α]
  {a b : α}, toQ a = toQ b → ¬¬ (a = b)

theorem ofDiseqIff : (type_of% @IntModule.OfNatModule.of_diseq.{u}) ↔ ReflectsDisequality.{u} :=
  ⟨fun law {_} _ _ {_ _} eq ne => law rfl rfl ne eq,
   fun reflect {_} _ _ {_ _ _ _} ha hb ne eq => reflect (ha.trans (eq.trans hb.symm)) ne⟩

section
variable {α : Type u} [NatModule α] [AddRightCancel α] (a : α)

private theorem row (x : α × α) : r α (a, 0) x ↔ a + x.2 = x.1 := by
  obtain ⟨b, c⟩ := x
  constructor
  · rintro ⟨k, h⟩
    exact (AddRightCancel.add_right_cancel _ _ k h).trans (AddCommMonoid.zero_add b)
  · intro h
    exact ⟨0, congrArg (· + 0) (h.trans (AddCommMonoid.zero_add b).symm)⟩

/-- Deciding this single row of the representative relation suffices to separate
the image of a from every other embedded value. -/
theorem injectiveAt (dec : ∀ b c : α, Decidable (a + c = b)) {b : α} (eq : toQ a = toQ b) : a = b := by
  letI (x : α × α) : Decidable (r α (a,0) x) := @decidable_of_iff' _ _ (row a x) (dec x.1 x.2)
  let observe : Q α → Bool := Quot.lift (fun x => decide (r α (a,0) x)) fun _ _ h =>
    decide_eq_decide.mpr ⟨fun hx => r_trans hx h, fun hy => r_trans hy (r_sym h)⟩
  have seen := congrArg observe eq
  change decide (r α (a,0) (a,0)) = decide (r α (a,0) (b,0)) at seen
  have related := _root_.of_decide_eq_true (seen.symm.trans (decide_eq_true (r_rfl (a,0))))
  exact (AddCommMonoid.add_zero a).symm.trans ((row a (b,0)).mp related)

/-- For the negative official conclusion, a double-negated row decision suffices. -/
theorem ofDiseqOfRow (dec : ¬¬ Nonempty (∀ b c : α, Decidable (a + c = b)))
    {b : α} {qa qb : Q α} (ha : toQ a = qa) (hb : toQ b = qb) (ne : a ≠ b) : qa ≠ qb :=
  fun eq => dec fun ⟨test⟩ => ne (injectiveAt a test (ha.trans (eq.trans hb.symm)))

end
end OmegaChecks.InitBoundaries.ModuleEnvelopeExact
