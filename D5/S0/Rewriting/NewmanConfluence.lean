/- GID: D5/S0/Rewriting/NewmanConfluence
   generality: G
   mirror-B: D5/B/S0/Rewriting/NewmanConfluence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Terminating locally confluent rewrite systems have globally joinable reductions. -/

import D5.S0.Rewriting.Newman

namespace D5.S0.Rewriting.NewmanConfluence

/-- Newman convergence: any two reflexive-transitive reductions from one source join. -/
theorem newman_confluent {α : Type*} (r : α → α → Prop)
    (termination : WellFounded (Function.swap r))
    (localConfluence : ∀ h a b, r h a → r h b →
      ∃ c, Relation.ReflTransGen r a c ∧ Relation.ReflTransGen r b c) :
    ∀ h a b, Relation.ReflTransGen r h a → Relation.ReflTransGen r h b →
      ∃ c, Relation.ReflTransGen r a c ∧ Relation.ReflTransGen r b c := by
  intro h a b hha hhb
  obtain ⟨n, hn, huniq⟩ := newman_unique_normal_form r termination localConfluence h
  obtain ⟨na, hna, _⟩ := newman_unique_normal_form r termination localConfluence a
  obtain ⟨nb, hnb, _⟩ := newman_unique_normal_form r termination localConfluence b
  have hnaFromH : Relation.ReflTransGen r h na := hha.trans hna.1
  have hnbFromH : Relation.ReflTransGen r h nb := hhb.trans hnb.1
  have hnaEq : na = n := huniq na ⟨hnaFromH, hna.2⟩
  have hnbEq : nb = n := huniq nb ⟨hnbFromH, hnb.2⟩
  refine ⟨n, ?_, ?_⟩
  · simpa [hnaEq] using hna.1
  · simpa [hnbEq] using hnb.1

private inductive DiamondState where
  | top
  | left
  | right
  | bottom
  deriving DecidableEq

private inductive DiamondStep : DiamondState → DiamondState → Prop where
  | top_left : DiamondStep .top .left
  | top_right : DiamondStep .top .right
  | left_bottom : DiamondStep .left .bottom
  | right_bottom : DiamondStep .right .bottom

private def diamondRank : DiamondState → Nat
  | .top => 2
  | .left => 1
  | .right => 1
  | .bottom => 0

private theorem diamondTermination : WellFounded (Function.swap DiamondStep) := by
  refine Subrelation.wf (q := Function.swap DiamondStep)
    (r := InvImage (· < ·) diamondRank) ?_ (InvImage.wf diamondRank Nat.lt_wfRel.wf)
  · intro a b hab
    cases hab with
    | top_left => change diamondRank .left < diamondRank .top; decide
    | top_right => change diamondRank .right < diamondRank .top; decide
    | left_bottom => change diamondRank .bottom < diamondRank .left; decide
    | right_bottom => change diamondRank .bottom < diamondRank .right; decide

private theorem diamondLocalConfluence :
    ∀ h a b, DiamondStep h a → DiamondStep h b →
      ∃ c, Relation.ReflTransGen DiamondStep a c ∧ Relation.ReflTransGen DiamondStep b c := by
  intro h a b hab hbb
  cases hab with
  | top_left =>
    cases hbb with
    | top_left => exact ⟨.left, .refl, .refl⟩
    | top_right => exact ⟨.bottom, .single .left_bottom, .single .right_bottom⟩
  | top_right =>
    cases hbb with
    | top_left => exact ⟨.bottom, .single .right_bottom, .single .left_bottom⟩
    | top_right => exact ⟨.right, .refl, .refl⟩
  | left_bottom =>
    cases hbb with
    | left_bottom => exact ⟨.bottom, .refl, .refl⟩
  | right_bottom =>
    cases hbb with
    | right_bottom => exact ⟨.bottom, .refl, .refl⟩

private example : ∀ h a b, Relation.ReflTransGen DiamondStep h a →
    Relation.ReflTransGen DiamondStep h b →
    ∃ c, Relation.ReflTransGen DiamondStep a c ∧ Relation.ReflTransGen DiamondStep b c := by
  exact newman_confluent DiamondStep diamondTermination diamondLocalConfluence

end D5.S0.Rewriting.NewmanConfluence
