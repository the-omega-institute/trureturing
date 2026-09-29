/- GID: D5/S3/TotalVariation/TwistedSameRuleDefect
   generality: G
   mirror-B: D5/B/S3/TotalVariation/TwistedSameRuleDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every antiperiodic signed cycle forces a defect of each fixed relation-window rule. -/

import D5.S3.TotalVariation.TwistedResetPaths

open scoped BigOperators
namespace D5.S3.TotalVariation.TwistedSameRuleDefect

/-- Extend one signed cycle, complementing its sign on each successive turn. -/
def cycleSign (L : ℕ) (hL : 0 < L) (v : Fin L → Bool) (i : ℕ) : Bool :=
  xor (v ⟨i%L,Nat.mod_lt i hL⟩) (decide ((i/L)%2 = 1))

/-- Relation one means that the two actual successive absolute signs agree. -/
def cycleRelation (L : ℕ) (hL : 0 < L) (v : Fin L → Bool) (i : ℕ) : Bool :=
  !(xor (cycleSign L hL v i) (cycleSign L hL v (i+1)))

/-- The strict R-past rule at the endpoint t+R of the window starting at t. -/
def ruleValue (L : ℕ) (hL : 0 < L) (v : Fin L → Bool) (R : ℕ)
    (f : (Fin R → Bool) → Bool) (t : ℕ) : Bool :=
  f (fun i => cycleRelation L hL v (t+i.val))

/-- The same fixed table is used at both adjacent vertices. -/
def ruleDefect (L : ℕ) (hL : 0 < L) (v : Fin L → Bool) (R : ℕ)
    (f : (Fin R → Bool) → Bool) (t : ℕ) : Bool :=
  xor (xor (ruleValue L hL v R f (t+1)) (ruleValue L hL v R f t))
    (!(cycleRelation L hL v (t+R)))

/-- A single deterministic relation-window rule has at least one transport defect
in every twisted period. No legal-word, probabilistic, or parity premise is needed:
the actual complemented extension supplies the obstruction. -/
theorem twisted_same_rule_forces_defect (L : ℕ) (hL : 0 < L)
    (v : Fin L → Bool) (R : ℕ) (f : (Fin R → Bool) → Bool) :
    (∃ t < L, ruleDefect L hL v R f t = true) ∧
    1 ≤ ∑ t ∈ Finset.range L, if ruleDefect L hL v R f t then (1:ℕ) else 0 := by
  have hsign (i : ℕ) : cycleSign L hL v (i+L) = !(cycleSign L hL v i) := by
    have hmod : (i+L)%L = i%L := by simp
    have hdiv : (i+L)/L = i/L+1 := by
      rw [Nat.add_div hL]
      simp [Nat.div_self hL, Nat.not_le.mpr (Nat.mod_lt i hL)]
    have hpar : decide (((i/L+1)%2)=1) = !(decide ((i/L)%2=1)) := by
      by_cases hi : (i/L)%2=1
      · have hh : (i/L+1)%2 ≠ 1 := by omega
        simp [hi,hh]
      · have hh : (i/L+1)%2 = 1 := by omega
        simp [hi,hh]
    unfold cycleSign
    simp only [hmod,hdiv,hpar]
    cases v ⟨i%L,Nat.mod_lt i hL⟩ <;> cases decide ((i/L)%2=1) <;> rfl
  have hrel (i : ℕ) : cycleRelation L hL v (i+L) = cycleRelation L hL v i := by
    unfold cycleRelation
    rw [hsign, show i+L+1 = (i+1)+L by omega, hsign]
    cases cycleSign L hL v i <;> cases cycleSign L hL v (i+1) <;> rfl
  have hvalue (t : ℕ) : ruleValue L hL v R f (t+L) = ruleValue L hL v R f t := by
    unfold ruleValue
    congr 1
    funext i
    rw [show t+L+i.val = (t+i.val)+L by omega, hrel]
  let b : ℕ → Bool := fun t => xor (cycleSign L hL v (t+R)) (ruleValue L hL v R f t)
  have hb (t : ℕ) : b (t+L) = !(b t) := by
    dsimp [b]
    rw [hvalue, show t+L+R = (t+R)+L by omega, hsign]
    cases cycleSign L hL v (t+R) <;> cases ruleValue L hL v R f t <;> rfl
  have hdef (t : ℕ) : ruleDefect L hL v R f t = xor (b (t+1)) (b t) := by
    dsimp [ruleDefect,cycleRelation,b]
    rw [show t+1+R = t+R+1 by omega]
    cases ruleValue L hL v R f (t+1) <;> cases ruleValue L hL v R f t <;>
      cases cycleSign L hL v (t+R) <;> cases cycleSign L hL v (t+R+1) <;> rfl
  have hex : ∃ t < L, ruleDefect L hL v R f t = true := by
    by_contra hn
    have heq (t : ℕ) (ht : t < L) : b (t+1) = b t := by
      have hd : ruleDefect L hL v R f t ≠ true := fun h => hn ⟨t,ht,h⟩
      rw [hdef] at hd
      by_contra hne
      exact hd (Bool.xor_iff_ne.mpr hne)
    have hconst : ∀ t ≤ L, b t = b 0 := by
      intro t
      induction t with
      | zero => intro _; rfl
      | succ t ih =>
        intro ht
        exact (heq t (by omega)).trans (ih (by omega))
    have hlast := hconst L le_rfl
    have htw := hb 0
    simp only [zero_add] at htw
    rw [hlast] at htw
    exact Bool.self_ne_not (b 0) htw
  refine ⟨hex, ?_⟩
  obtain ⟨t,ht,hd⟩ := hex
  calc
    1 = (if ruleDefect L hL v R f t then (1:ℕ) else 0) := by simp [hd]
    _ ≤ _ := Finset.single_le_sum (s := Finset.range L)
      (f := fun u => if ruleDefect L hL v R f u then (1:ℕ) else 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr ht)

#print axioms twisted_same_rule_forces_defect
end D5.S3.TotalVariation.TwistedSameRuleDefect
