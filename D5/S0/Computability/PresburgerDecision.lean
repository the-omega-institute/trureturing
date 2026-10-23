/- GID: D5/S0/Computability/PresburgerDecision
   generality: G
   mirror-B: D5/B/S0/Computability/PresburgerDecision
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Executable integer Presburger decision with exact semantics. -/

/- Source: VladimirReshetnikov/ProveIt, ec9ab2ffd49f8861022d6f3d4c30205545a3386d,
   PresburgerArithmetic/Decision.lean.
   Original SHA256: 7906f1f8d71528ff5635bd1e39d214e6ee15f3ff887f7306486f5b0f9b792e97.
   License: MIT-0; docs/reports/presburger-suppliers/ProveIt-LICENSE.txt. -/

import D5.S0.Computability.PresburgerElimination

namespace PresburgerArithmetic

namespace Formula

/-! Full Cooper quantifier elimination.  Universal quantification is the
derived operation `¬∃¬`, so eliminating `exists_` is the only genuinely
arithmetic recursive case. -/

def quantifierEliminate : Formula → QF
  | .qf p => p
  | .and p q => .and p.quantifierEliminate q.quantifierEliminate
  | .or p q => .or p.quantifierEliminate q.quantifierEliminate
  | .not p => .not p.quantifierEliminate
  | .exists_ p => Cooper.eliminate p.quantifierEliminate

theorem holds_iff_quantifierEliminate : ∀ (p : Formula) (xs : List Int),
    p.holds xs ↔ p.quantifierEliminate.eval xs = true := by
  intro p
  induction p with
  | qf p => intro xs; rfl
  | and p q ihp ihq =>
      intro xs
      simp [holds, quantifierEliminate, QF.eval, ihp xs, ihq xs]
  | or p q ihp ihq =>
      intro xs
      simp [holds, quantifierEliminate, QF.eval, ihp xs, ihq xs]
  | not p ih =>
      intro xs
      simp [holds, quantifierEliminate, QF.eval, ih xs]
  | exists_ p ih =>
      intro xs
      calc
        (∃ x : Int, p.holds (x :: xs)) ↔
            ∃ x : Int, p.quantifierEliminate.eval (x :: xs) = true :=
          exists_congr fun x => ih (x :: xs)
        _ ↔ (Cooper.eliminate p.quantifierEliminate).eval xs = true :=
          (Cooper.eliminate_correct _ _).symm

def decideHolds (p : Formula) (xs : List Int) : Bool :=
  p.quantifierEliminate.eval xs

theorem decideHolds_eq_true_iff (p : Formula) (xs : List Int) :
    p.decideHolds xs = true ↔ p.holds xs :=
  (holds_iff_quantifierEliminate p xs).symm

def holdsDecidable (p : Formula) (xs : List Int) : Decidable (p.holds xs) :=
  if h : p.decideHolds xs = true then
    isTrue ((decideHolds_eq_true_iff p xs).mp h)
  else
    isFalse fun hp => h ((decideHolds_eq_true_iff p xs).mpr hp)

def decideSentence (p : Sentence) : Bool := p.decideHolds []

theorem decideSentence_eq_true_iff (p : Sentence) :
    decideSentence p = true ↔ p.holds [] :=
  decideHolds_eq_true_iff p []

/- This is the advertised decidability theorem.  Its decision procedure is
`decideSentence`, not an appeal to classical excluded middle. -/
def presburgerArithmetic_decidable (p : Sentence) : Decidable (p.holds []) :=
  holdsDecidable p []

end Formula

end PresburgerArithmetic
