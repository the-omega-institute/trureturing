/- GID: D5/S0/Certificates/CheckedRationalBoxCover
   generality: G
   mirror-B: D5/B/S0/Certificates/CheckedRationalBoxCover
   mirror-E: none(waiver:checked-continuous-cover)
   anchors: []
   digest: Exact rational checks of an explicitly ordered box forest supply the local real proofs required by FiniteSublevelCover. -/

import D5.S0.Certificates.RationalIntervalExpression
import D5.S0.Certificates.FiniteSublevelCover

/- This executable adapter reuses both existing owners. Only the proof-node
   index is finite. Real inputs are not replaced by a finite root list.
   Residual syntax is compared after erasing numeric endpoint annotations.
   Changing the outcome or expression therefore requires its own checked proof.
   Children must have smaller indices and must cover both closed split halves.
   The currently supported records are tube inclusion, expression exclusion,
   and split. A legacy Krawczyk contraction is NOT accepted by this adapter;
   its numerical derivative and balanced-readout proofs remain separate work.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.CheckedRationalBoxCover

open D5.S0.Certificates.RationalIntervalExpression
open D5.S0.Certificates.FiniteSublevelCover

private def erase {n : ℕ} : Expr n → Expr n
  | .input i _ _ => .input i 0 0
  | .const q _ _ => .const q 0 0
  | .add _ _ a b => .add 0 0 (erase a) (erase b)
  | .neg _ _ a => .neg 0 0 (erase a)
  | .mul _ _ a b => .mul 0 0 (erase a) (erase b)
  | .square _ _ a => .square 0 0 (erase a)
  | .inv _ _ a => .inv 0 0 (erase a)

private theorem erase_value {n : ℕ} (x : Fin n → ℝ) (e : Expr n) :
    value x (erase e) = value x e := by
  induction e <;> simp_all only [erase, value]

private def region {n : ℕ} (box : Fin n → ℚ × ℚ) : Set (Fin n → ℝ) :=
  {x | ∀ j, ((box j).1 : ℝ) ≤ x j ∧ x j ≤ ((box j).2 : ℝ)}

private def boxSub {n : ℕ} (a b : Fin n → ℚ × ℚ) : Prop :=
  ∀ j, (b j).1 ≤ (a j).1 ∧ (a j).2 ≤ (b j).2

private instance {n : ℕ} (a b : Fin n → ℚ × ℚ) : Decidable (boxSub a b) :=
  inferInstanceAs (Decidable (∀ j, (b j).1 ≤ (a j).1 ∧ (a j).2 ≤ (b j).2))

private theorem sub_sound {n : ℕ} {a b : Fin n → ℚ × ℚ}
    (h : boxSub a b) : region a ⊆ region b := by
  intro x hx j
  have hlo : ((b j).1 : ℝ) ≤ ((a j).1 : ℝ) := by exact_mod_cast (h j).1
  have hhi : ((a j).2 : ℝ) ≤ ((b j).2 : ℝ) := by exact_mod_cast (h j).2
  exact ⟨hlo.trans (hx j).1, (hx j).2.trans hhi⟩

private def leftBox {n : ℕ} (box : Fin n → ℚ × ℚ) (k : Fin n) (cut : ℚ) :
    Fin n → ℚ × ℚ := fun j ↦ if j = k then ((box j).1, cut) else box j

private def rightBox {n : ℕ} (box : Fin n → ℚ × ℚ) (k : Fin n) (cut : ℚ) :
    Fin n → ℚ × ℚ := fun j ↦ if j = k then (cut, (box j).2) else box j

private theorem split_retains {n : ℕ} (box : Fin n → ℚ × ℚ)
    (k : Fin n) (cut : ℚ) :
    region box ⊆ region (leftBox box k cut) ∪ region (rightBox box k cut) := by
  intro x hx
  by_cases hcut : x k ≤ (cut : ℝ)
  · left
    intro j
    by_cases hj : j = k
    · subst j
      simpa only [leftBox, ite_true, ↓reduceIte] using And.intro (hx k).1 hcut
    · simpa only [leftBox, if_neg hj] using hx j
  · right
    intro j
    by_cases hj : j = k
    · subst j
      simpa only [rightBox, ite_true, ↓reduceIte] using And.intro (le_of_not_ge hcut) (hx k).2
    · simpa only [rightBox, if_neg hj] using hx j

/-- Finite certificate instructions with typed outcome, tube and node indices.
A split has two children. Missing children, cyclic proof references and
unsupported external instructions cannot be represented as accepted proofs. -/
inductive Step (n outcomes tubes nodes : ℕ) where
  | covered (label : Fin tubes)
  | excluded (outcome : Fin outcomes) (expression : Expr n)
  | split (axis : Fin n) (cut : ℚ) (left right : Fin nodes)

private def nodeCheck {n outcomes tubes nodes : ℕ}
    (boxes : Fin nodes → Fin n → ℚ × ℚ)
    (targets : Fin tubes → Fin n → ℚ × ℚ)
    (residual : Fin outcomes → Expr n) (epsilon : ℚ)
    (steps : Fin nodes → Step n outcomes tubes nodes) (i : Fin nodes) : Bool :=
  match steps i with
  | .covered k => decide (boxSub (boxes i) (targets k))
  | .excluded a e => check (boxes i) e && decide
      (erase e = erase (residual a) ∧
        (epsilon < (bounds e).1 ∨ (bounds e).2 < -epsilon))
  | .split k cut left right => decide
      (left.val < i.val ∧ right.val < i.val ∧
        (boxes i k).1 ≤ cut ∧ cut ≤ (boxes i k).2 ∧
        boxSub (leftBox (boxes i) k cut) (boxes left) ∧
        boxSub (rightBox (boxes i) k cut) (boxes right))

/-- Exact decidable verification of every node. This recomputes rational
arithmetic, formula identity and both closed split inclusions. It is not a
hash check, a stored external status, or a sampled-real verification. -/
def checkForest {n outcomes tubes nodes : ℕ}
    (boxes : Fin nodes → Fin n → ℚ × ℚ)
    (targets : Fin tubes → Fin n → ℚ × ℚ)
    (residual : Fin outcomes → Expr n) (epsilon : ℚ)
    (steps : Fin nodes → Step n outcomes tubes nodes) : Bool :=
  decide (∀ i, nodeCheck boxes targets residual epsilon steps i = true)

/-- An accepted finite rational forest covers every real point of the actual
residual sublevel in each of its root boxes. Numerical local enclosures,
formula identity and split completeness are discharged by the checker.
The global proof descends through the existing FiniteSublevelCover theorem.

The residual is the supplied expression's REAL semantics. An application to
Hadamard matrices must also prove that this semantics is its actual residual.
No Krawczyk contract rule or complete 32-chart instance is asserted here. -/
theorem checked_forest_covers_sublevel
    {n outcomes tubes nodes : ℕ}
    (boxes : Fin nodes → Fin n → ℚ × ℚ)
    (targets : Fin tubes → Fin n → ℚ × ℚ)
    (residual : Fin outcomes → Expr n) (epsilon : ℚ)
    (steps : Fin nodes → Step n outcomes tubes nodes)
    (accepted : checkForest boxes targets residual epsilon steps = true)
    (root : Fin nodes) (x : Fin n → ℝ)
    (hx : ∀ j, ((boxes root j).1 : ℝ) ≤ x j ∧ x j ≤ ((boxes root j).2 : ℝ))
    (hr : ∀ a, |value x (residual a)| ≤ (epsilon : ℝ)) :
    ∃ k, ∀ j, ((targets k j).1 : ℝ) ≤ x j ∧ x j ≤ ((targets k j).2 : ℝ) := by
  have hc : ∀ i, nodeCheck boxes targets residual epsilon steps i = true :=
    of_decide_eq_true accepted
  have localProof : ∀ i, LocalStep (fun j ↦ region (boxes j))
      (⋃ k, region (targets k)) (fun y a ↦ value y (residual a)) (epsilon : ℝ) i := by
    intro i
    have hi := hc i
    cases hstep : steps i with
    | covered k =>
      simp only [nodeCheck, hstep] at hi
      apply LocalStep.covered
      intro y hy
      exact Set.mem_iUnion.mpr ⟨k, sub_sound (of_decide_eq_true hi) hy⟩
    | excluded a e =>
      simp only [nodeCheck, hstep] at hi
      obtain ⟨he, hrest⟩ := Bool.and_eq_true_iff.mp hi
      obtain ⟨hsame, hsep⟩ := of_decide_eq_true hrest
      apply LocalStep.excluded a ((bounds e).1 : ℝ) ((bounds e).2 : ℝ)
      · intro y hy
        have hbound := checked_expression_encloses (boxes i) y hy e he
        have hvalue : value y e = value y (residual a) := by
          calc
            value y e = value y (erase e) := (erase_value y e).symm
            _ = value y (erase (residual a)) := congrArg (value y) hsame
            _ = value y (residual a) := erase_value y (residual a)
        simpa only [hvalue] using hbound
      · rcases hsep with hlo | hhi
        · left; exact_mod_cast hlo
        · right; exact_mod_cast hhi
    | split k cut left right =>
      simp only [nodeCheck, hstep] at hi
      obtain ⟨hle, hre, _, _, hl, hr'⟩ := of_decide_eq_true hi
      apply LocalStep.split left right hle hre
      intro y hy
      rcases split_retains (boxes i) k cut hy with hyLeft | hyRight
      · exact Or.inl (sub_sound hl hyLeft)
      · exact Or.inr (sub_sound hr' hyRight)
  have htarget := sublevel_mem_target_of_local_steps
    (fun j ↦ region (boxes j)) (⋃ k, region (targets k))
    (fun y a ↦ value y (residual a)) (epsilon : ℝ) localProof root x hx hr
  exact Set.mem_iUnion.mp htarget

#print axioms checked_forest_covers_sublevel

end D5.S0.Certificates.CheckedRationalBoxCover
