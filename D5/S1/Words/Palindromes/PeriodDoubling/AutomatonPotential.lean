/- GID: D5/S1/Words/Palindromes/PeriodDoubling/AutomatonPotential
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/AutomatonPotential
   mirror-E: none(waiver:integer-potential-path-induction)
   anchors: []
   utility: none
   digest: Integer potentials bound every finite nondeterministic transducer run. -/

/-
proof_shape: content (accepted_path_bound, accepted_path_bound_partial)
escape_witness: Path induction propagates edge inequalities through unbounded input lengths.
admission_basis: escape-witness
Direct frozen dependencies: none.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Computability.NFA

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Palindromes.PeriodDoubling

/-- The sum of integer edge charges along a particular nondeterministic run. -/
def pathCharge {α σ : Type*} {M : NFA α σ} (charge : σ → α → σ → ℤ)
    {s t : σ} {xs : List α} : M.Path s t xs → ℤ
  | .nil _ => 0
  | .cons q s _ a _ _ p => charge s a q + pathCharge charge p

/-- Every accepting run satisfies the source, edge, and terminal potential bound. -/
theorem accepted_path_bound {α σ : Type*} (M : NFA α σ)
    (charge : σ → α → σ → ℤ) (potential : σ → ℤ)
    (offset : σ → ℤ) (B : ℤ)
    (hsource : ∀ s ∈ M.start, 0 ≤ potential s)
    (hedge : ∀ (s q : σ) (a : α), q ∈ M.step s a →
      potential s + charge s a q ≤ potential q)
    (hgoal : ∀ t ∈ M.accept, potential t + offset t ≤ B)
    {s t : σ} {xs : List α} (hs : s ∈ M.start) (ht : t ∈ M.accept)
    (p : M.Path s t xs) : pathCharge charge p + offset t ≤ B := by
  have path_bound {s t : σ} {xs : List α} (p : M.Path s t xs) :
      potential s + pathCharge charge p ≤ potential t := by
    induction p with
    | nil s => simp [pathCharge]
    | cons q s t a xs hstep p ih =>
      have he := hedge s q a hstep
      simp only [pathCharge]
      omega
  have hp := path_bound p
  have hi := hsource s hs
  have hf := hgoal t ht
  omega

/-- Optional potentials propagate backwards from the selected terminal states. -/
theorem accepted_path_bound_partial {α σ : Type*} (M : NFA α σ)
    (charge : σ → α → σ → ℤ) (potential : σ → Option ℤ)
    (offset : σ → ℤ) (B : ℤ)
    (hsource : ∀ s ∈ M.start, ∀ V, potential s = some V → 0 ≤ V)
    (hedge : ∀ (s q : σ) (a : α), q ∈ M.step s a →
      ∀ W, potential q = some W → ∃ V, potential s = some V ∧ V + charge s a q ≤ W)
    (hgoal : ∀ t ∈ M.accept, ∃ W, potential t = some W ∧ W + offset t ≤ B)
    {s t : σ} {xs : List α} (hs : s ∈ M.start) (ht : t ∈ M.accept)
    (p : M.Path s t xs) : pathCharge charge p + offset t ≤ B := by
  have path_bound {s t : σ} {xs : List α} (p : M.Path s t xs)
      (W : ℤ) (hW : potential t = some W) :
      ∃ V, potential s = some V ∧ V + pathCharge charge p ≤ W := by
    induction p generalizing W with
    | nil s => exact ⟨W, hW, by simp [pathCharge]⟩
    | cons q s t a xs hstep p ih =>
      obtain ⟨U, hU, htail⟩ := ih W hW
      obtain ⟨V, hV, hedge'⟩ := hedge s q a hstep U hU
      exact ⟨V, hV, by simp only [pathCharge]; omega⟩
  obtain ⟨W, hW, hlast⟩ := hgoal t ht
  obtain ⟨V, hV, hpath⟩ := path_bound p W hW
  have hfirst := hsource s hs V hV
  omega

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.accepted_path_bound

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.accepted_path_bound_partial
