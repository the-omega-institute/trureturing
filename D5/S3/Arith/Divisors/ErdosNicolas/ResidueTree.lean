/- GID: D5/S3/Arith/Divisors/ErdosNicolas/ResidueTree
   generality: G
   mirror-B: none(waiver:proof-helper-in-main-import-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; instance=D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueP19/Cover.coverage_checked
   digest: Exhaustive prefix-tree coverage of bounded exponent domains. -/

import D5.S3.Arith.Divisors.ErdosNicolas.ResidueChecker
import Mathlib.Data.List.Forall2

/-! Prefix pruning preserves coverage of the complete finite exponent domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.ErdosNicolas

/-- Stop at listed terminal prefixes; otherwise inspect every possible next exponent. -/
def checkPrefixCover (terminals : List (List ℕ)) (pre : List ℕ) : List ℕ → Bool
  | [] => terminals.contains pre
  | cap :: caps =>
      match terminals.contains pre with
      | true => true
      | false =>
          (List.range (cap + 1)).all fun e => checkPrefixCover terminals (pre ++ [e]) caps

/-- Opaque child checks compose without reducing the parent coverage computation. -/
theorem checkPrefixCover_of_children (terminals : List (List ℕ)) (pre : List ℕ)
    (cap : ℕ) (caps : List ℕ)
    (hchildren : (List.range (cap + 1)).all
      (fun e => checkPrefixCover terminals (pre ++ [e]) caps) = true) :
    checkPrefixCover terminals pre (cap :: caps) = true := by
  cases hc : terminals.contains pre with
  | false => simpa only [checkPrefixCover, hc] using hchildren
  | true => simp only [checkPrefixCover, hc]

/-- Every bounded vector reaches a listed terminal; no branch can be omitted. -/
theorem checkPrefixCover_sound {terminals : List (List ℕ)} {pre caps : List ℕ}
    (h : checkPrefixCover terminals pre caps = true) :
    ∀ exps : List ℕ, List.Forall₂ (· ≤ ·) exps caps →
      ∃ terminal ∈ terminals, terminal.IsPrefix (pre ++ exps) := by
  induction caps generalizing pre with
  | nil =>
    intro exps hexps
    have he : exps = [] := by simpa using hexps
    subst exps
    have hp : pre ∈ terminals := List.contains_iff_mem.mp h
    exact ⟨pre, hp, ⟨[], by simp⟩⟩
  | cons cap caps ih =>
    intro exps hexps
    by_cases hp : pre ∈ terminals
    · exact ⟨pre, hp, ⟨exps, rfl⟩⟩
    · have hcontains : terminals.contains pre = false := by
        cases hc : terminals.contains pre with
        | false => rfl
        | true => exact False.elim (hp (List.contains_iff_mem.mp hc))
      simp only [checkPrefixCover, hcontains, List.all_eq_true] at h
      cases exps with
      | nil => cases hexps
      | cons e es =>
        have he : e ≤ cap := (List.forall₂_cons.mp hexps).1
        have hes := (List.forall₂_cons.mp hexps).2
        have hc := h e (List.mem_range.mpr (by omega))
        obtain ⟨terminal, ht, hprefix⟩ := ih hc es hes
        refine ⟨terminal, ht, ?_⟩
        simpa only [List.append_assoc, List.singleton_append] using hprefix

#print axioms checkPrefixCover_of_children
#print axioms checkPrefixCover_sound

end D5.S3.Arith.ErdosNicolas
