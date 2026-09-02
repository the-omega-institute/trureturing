/- GID: D5/S3/Quantum/Algebra/WeylDisplacementTwoTorsion
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/WeylDisplacementTwoTorsion
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: A two-torsion displacement overlap of a self-adjoint matrix is phase-rigid. -/

/- Library-search audit trail (2026-09-02). The commands below are reproduced literally as they
   were run, each followed by the count it returned. Paths are relative to the delivery worktree.

   grep -Eic 'Weyl[-_ ]*Heisenberg|displacement[-_ ]*operator|
     displacement.*(torsion|phase[-_ ]*real|overlap)|torsion.*displacement' /tmp/decl_names.txt
     -> 0
   The same expression over /tmp/mod_names.txt                                              -> 0
   git grep -Eni '<the same expression>' origin/dev -- '*.lean' | grep -c .                 -> 19
     All nineteen lie in the three frozen modules of this family, and each file was opened.
     `WeylDisplacement` defines the word and proves composition, squaring and the two-dimensional
     anticommutation; `WeylDisplacementAdjoint` proves the adjoint law used below;
     `WeylDisplacementTrace` proves the vanishing trace and the trace pairing. None states an
     overlap against a self-adjoint matrix, and none carries a two-torsion hypothesis.
   git grep -Eil 'IsHermitian.*trace' origin/dev -- 'D5/S3/Quantum/*.lean'
     'D5/S3/Quantum/**/*.lean'                                                              -> 3
     All three were opened by digest: an invariant state for positive trace-preserving maps, a
     physical readout fiber, and trace-zero Hermitian readout fibers. None concerns displacement
     words.
   git grep -Eil 'twoTorsion|two_torsion' origin/dev -- 'D5/S3/Quantum/*.lean'
     'D5/S3/Quantum/**/*.lean'                                                              -> 0
   git grep -Eil 'expectation.*displacement' origin/dev -- 'D5/S3/Quantum/*.lean'
     'D5/S3/Quantum/**/*.lean'                                                              -> 0

   grep -ril "Weyl-Heisenberg"       .lake/packages/mathlib   --include='*.lean' | wc -l    -> 0
   grep -ril "displacement operator" .lake/packages/mathlib   --include='*.lean' | wc -l    -> 0
   The same two over .lake/packages/batteries
     -> 0 each

   gh search prs --repo leanprover-community/mathlib4 --state open "Weyl-Heisenberg"     --limit 20
                                                                                            -> 0
   gh search prs --repo leanprover-community/mathlib4 --state open "displacement operator"
     --limit 20                                                                             -> 0
   gh search prs --repo leanprover-community/mathlib4 --state open "torsion phase real"   --limit 20
                                                                                            -> 0
   gh search code --repo leanprover/cslib "Weyl-Heisenberg" --limit 5                       -> 0
   gh search code --repo leanprover/cslib "displacement operator" --limit 5                 -> 0
   gh search code --repo TauCetiProject/TauCeti "Weyl-Heisenberg" --limit 5                 -> 0
   gh search code --repo TauCetiProject/TauCeti "displacement operator" --limit 5           -> 0

   Zulip was searched for the earlier nodes of this family through a web index of the public
   archive, which surfaced no topic on formalizing these operators; no separate query was issued
   for this overlap statement. That instrument is weaker than the commands above and the archive's
   own search was not queried directly, so this domain stays a weaker negative.

   The upstream results used rather than reproved are `Matrix.trace_conjTranspose` and
   `Matrix.trace_mul_comm`. The adjoint law comes from the frozen node this module imports.
-/

import D5.S3.Quantum.Algebra.WeylDisplacementAdjoint

/-!
# Two-torsion displacement overlaps are phase-rigid

At an index whose two components are their own negatives, the adjoint law collapses: the adjoint
of the displacement word is the word itself, scaled by a single phase. Pairing that word against
any self-adjoint matrix therefore produces a number whose conjugate is that same phase times
itself, so the overlap is confined to one line through the origin determined by the index alone,
and not by the matrix it is paired against.

What is proved is the conjugation identity. No statement is made here about which line, about
density matrices, or about any spectral consequence.
-/

namespace D5.S3.Quantum.Algebra.WeylDisplacementTwoTorsion

open D5.S3.Observer.WindowRegister
open D5.S3.Quantum.Algebra.WeylDisplacement
open D5.S3.Quantum.Algebra.WeylDisplacementAdjoint

noncomputable section

variable {M : ℕ} [NeZero M]

/-- At a two-torsion index the displacement word is its own adjoint up to one phase. -/
theorem star_displacement_of_two_torsion (a b : ZMod M) (ha : a + a = 0) (hb : b + b = 0) :
    star (displacement M a b) = windowRoot M ^ (a * b).val • displacement M a b := by
  have hna : -a = a := by linear_combination -ha
  have hnb : -b = b := by linear_combination -hb
  rw [displacement_adjoint, hna, hnb]

/-- Pairing a self-adjoint matrix against a two-torsion displacement word gives a number whose
conjugate is the index phase times itself. -/
theorem two_torsion_overlap_conj (a b : ZMod M) (ha : a + a = 0) (hb : b + b = 0)
    (rho : Matrix (ZMod M) (ZMod M) ℂ) (hrho : star rho = rho) :
    star (Matrix.trace (rho * displacement M a b)) =
      windowRoot M ^ (a * b).val * Matrix.trace (rho * displacement M a b) := by
  have hstar : star (rho * displacement M a b)
      = (windowRoot M ^ (a * b).val • displacement M a b) * rho := by
    rw [star_mul, hrho, star_displacement_of_two_torsion a b ha hb]
  calc
    star (Matrix.trace (rho * displacement M a b))
        = Matrix.trace (star (rho * displacement M a b)) :=
          (Matrix.trace_conjTranspose _).symm
    _ = Matrix.trace ((windowRoot M ^ (a * b).val • displacement M a b) * rho) := by
          rw [hstar]
    _ = Matrix.trace (rho * (windowRoot M ^ (a * b).val • displacement M a b)) :=
          Matrix.trace_mul_comm _ _
    _ = windowRoot M ^ (a * b).val * Matrix.trace (rho * displacement M a b) := by
          rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

end

end D5.S3.Quantum.Algebra.WeylDisplacementTwoTorsion
