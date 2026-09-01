/- GID: D5/S3/Quantum/Algebra/WeylDisplacementTrace
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/WeylDisplacementTrace
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: Displacement words have vanishing trace off the origin and pair orthogonally. -/

/- Library-search audit trail (2026-09-01). The commands below are reproduced literally as they
   were run, each followed by the count it returned. Paths are relative to this worktree.

   git grep -n -E "trace.*(clockMatrix|shiftMatrix|displacement M)" origin/dev -- '*.lean'   -> 0
   git grep -l "Matrix.trace" origin/dev -- 'D5/S3/Quantum/*' 'D5/S3/Observer/*'             -> 8
     The digests of those eight were listed with
     `git show "origin/dev:<path>" | grep -m1 "digest:"` for each path returned above; they are
     Born-rule readouts, conditioning, Gramian energy, a channel-pullback trace identity, and a
     rotation-trace bridge sending thirty-six degrees to the golden ratio. None concerns
     displacement words.
   git ls-tree -r --name-only origin/dev -- D5/S3/Quantum D5/S3/Observer | grep -iE "trace|orthogon"
     -> 10 files; their digests were listed the same way. They are subspace orthogonal
     complements, De Morgan for closed subspaces, residual recurrence, and task-separation
     completion. None is trace-pairing orthogonality for displacement words.

   grep -ril "trace_permMatrix" .lake/packages/mathlib --include='*.lean' | wc -l              -> 0
   grep -ril "circulant.*trace" .lake/packages/mathlib --include='*.lean' | wc -l              -> 0

   grep -ril "Weyl-Heisenberg"       .lake/packages/mathlib --include='*.lean' | wc -l    -> 0
   grep -ril "generalized Pauli"     .lake/packages/mathlib --include='*.lean' | wc -l    -> 0
   grep -ril "displacement operator" .lake/packages/mathlib --include='*.lean' | wc -l    -> 0
   grep -ril "trace orthogonality"   .lake/packages/mathlib --include='*.lean' | wc -l    -> 0
   grep -ril "operator basis"        .lake/packages/mathlib --include='*.lean' | wc -l    -> 0
     The same five commands with .lake/packages/batteries in place of mathlib -> 0 each.

   gh search prs --repo leanprover-community/mathlib4 --state open "Weyl-Heisenberg trace"
     --limit 20                                                                           -> 0
   gh search prs --repo leanprover-community/mathlib4 --state open
     "displacement operator orthogonal" --limit 20                                        -> 0
   gh search prs --repo leanprover-community/mathlib4 --state open "generalized Pauli basis"
     --limit 20                                                                           -> 0

   gh search code --repo leanprover/cslib "trace orthogonality" --limit 5                 -> 0
   gh search code --repo leanprover/cslib "displacement operator" --limit 5               -> 0
   gh search code --repo TauCetiProject/TauCeti "trace orthogonality" --limit 5           -> 0
   gh search code --repo TauCetiProject/TauCeti "displacement operator" --limit 5         -> 0

   Zulip was searched for the two preceding nodes of this family through a web index of the public
   archive, which surfaced no topic on formalizing these operators; no separate query was issued
   for the trace identity specifically. That instrument is weaker than the commands above and the
   archive's own search was not queried directly, so this domain is recorded as a weaker negative.

   The two upstream results this module does use rather than reprove are
   `Matrix.trace_mul_comm` and `IsPrimitiveRoot.pow_inj`; the composition law and the adjoint law
   come from the two frozen nodes this module imports.

   The proof deliberately avoids entry-level computation. `MatrixUnitCertificate` does carry an
   entry formula for shift powers and a character sum, but both are `private` there, so they are
   not reusable; instead the vanishing trace is obtained from the frozen composition law and the
   fact that a trace does not see the order of a product.
-/

import D5.S3.Quantum.Algebra.WeylDisplacementAdjoint

/-!
# Trace and orthogonality of Weyl displacement words

A displacement word away from the origin is conjugate to a nontrivial multiple of itself, so its
trace must vanish. At the origin the word is the identity and its trace is the window cardinality.
Together these make the words pairwise orthogonal for the trace form. Whether that pairing extends
to a basis statement is not proved here: no linear independence or spanning result appears below,
so nothing in this module should be read as claiming one.

The argument never inspects a matrix entry. It uses only the frozen composition law and the fact
that the trace does not see the order of a product.
-/

namespace D5.S3.Quantum.Algebra.WeylDisplacementTrace

open D5.S3.Observer.WindowRegister
open D5.S3.Quantum.Algebra.WeylDisplacement
open D5.S3.Quantum.Algebra.WeylDisplacementAdjoint

noncomputable section

variable {M : ℕ} [NeZero M]

/-- Distinct residues give distinct window phases. -/
private theorem windowRoot_pow_val_inj {x y : ZMod M}
    (h : windowRoot M ^ x.val = windowRoot M ^ y.val) : x = y :=
  ZMod.val_injective M
    ((windowRoot_isPrimitiveRoot M).pow_inj (ZMod.val_lt x) (ZMod.val_lt y) h)

/-- Swapping the two factors of a displacement product only changes the phase, and the trace
cannot see that swap. -/
private theorem trace_phase_relation (a b c d : ZMod M) :
    windowRoot M ^ (d * a).val * Matrix.trace (displacement M a b * displacement M c d) =
      windowRoot M ^ (b * c).val *
        Matrix.trace (displacement M a b * displacement M c d) := by
  have hswap :
      Matrix.trace (displacement M c d * displacement M a b) =
        Matrix.trace (displacement M a b * displacement M c d) :=
    Matrix.trace_mul_comm _ _
  have hcomm := displacement_comm (M := M) a b c d
  have := congrArg Matrix.trace hcomm
  simpa [Matrix.trace_smul, smul_eq_mul, hswap] using this

/-- Off the origin the trace of a displacement word vanishes. -/
theorem displacement_trace_eq_zero (e f : ZMod M) (hne : ¬(e = 0 ∧ f = 0)) :
    Matrix.trace (displacement M e f) = 0 := by
  obtain ⟨a, b, hphase⟩ : ∃ a b : ZMod M, b * e ≠ f * a := by
    by_cases he : e = 0
    · have hf : f ≠ 0 := fun hf0 => hne ⟨he, hf0⟩
      exact ⟨1, 0, by simpa using Ne.symm hf⟩
    · exact ⟨0, 1, by simpa using he⟩
  have hkey := trace_phase_relation (M := M) a b (e - a) (f - b)
  have hsum : a + (e - a) = e := by ring
  have hsum' : b + (f - b) = f := by ring
  have hprod :
      displacement M a b * displacement M (e - a) (f - b) =
        windowRoot M ^ (b * (e - a)).val • displacement M e f := by
    rw [displacement_mul, hsum, hsum']
  rw [hprod, Matrix.trace_smul, smul_eq_mul] at hkey
  have hne' : windowRoot M ^ ((f - b) * a).val ≠ windowRoot M ^ (b * (e - a)).val := by
    intro heq
    have heq2 : (f - b) * a = b * (e - a) := windowRoot_pow_val_inj (M := M) heq
    exact hphase (by linear_combination -heq2)
  have hroot_ne : windowRoot M ≠ 0 :=
    (windowRoot_isPrimitiveRoot M).ne_zero (NeZero.ne M)
  have hpow_ne : windowRoot M ^ (b * (e - a)).val ≠ 0 := pow_ne_zero _ hroot_ne
  have hzero :
      (windowRoot M ^ ((f - b) * a).val - windowRoot M ^ (b * (e - a)).val) *
        (windowRoot M ^ (b * (e - a)).val * Matrix.trace (displacement M e f)) = 0 := by
    rw [sub_mul]
    linear_combination hkey
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd (sub_eq_zero.mp h) hne'
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hpow_ne
    · exact h'

/-- At the origin the displacement word is the identity, whose trace is the window cardinality. -/
theorem displacement_trace_origin :
    Matrix.trace (displacement M (0 : ZMod M) (0 : ZMod M)) = (M : ℂ) := by
  rw [displacement_zero, Matrix.trace_one]
  simp [ZMod.card]

/-- The trace of a displacement word, in one statement. -/
theorem displacement_trace (e f : ZMod M) :
    Matrix.trace (displacement M e f) = if e = 0 ∧ f = 0 then (M : ℂ) else 0 := by
  by_cases h : e = 0 ∧ f = 0
  · obtain ⟨he, hf⟩ := h
    subst he; subst hf
    simp
  · simpa [h] using displacement_trace_eq_zero (M := M) e f h

/-- Opposite residues contribute inverse window phases. -/
private theorem windowRoot_pow_val_neg_mul (x : ZMod M) :
    windowRoot M ^ (-x).val * windowRoot M ^ x.val = 1 := by
  rw [← pow_add]
  have hzero : ((-x).val + x.val) % M = 0 := by
    have hval : ((-x) + x).val = ((-x).val + x.val) % M := ZMod.val_add _ _
    simpa using hval.symm
  conv_lhs => rw [← Nat.div_add_mod ((-x).val + x.val) M]
  rw [hzero, Nat.add_zero, pow_mul, (windowRoot_isPrimitiveRoot M).pow_eq_one, one_pow]

/-- Displacement words are pairwise orthogonal for the trace form, and at equal indices the pairing
returns the window cardinality. This is the pairing identity only; no basis, linear independence,
or spanning claim is made or proved here. -/
theorem displacement_trace_orthogonal (a b c d : ZMod M) :
    Matrix.trace (star (displacement M a b) * displacement M c d) =
      if a = c ∧ b = d then (M : ℂ) else 0 := by
  have hstar := displacement_adjoint (M := M) a b
  rw [hstar, Matrix.smul_mul, displacement_mul, smul_smul, Matrix.trace_smul, smul_eq_mul,
    displacement_trace]
  by_cases h : a = c ∧ b = d
  · obtain ⟨hac, hbd⟩ := h
    subst hac; subst hbd
    have hsum : (-a + a : ZMod M) = 0 := by ring
    have hsum' : (-b + b : ZMod M) = 0 := by ring
    rw [if_pos ⟨hsum, hsum'⟩, if_pos ⟨rfl, rfl⟩]
    have hphase : windowRoot M ^ (a * b).val * windowRoot M ^ (-b * a).val = 1 := by
      have hneg : (-b * a : ZMod M) = -(a * b) := by ring
      rw [hneg, mul_comm]
      exact windowRoot_pow_val_neg_mul (M := M) (a * b)
    rw [hphase, one_mul]
  · have hindex : ¬((-a + c : ZMod M) = 0 ∧ (-b + d : ZMod M) = 0) := by
      intro hcontra
      apply h
      obtain ⟨h1, h2⟩ := hcontra
      constructor
      · linear_combination -h1
      · linear_combination -h2
    rw [if_neg hindex, if_neg h, mul_zero]

end

end D5.S3.Quantum.Algebra.WeylDisplacementTrace
