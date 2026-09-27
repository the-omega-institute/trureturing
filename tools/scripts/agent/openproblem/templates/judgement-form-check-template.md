# sshx judgement-form brief — codex-cli — PRE-FREEZE §3.2 review for lane `__LANE__`

You are a single read-only `review_worker` (role: `judgement-form`, stage: review, BEFORE any
freeze or deposit). The implementation seat has produced, in the worktree `__WORKTREE__` on
branch `__BRANCH__`, the Lean module `__MODULE__.lean`. Your only job is to decide, for every
declaration the module would deposit, whether it is `content` or `bind-only` under §3.2.

Do NOT edit tracked files. Do NOT run `deposit`, `cover`, `make lean`, any gate, or any build.
Read only: `cat`, `sed -n`, `grep`, `git show`. At most 12 commands. Return one result envelope.

## Why this stage exists

A bind-only module cannot be deposited under the `escape-witness` basis (the one exception is CLAUDE.md §3.2 「开放问题结算依据」: a preregistered, literature-checked external named open problem may be settled by a bind-only proof under `admission_basis: open-problem-resolution`, shape reported honestly), and the decision is not mechanical: no current
check computes it. The Lean report carries `axioms`, `statement_id` and `type_sha256` per
declaration, but no constant-dependency closure, so nothing in the machine surface can raise
this. It therefore has to be judged by reading, and it has to be judged BEFORE the freeze:
once `ledger-align` has written the state pin, the module is frozen, and editing the `.lean`
afterwards collides with SL-008 — the only remedy is to discard the deposit and redo it, which
costs the whole landing chain and a pull request.

Two recorded lanes were lost this way. In the second, a module was reduced from three
theorems to one on utility grounds (§3.3), landed, frozen, and opened as a pull request, and
only then was the surviving theorem found to be bind-only: the subgroup in question was
isomorphic to a symmetric group by an evident map, and the whole proof was an existing Mathlib
generation theorem transported along that isomorphism. Judging utility is not judging form.

## The test — apply it declaration by declaration

Inline everything the module itself introduces: local aliases, `have`s, private helpers added
in the same delivery, tactic expansions, definitional equalities. Then ask whether the
conclusion follows from (a) already-frozen project prerequisites and (b) pinned upstream
declarations, using only:

  * instantiation of a general statement at particular arguments,
  * substitution of hypotheses,
  * logical projection or repackaging (`.1`, `.2`, `.mp`, `.mpr`, conjunction, TFAE),
  * normalisation — definitional unfolding, `simp` with existing lemmas, and, once every
    atomic fact is already supplied, `ring` / `linarith` / `omega` / `norm_num` / `decide`.

If yes, the declaration is **bind-only** and the delivery must be refused — unless the module settles a preregistered external named open problem under `admission_basis: open-problem-resolution` (CLAUDE.md §3.2), in which case report the shape as bind-only and check that basis's conditions (a)–(d) instead. The tree you review is in **Phase-A shape**: the `OpenProblemResolutionClaim` node and the `Problems/` dossier are added in Phase B, after `make deposit` has frozen the host (the emitter refuses a resolution claim whose host is not yet a frozen-state member), so their absence is not a condition-(c) finding — judge (a), (b), (d) and the honesty of the labels; report (c) only if a claim node or dossier is present and wrong.

Watch for the two shapes that hide best:

  1. **Transport along an evident isomorphism.** The module builds a map, shows it injective
     and surjective by small arguments, and carries an upstream theorem across it. Ask
     explicitly: *is there an upstream theorem that this conclusion is the image of?* Name it
     if there is.
  2. **A small finite check dressed as the content.** A `decide` over a two- or four-element
     structure is normalisation, not new mathematics. It does not make a declaration content,
     and it does not make it computational either.

  3. **A witness the conclusion does not need.** The module proves a genuinely new lemma
     (a classification, a structure theorem) and routes the main theorem through it, so the
     deletion control passes — but the main theorem also follows from pinned Mathlib by the
     operations above WITHOUT that lemma. Then the lemma is not a witness for it (§3.2: a
     proposition the conclusion can be reached without, by bind-only operations, is not on the
     live path in the sense that matters), the main theorem is bind-only, and under
     `escape-witness` the delivery is refused; the true content lemma, if any, is a separate
     question. Run the bypass test explicitly: for the main theorem's conclusion, search pinned
     Mathlib for a direct route (`rg` the conclusion's core symbols under
     `.lake/packages/mathlib/Mathlib`, e.g. divisibility, monotonicity or multiplicativity
     lemmas about the same function) and say which upstream declarations close it or that none
     do. Third recorded lane lost this way (2026-09-18): a divisor-product parity theorem was
     routed through a modulo-four classification, and two review seats found
     `Nat.totient_dvd_of_dvd` plus the pairing identity gave the parity by instantiation; the
     lane was at its third deposit and could not be redone.

Syntactic position is never the criterion. Any test whose answer flips when a step is
extracted into a helper is not a test of judgement form.

## What to report

For each declaration: `proof_shape` (`content` or `bind-only`), the direct frozen dependencies
by GID and `statement_id`, and — if you judge it content — the **escape witness**: the
intermediate proposition that is in the elaborated dependency closure, is not obtainable from
the prerequisites by the operations above, is not definitionally equivalent to the conclusion,
and survives on the live derivation path. If you cannot name one, the declaration is bind-only;
say so rather than describing the proof as intricate.

Also check, independently of form: does the delivered statement actually say what the source
claims? A conjecture asserting an exact value or an exact rank is not settled by a one-sided
bound. Quote the source sentence and the Lean type side by side.

## Verdict

`approve` only if every declaration is content with a named escape witness, and the statement
is faithful to the source. Otherwise `reject`, quoting the declaration and the upstream result
that already yields it. Do not approve because a build was green; a green build says the proof
elaborates, not that it contributes.
