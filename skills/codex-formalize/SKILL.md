---
name: codex-formalize
description: Use when asked to formalize and close an open digestion atom in this repository.
---

# Codex Formalization Workflow

## Install

This is a Codex skill package. Install it by copying the `skills/codex-formalize/` directory into `$CODEX_HOME/skills/` (default `~/.codex/skills`), or load it by naming this `SKILL.md` path directly in a dispatcher. This repository copy is the single source of truth; any installed copy is a projection of it.

## Scope and authority

This file is Codex-specific packaging of repository obligations; it has no authority of its own. `docs/develop/spec/golden-ledger-repo-spec.md` is the sole normative specification; `CLAUDE.md` is the invariant frame governing how work is done; and `agents/CONTEXT.md` is the finite-context map and routing aid, not an authority above the specification. Live harness output is the decisive judge of fact about the current tree. If this file disagrees with any of them, they win and this file is the bug.

## Read first

- `CLAUDE.md` - owns the repository's invariant frame and working ethics.
- `agents/CONTEXT.md` - owns the finite-context map, routing, and naming guidance.
- `docs/develop/spec/golden-ledger-repo-spec.md` - owns the normative repository specification.
- The applicable `agents/*.md` role charter - owns role-specific duties.
- `agents/echo-template.md` - owns the statement-echo record.
- `make help` - owns the live catalogue of canonical doors.
- `tools/` - owns executable admission and repository enforcement.

## State machine

Follow these steps in order. Do not pass a step until its postcondition holds.

### 0. Establish the environment and isolation

Run:

```sh
eval "$(sed -n '/^export PATH=/p' tools/scripts/local-harness-gate.sh)"
# If not already in a dispatcher-assigned isolated lane:
make worktree KIND=math NAME=<lane> && cd <created-path-from-output>
pwd -P && git rev-parse --show-toplevel && make -C tools dotnet
```

Re-read the current `export PATH` from `tools/scripts/local-harness-gate.sh` for every task rather than trusting a list quoted elsewhere; its `/usr/sbin` entry must survive because the report supervisor requires `lsof`, which lives there. If a dispatcher already assigned an isolated lane, do not create a second one: confirm the existing lane with the same `pwd -P` / `git rev-parse --show-toplevel` check. Otherwise, the `make worktree` output is JSON whose `path` field names the created path; substitute that value for `<created-path-from-output>` and work only there.

Build through the canonical `make -C tools dotnet` door because `make show-atom` runs the Release CLI with `--no-build`.

Before any deposit, require `git status --short` to print nothing except the intended formalization changes. Prefer a fully clean tree before beginning the task. The deposit workflow in `tools/scripts/workflow/playbook-workflows.sh` stages with `git add -A` in both `commit_phase_a_if_needed` and `commit_all_if_needed`; therefore every change in the tree can enter a deposit commit.

Postcondition: the pinned toolchain is on PATH; `pwd -P` and `git rev-parse --show-toplevel` agree with the assigned or created isolated lane; `make -C tools dotnet` has built the CLI so `make show-atom` succeeds; and no unrelated or unexplained change is present.

### 1. Choose exactly one open atom

Inspect candidate snapshots in `Generated/echo-residuals/<source_id>.md`. Treat them only as candidate listings. Obtain the authoritative atom text with:

```sh
make show-atom ATOM_ID=<id>
```

Never quote the projection as authoritative. Prefer an atom with few unresolved subitems and an elementary, self-contained statement.

Triage the claim class before committing to it; each class below is named by landed outcomes, not speculation:

- **Best odds — concrete certificate/computation claims** whose data is inside the atom text (a walk value, a finite identity, explicit witnesses): these close with `decide`/`norm_num` and have the highest landed success rate.
- **Good odds — claims whose machinery is already frozen**: a bridge, instantiation, or characterization theorem connecting existing declarations.
- **Definition clauses — only with an earning theorem** (see the thin-deposit taxonomy below); a definition alone is not a target.
- **Do not encode — institutional/philosophical prose clauses** (governance clauses, postmortem narratives, interpretive premises): they have no mathematical content, and encoding them as generic set/logic predicates is how thin deposits happen. Report them as not-formalizable prose rather than dressing them in Lean.
- **Do not attempt without a machinery plan — heavy universal claims** (representation theorems, general-dimension obstructions): landed lanes on these either time out or fabricate. If the machinery gap is real, `open` naming the gap is the valuable output.

Postcondition: one atom ID is selected, its claim class is named in the report, and its verified `make show-atom` output is retained as the statement source.

### 2. Echo the statement before proving it

Follow `agents/echo-template.md`. Write a clause-level mapping from every quantifier, domain, hypothesis, conclusion, and generality claim in the authoritative atom text to the intended Lean declaration. Account for every unresolved subitem.

If an ambiguity cannot be resolved without weakening the claim, stop and report the result as `open`.

Postcondition: every source clause has one intended Lean counterpart, or the task has ended as `open` with the ambiguity named.

### 3. Search the library before proving

Apply `CLAUDE.md` 11, "library before proof." Search pinned mathlib and the repository's `D5/` declarations for the complete statement and for lemmas that close its dependencies. Record every query verbatim and record whether it hit.

Check the bind path first: the cheapest faithful discharge is an existing frozen theorem, and dozens of residues have been discharged with zero new Lean. If a frozen declaration already covers the residue leg verbatim (not narrower — watch the grader traps below), the correct deliverable is a bind recommendation naming that declaration and the evidence, not a new module. Ledger surgery itself is dispatcher-owned; your report carries the finding.

If the result exists upstream, import and apply it. Do not reprove it: a reproof of an existing declaration creates a second source of truth.

Search for the statement shape, not the module name. A landed lane died reproving a frozen theorem in strictly weaker form (it added a derivable `Odd d` hypothesis) even though it had been told to read that exact module: reading a module and greping for the identity are different acts, and only the second one protects you. Grep `D5/` for the hypothesis pattern and the conclusion pattern of your target, for example:

```sh
grep -rn "≡ -1 \[ZMOD" D5/ --include='*.lean'
grep -rn "jacobiSym\|J(" D5/ --include='*.lean' | grep -i <conclusion-token>
```

If the identity already exists in equal or stronger form, the correct output is the reuse or an `open`/abstain naming the frozen declaration — never a new module. A hypothesis derivable from your other hypotheses (parity from a congruence, coprimality from an inverse relation) must be derived, not assumed: assuming it makes your theorem strictly weaker than the source claim and reviewers reject it as a weaker duplicate.

Postcondition: the search trace is recorded and every hit is either reused or accompanied by a concrete explanation of why it is not the same claim.

If the search cannot be completed faithfully, end the task as `open` with no deposit, carrying the Step 8 evidence: statement echo, search trace, failed approaches with reasons, and machine diagnostics.

### 4. Learn the current artifact shape

Run:

```sh
git log --no-merges -20 --format=%H --grep='^formalize: deposit'
git show <sha>
```

Read the most recent actual `formalize: deposit` commit. That commit is the live template for the exact Lean header shape, the `.scribe.cs` mirror shape, and the files touched by deposit. Copy its shape rather than formats remembered or restated here. If this file and that commit disagree, the commit wins.

Postcondition: the chosen template SHA and its touched paths are recorded, and the planned artifacts follow that observed shape.

### 5. Write and compile the artifacts

Write the Lean module and its `.scribe.cs` mirror using the live template. Discover the current path-to-GID rule from that template and the live path-policy owner; do not rely on a remembered grammar.

A new theorem must go in a new Lean module. Before writing into an existing module, check whether it has an active Freeze event:

```sh
module_path='D5/path/Module.lean'; grep -l -F "$module_path" Golden/Frozen/accepted/*.json
```

Exit 0 with an accepted-record path means frozen; exit 1 with no output means not frozen (any other result is a failed check). The frozen ledger pins the module's declaration set, not just its bytes, so it refuses adding a declaration to a frozen module. Reattest covers changed bytes with an unchanged declaration set; it is not an escape hatch for adding a declaration. If the atom genuinely belongs inside an existing frozen module, do not edit it: end `open`, naming that module and the frozen-ledger constraint.

Before creating the new module, set `lean_dir` to its target directory and `blueprint_dir` to the corresponding `Blueprint/` mirror directory, then measure both and confirm that adding one counted file to each stays within the limit:

```sh
lean_count=$(git ls-files "$lean_dir" | awk 'END { print NR+0 }'); blueprint_count=$(git ls-files "$blueprint_dir" | awk '!/\.md$/ { n++ } END { print n+0 }'); printf '%s %s\n%s %s\n' "$lean_dir" "$lean_count" "$blueprint_dir" "$blueprint_count"; test $((lean_count + 1)) -le 12 && test $((blueprint_count + 1)) -le 12
```

Committed Blueprint `.md` renderer oracles are excluded from capacity, but `.scribe.cs` sources count. If the natural target directory is full, do not place the module in a semantically wrong directory to evade the limit: split the bucket, register the new domain in `Meta/domains.yaml`, place the module in the new directory, and carry the protected-surface cost for the conservative-extension gate to judge. A protected-surface change is priced work, not a stopping condition. Reserve `open` for what is genuinely unresolvable, such as an ambiguity that cannot be settled without weakening the claim or a proof that will not close, never for work that merely costs more.

Iterate with a scoped build (`lake build <YourModuleName>`), then run the canonical door once when the artifacts are final:

```sh
make lean
```

Judge completion only by exit code, never elapsed time or quiet output. Full doors cost minutes each; a landed lane died by burning its entire three-hour budget on seventy-two full preflight runs chasing a flaky unrelated test. Iterate scoped, verify canonically once.

Run every shape check NOW, before Step 7: line 6 ends with ` -/`, the generality tag matches the weakest import and the module's nature, the scribe formulas obey the rejection taxonomy, the emitted `.md` mirrors every conjunct. After a successful deposit the module's bytes are pinned by the frozen ledger — a defect found before the ceremony is a free edit; the same defect found after is a full rewind ritual (restore the frozen ledger and receipts from `origin/dev`, re-run the ceremony). Three landed header violations were repaired the expensive way; do not join them.

Postcondition: both source artifacts exist in the observed shape and `make lean` exits 0.

If a faithful proof cannot be made to compile, end the task as `open` with no deposit, carrying the Step 8 evidence: statement echo, search trace, failed approaches with reasons, and machine diagnostics.

### 6. Run the fidelity and non-hollowness gate

Complete every evidence item in the checklist below. A green compiler and harness do not discharge this step.

Postcondition: every checklist item has evidence and none is `ASSUMED-UNVERIFIED`; otherwise deposit is blocked.

If any checklist item cannot be evidenced, end the task as `open` with no deposit, carrying the Step 8 evidence: statement echo, search trace, failed approaches with reasons, and machine diagnostics.

### 7. Deposit, verify, and cover

Only after Step 6 passes, run:

```sh
make deposit ATOM_ID=<id> GID=<D5/Path/Module.theorem_name>
make preflight
```

Both commands must exit 0. Judge them only by exit code, and never pipe a judgment command: `cmd | tail -1` reports the pipe's exit status, not the command's, and three landed incidents (a merge that silently failed, a ceremony run on a stale base, a cover failure read as success) trace to exactly this. Run the command bare, or capture `$?` on the command itself before any formatting.

If `make deposit` or `make preflight` exits nonzero, stop before `cover` and end as `open`. Report the failed command and exit code, machine diagnostics, touched paths, and the actual resulting tree and commit state; `deposit` may already have produced commits before failing.

To close the atom, run:

```sh
make cover ATOM_ID=<id> GID=<gid>
```

Before reporting commit structure, inspect:

```sh
git log --no-merges --grep='^formalize: cover'
```

Recheck the live history and report what it actually shows; do not turn this observation into a permanent rule.

Postcondition: deposit and preflight exited 0, and cover either exited 0 or its failure is captured as an `open` outcome with diagnostics.

### 8. Push and open the pull request, or report `open`

After `make deposit` and `make preflight` both exit 0 and Step 7 completes, push the current branch and use the repository door:

```sh
git push -u origin <branch>
make pr-open HEAD=<branch> MESSAGE=<message-file>
# The message file's first line is the PR title; the rest is the PR body.
```

The door arms auto-merge. After it opens the pull request, do not push further changes to that branch: the pull request may already have merged, in which case a later successful push does not put that commit on `dev`. Any further change requires a new branch and a new pull request.

If the dispatched sandbox forbids git writes, state that constraint explicitly and hand the exact `git push` and `make pr-open` invocations above, with substituted arguments, to the caller; do not report `success` as though the work landed. Otherwise report `success` only with the opened pull request, touched paths, door-produced commit subjects, every relevant exit code, and completed fidelity-gate evidence. Or report `open`, naming the stopping step and carrying every evidence class reached; mark each unreached class not run and explain why. There is no third outcome.

Postcondition: the task ends with an opened pull request, or with evidence-complete `open`.

## Fidelity and non-hollowness gate

Before Step 7, the producing seat must answer every item with concrete evidence. This checklist collects producer-side evidence; it is not machine-verified and does not itself prove non-hollowness. The repository's own machine gate is deferred by the skipped `CoverAtomEnvelopeTests.cs` signature-match test cited below. An independent adversarial reviewer, not the producing seat, would turn this evidence into verification.

- Conclusion substance: show that the conclusion is not `True`, not definitionally equal to `True`, and not a restatement of a hypothesis.
- Hypothesis satisfiability: exhibit a Lean term witnessing the hypotheses that elaborates in the pinned toolchain, such as a checked `example` in the module or a term the seat states and checks, and carry that term in the report. Prose asserting or naming a witness does not discharge this item; if no compiling witness can be produced, the outcome is `open` and deposit is blocked.
- Domain inhabitance: exhibit a Lean term inhabiting the domain that elaborates in the pinned toolchain, such as a checked `example` in the module or a term the seat states and checks, and carry that term in the report. Prose asserting or naming an inhabitant does not discharge this item.
- Proof substance: show that the statement carries content beyond unfolding a definition the producing seat itself introduced, whatever tactic closes it.
- Deposit substance: for a module introducing a new definition, name the theorem(s) that make the definition earn its freeze (instantiation against existing repository structures, an independent-sides characterization, or a citable property), and show the module's connection to the existing machinery its vocabulary names. Anonymous `example`s do not discharge this item; see the thin-deposit taxonomy above.
- Duplicate search: cite the Step 3 trace showing this is not a renamed duplicate of a mathlib or `D5/` declaration.
- Clause fidelity: place the authoritative atom clauses beside the Lean clauses one-to-one, mapping every clause to an exact Lean binder, hypothesis, or conclusion. The dropped-or-weakened set must be empty; any weakening, omission, or unresolved ambiguity forces `open` before deposit.
- Rendered-statement fidelity: read the emitted Blueprint `.md` for this document and compare its displayed statement against the Lean declaration symbol by symbol; use a neighbouring landed mirror as a shape check.
  The formula DSL and writer own tokens that can be valid LaTeX and structurally accepted yet mean something different from the theorem, so `emit` exiting 0 is not evidence that the rendering is faithful.
  A mismatch blocks deposit; resolve it against `tools/StrataLint.Scribe/Ast/FormulaDsl.cs` and `tools/StrataLint.Scribe/Writers/LatexWriter.cs`, or end the task `open`.

Finally, run the grader-trap checklist against your own work before sign-off — witness-vs-universal, instance-vs-general, conditional-vs-unconditional, pointwise-vs-operator, proof-internal-vs-addressable-statement, multi-clause residue names, mechanism-vs-outcome — and record for each either "not applicable" or how your statement clears it. Reviewers will run exactly this list; a mismatch you find yourself is a free fix, one they find is a blocked lane.

Any item without evidence blocks deposit. Mark an unverified fact exactly `ASSUMED-UNVERIFIED`; never replace measurement with hedging language. The repository's current signature-match test explicitly leaves this gap open: `CoverAtomEnvelopeTests.cs` says an unchanged pre-committed `theorem t : True` would pass, so compilation, deposit, and cover do not certify fidelity.

## Earned hard gates (precedent taxonomy)

Every entry below names a failure class that actually occurred in landed rounds of this repository. These are not hypothetical defenses; they are the recurring ways seats fail review. The owners named in "What this skill does not own" still win on current thresholds — this section tells you where lanes die.

### Mathematical content

- **Definitional tautology (the most common kill, seven landed cases).** Never define a thing as the formula you then "prove"; never install the conclusion by definition; never prove an iff whose two sides you defined to coincide. Both sides of every equation and iff must have independent anchors: a frozen declaration, a mathlib declaration, or data present in the authoritative atom text.
- **Invented-classifier variant.** Defining your own key or equivalence (for example a `Setoid.ker` quotient of a tuple you chose) and then proving bijectivity or a count over its quotient proves nothing: the result is true by construction for any injective key, and the arithmetic coordinates you computed go unused. If the subject's own orbit/class notion is not in the repository, the honest outcome is `open` naming the missing carrier — reviewers reject the invented one 2-1 or worse.
- **Fabrication ban.** If a concrete datum your theorem needs — a case list, a walk, a witness pair, the meaning of a symbol — is not derivable from the authoritative atom text plus in-repo frozen definitions, do not invent it. Exhibiting concrete numerals you computed yourself from in-repo definitions is derivation and is fine; conjuring a list the source only attests is fabrication. End `open` naming precisely the missing datum.
- **A stronger variant does not excuse a duplicate.** Twice now a lane found the frozen theorem covering its residue leg and wrote a new module anyway, rationalizing the addition as "exposing hidden facts" or "removing a hypothesis" — a strictly stronger or nicer-shaped variant of an already-covering frozen statement. If the frozen statement covers the leg, the deliverable is the bind report; strengthening it is gold-plating unless a named consumer needs the stronger form, and reviewers discard the module either way.
- **Witness-vs-universal honesty.** An `∃`-witness does not discharge a universal claim; an instance (dim 4, a fixed modulus, an 18-ray set) does not discharge a general claim; a conditional theorem does not discharge its unconditional attestation. State exactly what you proved; graders run a named-trap checklist (witness-vs-universal, instance-vs-general, conditional-vs-unconditional, pointwise-vs-operator, proof-internal-vs-addressable-statement, multi-clause residue names, mechanism-vs-outcome) and a mismatch is a blocker, not a nuance.
- **Unused hypotheses are dishonest signatures.** A binder the proof never uses gets stripped at collection; write the minimal true signature.

### Artifact shape

- **No new top-level domain for one module (three landed rejections in one day).** When your module's natural parent directory is at its file limit, the repository convention is a SPLIT BUCKET under that parent (`Parent/NewBucket/`, split-only, no moves), recorded in the stratum's MAP file (split-history entry AND bucket-catalog line; create the stratum MAP and register it as a governance document if the stratum has none), with any new group name registered where the precedent registers it. Reuse an existing bucket whenever ownership genuinely fits (a symmetry theorem belongs in the existing `Symmetry/` bucket, not a new sibling). Registering a fresh top-level domain in `Meta/domains.yaml` for a single module is the anti-pattern: every instance was struck down by review and relocated.
- **FromLean is only legal for projector-registered shapes (five-statement landed rejection).** A lane once used `StatementSource.FromLean()` for all five of its Describes; the kernel projector returned Unprojectable for every one (`Finset`, a repo predicate, `LT.lt`, `DirichletCharacter`, `Nat.Prime` are all outside the registered shapes), the emitter exited 1, and no Blueprint mirror existed for the fidelity gate. `FromAuthor` with a typed Disp formula is the DEFAULT; before even considering FromLean, verify the statement's every constituent is projector-registered — when in doubt, FromAuthor. Then run the emit and READ the produced `.md`: a missing mirror blocks deposit by itself.

- **Header law (three landed violations).** The six-line header sits at byte zero and the digest is a SINGLE line ending ` -/` on line 6. A wrapped digest is a violation; ` -/` alone on line 7 is the same violation. Copy the shape from the latest landed deposit commit, then verify your file's line 6 ends with ` -/`.
- **Generality tag follows the weakest import and the module's nature (two landed blockers).** A concrete-instance module (fixed modulus, fixed witness set) is `generality: I`; a general theorem module is `G`; a `G` tag on a file importing `I`-level facts is a violation. Compare your nearest landed neighbors before writing the tag.
- **Scribe formula rejection taxonomy (dozens of mechanical rejections; owner `FormulaDsl.cs`/`LatexWriter.cs` wins on current tokens):** `F.Id` arguments are strictly alphabetic; `D()` takes one digit per argument (`D(2,3)` never `D(23)`); `Sp` is required after macro and relation tokens (`Neg`, `Neq`, `Vert`, `Lvert`, `Rvert`, `Forall`, `InMacro`, `Exists` after `Neg`, …) before `F.Id`/`Operatorname`; `Star` not `Ast`; `Neg` not `Not`; the `FormulaDsl` usings are required; no private string-to-Formula helpers; the displayed formula must mirror every conjunct of the Lean statement — mirror-value swaps (two constants exchanged between clauses) are a landed reviewer catch, so read your emitted `.md` value by value.

### Deposit substance (thin-deposit taxonomy)

A landed pull request consisting of one generic one-line `def` plus two `simp`-trivial anonymous `example`s, with an empty pull-request body, is the canonical thin deposit — it froze notation, not truth. The gates below name what was missing.

- **Encoding is not formalization.** Strip your Lean statement of its prose-borrowed names and read what remains. If it is a generic set/logic triviality (`∀ x ∈ S, f x ⊆ {c}` under an "observer" vocabulary), you have renamed the source clause, not discharged it. Before depositing a definition, answer in writing: *what named theorem would make this definition earn its freeze?* If no such theorem is in reach, the honest outcome is `open` with the definition offered as a sketch, not a deposit.
- **Definition-only modules are presumptively insufficient.** A new `def` must ship with at least one NAMED theorem that either instantiates it against existing repository structures, characterizes it (an iff with independently defined sides), or proves a property that some later consumer can cite. Anonymous `example`s are fidelity evidence, never deposit content: they have no GID, cannot enter coverage, and cannot be cited by anything.
- **No island modules.** A module whose only relationship to the repository is its directory path is a second framework wearing repository vocabulary. If your definition names a concept the repository already has machinery for (observers, windows, channels, walks), it must import and connect to that machinery — an "observer" predicate that touches none of the existing observer declarations belongs to nothing and discharges nothing. If the concept genuinely has no repository counterpart yet, say so explicitly and justify why a floating generic definition is worth freezing now rather than when its first theorem arrives.
- **The external-referee test.** Ask whether the module would survive review as a standalone library contribution: a one-line definition with `simp` examples would be rejected anywhere as content-free. The ceremony cost of a deposit (freeze, receipts, coverage) is justified by content, and "it compiles and is honest" is the floor for a report, not a reason to deposit.
- **The pull-request body is evidence, not decoration.** Carry the clause-mapping echo, the search trace, and the explicit honest-partial disclosure (what is asserted, what remains open) in the pull-request body. An empty body on a deposit pull request hides exactly the thinness these gates exist to catch.

### Moving base (multiple drivers, hourly-advancing dev)

Several machines drive this repository concurrently and `dev` advances roughly hourly; three landed incidents define the discipline:

- **Merge `origin/dev` and verify before any ceremony**: the only trustworthy sync check is `git merge-base --is-ancestor origin/dev HEAD` — a piped or prettified merge command has silently failed and sent a ceremony onto a stale base.
- **A capacity or baseline red may be the baseline's fault, not yours**: a candidate diffed against an older base once made another driver's new file look like this lane's twelfth — the remedy was merging newer `dev` and re-pushing, not restructuring. Before treating a structural red as yours, re-sync and re-run.
- **The remote branch may have been advanced by automation** (update-branch bots): if push is rejected, fetch the branch itself, merge, and push again — never force-push, and never rebase after a deposit (frozen provenance pins the commit lineage; rebasing orphans it).

### Process honesty

- **Never claim a build result without its exit code.** A seat once reported `lake` green while the build failed; since then the dispatcher re-runs the build at collection and a false green is a terminal lane offense. Report the command and the exit code; quiet output and elapsed time are not evidence.
- **Never touch `Meta/Digestion/**`.** Ledger surgery (coverage, residue removal, state moves) is exclusively the dispatcher's; a seat once edited it and the change was reverted wholesale. The same applies to `Golden/Frozen/**` and formalization receipts.
- **When a dispatcher assigns output paths, write exactly those.** `result.json` (a conclusion envelope, no logs inline) and `done.sentinel` at the assigned paths are the deliverable; your final prose message is not. A sentinel written while you keep running is worse than no sentinel — write it last, then stop.

## Prohibitions

- No `sorry` outside `D5/X_Frontier/`; the Lean admission harness owns this rule.
- No new axiom; the Lean admission harness and axiom policy own this rule.
- Never hand-write a status field; `agents/CONTEXT.md` and status derivation own it.
- Never hand-edit generated projections; their canonical producers own them.
- Never hand-edit the frozen ledger; the deposit door owns it.
- Never add a declaration to a module with an active Freeze event; the frozen ledger owns this constraint.
- Never exceed directory capacity; `tools/StrataLint.Engine/Rules/RepositoryRules.Structure.cs` owns this rule.
- Never hand-edit formalization receipts; the deposit and cover doors own them.
- Never edit `Meta/Digestion/**` from a producing seat; digestion-ledger surgery is dispatcher-owned.
- Never weaken the echoed statement to make a proof close; the statement echo and this fidelity gate own that obligation.
- Never invent a "needs human review" outcome; `CLAUDE.md` 22 forbids human-review gates outright.

## What this skill does not own

- Path policy is owned by `tools/StrataLint.Engine/Coordinates/RepositoryPathPolicy.cs` and its registered policy data.
- Capacity limits are owned by `tools/StrataLint.Engine/Rules/RepositoryRules.Structure.cs`.
- Lean header shape is owned by the live harness and demonstrated by the latest landed deposit.
- Import direction is owned by the repository specification and its StrataLint rules.
- Admission, freezing, receipts, coverage, and status are owned by the canonical `make` doors and `tools/`.

This skill names each concern's owner without reproducing its definitions or thresholds. The prohibitions above are pointers that carry the owner's name. Discover each concern's current form from its owner; the harness is the judge.
