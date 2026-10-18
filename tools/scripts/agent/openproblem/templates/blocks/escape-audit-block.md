## Escape audit (CLAUDE.md §3.9 at origin/dev; binding)
Each newly authored public D5 `theorem`/`lemma` in the delivery is an audit target. The designated refutation result (`utility: … basis=refutes; result=…`) is exempt.

**Refutation-only modules.** If the only public theorem is that exempt result, state it in one sentence in the module comment, the dossier and the PR body: "The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9)."

**For every other audit target**, attempt a faithful four-slot registration in the same delivery:
- Write `Reg/D5/<the module's mirrored path>.lean`, using a typed `Contract.Registration` whose `readout` applies an already-enrolled template.
- Search `Reg/Support/**`, for example `PointwiseEqualityRegistrations`, `PointwiseOrderRegistrations`, `GuardedEqualityRegistrations`, `IffRegistrations`, `ExistentialWitnessRegistrationTemplates` and `DependentFamily`, and the existing `Reg/D5/**` mirrors for a template that lawfully reads the theorem's statement.
- Follow `skills/codex-formalize/SKILL.md` "Escape-audit delivery" and spec A5.5/A5.6.
- Compile the Reg module through `make lean LEAN_TARGETS="<the delivered modules and every frozen module you re-pin, dotted>"`.
- Before the push, record the registration as "pending CI reading"; never write `declared_validated` without the CI reading.
- After pushing the delivery head, read the DTR finding for each audit target from its required CI `current` job: run `gh run view <run-id> --log --job <current-job-id>` and search the `DTR-` lines. Report each finding with the run id and job id; `DTR-Declared` means complete.

**If registration is missing, invalid or blocked** (no lawful template, failed E1–E8 or bridge checks, or missing evidence):
- Open one issue for this delivery, or reuse the lane's existing one: `gh issue create --title "Escape audit unfinished: <module>" --body-file …`.
- Name each audit target, the concrete template gap or failure verdict with its readings (for example `DTR-Unregistered` from the required CI `current` job for the pushed delivery head, with its run id and job id), and the missing evidence.
- Link the issue in the module comment (one line), the dossier and the PR body, and state that the escape audit is unfinished.
- Continue the delivery.

**Never:**
- modify the judge (`tools/**`, inspector, judge Interface/Impl packages);
- force a wrong template;
- weaken a theorem or add bind-only wrappers;
- claim `declared_validated` without the compiled evidence and the CI reading.

Report registration as complete or unfinished with its linked issue; never write "paused".

**Reg imports.** Import only what the registration uses:
- `Reg.Support.*` modules whose `TemplateEnrollment` the readout selects;
- the D5 owner;
- the contract types.

An enrollment module is not needed by Lean compilation, so a single-import deletion test compiles (exit 0). It is still needed, because the judge accepts only an enrolled template found in the Reg import closure. Say so in one sentence in the PR body next to the import-deletion readings. Every other import must fail the deletion test; remove any that does not.
