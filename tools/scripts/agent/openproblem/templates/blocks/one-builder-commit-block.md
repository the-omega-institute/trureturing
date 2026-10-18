
## One builder commit for the door output (binding; overrides every "commit the writer output" step above)
`skills/codex-formalize/SKILL.md` Step 7 requires the complete **deposit-and-cover delta** in ONE builder-owned commit. That delta is:
- every supporting module's state record;
- owner re-pins;
- the settling module's state record;
- the Problems dossier;
- any mirror the doors regenerated.

The freeze tools read the working tree (CLAUDE.md §6.1), so do **not** commit between doors:
1. Commit the Phase A source (Lean, Scribe, Library note) first, as its own content commit.
2. Run the owner re-pins, the supporting `ledger-align --add`, and the settling `make deposit-uncovered` in sequence on the working tree.
3. Then run `git status --short` and `git diff --check`, stage everything, and create **one** builder commit with the door output.

Never split the door output across commits.
