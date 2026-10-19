
## Independent check before the door (binding; overrides any step that runs a freeze door in the same attempt)
A rework that changes a definition, a public statement or a proof must pass an independent mirror, fidelity and judgement-form check **before** its freeze door. A post-freeze review round does not replace this check, and freezing first costs a further rebuild.
- Therefore, when this rework changes any `.lean` declaration (body or statement), stop after the Phase A source commit and before any `ledger-align`, `deposit` or `deposit-uncovered`, with `verdict: mirror-ready`.
- Report the changed declarations, the compiled checks and the head. The orchestrator dispatches an independent mirror seat, and then a continuation that runs the doors.
- A rework that changes only Scribe prose, the dossier, the Library note or the PR body does not stop here.
