<!-- Title format `type(scope): action and result`, such as
`docs(contributing): clarify the Issue template`.
Target `dev` for ordinary contributions.
See https://github.com/the-omega-institute/trureturing/blob/dev/docs/CONTRIBUTING.md#branch-pr-and-issue-format
Remove sections that do not apply. -->

- **Skills** <!-- List skills used or state that none were used. -->
- **Contributors** <!-- Name the implementers and reviewers, their roles and model families where applicable. Disclose AI assistance. -->
- **Review and verification scope** <!-- Record a self-check or give the independent review method, votes and resolution of disagreements. Distinguish firsthand checks from reviewer reports. -->
- **Agent session** <!-- Give the host session ID and resume command (`claude --resume <id>` or `codex resume <id>`), if applicable. When taking over and updating the PR, append the new session and keep the original entries. -->

## Summary

<!-- State the result, why it matters, and the source or requirement. Name the dependencies it relies on, such as prior results, sources or tool versions. For theory text, state the literature position and limits of the claims. -->

## Related issues

<!-- Use `Closes #123` for a full resolution or `Refs #123` for a related or partial change. Use `owner/repo#123` for another repository. Omit this section if no Issue applies. -->

## Proof shape and admission

<!-- For new Lean declarations, report these fields per declaration under CLAUDE.md §§3.2–3.3. -->

- `proof_shape`
- `escape_witness`
- `admission_basis` <!-- escape-witness / open-problem-resolution (with preregistration Issue) / none -->
- `utility` <!-- For computational results, include `question_answered` (with preregistration) and `dominating_theorem_search` (scope, method and result). -->

## Freeze and coverage

<!-- Complete for freeze or coverage work under CLAUDE.md §4.7. -->

- **Change** <!-- deposit / deposit-uncovered / cover / deposit+cover / ingest -->
- **Links** <!-- Give source_id and atom → GID. State when there is no atom. -->
- **Resulting state** <!-- Give the frozen state path or the atom state transition. -->

## Verification

<!-- List actual commands, scope and exit codes. Report what the evidence ruled out, relevant open cases and pending checks. -->

- [ ] This PR leaves all previously closed results valid.
<!-- Check only if true. If a previously closed result is overturned, identify it and link the correction here. -->
