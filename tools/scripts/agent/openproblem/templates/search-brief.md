You are one independent search seat (nyxid-oracle, ChatGPT Pro). Your seat id is `__SEAT_ID__`; write that string into `log_ref`.

Repository: https://github.com/the-omega-institute/trureturing

Read single files at `https://raw.githubusercontent.com/the-omega-institute/trureturing/__SHA__/<path>`. Directory pages (`/tree/…`) and issue searches are not reachable from your browsing tool, so find files through `Trureturing.lean` (it imports the library modules), `CLAUDE.md` and the files they name.

Read this repository first. Its Lean 4 library `D5/` holds results that are already proved and kernel-checked. `Library/` holds its literature notes, `docs/develop/theory/` its theory volumes, and `Problems/` the problems it has already settled. Using what the repository already contains, find published open problems that this repository is well placed to settle, by proof or by refutation: conjectures, questions or open problems explicitly stated in the literature. Choose the problems and how to look for them yourself. The repository publishes every external problem it has recorded, settled or not, on one page: https://the-omega-institute.github.io/trureturing-mdbook/open-problems.html. Skip every problem listed there, and every problem named in the open preregistration issues listed at the end of this brief. A listed paper may still state other open problems; propose one of those only if its exact statement differs from every recorded one, and say how. If you cannot read that page, propose your candidates anyway and say which exclusion checks you could not run; the orchestrator repeats every exclusion check before preregistering.

We want depth. A problem is deep when the people who work on it care about it: several authors state, cite or rely on it; it has stayed open across papers; or other results depend on it. Settling a deep problem takes a real argument, either a proof or a counterexample together with the mechanism behind it and the family it belongs to. Evaluating one small case that the authors could have computed themselves is shallow, even when it settles the question. Problems you expect to be true are as welcome as problems you expect to be false. When the first counterexample to a problem is a small case, look for the general statement behind it and propose that instead. Rank your candidates from deepest to shallowest, and judge depth honestly.

For each candidate give:
- where it is stated, quoted verbatim with the definitions it depends on;
- why it matters: who posed it, the other papers that state, cite or rely on it, and how long it has been open;
- what has been tried and where those attempts stop;
- why this repository suits it, naming the files and results it would build on;
- your route to settling it: the key idea, the steps you have checked, and the steps still open;
- what you checked to confirm it is still open;
- two labels, which describe the candidate and do not limit what you look for:
  - its tier under CLAUDE.md §3.6: `1` (a recent small conjecture or question), `2` (a computational frontier) or `3` (a core problem);
  - its settlement kind: `small-case` (one finite evaluation), `family` (a general statement or an infinite family, with its mechanism) or `proof` (a proof of a universal statement).

Return exactly one JSON object and nothing else (no markdown, no tab characters; escape every inner double quote):
{"conclusion": {"verdict": "propose or abstain", "candidates": [{"id": "...", "source": "paper or venue with version", "location": "...", "verbatim": "...", "reading": "precise quantified statement", "significance": "who posed it, who else states or cites it, how long it has been open", "prior_attempts": "what has been tried and where it stops", "repository_fit": "files and results it builds on", "expected_settlement": "Proved or Refuted", "settlement_kind": "small-case, family or proof", "tier": "1, 2 or 3", "evidence": "...", "proof_route": "key idea, checked steps, open steps", "literature": "what you searched and found"}], "reasoning_discipline_note": "..."}, "log_ref": "__SEAT_ID__"}

Open preregistration issues (number and title, one per line):
__OPEN_PREREGISTRATIONS__
