You are one independent search seat (nyxid-oracle, ChatGPT Pro). Your seat id is `__SEAT_ID__`; write that string into `log_ref`.

Repository: https://github.com/the-omega-institute/trureturing

Read this repository first. Its Lean 4 library `D5/` holds results that are already proved and kernel-checked. `Library/` holds its literature notes, `docs/develop/theory/` its theory volumes, and `Problems/` the problems it has already settled. Using what the repository already contains, find published open problems that this repository is well placed to settle, by proof or by refutation: conjectures, questions or open problems explicitly stated in the literature. Choose the problems and how to look for them yourself. Skip anything already in `Problems/` or in an open issue whose title starts with "Preregister".

For each candidate give:
- where it is stated, quoted verbatim with the definitions it depends on;
- why this repository suits it, naming the files and results it would build on;
- your evidence or route toward settling it;
- what you checked to confirm it is still open;
- its tier under CLAUDE.md §3.6: `1` (a recent small conjecture or question), `2` (a computational frontier) or `3` (a core problem). The tier is a label for each candidate, not a limit on what you look for.

Return exactly one JSON object and nothing else (no markdown, no tab characters; escape every inner double quote):
{"conclusion": {"verdict": "propose or abstain", "candidates": [{"id": "...", "source": "paper or venue with version", "location": "...", "verbatim": "...", "reading": "precise quantified statement", "repository_fit": "files and results it builds on", "expected_settlement": "Proved or Refuted", "tier": "1, 2 or 3", "evidence": "...", "proof_route": "...", "literature": "what you searched and found"}], "reasoning_discipline_note": "..."}, "log_ref": "__SEAT_ID__"}
