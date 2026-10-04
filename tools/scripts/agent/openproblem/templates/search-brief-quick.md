You are one independent search seat (nyxid-oracle, ChatGPT Pro). Your seat id is `__SEAT_ID__`; write that string into `log_ref`.

Repository: https://github.com/the-omega-institute/trureturing

Read single files at `https://raw.githubusercontent.com/the-omega-institute/trureturing/__SHA__/<path>`. Directory pages (`/tree/…`) and issue searches are not reachable from your browsing tool, so find files through `Trureturing.lean` (it imports the library modules), `CLAUDE.md` and the files they name.

This is the fast track of the repository's search: find published open problems that this repository can settle now, with a kernel-checked proof or refutation, through a pipeline measured in hours. A separate deep track handles core problems, so skip famous named conjectures, prize problems, anything an active specialist community is attacking, and anything whose settlement needs a research programme.

The repository publishes every external problem it has recorded, settled or not, on one page: https://the-omega-institute.github.io/trureturing-mdbook/open-problems.html. Skip every problem listed there, and every problem named in the open preregistration issues listed at the end of this brief. A listed paper may still state other open problems; propose one of those only if its exact statement differs from every recorded one, and say how. If you cannot read that page, propose your candidates anyway and say which exclusion checks you could not run; the orchestrator repeats every exclusion check before preregistering.

Where to look. Scan the arXiv listings of __WINDOW__. Mathematical physics comes first (math-ph, quant-ph, hep-th, cond-mat.stat-mech, cond-mat.str-el, nlin); any other area is also welcome. Also accept OEIS conjecture lines (`%C`, `%F`) and explicitly stated questions in older papers that nobody has followed up. Report how many papers you scanned per archive.

What to propose. Look for a conjecture, question or belief explicitly stated in a paper and still unsettled, about finite or algebraic objects, that you can settle yourself now in one of two ways:
- (a) it is false at a small explicit case, and you give the exact counterexample with every number;
- (b) it is true with a short proof whose every step you can write down.

A strategy sketch does not qualify; propose nothing rather than an unsettled candidate.

The shapes that settle best:
- a theorem proved under a restriction (small parameter, special family, low dimension, small fugacity, regular graphs, n ≤ 8), followed by a sentence saying the restriction can probably be removed. Test the first values outside the restriction, the degenerate and extreme cases (zero, one, very large or very unequal parameters, disconnected or star-shaped inputs, n = 1, 2), and weighted or multivariate versions;
- an exact constant the authors found numerically and whose analytic proof they leave open;
- a sufficient condition for positivity, entanglement or nonlocality checked only numerically;
- a structural property of an explicit state, matrix or sequence observed for a few sizes and conjectured for all;
- a closing-list question with a finite answer.

Formalization cost is not a filter.

For each candidate give:
- where it is stated, quoted verbatim with the definitions it depends on;
- the exact counterexample or the complete short proof;
- what you checked to confirm it is still open: later arXiv versions and their comments, citing works, mathdb.com searched by title words and authors, and github.com/google-deepmind/formal-conjectures;
- why this repository suits it, naming the files and results it would build on;
- two labels:
  - its tier under CLAUDE.md §3.6: `1` (a recent small conjecture or question) or `2` (a computational frontier);
  - its settlement kind: `small-case`, `family` or `proof`.

Return exactly one JSON object and nothing else (no markdown, no tab characters; escape every inner double quote):
{"conclusion": {"verdict": "propose or abstain", "candidates": [{"id": "...", "source": "paper or venue with version", "location": "...", "verbatim": "...", "reading": "precise quantified statement", "significance": "who posed it and why it matters", "prior_attempts": "what the source proves and where it stops", "repository_fit": "files and results it builds on", "expected_settlement": "Proved or Refuted", "settlement_kind": "small-case, family or proof", "tier": "1 or 2", "evidence": "the exact counterexample or the complete proof", "proof_route": "the non-trivial step", "literature": "what you searched and found"}], "scan_counts": "papers scanned per archive", "reasoning_discipline_note": "..."}, "log_ref": "__SEAT_ID__"}

Open preregistration issues (number and title, one per line):
__OPEN_PREREGISTRATIONS__
