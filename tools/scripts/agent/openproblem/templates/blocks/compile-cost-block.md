
## Compile-cost readings in the PR body (CLAUDE.md §10.2; mandatory)
Review seats reject a body that gives only plain timings. At the delivered head, for **every** delivered `.lean` module, run
`/usr/bin/time -l lake env lean -Dprofiler=true -Dtrace.profiler=true -Dtrace.profiler.threshold=1000 <module path>`
and put these in the Verification section as current result data:
- the command, head, exit code, wall seconds and peak RSS bytes;
- a ranked table of the ten most expensive declarations or tactic blocks, with seconds, taken from that profiler output.

A before/after table appears only for a module whose source this delivery changed to reduce its compile cost (CLAUDE.md §10.2, second hard projection). It has two rows: the committed revision before that change and the delivered head, each with revision and exit code. Readings from the probe, Stage A or any other undelivered head are process history (CLAUDE.md §2.10), so they never appear in the body.

Also give one import-only baseline: a scratch file under `.lake/scratch/` holding exactly the module's `import` lines, timed the same way. State what share of the peak RSS it accounts for. Report measurements only, with no speculation about causes.

**Two runs, both reported.**
- The threshold-1000 run above is the binding cost reading: wall seconds, peak RSS, and the declarations above 1 s, each row with revision and exit code.
- When fewer than ten declarations exceed 1 s, add a second run with `-Dtrace.profiler.threshold=10` and report the ten slowest distinct declarations from it, labelled as the threshold-10 run, with its revision and exit code.
- A before/after comparison, where one is required, names both revisions and both exit codes.
