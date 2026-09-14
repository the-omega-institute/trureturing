# Foreground actual-prime slab inquiry

`prime_slab_cpu.py` evaluates the registered adjacent and active-reflection
nodes for `(2,3,q)`, `q=23,29,31`, and exponents `0..15`. The first phase is
the 64-box `q=23`, `{0,5,10,15}³` pilot. Its cumulative tier-evaluation
allowance is 600 seconds across all resumes. The fixed window has 12,288
boxes and 307,200 raw slots before exact guards. No precision above
128/256/512 is available through this command.

The scientific question is the full actual-prime `U_dual <= U_var`
comparison in `ARITHMETIC_BOUNDARY_QUANTIZATION.md` §25.16 with its
surrounding definitions and corrections. That question quantifies over
all `k>=3`, distinct actual primes, nonnegative exponents and admissible
closed real slabs. This finite experiment cannot establish the universal
comparison. A positive enclosure is a proposed witness requiring
independent reconstruction and certification, followed by the appropriate
Lean proof. A completed negative window supplies experiment data only.

## Run

Use explicit portable input and output paths, including when invoking make
from another directory:

```sh
make -C /path/to/repository/tools prime-slab-cpu \
  CPU_SLAB_INPUT='/path/to/input.json' \
  CPU_SLAB_SHA='<sha256 of those exact input bytes>' \
  CPU_SLAB_OUTPUT='/path/to/experiment results' \
  CPU_SLAB_PHASE=pilot CPU_SLAB_BOXES=64 \
  CPU_SLAB_DEADLINE='2026-09-15T01:34:55Z'
make -C /path/to/repository/tools prime-slab-cpu-test
```

Supply a future finite UTC deadline for the actual authorized flight. The
make target uses the existing Python 3.12 / python-flint 0.8.0 command
prefix. Neither torch nor a GPU backend is imported by this driver.
The entry point also accepts `--help`. After measuring the completed
pilot, use `CPU_SLAB_PHASE=window` and an explicitly chosen positive batch
size. Each invocation starts at the first unfinished box in the declared
order, validating and skipping previously completed exact keys. It stops
at the batch boundary, fixed window, candidate, resource limit or clock.
The process requires 4 GiB of free output-filesystem space at startup and
stops new work below 2 GiB. It creates no subprocesses or background job.

The input JSON carries:

| Field | Meaning and validation |
| --- | --- |
| `experiment` | Exact `prime_slabs.cpu.EXPERIMENT` value; includes meaning, fixed window, ladder and persistent pilot cap. |
| `question` | Full C, prospective R/R_nodes, source clauses and domain, supplied as useful experiment input. |
| `source_bindings` | Repository-relative path/SHA-256 pairs; both the source theory and `certify.py` are required and hashed before evaluation. |
| `retained_supports` | Complete bound prior prime-support sets, with `primes`, `support_complete: true` and source provenance. Disjoint sets are excluded before legacy node decoding. A matching set returns its named input dependency. |
| `corpus_bindings` | Scope and digests of the already-accounted input corpus and formal support decision. These are retained provenance, not a claim about all history. |
| `provenance` | Optional repository/Goal/plan bindings supplied by the experiment owner. |

The command does not follow references within the question, corpus or
producer records. Source hashes are checked against explicit repository
files; deciding whether changed scientific definitions mean the same
thing remains a research obligation. Matching records with an invalid
definition, input, witness, guard, status, producer or expenditure fail
before evaluating that unit.

## Exact data and resume

All corners, comparisons and clipping decisions use unbounded integers
and reduced positive `Fraction` values. The canonical key hashes the
definition meaning, sorted paired prime/exponent coordinates (including
zero exponents), and rational `exp(M0), exp(M1)`. Here
`M=T+sum(log p)`. Sorting happens before masks, witnesses and branch arrays
are constructed, so all indexed data use the same coordinate order.
Program and run hashes are provenance and never make a new mathematical
key. The fixed-through-19 decoder is not used.

`results.sqlite3` is the scoped data and resume file:

| Table | Contents |
| --- | --- |
| `metadata` | Exact experiment and scientific-input bindings. |
| `producers` | Content-hashed input/program/runtime/flight documents. Executed program bytes are retained once per hash in `producer-sources/`. |
| `boxes` | Sorted integer corners, all 25 raw guard dispositions, corresponding keys and completion. |
| `nodes` | Canonical inputs, exact endpoint exponentials, original slab budgets, two distinct admitted configurations, exact guards, origin, sign, status, tiers and interruptions. |
| `costs` | Cumulative measured tier-evaluation nanoseconds, separately for pilot and remaining window. Opening the store reconciles these totals with retained tier/interruption events. |

Each tier contains precision, producer, phase, elapsed nanoseconds and
exact rational outward bounds for `G`, `D`, `Psi`, `V0`, `rho`, `L`, `H`,
`ell`, `M0`, `M1` and `min(C_i)*G`. It also retains distance ratios/ties,
all six greedy mixtures and weights, and exact clipping branches. The
scaling is a diagnostic normalization; the decision uses the full `G`.

Statuses are `pending`, `completed`, `candidate`, `residual` or `invalid`.
The sign is separate. Every bound completed sign skips evaluation,
including nonnegative enclosures that do not establish strict positivity.
A strict positive routes directly to independent certification. An
unresolved completed 512-bit tier remains a residual. Interruptions retain
their measured cost and resume only the unfinished tier. An unclean kill
leaving an in-flight tier has unknown expenditure and requires correction;
the driver never resets it to zero. SQLite commits the result and its cost
in one transaction. Exclusive SQLite ownership prevents concurrent writes.

Result JSON files contain useful run measurements and coverage, written
atomically after closing the database. Exit 0 means a bounded invocation
finished normally, including a documented stop with unfinished work;
inspect `result.reason` and per-key statuses. Exit 2 reports a concrete
input/evaluator failure. SIGINT/SIGTERM request a cooperative stop; the
remaining evaluation/flight budget arms a foreground alarm around the
current tier. Signal delivery during native arithmetic is subject to
Python's delivery granularity, and any measured overshoot remains charged.

`measurement.evaluation_ns` includes the one-tier Arb expression and
outward-enclosure encoding, excluding SQLite, decoding and run setup.
Version 2 run measurements cover setup through the final streaming database
hash; only small JSON/stdout publication follows the sample. For an entire
command's terminal resource reading, wrap the make invocation with the
platform's foreground resource timer. Version 1 measurements ended before
database hashing and must be described as search-phase readings; their
whole-process memory peak was not measured.

The tests cover exact identities/permutations/zero labels, strict guards,
noninteger reflection budgets/ties, the pure three-row Arb interface on
synthetic analytic equalities, completed-sign skipping, bounded execution,
remaining-tier resume, interruptions, immutable cumulative cost, malformed
bindings, command portability and bounded-memory hashing. They do not
constitute independent mathematical adjudication of a discovered witness.

`make -C tools prime-slab-cpu-mutation-test` weakens the strict5040 guard
only inside a bounded child process. It preregisters the expected named
failure, checks a nonzero test exit with successful compilation, then runs
the unchanged test successfully. Both child processes are joined.
