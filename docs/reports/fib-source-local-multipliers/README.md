# Source-local one-prime and two-prime comparisons

This experiment reuses the integer factorizations in Mantovanelli's archived
`data/certified_regular_returns_X1000.csv`. It asks a different finite question:
can simultaneous prime insertions improve a source whose individual prime
insertions and deletions all decrease the Robin quotient? The CA states and
event tables are not re-enumerated, and the archive's event/root certification
is not rerun. No new CA examples, literature originality or Lean theorem is
claimed.

The [primary-source note](../../../Library/Analytic/mantovanelli2026primeworkload.md)
pins Zenodo record 22014299, version 1.0.0. Its computational files are MIT
licensed. The program loads the original `reference_event_sweep.py` from the
caller-supplied archive only after checking SHA-256
`e77735e9fd3dac38ca36933c3ac36776c70b0a1fe52d278256f4d7e507f3f58a`.
It calls that source's `log_interval`, `dyadic_enclosure` and `Interval`
interfaces; the logarithm series and its tail proof are reused rather than
rewritten. Neither the supplier code nor the original catalog is redistributed
here. The result records the exact catalog and query hashes.

## Quantity, candidate pool and coverage

Put $G(n)=[\sigma(n)/n]/\log\log n$, and let $m$ be obtained from $N$ by the
queried prime-exponent changes. The exact rational abundancy ratio is
$R=[\sigma(m)/m]/[\sigma(N)/N]$. Each reported interval encloses

$$
T_N(m)=R\log\log N-\log\log m.
$$

Every deletion is checked to leave $m>e$, so the denominator of $G(m)$
is positive. The sign of $T_N(m)$ is therefore the sign of $G(m)-G(N)$.
Logarithms use rational enclosures, with outward dyadic rounding before the
outer logarithm. The retained result uses 80 enclosure bits and has no
undecided sign.

The candidate pool contains every prime factor of $N$ and its first two
absent primes. Deletions use every present prime. This also covers all
one-prime insertions and all two-prime insertions, including repeated primes,
by the following elementary prime replacement correspondence. For an absent
prime $p$, its abundancy factor $1+1/p$ decreases with $p$, while the budget
denominator increases with $\log p$. Replacing an absent inserted prime by
a smaller absent prime can therefore only increase $G$ after the move. A
mixed present/absent pair uses the first absent prime; two distinct absent
primes use the first two; a repeated absent prime uses the first, since
$1+1/p+1/p^2$ also decreases with $p$. Present prime choices remain in the
pool. This is the paper justification for the finite reduction, not a
machine proof of that universal correspondence.

## Retained finite results

The source catalog's return indices 4 and 6 have integer values

$$
\begin{aligned}
N_A&=160626866400
=2^5 3^3 5^2 7\,11\,13\,17\,19\,23,\\
N_B&=2021649740510400
=2^6 3^3 5^2 7^2 11\,13\,17\,19\,23\,29\,31.
\end{aligned}
$$

Both sources are proper for every prime deletion. The following coarse
rational bounds follow from the retained intervals; they concern $T$,
not the logarithm of the quotient ratio.

| Source | Compared moves | Certified bound for each requested move |
| --- | --- | --- |
| $N_A$ | One-prime insertions | $T<-7/10000$ |
| $N_A$ | One-prime deletions | $T<-5/1000$ |
| $N_A$ | Newly evaluated two-prime insertions, including repetition | $T<-7/1000$ |
| $N_B$ | One-prime insertions | $T<-1/1000$ |
| $N_B$ | One-prime deletions | $T<-5/1000$ |

The first query has 11 insertion checks, 9 deletion checks and 65 pair
checks. Its remaining pair $(2,29)$ is directly reused from the archive's
`packet_checks` entry with source 4 and target 5, which has two events and
reports a negative common certified log-ratio intersection near
$-0.002173883872171688350603874436$. The factorization changes by exactly
$2\cdot29$. That published negative comparison completes the 66-pair pool
and is listed in the query's `reused_pairs`, not recalculated by the consumer.
The second query has 13 insertion checks and 11 deletion checks:
109 additional exact comparisons in total. The complete dyadic
intervals and moves are in [results.json](results.json); the finite requests
are in [queries.json](queries.json).

The same existing archive already reports $G(111N_B)>G(N_B)$ in
`verification/packet_identity_checks.json`, the `packet_checks` entry with
`source_return_index: 6` and `target_return_index: 7`. That entry has two
events and reports a common certified log-ratio intersection near
$0.0003630154934124059372607234863$. Its decimal fields are descriptive;
the published computation uses exact rational intervals. This positive
joint comparison is cited directly and is not recalculated by this consumer.
The target catalog factorization differs by precisely $3\cdot37$, with
joint abundancy multiplier $2299/2220$.

The new intervals and paper prime-pool reduction identify this same source
as proper and stable under every single-prime insertion and deletion, so
the published joint ascent occurs although each constituent insertion
separately decreases $G$.
They also rule out every two-prime improvement at the proper local source
$N_A$. The latter refutes the stronger proposal that *every* proper
prime-local stable source admits an improving two-prime multiplier. It does
not refute that proposal restricted to hypothetical sources at or above
Robin's critical level; no such source is asserted here.

The source's `lem:neutral-point` already shows why a winning singleton
packet starts at an insertion-unstable source. Its `thm:cone-envelope`
already transports any improving multiple, such as $111N_B$, to an
improving later regular return. Those published results are directly reused;
there is no need to specify that return in advance or exclude every other
event between the source and that return.

These are additional finite source-specific comparisons joined to directly
reused published packet comparisons, with a paper justification
of prime-pool completeness. They provide no unbounded family, no universal
block-size bound, no coverage of potentially persistent dangerous minima,
and no full Robin/RH proof. No Lean verification is included.

## Reproduce

Download the computational archive identified in the primary-source note.
Set `CA_ARCHIVE` to its local path, then run from the repository root:

```sh
python3 docs/reports/fib-source-local-multipliers/certify_multipliers.py \
  --archive "$CA_ARCHIVE" \
  --queries docs/reports/fib-source-local-multipliers/queries.json \
  --output docs/reports/fib-source-local-multipliers/results.json
```

The program is an exact consumer for these additional queries, not the
archive's root verifier. Additional catalog queries can use the same input
format; they do not inherit the retained sign conclusions. The invoked
supplier functions and consumer were exercised on Python 3.9.6; the archive
declares Python 3.11 or newer for its full reference workflow, which is not
run by this experiment.
