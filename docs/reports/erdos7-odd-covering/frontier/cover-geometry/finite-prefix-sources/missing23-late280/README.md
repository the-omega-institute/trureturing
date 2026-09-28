# All allowed later phases at the fixed missing23 node

This extends the sibling `missing23-eta14` certificate. It fixes exactly the
same node `(2,4,1,8,1,2,1,0,13)`, `xi7=(1,4,7,14)`, source thresholds
`(2,4,4,8,8,16)` and query16. The projections at 11 and13 still range over
40 eta14 labels each. At 17,19,29 each projection now ranges independently
over all280 source labels, with last coordinate in `(1,4,7,8,11,13,14)`.
It does not extend the first two eta values, the node, xi7, or the entire
missing23 support.

The new domain has `1600*280^3=35123200000` tuples. All1600 prefix-label
pairs satisfy the common query16 criterion uniformly over their later
choices. The worst rational query upper rounded upward is `28.9603851962`,
at `(xi11,xi13)=(A,C)` or `(B,C)`, where
`A=(2,4,2,14)`, `B=(2,4,5,14)`, `C=(2,4,8,14)`.
Ceiling each of six losses and H16 to one millionth leaves
`D>=2.318861` and `14D-H16>=0.091827>0`.

## Verification layers

`verify.py` pins the new bounds file and the exact prior consumer. The
prior consumer then checks its own literal manifest and inputs. The
new consumer recomputes all1600 route inequalities with exact fractions
and active exception checks. It does not run a geometry producer.
Default output is a JSON summary; `--output` explicitly writes the full
coverage result. Both normal Python and `-O` keep its checks active.

With this directory installed beside `missing23-eta14`:

```sh
python3 -I -S -B verify.py
python3 -I -S -B -O verify.py --output /tmp/e7_late280_coverage.json
```

For a temporary layout provide `--base PATH_TO_PRIOR_PACKAGE`.

`geometry_replay.py` pins and imports the prior producer. It inherits the
pinned source model, C++ algorithm, numerical range checks, exact tails
and source MIT attribution from that package. It does not copy or mutate
any prior inputs. Run this producer with normal Python, because the
attributed source helpers reject `-O`.

Default geometry replay is cache-only. `--cache DIR` can be repeated;
lookup uses each complete geometry input's SHA256, without traversing
unrelated directories. `--fresh` explicitly permits generating missing
keys; `--regenerate` explicitly reruns even cached keys. A C++17 compiler
is needed for generation; `--binary FILE` supplies a trusted existing
binary. New cache files live in this extension's `geometry-cache`.
No raw maxima are duplicated in this extension's default arithmetic
inputs. This is a separate reconstruction surface, not a claim that
reading the pinned numerical bounds reruns their enumeration.

Rebuild the released tables by selecting each `PAIR` from
`AB CC CA AA FA`, each `P` from `17 19 29`, and each `E` from
`1 4 7 8 11 13 14`:

```sh
python3 -I -S -B geometry_replay.py --task released --pair PAIR --stage P --eta E --fresh
```

Rebuild the full13 current17 reference at all seven eta values:

```sh
python3 -I -S -B geometry_replay.py --task full13-released --eta E --fresh
```

Rebuild its two full four-head refinements and the two actual-C current13
values:

```sh
python3 -I -S -B geometry_replay.py --task full13-four --eta 8 --fresh
python3 -I -S -B geometry_replay.py --task full13-four --eta 11 --fresh
python3 -I -S -B geometry_replay.py --task current13-C --projection 2,4,2,14 --fresh
python3 -I -S -B geometry_replay.py --task current13-C --projection 2,3,2,14 --fresh
```

There are116 table-producing commands:105 released values, seven full13
reference values, two all40 refinements and two current13 values. All have
been checked against the retained inputs using existing full-input caches.
That cached check establishes reconstruction correspondence; it is not an
independent second enumeration of the maxima.

These are ordinary source-comparison deductions and exact computations,
not new Lean verification. The prior source attribution and full MIT
notice remain in `../missing23-eta14/LICENSE-MIT.txt`. No claim is made
about eta11/eta13 outside14, other anchor nodes, other xi7, continuous
interpolation, or unrestricted Erdos#7.
