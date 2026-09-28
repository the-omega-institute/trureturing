# Ordinary continuation for 255 actual first labels

This package certifies 255 of the 280 physical choices of the first label
`xi7` at the missing23 node `(2,4,1,8,1,2,1,0,13)`. For every certified
choice, all `280^5 = 1,721,036,800,000` choices of the later physical labels
at 11, 13, 17, 19 and 29 are covered. The support is exactly
`(3,5,7,11,13,17,19,29)`, the threshold schedule is `(2,4,4,8,8,16)`, the
final query is 16, and the starting reserve is `135/4`.

The physical domain at each stage is
`{1,2} × {1,2,3,4} × {2,4,5,7,8} × {1,4,7,8,11,13,14}`.
No modulo23 coordinate is present. Every comparison is an upper bound on
the same actual source, complete padding and original schedule. It does
not identify independently maximizing layouts with a jointly attainable
family.

## The complete majorant at seven

For a fixed actual first label, its zero7 multiplier at a source cell is
`K7(s)/14`, where `s` is the overlap count and
`K7=(11,11,9,6,3)`. Its positive7 measure has atoms `9/7^m` for all `m>=2`,
total mass `3/14` and first moment `13/28`.

Replacing only the zero atom by `11/14` therefore dominates every actual
first-label field pointwise. Together with the unchanged positive7 law it
is precisely `full(7,2)`, of total mass one and first moment `5/4`.
Nonnegative source weights, positive-part kernels and multiplier factors
preserve this upper comparison. Replacing all later actual fields by their
complete `full(p,t)` majorants likewise bounds every later physical label.

Let `G(t,nu,E)` denote the pinned base package's ordinary envelope integral
of the hinge at threshold `t`, using complete multiplier law `nu` and
source envelope `E`. Start with `nu=full(7,2)` and the original ordinary
44-cell source envelope. At each stage `(p,t)` in
`(11,4),(13,4),(17,8),(19,8),(29,16)`, charge the upward-rounded loss

`G(t,nu,E)/(p-1-t)`

and then replace `nu` by `nu * full(p,t)`. The final query uses
`H16=G(16,nu,E)` after the full29 factor. There is no loss divisor on this
query. Thus all five later losses and the query include every previous
positive and zero component exactly as required. The finite multiplier
tables are accompanied by their exact total masses and first moments;
the infinite remainder is retained by the pinned hinge formula.

The common later loss upper bounds are

`5.6613309293, 6.3779676675, 3.9940469465, 4.5013887284, 2.1244751754`.

The common query hinge is `33.15651876570184...`. Consequently a current7
loss below `8.722467783921298...` suffices. Exactly 240 of the 280 pinned
current7 inputs satisfy the exact rational condition. Decimal displays
are informational; the checker uses the exact fractions.

## Fifteen additional labels with their actual zero7 field

For 37 of the remaining 40 labels, the package retains an ordinary source
envelope weighted by that label's actual numerator `K7(s)` at each cell.
For these comparisons, the continuation is the sum of two components:

`G(t,POS7*M,Eordinary) + G(t,M,Eactual-zero7)/14`,

where `M` starts as the unit multiplier and successively acquires the
complete factors at 11, 13, 17, 19 and 29. The positive7 component is
unchanged and appears once. The actual zero7 numerator appears once,
with the factor `1/14`. At each current stage the displayed sum is divided
by `p-1-t`; at the final query it is not divided.

For any route, put `D=135/4-current7-sum(later losses)`. The sufficient
conditions checked are `D>0` and `14*D-H16>0`, giving

`15+H16/D < 29`.

Exactly 15 of the 37 comparisons satisfy these conditions. They are
disjoint from the first 240, so this package certifies 255 actual first
labels, representing `438,864,384,000,000` complete six-label tuples.
The other 25 first labels are explicitly listed as unclaimed. Three have
no actual-zero7 envelope in this package; 22 do not pass this particular
ordinary bound. Neither omission nor failure is a claim of infeasibility.
This package has no dependency on separate first-label certificates.
The largest displayed certified query upper bound is `28.9315451319`, at
`xi7=(2,4,8,11)`. This is a maximum of rounded query upper bounds; it is not
used to select or assert an exact minimum live mass.

## Reproduction

The arithmetic consumer and geometry producer pin both numerical inputs
and the required base code. The base package verifies its own source and
input manifest. From an installed sibling directory:

```sh
python3 -I -S -B verify.py
python3 -I -S -B -O verify.py
python3 -I -S -B geometry_replay.py --kind current280 --cache /explicit/cache
python3 -I -S -B geometry_replay.py --kind zero37 --cache /explicit/cache
```

Both tools accept `--base /explicit/missing23-eta14`. Replay accepts repeated
explicit `--cache` directories and defaults to cache-only operation.
`--projection 1,1,7,1` restricts either replay to one declared label.
`--fresh` permits generating missing full-input SHA256 keys;
`--regenerate` recomputes even existing keys; `--binary` selects the
integer enumerator. The base package contains the source, license,
source model and integer enumerator code. The producer reconstructs all
280 current7 values or all 37 ordinary envelopes without a future-label
geometry grid. It inherits the base source's refusal of `-O`; the
arithmetic consumer supports normal and optimized execution.

Default execution writes only stdout; `--output` explicitly retains a
result. Reading the arithmetic inputs
does not itself reconstruct the geometric maxima. These are scoped
ordinary mathematical and computational bounds, not new Lean
verification, a result for every source node, or a resolution of
Erdős #7.
