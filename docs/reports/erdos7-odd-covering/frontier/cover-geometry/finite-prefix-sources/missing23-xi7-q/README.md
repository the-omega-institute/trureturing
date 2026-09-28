# The fixed Q source and its complete future domain

This package certifies all `280^5 = 1,721,036,800,000` future physical label choices at the missing23 A1 node `(2,4,1,8,1,2,1,0,13)` with `xi7 = Q = (2,4,2,14)`. The primes are `(3,5,7,11,13,17,19,29)`, the thresholds are `(2,4,4,8,8,16)`, and the final query is 16. The reserve is `135/4`. Every bound concerns the same actual source, padding and schedule. Later full-field majorants are upper bounds, not assertions that independently maximizing layouts coexist.

The actual Q zero7 field uses `(11,11,9,6,3)/14`, indexed by overlap with the four selected classes. Its entire ordinary envelope is retained. The positive7 component is unchanged. The current7 upper bound is `10.2215449381`, and the common final hinge upper bound is `32.466043606804874...`.

`bounds.json` contains 35 released-head comparisons, one for every stage in `(11,13,17,19,29)` and every phase in `(1,4,7,8,11,13,14)`. Each keeps the actual modulo15 head and releases the other current heads. Nine phases additionally retain all 40 physical current labels:

| Current stage | Refined modulo15 phases |
| --- | --- |
| 11 | 4, 7, 8, 13 |
| 13 | 4, 7, 8, 13, 14 |

The stage13 tables use the flat/full11 upper field. The later uniform upper bounds are `3.8046758456`, `4.2792453624`, and `2.0467337265`. The arithmetic consumer checks all 78,400 pairs of the first two future labels; the last three labels are covered by their uniform bounds. Only the pair `X/X`, where `X=(1,4,7,4)`, needs the following analytic improvement.

## A pointwise credit valid before geometric maximization

The actual zero11 numerator is `(28,28,28,28,25)/33`. It differs from its flat value `28/33` only on the four-way intersection selected by `X`. In the 44-cell source this is exactly

`C = {34,79,124}`.

Each of these cells has integrated source weight one. The Q overlap on each cell is one, so the complete charged7 measure there has total mass

`11/14 + 3/14 = 1`.

For current13 with label `X`, all four fixed heads contribute at each such cell. For every shared layout, every nonnegative source depth, and every preceding multiplier `m >= 1`, the padded expression has a base `m`, fixed offset `48/13`, and nonnegative free-category terms. The positive-part kernel above threshold four is therefore at least

`[m + 48/13 - 4]_+ >= 9/13`.

The zero11 reduction is `3/33=1/11`; the current13 divisor is eight. Thus, for every layout, the flat current13 functional exceeds the actual one by at least

`3 × (1/11) × (9/13) / 8 = 27/1144`.

The positive11 contribution is identical on both sides. Integrating the complete source and multiplier laws preserves the inequality, including their infinite tails. If `A(layout) <= B(layout) - 27/1144` for every layout, then `max A <= max B - 27/1144`. The computed flat envelope is an upper bound on `max B`, so

`L13_actual(X,X) <= L13_flat(X) - 27/1144`.

The inequality is established on the complete padded kernels before maxima, tail estimates or numerical rounding. It is not obtained by subtracting unrelated maxima or two tail upper bounds.

At phase four, `X` is the unique maximum in both tables. Its gap above the runner-up is `73284861/200000000` at stage11 and `2673800669/10000000000` at stage13. Across the full 78,400 pairs, exactly `X/X` fails without the credit and every pair succeeds with it. The final common result is

`15 + H16 / (135/4 - sum of six loss upper bounds) <= 28.9678985746 < 29`.

Rounding each loss upward to a millionth leaves a minimum live lower bound of `2.324331` and minimum strict slack `0.074590`.

## Transport to a second source

Fix modulo5 and permute the modulo27 branches with modulo9 residues two and five, preserving the final ternary digit. This preserves the active carrier, each named source partition `(3,9,27,5,15,45)`, and all four source weight fields. It transports `Q` to `Q'=(2,4,5,14)` and simultaneously transports every future label by swapping its modulo9 entry two and five. All 280 labels remain in the same domain; the padded kernels and full-family geometric maxima are transported along with them. Consequently the full `280^5` certificate also holds for Q'.

This is a transport between two complete sources. It is not a self-symmetry of Q and does not justify a 32-plus-8 shortcut in a Q table. Every refined table above contains 40 actual labels.

## Reproduction and scope

```sh
python3 -I -S -B verify.py
python3 -I -S -B -O verify.py
python3 -I -S -B geometry_replay.py --kind current7 --cache /explicit/cache
python3 -I -S -B geometry_replay.py --kind query --cache /explicit/cache
python3 -I -S -B geometry_replay.py --kind released --prime 29 --eta 4 --cache /explicit/cache
python3 -I -S -B geometry_replay.py --kind four --prime 13 --eta 4 --cache /explicit/cache
```

Both tools accept `--base` to locate the pinned `missing23-eta14` package. Default execution writes only stdout; `--output` retains the result explicitly. Geometry replay is cache-only by default. Repeat `--cache` for explicitly named directories. `--fresh` generates missing full-input SHA256 keys, while `--regenerate` recomputes even existing keys; `--binary` selects the enumerator. The base package retains the original source, license, source model and integer enumerator. No filesystem tree or Desktop search is used.

The consumer uses checks that remain active under `-O`. Its finite source transport and analytic-credit parameter checks accompany the ordinary proof above; reading numerical inputs does not itself regenerate geometric maxima. The separate producer reconstructs all 46 declared targets: current7, one full query envelope, 35 released comparisons and nine full40 tables. The geometry producer inherits the base source's explicit refusal of `-O`; only the arithmetic consumer is required to work in both modes.

These are scoped mathematical and computational bounds, not new Lean verification, a claim for every A1 node, or a resolution of Erdős #7.
