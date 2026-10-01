# Canonical Fibonacci summaries with a remaining future budget

This exact finite computation accompanies §108 of
[Fibonacci Atomic Relation Generation](../../develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md).
It derives the actual signature counts **61, 48459, 535501, 604801** for
remaining budgets 0, 1, 2, 3 at modulus 5040, using only local residue models
and their supports on a common phase orbit.

## Source domain and budget

The source domain contains every actual pair `(epsilon, prefix)` with
`epsilon` equal to 0 or 1 and an arbitrary finite past window word, including
the absorbing invalid sink. Window bits are low to high and the alphabet is
`000, 100, 010, 101, 001`. Adjacent 1 bits are illegal, including across the
unit/window seam. The initial End flag is `epsilon`; after a legal window it
is true exactly when that window is nonzero. Successful End requires a positive
integer and returns `5040/gcd(N,5040)`; all failures share one error label.

A depth `t` signature records the output after **every** literal suffix of
length at most `t`: empty, illegal, noncanonical-ending, and successful words
are all included. End costs no window. Budget starts at the current prefix,
after any amount of past input. The decoder may know `t`, but has no free past
length, phase, tag, residue, or source-prefix input. A static encoder may
inspect that prefix or a sufficient representation to acquire its snapshot.

The ordinary proof in §108.2 uses the union of both initializations and
§105.1's actual integer intervals. For each phase `j0`, taking past length
`j0+80k` sufficiently large gives every global residue for each tag at that
phase, including positive representatives. This is why the common-phase
residue model describes the actual source domain. Neither a fixed small past
length nor a fixed initialization is substituted in that argument. If a total
budget `T` starts at initialization, past length is bounded by `T-t`, and this
saturation argument does not establish the same counts for that contract.

## Files and reproduction

- `certificate.py`: portable Python 3.8+ standard-library program. It reads no
  input files and uses no network, Git, repository environment, or external
  count fixtures. Checks use an explicit exception function and remain active
  under `-O`; a failed check exits nonzero before JSON is written.
- `results.json`: deterministic mathematical data: the common orbit, periods,
  counts, full local support histograms and final intersection histograms,
  depth-zero labels, and literal counterexample checks.
- `README.md`: contract, method, reproduction, sources, and evidence boundary.

From the repository root:

```sh
python3 docs/reports/fib-canonical-budget/certificate.py --output /tmp/fib-canonical-budget.json
cmp docs/reports/fib-canonical-budget/results.json /tmp/fib-canonical-budget.json
```

Without `--output` the same JSON is written to stdout. Serialization uses
sorted keys, two-space indentation, UTF-8 bytes and a final newline. The script
can also be copied alone and run from another working directory.

The delivered program was run normally and with `-O` as a standalone copy
from a different working directory whose path contained spaces, in a minimal
environment without loading shell startup files. Both executions exited 0
and matched `results.json` byte for byte. A deliberately false check under
`-O` exited 1 with the expected exception. These executions verify those
conditions; other Python versions and operating systems were not tested.

## Exact finite method

The program derives the orbit of `(2,3)` modulo 5040 under
`T(u,v)=(u+2v,2u+3v)` until the first repeat, checking that the repeat is the
initial row. Its exact period is 80; projected local periods at 16, 9, 5, 7
are 8, 8, 20, 16. Projection is checked against each independently generated
local orbit. Only weight rows are enumerated globally: there is no global
5040 residue-by-phase state enumeration, transition graph, or BFS.

For each local modulus, the one-bit modular recurrence implements each
window. A depth-zero tree is its End output. A deeper tree is the current
output together with the five child trees, in the stated alphabet order.
Tuple interning gives exact tree equality, including every shorter suffix;
IDs are scoped to modulus and depth. These are complete tuple keys, not hash
digests, so hash collisions cannot identify different trees.

For each fixed tag and depth, every local residue and each of the 80 common
phases contributes its signature ID to a support map. Repeated occurrences
of one signature union their phase bits. Hexadecimal mask bit `j` means the
actual common phase `j`; a histogram entry counts **distinct signatures**
having that support, never residue or phase witnesses. Local periods are not
independently chosen phase clocks.

Starting with the full support mask of multiplicity one, the program
intersects each accumulated mask with each next-factor support mask, adds
the product of multiplicities to the resulting mask, and discards empty
intersections. The factor order is 16, 9, 5, 7. The final multiplicity sum
counts compatible ordered tuples once, even when they have several phase
witnesses. The generic bijection to actual global signatures and the counting
induction are the ordinary arguments in §§108.3–108.5.

| Depth | A=(0,false) | B=(0,true) | C=(1,true) | Actual total |
| --- | --- | --- | --- | --- |
| 0 | 1 | 60 | 60 | 61 |
| 1 | 11790 | 31096 | 5572 | 48459 |
| 2 | 189000 | 189000 | 157500 | 535501 |
| 3 | 201600 | 201600 | 201600 | 604801 |

At depth zero the program reconstructs the actual label sets from local
depth-zero trees: A and sink merge as error; B and C have the identical set
of all 60 divisors of 5040. It takes their union. At positive depth, the
ordinary empty-word/`100`/`010` separation proof permits adding the three
fixed-tag counts and one sink. Depth 1, tag A has local signature counts
17, 20, 9, 9: their independent product 27540 exceeds the compatible count
11790. The maximum number of nonempty masks at a DP layer is **216** over
these four depths, three tags and the stated factor order; this is a finite
measurement, not a general complexity bound. Full support and intersection
histograms are retained (their serialized block is below 50 KB).

An independent literal decoder builds integer Fibonacci numbers and sums
the selected digit positions without calling the modular transition code.
It verifies the two §107.7 prefixes, their integers 2179485 and 2182005,
their common next row `(3524578,5702887)`, and equality on all 31 suffixes
through depth 2. `S2_shared_outputs` records the common output for each word;
the empty key denotes the empty word and `|` separates windows. It also
checks all six suffixes through depth 1 after an initial `000`, and the
separating continuation `000|000|010` with outputs 6 and 3. The zero-budget
counterexample uses actual prefixes `000` and `001|100`, both initialized
with 0: both initially report error, while `010` gives 5040 and error.

For two witness prefixes, the epsilon-1 empty prefix, and an actual sink,
all 156 suffixes through depth 3 are also decoded literally and compared
with each local output tree: 2496 local coordinate comparisons. Successful
local labels must equal `gcd(global_label, local_modulus)` and multiply to
the global label; errors must synchronize. Expected periods, counts and DP
width are regression checks after derivation, never inputs to that derivation.

## Mathematical boundary and sources

This is a standalone finite certificate adapted from the completed local
signature counting calculation supplied for §108. Its enumeration is
independent of the earlier global graph and partition data; this description
does not claim a second author, an independent review vote, or model diversity.
The mathematical contribution is repo-derived from the current volume's
§§104–105 and §107, with ordinary CRT and response-equivalence arguments.
The code and prose use the repository's [Apache-2.0 license](../../../LICENSE);
no third-party source code is bundled.

The program checks the finite orbit, output-tree and intersection arithmetic.
Ordinary proofs supply actual full residue fibers over arbitrarily long
past inputs, the support compatibility bijection, histogram induction, tag
separation, and static-summary minimality. The smaller layers support
`Q_t -> Q_(t-1)` updates; they do not provide a fixed-layer autonomous reader
for acquiring arbitrary past input. Externally known budget permits label
reuse between layers, so summing layer sizes is not a minimal-memory claim.
An internally stored budget requires a separate contract; a tagged disjoint
union is only a sufficient implementation within the budget.

All budgets at least 3 have the same count only by §107.8, conditional on
§107.5's separate [local stability certificate](../fib-canonical-horizon/README.md).
This program does not recheck that certificate or infer stability from its
four counts. The universal coefficient depth 13 is a separate task. There is
no runtime, query-complexity, general-modulus horizon, originality, RH, Lean,
ingestion, coverage, or frozen-truth claim.
