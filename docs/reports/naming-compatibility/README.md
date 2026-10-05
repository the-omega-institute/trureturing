# Operation-compatible naming on a finite common state space

[compatible_quotient.py](../../../experiments/naming-compatibility/compatible_quotient.py) computes the least equivalence containing specified
permutation identifications and preserved by specified unary operations. This
is classical generated congruence, used to test whether naming, operations and
a target can coexist. Mathematical context and the signed Fibonacci application
are in [Naming Relations and Stability, §§9–12](../../develop/theory/NAMING_RELATIONS_AND_STABILITY.md).

Run from the repository root with Python 3.9 or newer; no third-party packages:

```sh
python3 experiments/naming-compatibility/compatible_quotient.py > /tmp/naming-result.json
cmp /tmp/naming-result.json docs/reports/naming-compatibility/result.json
python3 experiments/naming-compatibility/compatible_quotient.py --input /path/to/model.json
```

A model has a positive number of states, indexed from zero, permutations called
identifications, arbitrary total unary operations, and one string target label
per state. Empty identification or operation dictionaries are allowed.

```json
{
  "states": 3,
  "identifications": {"swap": [1, 0, 2]},
  "operations": {"update": [0, 2, 2]},
  "target": ["a", "a", "b"]
}
```

Every map acts on the same states. Operations need not be invertible, and their
inverse operations are not implicitly included. Stability means equal names
remain equal after an operation; it does not require reflection of equality.
A target is recoverable exactly when it is constant on every computed block.

The solver queues successful merge edges, then merges each operation's images
of their endpoints. At most `states - 1` successful merges occur. An ignored
edge already has a path of accepted edges; processing their images suffices.
Union-find constructs the partition. The `replay(model, result)` checker uses
graph traversal instead, checks initial identifications, all operation images,
descended operation tables and target claims, and verifies each merge reason.
Every operation reason points to an earlier accepted edge. Thus justified edges
and final stability check both sides of leastness. This is a finite recomputation
check, not a Lean proof or certificate.

`result.json` contains each input and its full result: initial blocks, compatible
blocks, merge reasons, descended operations, target-recovery flags and an
obstruction with a path of merge indices. The obstruction identifies two equal
names with different target labels. Its path is not a claim of a globally
shortest operation word.

| Fixture | States | Initial blocks | Compatible blocks | Block sizes | Target: initial → compatible |
| --- | ---: | ---: | ---: | --- | --- |
| compatible_control | 3 | 2 | 2 | 2, 1 | true → true |
| three_state_obstruction | 3 | 2 | 1 | 3 | true → false |
| fib_signed_mod_2 | 4 | 3 | 2 | 1, 3 | true → false |
| fib_signed_mod_3 | 9 | 3 | 2 | 1, 8 | true → false |
| fib_signed_mod_5 | 25 | 7 | 3 | 1, 20, 4 | true → false |
| fib_signed_mod_7 | 49 | 13 | 4 | 1, 16, 16, 16 | true → false |
| fib_signed_mod_11 | 121 | 31 | 7 | 1, 20, 20, 20, 20, 20, 20 | true → false |

Signed Fibonacci fixtures enumerate `(a,b)` in lexicographic order modulo `m`.
They identify `C(a,b)=(-b,a)`, allow `M(a,b)=(b,a+b)`, and target
`E(a,b)=a²+b² mod m`. This declared identification is a hypothesis of the model;
it is not the original nonnegative canonical Fibonacci syntax or evidence of
a physical gauge. Counts for these five moduli do not classify all moduli.
They already refute the suggestion that every nonzero state always merges.
The quadratic form `Q=a²+ab-b²` changes sign under both `C` and `M`, so `Q²`
survives. No complete orbit classification by `Q²` is claimed.

All result calculations use exact integers and string equality. The program
only handles explicitly enumerated finite carriers and total unary maps; it
does not solve infinite, partial, continuous, probabilistic or approximate
versions. Independent verification includes exhaustive small partition
comparison, result corruption checks and direct finite `C, M²` orbit comparison;
the algorithm and the complete orbit characterization have not been kernel
certified. Existing closure/descent results supply the formal background; this
delivery adds no named Lean wrappers.

License: Apache-2.0, under the repository LICENSE.
