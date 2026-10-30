# Finite True-Jump Endpoint Classification

## Abstract

The actual finite true-jump endpoint family determines exactly the truncated ancestral colours.

**Definition 1.1 (The infinite ordered address tree).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints.Address`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints.Address` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Addresses are all finite Boolean lists, using the existing literal address convention: false is L and true is R. The empty list is the root; appending a letter forms a child. There is no finite domain, killing, or restriction on subsequent addresses.

**Definition 1.2 (The incoming-increment table).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints.childIncrement`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints.childIncrement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Increment has values zero, plus and minus, representing integers 0, 1 and -1. From zero the ordered children have increments plus and minus; from plus they have zero and plus; from minus they have minus and zero. This is exactly Continuation V, Definition 120.3, equation (120.12).

**Definition 1.3 (Literal colour recursion).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints.code`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints.code` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Starting at colour zero and increment zero, fold update along the address in its given order. Each update first selects the child's increment from the table, then adds that integer modulo m to the current colour. The projections q and delta retain the colour and the incoming increment. The source is fixed independently of observations and jump budgets.

**Definition 1.4 (Ancestors and the root boundary).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints.ancestor`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints.ancestor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The kth ancestor is the prefix of length depth minus k, using truncated natural subtraction. Parent removes one final letter. Totalization beyond the root serves only intermediate formulas; no extra ancestor enters a signature.

**Definition 1.5 (The exact observation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints.observation`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints.observation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The observation is the pair of cycle colour and natural depth. Thus every actual seam changes observed depth, even when it preserves colour.

**Definition 1.6 (The finite signature).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints.signature`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints.signature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The signature consists of depth and the list of ancestor colours with indices zero through min(h,depth), inclusive. At budget zero it retains the current colour and depth. At the root its list contains just the root colour, for every budget.

**Definition 1.7 (The actual neighbor kernel).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints.J`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints.J` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At the root, J samples its two literal children uniformly. At every nonroot address, J samples parent, left child and right child uniformly. These probabilities are one half and one third respectively. The kernel has no dependence on colour or budget and has no hold at the root.

**Definition 1.8 (The finite actual-step law).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints.law`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints.law` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The zero-step law is the point mass at the starting address. The successor law samples J at that address and then continues with the remaining finite-step law from the selected neighbor. Root returns and later departures use J at the visited address, so they retain the degree-two rule.

**Definition 1.9 (An explicit finite experiment).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints.Seed`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints.Seed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A seed for h jumps is h independent choices from six equiprobable outcomes. In move, a root sends three outcomes to each child; a nonroot sends two outcomes to each of its three neighbors. The recursive run uses one choice and continues from the actual selected address. Equality of the uniform seed pushforward with law is proved by the exact one-step distribution identity and the product law of independent uniform choices.

**Definition 1.10 (Endpoint expectations).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints.B`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints.B` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

B is the real integral of f composed with observation against the actual j-step address law. The finite experiment gives the same integral, and its finite sum equals the backward evaluator. This correspondence is proved for every real function; only globally bounded functions occur in the classification statement.

**Definition 1.11 (Global test functions).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints.Bounded`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints.Bounded` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Bounded means that one real constant bounds the absolute value at every point of ZMod m times the natural numbers. In particular every cell indicator is an admissible test; the tests are not limited to a finite observation subset.

**Theorem 1.12 (All bounded endpoint tests classify the signature).**

$$\forall m: \operatorname{Nat}, ((3 \le m) \implies (\forall h: \operatorname{Nat}, (\forall p: \operatorname{Address}, (\forall t: \operatorname{Address}, (\operatorname{signature}\left(m, h, p\right) = \operatorname{signature}\left(m, h, t\right) \iff (\forall j: \operatorname{Nat}, ((j \le h) \implies (\forall f: (\operatorname{ZMod}\left(m\right) \times \operatorname{Nat}) \to \operatorname{Real}, ((\operatorname{Bounded}\left(f\right)) \implies (\operatorname{B}\left(m, p, j, f\right) = \operatorname{B}\left(m, t, j, f\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints.bounded_endpoints_iff_signature` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural modulus m at least three, every natural budget h and every two literal finite addresses p and t, signature equality is equivalent to equality of B for every j from zero through h and every globally bounded real test. The family includes its initial endpoint and every intermediate endpoint.

For the forward direction, equal current and parent colours determine the same incoming increment: the integers 0, 1 and -1 have distinct residues for all permitted moduli, including three. Applying the literal table then matches each child, while the ancestor lists match the parent move. Each matched move preserves the signature with one less unit of budget. Induction in the actual finite experiment gives equal endpoint observations, with identical degree-dependent probabilities even on routes that revisit the root.

For the converse, the zero-step cell indicators recover the initial colour and depth n. For every k at most n, an endpoint at depth n-k after exactly k jumps requires decreasing depth at every step. Induction on k excludes both child branches and identifies the unique all-parent route. Its cell expectation is (1/3)^k at its ancestor colour and zero at every other colour. Every departure on that route is nonroot, including the case k=n. Positivity therefore recovers every colour with k at most min(h,n).

The result formalizes Theorem 2.2 of FIB-ATOM boundary geometry: finite joint cycle and radial prediction, using its fixed infinite carrier and the recursion of Continuation V, Definition 120.3. It concerns separate true-jump endpoint expectations. It asserts no continuous-time or frozen-path law, total-variation estimate, whole-future observation, acquisition procedure, or physical conclusion.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints.Address`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints.B`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints.Bounded`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints.J`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints.Seed`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints.ancestor`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints.bounded_endpoints_iff_signature`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints.childIncrement`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints.code`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints.law`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints.observation`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints.signature`
- Dependency: [D5/S0/Diagonal/Probability/EquivariantEscape](../../../../S0/Diagonal/Probability/EquivariantEscape.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition](../ActualTreeReadoutAcquisition.md)
