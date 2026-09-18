# Brietzke Conjecture 15 probe

## Preregistered falsifiable predictions

Before executing commands, searches, downloads, or experiments, this probe predicts:

1. An independently written Python implementation of `d(n,k) = (k+1) * choose(2*(n+1), n-k) / (n+1)`, with `d(n,k)=0` when `k>n`, has exact integer division, reproduces the six printed rows, and satisfies the paper's proved identities (21) `sum_j (d(n,5*j+1)-d(n,5*j+2)) = F(2*n)` and (22) `sum_j (d(n,5*j)-d(n,5*j+3)) = F(2*n+1)` for `0 <= n < 300`.
2. `b(n) = sum_j (d(n,4*j)-d(n,4*j+2))` equals `2^n` for every `0 <= n < 300`.
3. The preregistered claim is faithful to the published source. A clause mismatch requires verdict `revise`; a counterexample requires verdict `reject`.
4. The expected proof shape is `bind-only` (Pascal identities, finite telescoping, and normalization). Admission, if the claim closes, is `open-problem-resolution`; no escape witness is claimed. Only a kernel-checked theorem without sorry or new axioms warrants `propose`.

The public definition will explicitly guard `k <= n` and preserve the source expression. Finite sums must cover all nonzero terms. The intended recurrence and its lower boundary will be checked rather than assumed.

## Current result

Experiments and source verification have not yet run. Verdict is not yet determined.
