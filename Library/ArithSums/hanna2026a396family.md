---
bibkey: hanna2026a396family
authors: Paul D. Hanna
year: 2026
title: "OEIS A396803, A396805 and A396806: iterated-exponential parity"
doi: null
url: https://oeis.org/A396803
claim: "For each of A396803, A396805 and A396806, a(n) is odd iff n is odd for n >= 1."
strata_touched:
  - D5/S1/Recurrence/Residue/IterateExponentialParity
license: citation-only
triage: anchor
---

# Iterated-exponential family

## Source and scope

Paul D. Hanna's entries A396803 (June 8, 2026), A396805 and A396806
(June 9, 2026) specify exponential generating series satisfying
`A(x) = x * exp(A^{[k]}(x))`, with `k = 3, 5, 6`, respectively.
Here `A^{[k]}` denotes the k-fold compositional iterate, not the k-th power;
the zeroth iterate is the identity series `x`.

The shared conjecture says that `a(n)` is odd exactly when `n` is odd,
for every `n >= 1`. The repository proves this parity statement uniformly
in the natural iterate count, together with the defining series equation
and uniqueness among rational formal series with zero constant coefficient.

Each entry carries further residue conjectures that this repository does not prove.
These concern modulus 3 for A396803, moduli 3 and 5 for A396805,
and moduli 3 and 6 for A396806.

## Verified locator

- URL: https://oeis.org/A396803
- URL: https://oeis.org/A396805
- URL: https://oeis.org/A396806
