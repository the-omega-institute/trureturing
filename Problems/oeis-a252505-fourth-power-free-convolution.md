---
slug: oeis-a252505-fourth-power-free-convolution
bibkey: oeis2026a252505
doi: null
url: https://oeis.org/A252505
triage: theorem
motivation_gids:
  - D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution.claim
---

# The whole A252505 convolution

## Problem

For every positive integer $n$,
$$
a(n)=\sum_{d\mid n}b(d)c(n/d).
$$
Here $a(n)$ counts positive divisors not divisible by any prime fourth power.
The value $b(n)$ counts positive integer pairs $x\le y$ satisfying
$1/n=1/x+1/y$ in $\mathbb Q$, with $x=y$ allowed. Write
$$
h(n)=\sum_{d\mid n}\left\lceil\frac{\tau(d)}2\right\rceil,
\qquad g(n)=h(n)\bmod2.
$$
The integer function $c$ has $c(1)=1$ and, for $n>1$,
$$
c(n)=-\sum_{d\mid n,\ d<n}g(n/d)c(d).
$$
The exact unchanged Lean proposition is 'claim'. Its quantifier is
'all n : Nat, 1 <= n -> ...'; no restriction on prime support or exponents
and no multiplicativity of $b$ or $g$ is assumed.

## Source and literature boundary

The primary conjecture is the A252505 FORMULA line quoted in
Library/PrimeForms/oeis2026a252505.md. Preregistration:
https://github.com/the-omega-institute/trureturing/issues/27491.
The accepted bounded source and literature screen supplies the attribution
and unproved-in-searched-scope premise. Worldwide openness and originality
outside that screen are ASSUMED-UNVERIFIED.

## Native bridges

The actual rational solutions biject with the positive factor pairs
$(x-n)(y-n)=n^2$, ordered by size. The swap involution has precisely the
fixed pair $(n,n)$; consequently $2b(n)=\tau(n^2)+1$, including the diagonal
$(x,y)=(2n,2n)$.

The canonical Mathlib Dirichlet inverse satisfies the stated recursion, whose
positive-domain solution is unique. No value at zero occurs in 'claim'.

## Remaining whole gap

There is no Lean theorem 'result : claim'. The missing universal bridge is
$$
b(n)=\sum_{d\mid n}a(d)g(n/d).
$$
The native fourth-power-free divisor count still needs its capped exponent-box
bridge $\prod_{p\mid n}(1+\min(v_p(n),3))$ in a live proof. The native ceiling
sum similarly needs its full exponent-box staircase bridge. These direct
library applications require an actual consumer in the whole proof.
In the finite-prime-support argument, the missing formal ingredients are the
coefficient encodings, lawful series identities, the residue characterization
of the zero-or-one coefficient gamma, and the integral parity descent
$h\bmod2=\gamma$. The final inverse-convolution cancellation also remains to
be applied to that bridge. The existing counting formulas do not by
themselves establish it.

For a fixed finite prime support, write
$N=\prod_i(1+X_i)+\prod_i(1-X_i)$.
The candidate identities over rational formal series are
$$
A=\prod_i\frac{1-X_i^4}{(1-X_i)^2},\quad
B=\frac{N}{2\prod_i(1-X_i)^2},\quad
G=\frac{N}{2\prod_i(1-X_i^4)},
$$
and
$$
H=G\prod_i\frac{1+X_i^2}{(1-X_i)^2}.
$$
Each local factor in the last product is
$1+2\sum_{k\ge1}kX_i^k$.
The coefficients of $G$ are zero or one: all exponent residues must lie in
$\{0,1\}$ modulo four, with an even number of one residues.
An integer-coefficient identity must precede reduction modulo two; there is
no coefficient homomorphism from $\mathbb Q$ to $\mathbb Z/2\mathbb Z$.

These are the uncompiled central proof obligations, not a stronger substitute
problem or a finite-range certificate. No settlement or solved-problem KPI is
claimed; no Proved OpenProblemResolutionClaim is attached to this source.
