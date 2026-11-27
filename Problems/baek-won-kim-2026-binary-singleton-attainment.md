---
slug: baek-won-kim-2026-binary-singleton-attainment
bibkey: baekwonkim2026easingleton
doi: 10.48550/arXiv.2611.32126
url: https://arxiv.org/abs/2611.32126v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Codes/BinaryEAAttainmentRefutation.result
---

# Binary attainment of the entanglement-assisted Singleton bound

## Problem

Jae-Hyun Baek, Byung-Sun Won and Jon-Lark Kim, *Validity and maximum violation
of the entanglement-assisted quantum Singleton bound for linear stabilizer
codes*, arXiv:2611.32126v1, Section 5, p. 10:

> The code $[\![8,2,5;2]\!]_{3}$ attains this bound, and binary attainment is open.

The binary event in the $k=\sigma=2$ case is the existence, for some natural
$n\ge6$, of a linear entanglement-assisted stabilizer code
$[\![n,2,n-3;n-6]\!]_{2}$ in the sense of Section 2. The quantifier includes
degenerate codes. [Versioned paper](https://arxiv.org/html/2611.32126v1#S5.p2.1)

### Statement echo

Write $\mathcal C$ for the sender's stabilizer space. Its symplectic dual
$U=\mathcal C^{\perp_s}\le(\mathbb F_2^2)^n$ has dimension $n+k-c=8$ and
the radical $H=U\cap U^{\perp_s}$ has dimension $n-k-c=4$. To see the
parameter correspondence, $\sigma=n-k-d+1=2$ gives $d=n-3$ and
$2(d-1)=n-k+c$ gives $c=n-6$. Nonnegative $c$ gives $n\ge6$.
Nondegeneracy of the ambient form gives $U^{\perp_s}=\mathcal C$, so the
radical agrees with the stabilizer hull.

In `BinaryEAAttainment.Attainment`, the quantified space is $U$ and
symplectic weight is $n-\operatorname{zeroCount}(v)$, the number of
nonzero coordinate pairs. Every $v\in U\setminus H$ has weight at
least $n-3$ and there exists $v\in U\setminus H$ of weight exactly
$n-3$. There is no weight restriction on $H$.
[Source conventions](https://arxiv.org/html/2611.32126v1#S2)

## Motivation

Proposition 17 bounds positive violation for the binary and ternary
$k=\sigma=2$ families. An equality decision determines whether the binary
family can use exactly the number of pairs prescribed by that inequality.
The [preregistration](https://github.com/the-omega-institute/trureturing/issues/34860)
fixes the event over all eligible lengths.

## Gap

The source's proof against positive violation uses a hull of larger
dimension. Equality has a four-dimensional hull, and its projections
onto individual binary symbol spaces can be surjective. The equality
case requires a proof that accounts for those projections.

## Route

The nonradical weight bound gives at most three zero sites. At least
seven sites must be occupied by the radical, excluding $n=6$. At
$n\ge9$, coordinate-kernel counts force radical site ranks at most one
and radical support of size at most ten. At $n=8$, two-site kernel
bounds and shortening rule out rank-two sites. For $n=7$, the rank-one
support argument applies when every radical site rank is at most one.

If there is a rank-two radical site at length seven, shorten at that
site. The remaining six sites carry a code of dimension six, a radical
of dimension two and a bound of two zeros per nonradical word. The
spread obstruction rules out a second rank-two shortening. After
symplectic changes of local coordinates, three-site projections leave
two type profiles. Two triples violate the zero bound. For three pairs,
the zero bound forces parity relations among lifts of a basis of the
projected code, making the shortened symplectic pairing vanish. Radical
representatives then transfer vanishing to $U$, which would have
dimension eight and be isotropic in dimension fourteen.

## Falsifier

An explicit space $U$ at any $n\ge6$ satisfying both dimension
equalities and both clauses of the exact nonradical minimum would
falsify the exclusion. Such a witness would also give the source's
stabilizer by taking $U^{\perp_s}$.

## Evidence

- `D5/S3/Quantum/Codes/BinaryEAAttainmentRefutation.result` proves
  `¬ BinaryEAAttainment.Attainment`. It is the designated refutation
  result and is exempt from four-slot escape registration under
  CLAUDE.md §3.9.
- `D5/S3/Quantum/Codes/BinaryEAAttainmentBridge.result` gives the
  exclusion for $n\ge8$. The conditional bridge handles $n=6$ and
  the length-seven rank-one case and consumes the remaining case.
- `D5.S3.Quantum.Codes.BinaryEAShortening.length_seven_no_rank_two_site`
  excludes the rank-two site. Its proof is in
  [BinaryEAShorteningLengthSeven.lean](../D5/S3/Quantum/Codes/BinaryEAShorteningLengthSeven.lean).
  The final theorem applies it with
  $H=U\cap U^{\perp_s}$ and the original binary symplectic form.

- The remaining public helper registrations are tracked in [#34915](https://github.com/the-omega-institute/trureturing/issues/34915).

## Triage

### What the settlement shows

The binary equality event is refuted by
`D5/S3/Quantum/Codes/BinaryEAAttainmentRefutation.result`. The case of
a surjective radical projection fails through the shortened
symplectic pairing, and the other cases fail through coordinate-kernel
counts and the rank-one support obstruction. Proposition 17's
inequality and the ternary equality example remain conclusions of the
source. Equality for other parameters and for encoders outside the
source's linear stabilizer model is outside this event.

## ASSUMED-UNVERIFIED

The paper's Section 2 supplies the identification of linear
entanglement-assisted stabilizer parameters with the symplectic
subspace formulation. Lean proves the subspace exclusion. The
identification with physical encoders is used as a source result.
