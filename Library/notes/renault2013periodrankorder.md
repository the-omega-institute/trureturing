---
bibkey: renault2013periodrankorder
authors: Marc Renault
year: 2013
title: The Period, Rank, and Order of the (a,b)-Fibonacci Sequence Mod m
doi: 10.4169/math.mag.86.5.372
claim: Theorems 1-2 give least-common-multiple period and rank laws and prime-power lifting with the actual initial delay retained; they do not assume absence of WSS primes.
strata_touched: []
license: citation-only
triage: anchor
---

# Golden prime clocks and actual interlevel reciprocity

## Primary source and precise role

Marc Renault, *The Period, Rank, and Order of the (a,b)-Fibonacci Sequence
Mod m*, Mathematics Magazine 86 (2013), 372-380.
https://doi.org/10.4169/math.mag.86.5.372
Author-hosted published text:
https://webspace.ship.edu/msrenault/fibonacci/RenaultPeriodRankOrderMathMag.pdf

The Preliminaries on printed pages373-374 identify the matrix order with
the pair period, and scalar return with the zero rank. Theorem1 on page374
proves the least-common-multiple laws. Theorem2 on page376 retains the
initial prime-power plateau before each lift multiplies the period by p.
These statements were read in the primary text; page376 was also viewed
as an image. The page374 image request failed, so no visual check of that
particular page is claimed. The proof of GPC1 also derives the needed
odd-prime lifting directly by a unit binomial expansion.

For the standard sequence, the repository's existing golden matrix differs
from this paper's matrix by the swap of its two coordinates. This conjugacy
preserves every modulus-dependent order. The real fractional-part return
in `PERIODIC_TREE.md`, Section8, remains a different observation; it is not
identified with reduction modulo a prime or a prime square.

## Existing owner: GPC.1-GPC.6

`Problems/wall-sun-sun-golden-unit-lift.md` keeps the actual blocks
B_j=L_(3^j)^2+3 and r_j=3^(j+1), whose factor valuations are the original
h_p by TBN. Its GPC section proves the following ordinary specializations:

1. Every nontrivial divisor of B_j has pair period and zero rank2r_j.
   For every a>=1, pi(B_j^a)=2r_j*B_j^(a-1), even when an individual
   factor has a longer initial p-power plateau. Thus normal composite
   clock growth cannot decide whether a factor is WSS.
2. For i<j, B_j=3-3^(2(j-i)-1)*B_i^2 modulo B_i^3. Hence at each
   actual p|B_i the later displacement B_j-3 has valuation exactly2h_p.
3. Quadratic reciprocity gives (B_j/B_i)=-1 and (B_i/B_j)=+1. The
   primewise refinement is product_(q|B_j)(p/q)^h_q=1 for every earlier
   p. It retains all earlier prime factors, including those of even depth.
4. If a later block has only one odd-depth prime Q, that Q must split
   completely in Q(sqrt(p):p divides an earlier block). In particular the
   remaining minimal all-WSS pattern P^2 Q^3 must satisfy all these
   simultaneous conditions, in addition to DCE's Q=19 modulo40.
5. For fixed j, the comparison primes with those quadratic tests and
   Q=1 modulo r_j have positive Dirichlet density1/(2^t*phi(40r_j)),
   where t is the number of distinct earlier primes. This comparison set
   omits the exact-clock condition. The primes of exact pair period2r_j
   are exactly the finite factor support of B_j, so the density is not
   a WSS or exact-period existence theorem.

The cross-block formulas are derived in the owner from the actual Lucas
product, then classical reciprocity. They are not attributed to Renault;
the paper supplies the period-theoretic input. Independent priority for
these particular block specializations has not been established.

## Other classical inputs, with exact boundaries

NIST Digital Library of Mathematical Functions, Section27.9,
https://dlmf.nist.gov/27.9 , supplies the Jacobi prime-factor definition,
the sign formula27.9.1 and quadratic reciprocity27.9.3, including its
extension to coprime odd composite denominators. A positive Jacobi symbol
at a composite modulus is not treated as a square-root certificate.

A. V. Sutherland, MIT18.785 Lecture28 (2021), Theorem28.9 on printed page6:
https://math.mit.edu/classes/18.785/2021fa/LectureNotes28.pdf
The theorem and its page image were read. GPC uses only the cyclotomic
Dirichlet-progression case to count the explicitly independent congruence
classes. The class-field family here exists without a WSS assumption,
but the target primes must still divide the specified integer B_j. No
Chebotarev application replaces this actual divisibility requirement.

The latest dev's HD/DF harmonic filters in the existing Medina-Rowland
note were inspected separately. Their two-scale cancellation removal is
prior repository work and is not recounted as a new GPC result.

## Formal and arithmetic boundary

The matrices, period laws, exact integer products and character identities
are ordinary proofs in the existing owner. The trace-image Scribe adds a
contextual reference without changing its three declarations or formal
formula. No new Lean source, compiler pass, kernel certificate, or solved
external open problem is asserted. Quadratic characters see depth parity;
they still allow both h=1 and odd h>=3. The remaining heterogeneous-depth
WSS branch is constrained, not eliminated or constructed.
