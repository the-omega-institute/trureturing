[Index](../../marked_head_profile.md) · [Actual maximal-height fibres](../../problem-details/04-a-complete-star-family-refutes-the-unrestricted-gamma-73-bound.md) · [Common-mask capacities](332-common-mask-capacity-and-the-kakeya-interface.md) · [Same-chain certificates](334-same-chain-overlap-and-future-risk-certificates.md)

# Maximal-label Fourier overlap and uncovered density

The primitive-character obstruction behind exact-cover impossibility has
a quantitative version for a general finite residue family. It gives a
label-resolved relation between overlap and uncovered mass, without
assuming that the family covers. The cover-only consequence forces Haar
overlap onto a chosen divisibility-maximal class. Transport to a distorted
survivor law still needs a new joint observation; these inequalities do
not settle unrestricted odd covering or333's through47 deficit.

These are direct finite Fourier and CRT deductions, not a claim of a new
published theorem or a new Lean result. The prime-power specialization
reuses the maximal-height fibre mechanism already in problem-details04.

## Isolate one original label by its primitive characters

Fix any finite family C_i=[a_i]_(d_i), with distinct original moduli d_i>1,
and N=lcm_i d_i. Work on Z/NZ with uniform probability u. Choose a label
C=[a]_d whose modulus is maximal under divisibility: d|d_i implies d_i=d.
No residue, repeated-prime height or original label is identified with
another. Write

    L=sum_i 1_(C_i), H=sum_i 1/d_i-1.

For gcd(k,d)=1, put chi_k(x)=exp(2 pi i k(x-a)/d). Averaging chi_k along
C_i gives zero unless d|d_i: its geometric sum has ratio
exp(2 pi i k d_i/d), and that ratio is one exactly in this case. Thus

    u(L chi_k)=u((L-1)chi_k)=1/d.                    (FO1)

Only C contributes, with chi_k=1 there. The mean of the nontrivial
character itself is zero. This identity does not require L>=1.
In an exact cover L=1 it is already a contradiction, recovering the
usual primitive-root obstruction for distinct nonunit moduli.

Average the primitive characters into the real Ramanujan kernel

    R_d(r)=(1/phi(d)) sum_(gcd(k,d)=1) exp(2 pi i kr/d).

For a prime power p^a its values are 1 when p^a|r, -1/(p-1) when
p^(a-1)|r but p^a does not divide r, and zero otherwise. Subtract the
sum over multiples of p from the full character sum to obtain these
three values. CRT factors R_d as the product of these prime-power
kernels. Equivalently, with q=d/gcd(d,r),

    R_d(r)=mu(q)/phi(q), u((L-1)R_d(x-a))=1/d.       (FO2)

Let p1<p2<... be the distinct prime factors of d, and define

    kappa=1/(p1-1),
    rho=0                         if d is a prime power,
    rho=1/((p1-1)(p2-1))          otherwise.

Then R_d=1 on C, R_d<=rho outside C, and R_d>=-kappa everywhere.
The negative bound is attained by one negative factor at p1. When d
has at least two prime factors, a positive off-C product uses at least
two negative factors, and choosing p1,p2 attains rho. For d=p^a with
a>=2 the off-C maximum is zero; for d=p it is -1/(p-1), so rho=0 is
a convenient weaker upper bound. For odd d, kappa<=1/2 and rho<=1/8.

## A noncovering version retains both excess and uncovered points

Define the nonnegative functions and masses

    v=1_(L=0), e=(L-1)_+, S=u(v), E=u(e)=H+S,
    X=u(e 1_C)=sum_(i!=*)u(C intersect C_i).

Here L-1=e-v. On C, v=0 and e=L-1 counts precisely the other original
classes. In particular, X has the exact arithmetic formula

    X=sum_(i!=*, a_i=a mod gcd(d,d_i)) 1/lcm(d,d_i). (FO3)

Multiply the upper bound for R_d outside C by e>=0 and its lower bound
by v>=0. From(FO2),

    1/d=u(e R_d)-u(v R_d)
       <=(1-rho)X+rho E+kappa S
       =(1-rho)X+rho H+(rho+kappa)S.

Since rho+kappa>0, this proves the complete-label lower bound

    S>=max(0, [1/d-rho H-(1-rho)X]/(rho+kappa)).    (FO4)

H may be negative; no covering premise or sign assumption on L-1 was
used. All inputs in(FO3)--(FO4) concern the same actual original family,
and pair intersections use the original residues. Replacing X by a
certified upper bound, or H by an upper bound when rho>0, preserves the
direction. Separate independently minimized overlap values do not.

For a hypothetical cover S=0, H=E>=0, so the necessary condition becomes

    X>=max(0, [1/d-rho H]/(1-rho)).                 (FO5)

Also H>=1/d by the absolute value of any one identity(FO1). Consequently,
for odd d, the weaker uniform version of(FO5) is

    X>=max(0, (8/d-H)/7).                          (FO6)

For prime powers rho=0, the stronger bound is X>=1/d. These are
constraints on a hypothetical whole cover, not on an isolated smooth
head assumed to be covered by its own labels.

## Prime powers give a pointwise sibling argument

If d=p^a is unique and divisibility-maximal, every other original modulus
divides N/p, while v_p(N)=a. Translation by N/p therefore fixes membership
in every other class and cycles the p top-digit siblings of C. Let

    A=C minus union_(i!=*) C_i

be the private portion of C. Its p-1 nonzero translates are pairwise
disjoint, lie outside C, and miss all other classes. Therefore

    S>=(p-1)u(A)>=(p-1)(1/d-X).                    (FO7)

This recovers(FO4) for prime powers, with the sharper private-set term
retained. If the whole family covers, A must be empty and C is redundant.
Thus a minimal distinct cover has no divisibility-maximal prime-power
label. This is the direct specialization of the actual maximal-height
fibre argument in problem-details04, not a new irredundancy theorem.

One concrete check of the noncovering interface uses the moduli
(3,5,7,9,11,13,15) and corresponding residues (0,0,0,1,0,0,2). They are
distinct odd nonunit moduli, with period45045 and

    H=982/45045>0,
    X_(d=9)=284/5005,
    S>=4898/45045>0.

The elementary sum of densities exceeds one, while the original-label
sibling bound certifies an uncovered point. Direct enumeration gives
S=272/1001. This is an illustration of the known fibre mechanism, not a
new sector theorem or an odd covering counterexample.

## The missing transport is a signed joint moment

For any positive measure xi on the same complete period, set

    J_d(xi)=xi((e-v)R_d(x-a)),
    E_xi=xi(e), S_xi=xi(v), X_xi=xi(e 1_C).

The same pointwise estimates give

    J_d(xi)<=(1-rho)X_xi+rho E_xi+kappa S_xi.        (FO8)

Formula(FO2) establishes J_d(u)=1/d for Haar; it supplies no such
identity for a general xi. Domination of xi by a multiple of u does
not provide the lower bound on this signed moment needed to replace
J_d(xi) by1/d. Under a whole-cover assumption v=0, a lower bound on
J_d(xi) together with an upper bound on E_xi would force X_xi. Without
that assumption, omitting S_xi discards exactly the uncovered mass being
studied. The noncovering fixtures327/334 cannot falsify a cover-only
inequality by treating L-1 as nonnegative.

Moreover X_xi=sum_(i!=*)xi(C intersect C_i) pools all partner labels.
Continuation at a particular prime needs the part carried by the relevant
original ending-prime bucket. Total overlap may be paid by old labels,
other future primes or points the actual survivor mask has removed.
Even within one bucket, X_xi counts label multiplicity. Passing from its
lower bound to a bad-event union/intersection also needs exact-union or
multiplicity control and the prescribed physical kernel.
Suitable extra observations retain gcd/prefix cells on which R_d is
constant, the actual mask and the partner-label bucket. Such observations
must enter332/334 on their own physical or killed law; they are not
supplied by the Haar identity alone.

There is also a height obstruction already at the Fourier relaxation.
For d=p^a the nonnegative integer function h=1_C satisfies all primitive
moments u(h chi_k)=1/d and attains H=X=1/d. Letting a increase sends this
forced overlap to zero. This is an abstract relaxation, not an asserted
distinct-modulus cover. Restricting its Haar measure to C's complement
keeps positive mass but gives J_d=0 and X=0. Thus primitive moments and
upper domination alone supply neither a height-independent correction
nor the required mask transport.

## Relation to solved covering problems and source scope

Mirsky--Newman/Davenport--Rado rules out an exact distinct cover, where
L is identically one. The public [Erdős947](https://www.erdosproblems.com/947)
entry records this solved problem. Formula(FO1) explains precisely what
changes for a general cover: the excess L-1 carries the isolated Fourier
coefficient instead of vanishing. Ordinary coverage L>=1 is not exact
coverage and supplies no contradiction by itself.

The stronger essential-class bounds of Lettl--Sun are already cited in
[the repository's literature entry](../../../../../Library/Arith/lettlsun2008cosets.md).
Their [Theorem1.3](https://arxiv.org/pdf/math/0411144v2) gives
k>=1+sum_p v_p(d)(p-1) and d<=2^(k-1) for an essential class in a
k-class ordinary cover. Their Theorem2.1 retains prime-specific label
mismatches. These results require the whole-cover premise. They bound
heights for fixed k, but unrestricted#7 has no fixed class count; they
do not turn1/d into an absolute positive constant.

A different solved relative is Schinzel's antichain problem:
[BBMST, Theorem9.1](https://arxiv.org/pdf/1811.03547v1) proves that a finite
cover with distinct nonunit moduli has two moduli with one dividing the
other. Its proof uses the antichain premise in the smooth-head first and
second moment estimates (Lemmas9.2--9.4); arbitrary distinct odd moduli
do not satisfy that premise. In a minimal cover, a divisibility pair's
residues must be incompatible, since compatible residues would make the
larger-modulus class redundant. This is an available original-label
constraint, not permission to discard all nonmaximal moduli or replace
the problem by an antichain.

The cited public problem pages and the two primary texts were checked on
19 September2026. [Erdős7](https://www.erdosproblems.com/7) still lists the
unrestricted question as open. These source comparisons delimit usable
hypotheses; they are not an exhaustive novelty or formalization claim.
