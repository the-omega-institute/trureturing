---
bibkey: fibcharacter2026bohrbarrier
authors: trureturing research synthesis
year: 2026
title: Bohr phase boxes and weighted characters at a fixed Fibonacci modulus
doi: null
url: https://arxiv.org/abs/1011.0107v2
claim: "Classical Bohr capacity supplies simultaneous phase alignment. Applied to the full divisor-increment law, it obstructs uniform nonprincipal-character decay at the Robin budget scale; it does not settle actual weighted residue hits."
strata_touched: []
license: citation-only
triage: anchor
---

# Bohr phase boxes and the actual residue target

The classical ingredients below are distinguished from the parameter-dependent application in §§220–222 of [the FIB theory](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md). The application is a paper derivation, with no Lean verification or originality claim. The fixed-modulus joint-weight interface is also recorded in [the complementary-divisor note](../ArithSums/fibcomplement2026weightedresidues.md).

## Primary sources and exact scope

Tom Sanders, *On the Bogolyubov–Ruzsa lemma*, arXiv:1011.0107v2 (2012), [original PDF](https://arxiv.org/pdf/1011.0107v2).

Section 5, Lemma 5.1 (PDF p.8) bounds the measure of intersections of Bohr sets. Equation (5.2) and the discussion on p.9 give the one-frequency estimate and explain the usual multiple-frequency lower bound. The paper points to Tao–Vu, *Additive Combinatorics*, Lemma 4.20, and distinguishes its chord-distance definition from the book's phase-distance definition. The book is a bibliographic pointer here; the explicit phase-box argument below supplies the constants used in the FIB application.

Jonathan Hermon and Sam Olesker-Taylor, *Cutoff for Almost All Random Walks on Abelian Groups*, arXiv:2102.02809v2 (2025), [original text, §2.6](https://arxiv.org/html/2102.02809v2#S2.SS6).

Section 2.6, “Lower Bound on Total-Variation Mixing”, proves the lower bound in Theorem 2.5 for every fixed choice of generators. Its proof explicitly fixes the generators instead of averaging over them. A source distribution concentrated on a small set of likely exponent vectors has an image supported on at most that many group elements. Random-generator upper bounds elsewhere in the paper do not establish mixing for the deterministic small-prime residues used here.

The elementary abstract interface is as follows. Let $\rho$ be a probability on a countable source, let $\pi$ map that source to a group of order $Q$, and let

$$
E_L=\{w:\rho(w)\ge e^L/Q\}.
$$

Then $|E_L|\le Qe^{-L}$ and $|\pi(E_L)|\le|E_L|$, so

$$
\|\pi_*\rho-\mathrm{Unif}\|_{\mathrm{TV}}
\ge\rho(E_L)-e^{-L}.
$$

No suitable high-probability source-entropy estimate for the present increment law is supplied here. In particular, this source does not establish that its total variation tends to one.

## Finite simultaneous phases

Let $G$ be any finite abelian group of order $Q$, and choose $a_1,\ldots,a_m\in G$.
Partition the circle into $L$ equal half-open arcs. The $Q$ characters occupy at most $L^m$ phase boxes at these elements. A largest box contains at least $Q/L^m$ characters. Dividing its characters by one fixed member produces that many distinct characters with

$$
\chi(a_j)=e^{i\theta_j},\qquad |\theta_j|\le2\pi/L\quad(1\le j\le m).
$$

This is a near-annihilator Bohr set in the dual group. It includes the principal character; the capacity comparison $Q/L^m>1$ is needed to ensure another one. Neither generation of the group nor independence of the phase coordinates is required.

For the actual FIB application, $V=F_r$ with prime $r\to\infty$,
$A=1+V\lceil V/10\rceil$, $y=\log A$, $\ell=\log y$, $s=y\ell$ and $R=y/\ell^2$.
Every prime divisor of $V$ is at least $2r-1$, so all $p\le2y$ are units eventually.
Here $Q=\varphi(V)$, $\log Q=y/2+O(1)$, $m=\pi(2y)=(2+o(1))y/\ell$,
and $L=\lfloor y^{1/8}\rfloor$ gives at least $\exp(y/4+o(y))$ aligned characters.

The actual increment law is

$$
b_s(1)=1,\quad b_s(p^a)=Z(p^a)^s-Z(p^{a-1})^s,\quad
\mu_s(d)=\frac{b_s(d)}{dU(s)},\quad Z(n)=\frac{\sigma(n)}n.
$$

Its unit-conditioned pushforward is $\nu_s$; for Dirichlet characters extended by zero off the units,
$\widehat\mu_s(\chi)=c_V\widehat\nu_s(\chi)$, where $c_V=\mu_s((d,V)=1)$.
Section 222 combines the phase count with the genuine exponent second moment and the large-prime tail to derive

$$
|\widehat\nu_s(\chi)|,\ |\widehat\mu_s(\chi)|
\ge\exp(-Cy^{3/4}\ell)=\exp(-o(R))
$$

for exponentially many nonprincipal characters. The classical Bohr count alone does not give this weighted estimate; the local increment and tail controls are necessary.

The existing [Kronecker note](onishchik2020kronecker.md) describes torus orbit closures, not this growing finite character count. The existing `PrimeOnlyNoGap` source treats a fixed summable jump law and integer Fourier modes. A return there may be trivial after passage to a finite quotient; it does not by itself give the nonprincipal characters or their number required here.

## What the actual kernel asks of the characters

Take the same actual interval $I=[g_-,g_+]\cap\mathbb Z$, with
$A=1+g_-V$, $X=1+g_+V$ and $g_+-g_-<V$.
Let $V<D<X$, $H=X/D<V$, and $Q=\varphi(V)$. For each positive integer $h\le H$ set

$$
J_h=(D,X]\cap[A/h,X/h]\cap\mathbb N.
$$

For nonnegative weights $a(d)$, define the actual hit sum

$$
S_a=\sum_{\substack{d>D\\\exists g\in I:\ d\mid1+Vg}}a(d).
$$

Each divisor hits at most once: a hit makes $d$ a unit modulo $V$, and $d>V>|I|-1$.
For the actual complementary factor $h$, character orthogonality therefore gives

$$
S_a=\frac1Q\sum_{\chi\bmod V}
\sum_{\substack{1\le h\le H\\(h,V)=1}}\chi(h)A_\chi(J_h),
\qquad
A_\chi(J)=\sum_{\substack{d\in J\\(d,V)=1}}a(d)\chi(d).
$$

The retained kernel uses $a(d)=(d/X)\mu_s(d)$.
Additional restrictions on the same product $dh$ must stay inside the joint sum; a condition depending on $dh$ cannot automatically be absorbed into $a(d)$ alone.

Writing $M_0=Q^{-1}\sum_h A_1(J_h)$, the exact target $S_a<\eta$ is equivalent to

$$
\operatorname{Re}\sum_{\chi\ne1}\sum_h\chi(h)A_\chi(J_h)
<Q(\eta-M_0).
$$

It asks for a signed aggregate with moving intervals. A uniform bound on every character is stronger. Large moduli of the full Euler coefficients do not imply a large mass at residue one, an inverse residue, or an actual multiplier. Conversely, truncation to $J_h$, a cap on $dh$, and the $d/X$ kernel destroy the simple full Euler-product identification. Neither upper nor lower modulus estimates for that product transfer without a separate argument.

## A fixed-modulus short-factor fourth moment

For a fixed unit subset $\mathcal H\subseteq[1,H]\cap\mathbb N$ with $H^2<V$, put
$B_\chi=\sum_{h\in\mathcal H}\chi(h)$.
Orthogonality gives

$$
\frac1Q\sum_\chi|B_\chi|^4
=\#\{h_1h_2\equiv h_3h_4\pmod V:h_i\in\mathcal H\}.
$$

Both products lie in $[1,H^2]$, so each congruence is an integer equality.
Write $h_1=gu$, $h_3=gv$ with $(u,v)=1$; equality then forces $h_2=kv$, $h_4=ku$.
Consequently

$$
\frac1Q\sum_\chi|B_\chi|^4
\le\sum_{\substack{u,v\le H\\(u,v)=1}}
\left\lfloor\frac H{\max(u,v)}\right\rfloor^2
\le2H^2(1+\log H).
$$

This elementary multiplicative-energy estimate needs no prime-modulus assumption. For a fixed interval $J$ and $A_\chi=A_\chi(J)$, Hölder yields

$$
\left|\frac1Q\sum_{\chi\ne1}A_\chi B_\chi\right|
\le\left(\frac1Q\sum_{\chi\ne1}|A_\chi|^{4/3}\right)^{3/4}
\left(2H^2(1+\log H)\right)^{1/4}.
$$

The core spectral moment has not been bounded at the required scale. The original intervals $J_h$ also move with $h$; using fixed rectangles requires explicit coverage and boundary errors. Enlarging a nonnegative hit set gives an upper bound, not an equality. These standard identities identify a possible aggregate estimate without supplying it or solving Robin for the full FIB family.
