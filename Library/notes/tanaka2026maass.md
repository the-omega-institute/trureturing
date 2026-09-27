---
bibkey: tanaka2026maass
authors: Daichi Tanaka
year: 2026
title: Explicit Construction of Maass Wave Forms and Their Petersson Inner Products
doi: 10.48550/arXiv.2601.21588
claim: Theorem 1.1 constructs Maass cusp forms from the specified primitive real-quadratic Hecke characters, including parameter zero; it does not supply a missing golden ring-class character.
strata_touched: []
license: citation-only
triage: anchor
---

# Real-quadratic Hecke construction and the complete golden tower

## Primary source and exact scope

Daichi Tanaka, *Explicit Construction of Maass Wave Forms and Their Petersson
Inner Products*, arXiv:2601.21588v3, revised February 3, 2026.

https://arxiv.org/abs/2601.21588
https://arxiv.org/html/2601.21588v3

The source passages used here are equation (1.1), the cosine/sine definition
immediately following it, Theorem 1.1, and the subsequent discussion of
spectral parameter zero. The theorem assumes a primitive Hecke character of
specified archimedean type that does not factor through the norm and a
Dirichlet character. It constructs a Maass cusp form at the displayed
quadratic-discriminant and conductor level. For the finite odd-order
anticyclotomic characters in the WSS dossier, the real components are
trivial, the parameter is zero, and the non-norm condition is satisfied.

The source's cosine form has first exponential Fourier coefficient one half.
The WSS dossier uses twice that form, with first exponential coefficient one.
The complete-tower arguments below depend on these coefficients and their
Hecke eigenvalues. No Petersson norm formula or earlier normalization
correction is an input to CTG.

## Actual mathematical consumer

`Problems/wall-sun-sun-golden-unit-lift.md`, ROC and CTG.1, starts with an
ACTUAL golden ordinary ring-class character eta of order p^k. This is an
arithmetic hypothesis, equivalent in ROC to h_p>=k+1. Its nontrivial powers
have primitive conductors appropriate to their orders. Apply the cited
construction at each primitive conductor and then include the unscaled
oldvector g(z) at the common level. This gives the complete tower, including
all smaller nontrivial p-power character orders.

CTG.1-CTG.6 then prove, by integer polynomial and trace-dual arguments, the
following statements about that already-existing tower:

- its good-Hecke order is Z[X]/Q_k, where
  Q_k=product_(j=1)^k Psi_(p^j), with Q_k(2)=p^k;
- adjacent primitive packets are glued over a nonreduced quotient of
  characteristic p, rather than being an integral direct product;
- its scalar Eisenstein congruence module is Z/p^k, although every individual
  primitive packet has module Z/p;
- a specified integral trace combination attains precisely this congruence
  depth, and its normalized mod-p^r class exists exactly for r<=k.

These complete-tower formulas are proved in the dossier and are not
attributed to Tanaka. Their independent priority is unconfirmed. They do not
construct eta at a new target prime and do not prove a new WSS family.

The existing arithmetic source
`D5/S3/Arith/Lattices/PrimeCyclotomicTraceImage.lean` already states the
integer-image and unique-reconstruction theorem for modulus 2n+3, without a
primality hypothesis. CTG.3 identifies the actual complete-tower trace matrix
with that template at 2n+3=p^k. Its companion Scribe records this ordinary
application and the cited ambient construction. The spectral identification
is not an additional kernel-certified conclusion of that Lean source.

## Single-prime reconstruction in HCR

The same existing WSS owner, HCR.1-HCR.7, also retains one primitive packet
rather than the complete tower. After an actual generator-rotation auxiliary
prime ell has been selected in the already-existing class field, its ideal
coefficients are P_n(t), where P_0=1, P_1=X and P_(n+1)=XP_n-P_(n-1).
They are the classical U_n(X/2), with generating function
1/(1-XZ+Z^2). The polynomial identity is NIST DLMF 18.12.10:
https://dlmf.nist.gov/18.12.E10

The ambient Fourier interpretation comes from Tanaka's construction, while
the reconstruction is proved in HCR by Lagrange interpolation and the
monogenic trace-dual formula. The classical codifferent input is explained
in A. V. Sutherland, MIT 18.785 Lecture 12 (2021), Definition 12.2,
Proposition 12.6 and the monogenic different formula:
https://math.mit.edu/classes/18.785/2021fa/LectureNotes12.pdf

For c in B=Q(zeta_(p^k)+zeta_(p^k)^(-1)), HCR gives the exact reciprocal
numerator N_c(Z)=Z^(d-1)R_c(Z+Z^(-1)), with
R_c(t)=c*Psi_(p^k)'(t), and denominator Phi_(p^k)(Z). The first d
prime-power coefficients determine the full form within this packet and
are integral exactly when c belongs to the codifferent. The displayed
integer inverse, odd periodic completion and its sharp maximum-norm bound
are repository derivations, not statements attributed to Tanaka.

For a non-generator rotation of order p^s, all its power observations
factor through Tr_(B/B_s). The codifferent trace is surjective onto the
smaller codifferent, and the exact kernel dimension is d-d_s. HCR treats
split identity and inert primes separately. These are task-specific
observation results, not a universal Sturm bound or an effective bound for
the selected auxiliary prime. Abstract integer sequences satisfying these
relations do not construct a global golden character.

HCR.6 consumes the existing integer-image theorem through the identity
D_j=P_j-P_(j-2), giving the ordinary-trace-lattice condition
y_j=(j+1)y_0 modulo p at the first layer. Its Scribe explanation is updated;
the Lean statement and its formula are unchanged. Neither HCR nor CTG
supplies a new actual WSS prime-family decision, and no additional kernel
certification is claimed by this literature note.
