[Index](../../../../Problems/erdos-7-odd-covering-systems.md)

# Audit of the claimed global nonexistence proof

This note records a source audit of Giovanni Esposito, *Global Nonexistence of
Odd Distinct Covering Systems*, Zenodo record `10.5281/zenodo.18440762`,
downloaded 22 September 2026. The record claims to prove the unrestricted
Erdős--Selfridge assertion. The claim does not provide a valid proof of the
original quantifiers.

The downloaded `Paper_I.pdf` has SHA-256
`9797688b82fefd76df386ec17bb5b9810993acb23e95d983f4f7cbd6be6728c4`.

## 1. The missing kernel-localization theorem

The proof starts from a deficit in

\[
  \mathbb Z/(3^2 5^2 7^2)\mathbb Z
\]

and then says, without a proof, that every hypothetical ODCS has a finite
kernel to which this deficit can be applied. Every *finite* family trivially
has a finite set of prime divisors, but that fact does not put its prime set
inside `{3,5,7}`, nor does it produce a quotient map preserving the stated
deficit. Hough's minimum-modulus theorem supplies a bound on a smallest
modulus; it does not supply this radical reduction. Thus the first step does
not cover arbitrary prime support.

The paper's own overview (Zenodo `18438393`) describes the uniform fixed-radical
obstruction as a remaining frontier. That is incompatible with using the
`{3,5,7}` certificate as an unconditional starting point for every ODCS.

## 2. The allocation lemma has a narrower hypothesis than an ODCS extension

The proposed extension argument treats every new class as either a single
`q`-fiber or as `q*d` with `d` in the old divisor set. An arbitrary distinct
odd family can also contain

\[
 q^e d\quad(e\ge 2),
 \qquad q_1q_2d,
 \qquad q_1^{e_1}q_2^{e_2}d,
\]

with independently chosen residues. The numerical moduli `q*d`, `q^2*d`,
and `q^3*d` are distinct, so numerical distinctness does not make them one
available copy of `d`. Consequently the asserted partition of the old set
`D` among the uncovered fibers is not a consequence of distinctness. A proof
covering all prime-power and multi-new-prime extensions would need a separate
capacity argument; none is supplied.

## 3. The renormalization inequality has the wrong sign

Paper G defines

\[
 E_e(y)=\sum_{u\in G_e}y(u),
 \qquad
 S_e(y)=\sum_{d\mid M_e}\sup_a\sum_{x\in C(d,a)}y(x),
 \qquad
 \beta_e(y)=S_e(y)/E_e(y).
\]

For the pullback lift `Ly`, every old coset has each of its points repeated in
`K=|G_{e+1}|/|G_e|` fibers. Hence

\[
 E_{e+1}(Ly)=K E_e(y),
 \qquad
 S_{e+1}^{\rm old}(Ly)=K S_e(y).
\]

The new-divisor terms are nonnegative. Therefore the definitions give

\[
 S_{e+1}(Ly)\ge K S_e(y),
 \qquad
 \beta_{e+1}(Ly)\ge\beta_e(y),
\]

before any additional normalization. The claimed strict decrease
`beta_(e+1)(Ly) < beta_e(y)` does not follow from the stated damping bound;
the bound controls each new coset, but does not make the aggregate new supply
negative. This independently blocks the claimed bounded-radical
non-liftability theorem.

## 4. The finite-radical attachment is not evidenced by the cited record

The Zenodo record `10.5281/zenodo.18438201`, cited in the program overview as
the finite-radical certificate, supplied a file named `2012.01677v1.pdf`.
Its title is *On the Critical Exponent for k-Primitive Sets* by Ho Chan,
Duker Lichtman, and Pomerance (arXiv:2012.01677), rather than a finite-radical
covering certificate. The downloaded file has SHA-256
`a5071f3436410b7790bc762b5bb35d3874b5a062b75f8d73270a11076914d0cc`.
Thus that record, as served, cannot substantiate the stated theorem.

## 5. Compactness does not repair the quantifiers

The final appeal to a profinite intersection would be valid only after one
has a nested sequence of nonempty clopen survivor sets for the *same finite
family of constraints*. A point of \(\widehat{\mathbb Z}\) obtained from an
infinite tower need not be an ordinary integer. More basically, an ODCS is a
finite family, so “infinite prime incidence” is not a third case of an ODCS;
it is a proposed limit of different finite families and requires a separate
uniform theorem.

## Status

This audit refutes the cited argument as a proof of unrestricted
Erdős--Selfridge #7. It does not settle #7 in either direction. The verified
project results remain restricted to finite-prime/support geometries and
conditional source transports; the unrestricted statement remains open.

