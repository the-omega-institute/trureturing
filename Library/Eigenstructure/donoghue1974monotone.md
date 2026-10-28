---
bibkey: donoghue1974monotone
authors: William F. Donoghue Jr.
year: 1974
title: "Monotone Matrix Functions and Analytic Continuation"
doi: 10.1007/978-3-642-65755-9
url: https://doi.org/10.1007/978-3-642-65755-9
claim: "Classical Pick and Loewner theory relates holomorphic functions with nonnegative imaginary part to positive kernels and positive boundary derivative matrices."
strata_touched:
  - D5/S3/Quantum/Matrix/AnalyticPickKernel
  - D5/S3/Quantum/Matrix/AnalyticPickHankel
license: citation-only
triage: anchor
---

# Analytic Pick kernels and boundary Hankel matrices

Donoghue's book treats the classical analytic continuation and matrix positivity theory. The title, author and DOI identify the book; Crossref lists its publication year as 1974. A further standard reference for positive kernels is J. Agler and J. E. McCarthy, *Pick Interpolation and Hilbert Function Spaces*, Graduate Studies in Mathematics 44, AMS, 2002, DOI [10.1090/gsm/044](https://doi.org/10.1090/gsm/044).

For a holomorphic finite matrix function G with G(z)+G(z)* positive semidefinite on the unit disk, the full block kernel

$$
L(z,w)=\frac{G(z)+G(w)^*}{1-z\overline w}
$$

is positive. The companion formalization proves this by the Banach-valued Cauchy circle formula, positivity of the average of C* (G+G*) C, and radial closure. It assumes neither a positive-kernel conclusion nor a representing measure, and requires no regularity on the unit circle.

The domain Cayley map sends u to i(1+u)/(1-u). Applied to G(u)=-i T(i(1+u)/(1-u)), it proves positivity of the full finite block Pick kernel

$$
K(z,w)=\frac{T(z)-T(w)^*}{z-\overline w}
$$

for a holomorphic matrix function T on the upper half-plane with nonnegative Hermitian imaginary part. The diagonal gauge is K=(1/2) C L C*, with C having diagonal entries 1-u.

At a real analytic continuation point, with T Hermitian on a real neighborhood, normalized Taylor coefficients c_k=T^(k)(0)/k! give the positive semidefinite block matrix with rows (c_1,c_2) and (c_2,c_3). This is a classical boundary confluence result. The matrix-valued Cauchy and limit proofs here are formal implementations of that theory, with no claim of mathematical novelty.

Applying this result to principal fractional powers of noncommuting matrix pencils additionally requires global holomorphy, the upper-half-plane imaginary-part inequality, and identification with the actual real-axis power. Those supplier statements are separate. These analytic results do not settle the He–Saunderson–Fawzi conjecture for independent X,Y.
