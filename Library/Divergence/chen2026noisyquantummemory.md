---
bibkey: chen2026noisyquantummemory
authors: Miaojiang Chen; Wenjing Xiao; Haiqiang Chen; Jiarong Liang; Anfeng Liu; Zhenrong Zhang; Athanasios V. Vasilakos; Saif Al-Kuwari; Ahmed Farouk; H. Herbert Song
year: 2026
title: Noise threshold for learning with quantum memory
doi: 10.48550/arXiv.2611.34474
url: https://arxiv.org/abs/2611.34474v1
claim: "Conjecture 1 asks whether the unoptimized sandwiched Rényi-2 coherent information is additive for Pauli memory channels."
strata_touched:
  - D5/S3/Quantum/Information/NoisyMemory/ParityResolventChord
  - D5/S3/Quantum/Information/NoisyMemory/StabilizerProductTilt
license: citation-only
triage: anchor
---

# Noise threshold for learning with quantum memory

## Verified locator

- [Pinned arXiv record](https://arxiv.org/abs/2611.34474v1) and [DOI](https://doi.org/10.48550/arXiv.2611.34474).
- [Conjecture 1](https://arxiv.org/html/2611.34474v1#Thmconjecture1) gives the all-input Pauli-channel additivity question. [Eq. (15)](https://arxiv.org/html/2611.34474v1#Sx4.E15) computes the collision quantity for stabilizer-code probes.

## Dephasing with arbitrary inputs

For a bipartite density operator \(\rho_{RB}\), put
\(F(\rho,\sigma)=\operatorname{Tr}(\rho\sigma^{-1/2}\rho\sigma^{-1/2})\)
with inverses on the support of \(\sigma\).
Take \(\sigma=I_R\otimes\rho_B\) to recover the collision quantity \(K\)
from Eq. (1). Let \(D_a\) preserve the even block and attenuate the odd
block by \(a\) under conjugation by a self-adjoint unitary. On a qubit
this is dephasing in its corresponding basis.

The collision quantity has an upper chord under simultaneous
attenuation of the state and its reference,
\[
 F(D_a\rho,D_a\sigma)\le
 (1-a^2)F(D_0\rho,D_0\sigma)+a^2 F(\rho,\sigma),\qquad 0\le a\le 1.
\]
To see this, first take \(\sigma\) strictly positive. The geometric
kernel on Hilbert–Schmidt space is the arcsine average of
\((tL_\sigma+(1-t)R_\sigma)^{-1}\). The scalar integral for positive
eigenvalues \(x,y\) is
\[
 \frac{1}{\pi}\int_0^1\frac{dt}{\sqrt{t(1-t)}[tx+(1-t)y]}=(xy)^{-1/2}.
\]
For each resolvent, the parity splitting gives diagonal blocks
independent of \(a\) and off-diagonal blocks multiplied by \(a\).
The source has odd component \(a r_-\). The inverse quadratic form
maximizes \(2\operatorname{Re}\langle v,r\rangle-\langle v,Av\rangle\).
Scaling the odd trial vector by \(a\) makes this expression affine
in \(a^2\), giving the upper chord by comparing the two suprema.
Regularize \(\sigma\) by \(\varepsilon I\) and pass to the limit on
the support. The joint state is supported on
\(I_R\otimes\operatorname{supp}\rho_B\) by positivity.

Applying the chord at successive qubits with attenuations \(a_i\)
bounds \(K_m\) by a weighted average over untouched sites. A site
is untouched with probability \(a_i^2\). Complete dephasing on the
other sites stores the outcomes of rank-one measurements in
orthogonal flags. Conditional on an outcome, the reference and
the untouched qubits remain in a pure state. For a set \(J\) of
untouched sites, the Schmidt coefficients give
\((\operatorname{Tr}\sqrt{\rho_{B_J}})^2\le 2^{|J|}\).
Averaging gives
\[
 \max_W K_m(W)=\prod_i(1+a_i^2).
\]
The equality uses a product of Bell probes. Signed attenuations
give the same value by a local Pauli conjugation. In the homogeneous
case this establishes Conjecture 1 on the dephasing family for
arbitrary memory marginals.

Lean checks the quadratic variational identity and the upper chord
for the parity blocks. The resolvent integral, support limit and
tensor-product quantum application use the analytic argument above.
The literature search found the positive resolvent representation
and general contraction results. Priority for the composed
sharp dephasing result remains unverified.

[Conjecture 1](https://arxiv.org/html/2611.34474v1#Thmconjecture1) ·
[Temme et al., quantum chi-square divergence](https://arxiv.org/abs/1005.2358) ·
[Hiai et al., resolvent representations](https://arxiv.org/abs/1212.1337) ·
[Hiai and Ruskai, noisy-channel contraction](https://arxiv.org/abs/1508.03551)

## Stabilizer codes with independent bit and phase errors

At site \(i\), let the two independent flip probabilities be \(x_i,z_i\).
Write \(p_i=(1-2x_i)^2\), \(q_i=(1-2z_i)^2\) and
\(\kappa_i=(1+p_i)(1+q_i)/2\). For stabilizer-code probes, the sharp
upper bound is \(\prod_i\max(1,\kappa_i)\). The maximization allows the
number of logical qubits to vary across codes.

Let \(D\) be the binary stabilizer subspace and \(C=D^\perp\) its
symplectic orthogonal. For a uniform \(A\in C\), logical label
\(L=A+D\), and observation \(Y=A+E\), the right side of Eq. (15)
is \(2^k\mathbb E\|P(L\mid Y)\|_2^2\). Each conditional
binary symmetric channel with attenuation \(a\) increases this
posterior moment by at most the increase from revealing the bit
with probability \(a^2\). For a conditional input probability
\(t\) and output probability \(s\),
\(s(1-s)=(1-a^2)/4+a^2t(1-t)\ge t(1-t)\).
The posterior variance comparison remains valid after conditioning
on all other outputs, so the erasure comparison iterates.

For a reveal set \(J\), define \(d(J)\) as the dimension of logical
information recovered by the coordinate projections. It equals
\(\operatorname{rank}\pi_J C-\operatorname{rank}\pi_J D\). Increasing
\(J\) by one coordinate raises \(d\) by at most one.
The complementary projection rank identity gives
\(d(J)+d(\tau(J^c))=2k\), where \(\tau\) exchanges the bit and phase
coordinates at each site. If \(r\) contains the reveal probabilities
\(p_i,q_i\), set \(w_j=1-r_{\tau(j)}\). For \(f=2^d\), the square of
the erasure bound is \(\mathbb E_r f\,\mathbb E_w(1/f)\).

The Boolean product theorem bounds these reciprocal moments by
\(\prod_j\max(1,(1+r_j)(1-w_j/2))\). Conditioning on one coordinate
reduces to the ratio of two positive conditional averages in
\([1,2]\). The resulting scalar function is an affine function
plus a nonnegative multiple of the reciprocal, so the maximum
occurs at an endpoint. The two factors per site give
\(\max(1,\kappa_i)^2\). A Bell probe or a pure stabilizer probe on
each site realizes the corresponding maximum.

Lean checks the product inequality. The stabilizer posterior and
symplectic identifications and the sharp channel endpoint above
use the analytic argument. This includes the independent-noise
CSS case discussed in the paper. The pinned main source refers to
Supplement S7. The supplementary equation itself was unavailable,
so the attribution is to the specialization of Conjecture 1 and
the collision formula in Eq. (15).

[Eq. (15)](https://arxiv.org/html/2611.34474v1#Sx4.E15) ·
[Polyanskiy and Wu, channel comparison and tensorization](https://arxiv.org/abs/1508.06025v4) ·
[Bravyi and Terhal, stabilizer cleaning](https://arxiv.org/abs/0810.1983v2)

## Stabilizer codes with correlated Pauli errors

The stabilizer bound also holds for site-dependent Pauli spectra whose
three eigenvalues, after a Pauli translation, are nonnegative numbers
\(x,y,z\) satisfying \(x\ge yz\), \(y\ge xz\), and \(z\ge xy\).
The single-site factor is \(\max(1,\kappa)\) with
\(\kappa=(1+x^2+y^2+z^2)/2\). Positive depolarizing attenuations
satisfy these inequalities.

In the binary two-dimensional character space, set \(r_g=\lambda_g^2\)
for each nonzero character, \(s=\sum_{g\ne0}r_g\), and \(c=xyz\).
A substitute observation reveals a random character subspace \(H\).
The probabilities for the full space, each line \(g\), and the zero
space are \(c\), \(r_g-c\), and \(1-s+2c\), respectively.
The last expression is the determinant of the Gram matrix of the
constant and two independent characters of the error variable.

The posterior moment is the supremum of a quadratic objective
\(\sum_{\ell,y}(2v_\ell(y)P(\ell,y)-v_\ell(y)^2P(y))\).
In Fourier coordinates, substitute test coefficients
\(\widehat v(g)=\lambda_g\widehat u(g)\). The linear coefficients
are multiplied by \(\lambda_g^2\). A surviving quadratic interaction
with indices \(g,h,g+h\) is multiplied by
\(\lambda_g\lambda_h\lambda_{g+h}\). These are exactly the inclusion
probabilities of the corresponding character spans in \(H\). Thus
the noisy moment is bounded by the average optimum of the substitute
observations. If some eigenvalues vanish, the live characters form a
subgroup. Averaging trial functions over its annihilator leaves the
linear term unchanged and can only improve the negative quadratic
term. This handles the zero eigenvalues.

For product subspaces, symplectic complement exchanges zero and full
space on each site and fixes the three lines. The same rank identity
gives the reciprocal product of moments. At one site, divide the
conditional averages by the one at the zero subspace. In base-two
logarithms their line values \(u_g\) and full-space value \(v\) satisfy
\(0\le u_g\le 1\) and \(u_g\le v\le u_g+1\).
The product with the complementary reciprocal average is a
nonnegative sum of exponentials of affine functions of these logs.
Its maximum occurs at a vertex. The vertices at \(v=0\) and \(v=2\)
give \(1\) and \(\kappa^2\). At \(v=1\) the value is
\((1+b)(1-(b+1-s+c)/2)\) with
\(b=c+\sum_{g\in J}(r_g-c)\) for a subset of lines \(J\).
Complementing \(J\) leaves this expression unchanged. For \(J\) empty,
the Gram determinant bound gives a value at most \(\kappa\).
For a singleton with square \(u\), write the other squares \(a,b'\).
The spectral inequalities give \(a\ge u b'\) and \(b'\ge u a\), hence
\((1+u)^2 a b'\ge u(a+b')^2\).
This gives \(c\ge u(s-u)/(1+u)\), which bounds the vertex value by
\(\kappa\). Induction over sites proves the sharp product bound.
A Bell or pure stabilizer probe at each site attains it.

The physical negative depolarizing interval \([-1/3,0]\) is a
mixture of complete depolarization and three basis pinchings with
output Pauli flips. At attenuation \(-a\) the mixture has weights
\(1-3a\) and \(a\) for each pinching. Revealing the independent
mixture choices can only increase the squared posterior norm by
conditional Jensen. Conditional on these choices, the channels
obey the spectral inequalities after Pauli translations, and
each of the four possibilities has single-site factor one.
The same product bound therefore applies with any combination of
negative depolarizing sites and the allowed nonnegative spectra.

The correlated extension is analytic. The search found no identical
statement in the reviewed literature. The priority question remains
open, as does the unrestricted Pauli conjecture.

[Conjecture 1](https://arxiv.org/html/2611.34474v1#Thmconjecture1) ·
[Eq. (15)](https://arxiv.org/html/2611.34474v1#Sx4.E15)
