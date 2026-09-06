* DLMF 5.7.6, digamma partial fractions, and the Gamma integral and recurrence,
  for the elementary resolvent and Mellin computations.

---

## [PR #5602] ARITHMETIC_FOURIER_DUAL_TAIL_AND_CERTIFIED_ZERO_COUNT

# 2026-09-06: effective arithmetic dual observations and a counted simple ground-transform zero

Lean: `D5/S3/Weil/ZetaBridge/WeilArithmeticFourierDualTail.lean`.
Scribe: `Blueprint/D5/S3/Weil/ZetaBridge/WeilArithmeticFourierDualTail.scribe.cs`.
Executed checker: `research/weil_ground_mode/certify_prime3_directional.py`.
Actual replay output: `research/weil_ground_mode/prime3_directional_certificate.json`.

The open problem is still CCM, arXiv:2511.22755v1, Section 8: prove simple-even
actual Weil ground modes and sufficient approximation by the explicit prolate
model on an unbounded scale family. The present increment makes the arithmetic
correction in (CO26) effectively computable, then certifies a local zero count
for the actual fixed-window ground transform. It does not identify that zero
with a Xi zero. The infinite operator/domain and variational implications
below are paper proofs; the new Lean script proves the concrete infinite
arithmetic series estimate. Lean and Scribe compilation were not run.

## 1. Cross-author input determines the mathematical deliverable

loning's merged PR #5326, head 3beb435bf9ca8aa35aa6079ea4033a9c2e6c9007,
separates a boundary Rouché inequality from a Schur floor and distinguishes
behavioral Hankel minimality from determinant preservation. His #5296 also
keeps dominant-channel boundary transversality separate from spectral
splitting. These are relevant warnings against inserting an unproved
arithmetic determinant or taking absolute values before signed couplings
have been combined.

AlyciaBHZ's draft #5882, head e89269583d0b05b24dca01939ae7245b62b12c35 at
inspection, already develops complex projective Rayleigh recovery and sharp
scalar readout bounds. We do not add a second generic projection owner.
The preceding (CO26)-(CO28) specifies the actual Weil Fourier correction
but had no evaluated arithmetic dual tail. Here the new owner uses the
existing actual symbol, proves an infinite-tail rate, and feeds a checker
that produces a strict complex-boundary zero-count certificate.
Classical Schur, Cauchy-Schwarz and Rouché principles are not claimed as
new results. The specific arithmetic evaluation and its quantified consumer
are the mathematical deliverable.

## 2. Keep the actual even coordinate normalization

Use the same L=2a=log(c), plus-sign Fourier transform, and basis e_n of (AC2).
For the unnormalized even basis set psi_0=e_0 and psi_n=e_n+e_-n for n>0.
Its mass matrix is M_0=diag(1,2,...,2). For an exterior positive index m>N,
the coupling row C^+ from low even coordinates to the e_m coordinate is

\[
 C^+_{m0}=-\frac{s_c(m)}{\pi m},\qquad
 C^+_{mn}=\frac{2(ns_c(n)-ms_c(m))}{\pi(m^2-n^2)}\quad(n>0).
 \tag{DZ1}
\]

This follows by adding the actual entries A_mn and A_m,-n and using the
proved oddness of s_c. In particular no abstract row is substituted.
The Fourier rows are

\[
 f_0(z)=\frac{2\sin(Lz/2)}{\sqrt L\,z},\qquad
 f_n(z)=\frac{4z\sin(Lz/2)}{\sqrt L\,(z^2-(2\pi n/L)^2)}\quad(n>0).
 \tag{DZ2}
\]

They equal the entire transforms away from the displayed removable poles.
The certified disk below lies strictly away from those poles. Even high
coordinates have energy 2*sum D_m*|y_m|^2 and readout sum f_m*y_m. Thus the
pure high dual energy has the factor 1/2 in sum |f_m|^2/(2D_m), while the
low correction is sum C^+_mn*f_m/D_m with no additional factor two.

## 3. New Lean theorem: the actual arithmetic dual tail is summable

Let c>=2, 0<=n<M be natural numbers, m=M+j+1, energy(j)>=beta>0, and
w be complex with |w|<=M/2. Define the explicit summand

\[
 T_j=\frac{ns_c(n)-ms_c(m)}{(m^2-n^2)\,\operatorname{energy}(j)\,(m^2-w^2)}.
\]

The existing arithmetic source proves |s_c(n)|<=B_c independently from its
prime, pole and absolutely convergent Gamma terms. The new main declaration
`arithmetic_even_fourier_dual_tail_bound` proves

\[
 \boxed{\sum_{j\ge0}|T_j|<\infty,\qquad
 \left|\sum_{j\ge0}T_j\right|\le
 \frac{2B_c}{3\beta M(M-n)}.}
 \tag{DZ3}
\]

No spectral gap, zero configuration, desired dual bound or Xi convergence
is an input. The energy hypothesis is just an explicit positive scalar
floor for the chosen diagonal comparison weights. Their applicability to
an actual operator must be proved independently, as (CO8) does here.

For completeness, the proof uses the exact difference of squares:

\[
 \left|\frac{ns_c(n)-ms_c(m)}{m^2-n^2}\right|\le\frac{B_c}{m-n},
 \quad |m^2-w^2|\ge\frac34m^2,
 \quad m-n\ge\frac{M-n}{M}m.
\]

Consequently |T_j|<=4*B_c*M/(3*beta*(M-n))*m^(-3). The identity

\[
 \frac1{2x^2}-\frac1{2(x+1)^2}-\frac1{(x+1)^3}
 =\frac{3x+1}{2x^2(x+1)^3}\ge0\quad(x>0)
\]

proves both summability and sum_{m>M}m^(-3)<=1/(2M^2), by bounded positive
partial sums and telescoping. Applying the triangle inequality to the
absolutely convergent complex series gives (DZ3).

For the physical observation put w=L*z/(2*pi), and t_0=1, t_n=2 for n>0.
Combining (DZ1)-(DZ3) gives the effective missing dual component

\[
 \boxed{\left|\sum_{m>M}\frac{C^+_{mn}f_m(z)}{D_m}\right|
 \le\frac{2t_nB_cL^{3/2}}{3\pi^3\beta M(M-n)}
 |z\sin(Lz/2)|.}
 \tag{DZ4}
\]

The pure high component follows from the previously proved even observation
bound, equivalently from (DZ2) and sum_{m>M}m^(-4)<=1/(3M^3):

\[
 \sum_{m>M}\frac{|f_m(z)|^2}{2D_m}
 \le\frac{8L^3}{27\pi^4\beta M^3}|z\sin(Lz/2)|^2.
 \tag{DZ5}
\]

Both inequalities cover the entire uncomputed tail, for arbitrary complex
z in the stated band, and retain the exponential complex-frequency weight.

## 4. Constrain the low inverse to the actual candidate-orthogonal space

Let ell<=lambda_0<=mu<U<T be certified for the same normalized candidate k
and actual lowest eigenvector u. Put alpha=<k,u> and e=u/alpha-k. The
projective argument in (RE2)-(RE4) gives alpha!=0, e perpendicular to k,
and ||e||^2<1. Its exact energy identity therefore yields

\[
 q(e)-\ell\|e\|^2=(\mu-\lambda_0)
 +(\lambda_0-\ell)\|e\|^2\le U-\ell.
 \tag{DZ6}
\]

Use explicit high weights D_m=beta_m-T>0. They also bound the high part of
q-ell*||.||^2, since ell<T. In the coordinates of Section 2 suppose the
complete weighted coupling satisfies 2*(C^+)^*D^-1*C^+<=Gbar, and put
S=A_even-ell*M_0-Gbar. For e=x+y, Schur completion gives

\[
 x^*Sx+2\sum_{m>N}D_m|y_m+(C^+x)_m/D_m|^2\le U-\ell.
 \tag{DZ7}
\]

For the actual dyadic candidate v, v_0 is nonzero. Set p_i=2v_i/v_0 and
let P have columns E_i-p_i*E_0, i=1,...,N. This parameterizes exactly the
low space perpendicular to k in the correct mass matrix. Define

\[
 J=P^*SP,\qquad
 a_n(z)=f_n(z)-\sum_{m>N}C^+_{mn}f_m(z)/D_m,\qquad h(z)=P^Ta(z).
\]

When the actual J is positive definite, Cauchy-Schwarz in the direct-sum
energy coordinates of (DZ7) gives

\[
 \boxed{|\widehat e(z)|^2\le(U-\ell)\mathcal D(z),\qquad
 \mathcal D(z)=h(z)^*J^{-1}h(z)+\sum_{m>N}\frac{|f_m(z)|^2}{2D_m}.}
 \tag{DZ8}
\]

J is real symmetric. Thus the row-functional conjugation convention gives
the same inverse quadratic form in (DZ8). This removes the candidate line
exactly rather than paying for an arbitrary lifted inverse direction.
All high pairings are well-defined: the high form dominates D, D^-1 is
bounded, C^+ has finite domain and square-summable images, and (DZ3)-(DZ5)
prove the needed dual convergence. No domain of A^2 is assumed.

## 5. Executed arithmetic realization at c=3

Keep L=log3, N=64, M=32768, and the same fixed 129-entry even dyadic
candidate from `certify_prime3_refined.py`. The checker re-certifies

\[
 \ell=\frac{11}{200000000},\quad
 U=\frac{560909}{10^{13}},\quad T=\frac1{200000}.
 \tag{DZ9}
\]

The even high weights use (CO8). The odd threshold is rechecked using the
original all-parity lower bound beta>1 and full unweighted coupling.
Nine positive-mode shells have integer endpoints 65..128, 129..256, ...,
16385..32768. Their dyadic floors are chosen strictly below the directed
interval for log(n/L)-L/(pi*n)-log2/sqrt2 at the first shell index; this
lower expression is increasing. Every resolvent uses beta_shell-T, so the
same majorant also applies at ell. The far energy after subtraction of T
is bounded below by 502427869/51200000.

Four interval LDL tests pass: odd threshold, even full lower, even
candidate-orthogonal threshold, and the exact constrained J. They establish
the hypotheses used in (DZ6)-(DZ8) with every omitted high mode accounted
for. Their pivots certify positivity and are not eigenvalue lower bounds.
The resulting state-space bound is only ||e||^2<=10909/49450000<1/2500.
This is deliberately not advertised as an improvement of (CO10); the goal
is the actual scalar output near a zero.

All quantized Gram products use exact integers and checked intermediate
int64 bounds. The ordinary Gram hash remains
`7f4e1049624807432efe96a68fe63babbc1c3bd37f2d40600a4cddadbddb85a9`.
The weighted and unweighted error budgets are respectively
4/152587890625 and 1/10^10; the full second-jet scalar tail is below 9/10^13.

A new exact endpoint accumulator avoids unchecked floating reductions in
the directional sums. It decodes each finite binary64 endpoint as a signed
integer significand times a power of two, shifts to a common exponent,
adds Python integers, and converts the exact result outward into iv only
at the end. Signed zero and subnormal inputs are handled. Thirty-four
regressions against exact Fraction sums, including severe cancellation,
pass. The interval primitives, special-function remainders and interpreter
remain trusted numerical infrastructure, not Lean-certified software.

## 6. A strict complex-disk Rouché certificate

Let F=Fourier(u/alpha), K=Fourier(k), and set the exact rational center and
radius

\[
 z_0=\frac{2827}{200}=14.135,\qquad r=\frac1{250}=0.004.
\]

The checker encloses (DZ8) on the entire complex square
|Re z-z_0|<=r, |Im z|<=r containing the closed disk. The band L*|z|<pi*N
is separately checked. Computed quantities satisfy

\[
 \sup\mathcal D(z)<0.536805,\qquad
 \sup|F(z)-K(z)|<2.42\cdot10^{-5}.
 \tag{DZ10}
\]

The entire high observation energy is at most 4.601986*10^-7, and each
uncomputed dual correction is at most 1.995*10^-10. These are rounded
outward displays of the directed bounds; the verifier uses the full
interval comparisons.

Use the independently computed affine function
Q(z)=K(z_0)+K'(z_0)*(z-z_0). The actual candidate gives

\[
 K(z_0)=2.3040934104782876\ldots\cdot10^{-6},\quad
 K'(z_0)=0.0101016602716698139\ldots>0.
\]

On the disk boundary,

\[
 |Q(z)|\ge r|K'(z_0)|-|K(z_0)|>3.81\cdot10^{-5}.
 \tag{DZ11}
\]

Since ||k||=1 and integral_I x^4 dx=L^5/80, differentiating the compactly
supported Fourier integral twice gives the uniform Taylor remainder

\[
 |K(z)-Q(z)|\le\frac{r^2}{2}e^{ar}\sqrt{L^5/80}
 <1.14\cdot10^{-6}.
 \tag{DZ12}
\]

Equations (DZ10)-(DZ12) imply |F-Q|<|Q| on the full circle, with actual
strict interval margin greater than 1.2769*10^-5. The affine root is inside
the disk because r|K'|>|K|. Rouché gives exactly one zero of F there, counted
with multiplicity. The actual simple-even ground line can be chosen real,
and the candidate is real, so F respects conjugation. Uniqueness in this
conjugation-invariant disk forces the zero to be real; multiplicity one
forces it to be simple. Evenness yields the reflected conclusion:

\[
 \boxed{\text{Each of }|z-14.135|<0.004\text{ and }|z+14.135|<0.004
 \text{ contains exactly one simple real zero of }F.}
 \tag{DZ13}
\]

The positive zero lies in (14.131,14.139). We do not claim it is the first
positive zero, since smaller frequencies have not been globally excluded.
No Xi evaluations, zeta-zero positions or eigensolver enter the checker.
The center is a fixed rational examination window, not a supplied zero
identity. The argument counts zeros of the actual infinite-dimensional
ground transform through the full-form certificate, rather than counting
only roots of the finite candidate transform.

## 7. Replay, formal scope and the remaining arithmetic problem

Final checker SHA-256:
`4343355f261f800e77b518244946b311eae3a656e79dcf9b6421d901382dfc4b`.
Pinned arithmetic dependency SHA-256:
`8bb067fc5499b0f2e1e48836e7a82237a15504109f82a856c72478d1096d69d0`.
The final source was replayed successfully, and its remote Git blob equals
the local replay source. The recorded JSON belongs to that exact source.
Both the executable inequality and the elementary all-scale series proof
have been reviewed. There was no Lean/lake or Scribe compiler in this runtime.
No kernel acceptance or executed #print axioms report is asserted.

The new Lean declaration proves (DZ3) and absolute convergence using the
actual arithmetic symbol. (DZ4) is its paper Fourier normalization,
(DZ6)-(DZ8) are the paper operator/variational transport, and (DZ9)-(DZ13)
are the executed interval realization and its Rouché consequence. These
layers must not be confused with an end-to-end Lean theorem about A_a.

This removes one concrete unresolved quantity from (CO26): the arithmetic
infinite dual correction now has a complete effective tail estimate and an
executed consumer. It does not remove the main scale-family obligation.
For the explicitly constructed prolate family of (CO20), one must still
establish actual simple-even coercivity and prove, on each compact substrip K,

\[
 |c_a|^2(U_a-\ell_a)\sup_{z\in K}\mathcal D_a(z)\longrightarrow0.
 \tag{DZ14}
\]

The dyadic c=3 candidate has not been identified with that prolate family.
The local counted zero in (DZ13) is not a new result about the zeros of Xi.
It is a concrete, reproducible test of the analytic approximation mechanism
required by CCM's open problem. The next mathematical work is to evaluate
these same signed observations on an explicit growing-scale candidate
family, rather than to add another general positivity or RH-implication
wrapper. No novelty priority or completion of RH is claimed.

References and source interfaces:

* Connes, Consani, Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755v1,
  Sections 4, 7 and 8; the simple-even and model-approximation tasks are
  explicitly distinguished in Section 8.
* Connes, Consani, *Spectral triples and zeta-cycles*, arXiv:2106.01715v1,
  Lemma 2.2 and Proposition 2.3, for the actual Weil form core.
* Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096,
  for the same closed form and Friedrichs interface.
* loning, trureturing PR #5326, Sections C14-C15, and #5296, the separate
  boundary-transversality obligation. Neither theoretical transfer is
  treated as a proved identity with this Weil ground transform.
* AlyciaBHZ, trureturing PR #5882, complex projective recovery and readout
  sharpness; those general results are not duplicated in the new owner.
