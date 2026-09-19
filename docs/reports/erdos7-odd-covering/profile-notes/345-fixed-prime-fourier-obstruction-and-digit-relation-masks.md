[Index](../marked_head_profile.md) · [Character moment tests](344-original-fourier-moments-and-finite-probe-obstructions.md) · [Exact conditional redundancy](341-conditional-future-avoidance-controls-the-current-prefix.md)

# Fixed-prime Fourier obstruction and digit-relation masks

For every fixed prime `p>=7`, an actual irredundant family of distinct odd
original moduli can have a conditional hole of mass `1/p`, while every
fixed-size additive-character moment block becomes positive definite as
the residual prime-power height grows. All primitive coefficients are
nonzero, and no proper prime-power cylinder is completely covered. A
joint digit relation nevertheless detects the hole with a fixed number
of running states.

This strengthens344's probe obstruction by keeping both the future prime
and conditional hole mass fixed. It is not a new unrestricted noncoverage
theorem, nor a failure of all low-order original-label incidence tests.
The original families have explicit uncovered integers. Their old-fibre
mass and complete original moduli are retained below.

## 1. The finite relation and its proper-prefix marginals

Fix a prime `p>=7` and an integer `t>=1`. Put `n=p^t`, `m=p^(t+1)` and write

\[
r=\sum_{j=0}^{t-1}a_jp^j,\qquad
f_t(r)=\sum_{j=0}^{t-2}a_ja_{j+1}\pmod p,\qquad 0\le r<n.
\]

For `t=1` the sum is zero. There is no parity restriction or additional
endpoint term. Define

\[
A_t=\{r+n f_t(r):0\le r<n\},\qquad
M_t=2\mathbf1_{A_t^c},\qquad g_t=M_t-1.
\]

Expectations in Sections1--4 use the same uniform probability on the
complete residual group `Z/mZ`. There is exactly one missing top digit
above each lower-digit tuple, so

\[
\Pr(A_t)=1/p,\qquad \mathbb E g_t=1-2/p>0.
\]

Every proper prefix `z=a mod p^e`, `0<=e<=t`, contains exactly `p^(t-e)`
holes among `p^(t+1-e)` points. Its conditional hole ratio is also `1/p`.
In particular, the positive support contains no full top `p`-cycle and
no nonempty coset of a proper lower conductor.

## 2. Every nonzero additive Fourier coefficient becomes small

Use the convention

\[
\widehat g_t(k)=\frac1m\sum_zg_t(z)\zeta_m^{-kz},
\qquad \omega=\exp(2\pi i/p).
\]

For `k!=0 mod m`,

\[
\widehat g_t(k)=-\frac2m\sum_{r<n}
\zeta_m^{-kr}\omega^{-k f_t(r)}.
\]

If `p|k`, the second phase is one and the remaining sum is a nontrivial
`n`-th-root geometric sum, hence zero. If `p` does not divide `k`, define
for `|z|=1`

\[
P_{t,b}(z)=\sum_{r<p^t}
\omega^{-k(f_t(r)+ba_{t-1})}z^r,
\qquad b\in\mathbb Z/p\mathbb Z,
\]

and set `P_(0,b)=1`. Appending a highest lower digit gives

\[
P_{t+1,b}(z)=\sum_{j=0}^{p-1}
\omega^{-kbj}z^{jp^t}P_{t,j}(z).
\]

The matrix with entries `omega^(-kbj)` has conjugate-transpose product
`pI`. The diagonal phases have modulus one. Starting with squared norm
`p`, induction therefore gives the exact identity

\[
\sum_b|P_{t,b}(z)|^2=p^{t+1}=m.
\]

Taking `b=0` and `z=zeta_m^(-k)` proves, for every nonzero frequency,

\[
\boxed{|\widehat g_t(k)|\le2/\sqrt m.}
\]

This is a finite instance of the Hadamard/Rudin--Shapiro construction.
The standard input is Allouche--Liardet, *Generalized Rudin--Shapiro
sequences*, Acta Arith.60(1991),1--27,
[DOI10.4064/aa-60-1-1-27](https://doi.org/10.4064/aa-60-1-1-27):
Definition2.4 on p.10 and the transfer recurrence and equation(11) on
p.12. These primary passages have been checked. The elementary
specialization above states its full phase convention and exact constant;
it is not presented as new Rudin--Shapiro theory.

## 3. Nonvanishing does not give a height-independent probe margin

For an integer polynomial `C` of degree less than `m`,

\[
\Phi_m(X)=\sum_{j=0}^{p-1}X^{jn}
\]

divides `C` exactly when the `p` coefficients `C_(r+jn)` are all equal
for every `r<n`. Indeed the quotient has degree less than `n`, and
multiplication replicates each quotient coefficient into those positions;
conversely the equal columns construct the quotient. Irreducibility of
the cyclotomic polynomial makes this equivalent to vanishing at any
primitive `m`-th root.

Each column of `g_t` has one `-1` and `p-1` entries `1`. Each column of
`M_t` has one zero and `p-1` entries `2`. Consequently every primitive
Fourier coefficient of either function is nonzero. Small amplitude is
not a numerical zero or a complete-cycle cancellation.

The total nonconstant energy does not shrink. Parseval and `g_t^2=1`
give

\[
\sum_{k\ne0}|\widehat g_t(k)|^2=4(p-1)/p^2.
\]

Only the `m(p-1)/p` primitive modes contribute. Consequently the best
single-mode amplitude is bracketed by

\[
\frac2{\sqrt{pm}}\le\max_{k\ne0}|\widehat g_t(k)|\le\frac2{\sqrt m}.
\]

At fixed `p`, energy is spread over a growing number of primitive modes.

Choose any `s` distinct additive characters, with frequencies allowed
to depend on `t`, and set

\[
K_{ab}=\mathbb E[g_t\chi_{k_a}\overline{\chi_{k_b}}].
\]

Its diagonal is `r=1-2/p`, and every off-diagonal entry has modulus at
most `epsilon=2/sqrt(m)`. For any vector `c`,

\[
c^*Kc\ge r\sum_a|c_a|^2-\epsilon\sum_{a\ne b}|c_a||c_b|
\ge [r-\epsilon(s-1)]\sum_a|c_a|^2.
\]

Thus

\[
\boxed{\lambda_{\min}(K)\ge1-2/p-2(s-1)/\sqrt m.}
\]

For each fixed `p>=7` and each fixed character count `s`, sufficiently
large `t` makes **every** such block strictly positive definite, while
the conditional hole mass stays `1/p`. The quantifier is fixed `s`
followed by sufficiently large `t`; a single finite example does not
pass all block sizes. The complete character matrix still detects the
negative values of `g_t`.

## 4. A joint digit mask and its exact state requirement

Write `z=r+nb`. Character orthogonality gives

\[
h_t(z)=\left|\frac1p\sum_{\ell=0}^{p-1}\omega^{\ell b}
\prod_{j=0}^{t-2}\omega^{-\ell a_ja_{j+1}}\right|^2
=\mathbf1_{A_t}(z).
\]

In particular,

\[
0\le h_t\le1,\qquad h_t^2=h_t,\qquad
\boxed{\mathbb E[g_th_t]=\mathbb E[g_t|h_t|^2]=-1/p.}
\]

These factors use the same actual digits; none is independently
resampled. At fixed `p` their number is linear in `t`. A deterministic
reader, with the final position specified by the fixed height, stores
`(a,s)` in `(Z/pZ)^2`. Initialize at `(a_0,0)`; on each further **lower**
digit `b`, update

\[
(a,s)\longmapsto(b,s+ab).
\]

After the `t` lower digits, accept exactly when the final top digit equals
`s`. The top digit is not appended to the adjacent-product sum.

The width `p^2` is exact at every layer `3<=j<=t-1`, where `j` lower
digits have been read. To reach `(a,s)`, use `j-3` zeros followed by
`(s-a,1,a)`, with entries reduced modulo `p`. For different states
`(a,s)` and `(a',s')`, take the next lower digit to be zero if `s!=s'`,
and one otherwise. The resulting sums differ. Put zero in all remaining
lower positions and choose the top digit to equal the first sum. This
one common suffix is accepted from exactly one state. Hence no two
states can be merged by any deterministic reader at that layer. At
`j=t` only the sum is needed; there is no claim of a `p^2` lower bound
there or for an arbitrary-length automaton without an end marker.

This mask is not the only cheap detector. Here `M_t` takes only values
zero and two, so

\[
h_t=(1-g_t)/2,\qquad
\mathbb E[(M_t-1)(M_t-2)^2]=-4/p.
\]

Exact conditional union reduction and duplicated-residue incidence also
detect the hole. The example does not defeat all low-order joint tests
on original labels. Nor does a short mask provide a general discovery
algorithm: once an uncovered point is known, its indicator also has a
short digit factorization. No uniform rule finding a successful mask in
every hypothetical minimal odd cover is established.

## 5. Literal original moduli, private witnesses and the old-law cost

List each residue of `A_t^c` twice as `r_0,...,r_(L-1)`, where
`L=2(p-1)p^t`. Set

\[
G_e=3^e5^{L-1-e},\qquad d_e=mG_e,
\qquad a_e\equiv0\pmod{G_e},\quad a_e\equiv r_e\pmod m.
\]

All original moduli are distinct odd integers and form a divisibility
antichain. With inverses taken modulo `m`, let

\[
s_e=((r_eG_e^{-1}-1)15^{-1})\bmod m,
\qquad w_e=G_e(1+15s_e).
\]

Then `w_e` belongs to original class `e` and has exact old valuations
`(e,L-1-e)`. Every other old cofactor requires one higher valuation and
cannot divide `w_e`. Thus every original class has a private integer.
The duplicate conditional residues do not make the original classes
globally redundant.

The complete old period is `D=15^(L-1)` and the full period is `mD`.
There are no old-only forbidden labels, so `N=0 mod D` is a genuine
old-survivor fibre. Its physical residual coordinate is `z=N mod m`;
a representative is

\[
N=D((zD^{-1})\bmod m).
\]

Its actual original-label incidence vector is exactly
`(1_(z=r_e))_e`, whose sum is `M_t`. Integer zero is uncovered since
`f_t(0)=0`.

The fixed conditional hole mass must not be confused with a fixed
global contribution. The old fibre has Haar mass `1/D`; extending the
mask by zero off that fibre gives a full-Haar negative moment
`-1/(pD)`, not `-1/p`. Also

\[
L/m=2(1-1/p),\qquad
\sum_e\frac1{d_e}
=\frac{5^L-3^L}{2m\,3^{L-1}5^{L-1}}.
\]

The old period and original cofactor sizes grow with `t`, while the
slice's full-Haar weight tends to zero. These examples therefore do not
refute every margin normalized by the original reciprocal-modulus cost,
and do not provide a uniform positive integral over all old survivors.
They isolate a limitation of local character probes.

## 6. Exact verification

The [standalone program](../frontier/original_digit_relation_masks.py)
uses Python standard-library integers, fractions and exact cyclotomic
reduction. It writes no files. The default `p=7,t=2` case has588 original
labels, residual period343 and49 holes. It verifies345744 private-point
memberships and201684 literal CRT memberships,294 nonzero primitive
coefficients and48 zero lower-conductor coefficients, mean5/7 and mask
moment-1/7. It checks the Fourier transfer phases and orthogonality
exactly. A separate `t=4` state check verifies49 reachable states,1176
distinguishable state pairs and2801 proper-prefix cells.

```sh
python3 -I -S -O docs/reports/erdos7-odd-covering/frontier/original_digit_relation_masks.py
python3 -I -S -O docs/reports/erdos7-odd-covering/frontier/original_digit_relation_masks.py --prime 11 --depth 1
```

The arbitrary-height Fourier and state-width statements are the
ordinary proofs above; finite checks do not replace their quantifiers.
No new Lean declaration, build, deposit or frozen result is claimed.
