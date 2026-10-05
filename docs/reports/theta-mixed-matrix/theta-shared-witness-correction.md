# Shared critical and dual correction for two actual J4 columns

This conditional computation supplies nonzero primal and dual witnesses
for the two left J4 columns in
[the actual midpoint report](theta-profile-residual-gram.md). It reuses
the original probability measure, physical unitary, negative-edge metric,
critical source space and [J5 inverse estimate](../../../Library/Dynamics/clason2021regularization.md#pay-the-finite-remainder-with-the-existing-common-source-certificate).
The shared witness and direct corrected producers retain full spatial
tails and one simultaneous complex coefficient vector. Under the
inherited actual-model, numerical-supplier and certified-input-row
premises, the directed upper Gram allowances are

$$
\|G_{\mathrm{zero}}\|<0.001523,
\qquad \|G_{\mathrm{corrected}}\|<0.000981.
$$

The exact directed quantities have ratio below $0.65$. This compares
upper allowances obtained by the same transport method; it establishes
no ordering of the true residual norms. It does not certify the complete
growing family, common coefficient cost, cofinal signs, original
all-input half-bound, Robin inequality or RH. No new Lean theorem or
originality claim is made.

## Same sources and legitimate witnesses

Keep $d\nu=2\Phi(x)\cosh(x/2)dx$, $Uh=v_0h$ with
$v_0=\sqrt{2\Phi\cosh(x/2)}$, $N_c=UN$ and
$\mathcal B=UBU^{-1}$. The two unchanged columns are

$$
e_i=\sqrt{\Delta_i}\,Q_0[G(|x|-R_i)],\quad
G(y)=e^{5y/2-(\pi/2)e^{2y}},\quad
(R_1,R_2)=(0,1/2),\quad\Delta_1=\Delta_2=1/2.
$$

Their coefficient cells remain $[-1/4,1/4]$ and $[1/4,3/4]$.
Write $h_i=G(|x|-R_i)/v_0$. Reuse the
[critical-vector membership](../../../Library/Weil/lagarias2004li.md)
and the individual certified real Xi-root dual premise to choose

$$
v_1=\Phi''/\Phi-1/4,\qquad n=Uv_1/64\in N_c,
\qquad w=U\frac{\cos(\gamma_1x)}{16\cosh(x/2)}\in N_c^\perp.
$$

Here $\gamma_1$ is the first positive real Xi zero enclosed by the
existing `acb.zeta_zero(1)` supplier. Only this individual-root premise
is used. Completeness of the real-zero family and RH are not assumed.
The centered critical vector and original columns retain their inherited
form-domain membership.

Use the following exact dyadic coefficients, with $a_i$ multiplying
$n$ and $b_i$ multiplying $w$:

| Center $R_i$ | $a_i$ | $b_i$ |
|---|---:|---:|
| $0$ | $-711/1048576$ | $21/524288$ |
| $1/2$ | $34641/524288$ | $725/262144$ |

Thus $\eta_i=a_in\in N_c$, $\omega_i=b_iw\in N_c^\perp$, and

$$
\beta_i=\mathcal B(e_i-\eta_i)-\omega_i.
$$

The coefficient symbol $b_i$ is distinct from the inverse lower bound
$b_0=1/100$. The [shared basis result](theta-shared-witness-gram-result.json)
encloses the full Gram of
$(\mathcal Be_1,\mathcal Be_2,\mathcal Bn,w)$ and records these
coefficients. They are rounded solutions of the positive witness
two-by-two block against each source cross column. Applying the single
congruence matrix

$$
T=\begin{pmatrix}1&0\\0&1\\-a_1&-a_2\\-b_1&-b_2\end{pmatrix}
$$

to that enlarged upper Gram gives a valid allowance below $0.005914$.
The enlarged allowance is too loose to improve the supplied zero
baseline. It is an upper bound, with no implication that the actual
correction is ineffective. The coefficient selection does not claim to
minimize the true joint residual norm.

## Direct transport and the matching zero control

The [direct producer](theta_corrected_profile_gram.py) reuses the
supplied profile midpoint actions and new critical midpoint actions.
It makes no additional metric-action callbacks. Its source representative is

$$
f_i=\sqrt{\Delta_i}h_i-a_iv_1/64-c_i,
\qquad
g_i=Bf_i-b_i\frac{\cos(\gamma_1x)}{16\cosh(x/2)},
\qquad \beta_i=Ug_i.
$$

Each $c_i$ is an arbitrary exact point dyadic chosen near
$\sqrt{\Delta_i}h_i(0)-a_iv_1(0)/64$. It is a transport offset,
not an exact mean. Since $B1=0$ and $v_1$ is centered,

$$
Bf_i=B(\sqrt{\Delta_i}h_i-a_iv_1/64),
\qquad Q_0Uf_i=e_i-a_in.
$$

Removing this constant tightens the derivative allowance without
changing the physical residual. The zero control uses $a_i=b_i=0$
and applies the same offset rule, source-L1 bound, full-cell transport,
row inflation and exterior treatment. Thus the comparison accounts for
constant removal on both sides.

The scaled critical source satisfies

$$
\Phi(v_1/64)=(\Phi''-\Phi/4)/64,
\qquad (v_1/64)'=(\Phi'''/\Phi-\Phi''\Phi'/\Phi^2)/64.
$$

The implementation obtains this derivative from the existing source
derivative with coefficient $-1/64$, subtracting its extraneous $2r$
term. It does not acquire or reuse quadratic-input action rows.

Let $M_{1,i}\ge\|f_i\|_{L^1(\nu)}$ include the complete weighted-source
tail. On a real cell with the supplied common active-gap lower bound
$g>0$, the existing derivative transport gives

$$
|g_i'|\le\frac12\bigl[|f_i'|+\coth(g)(|f_i|+M_{1,i})\bigr]
+\frac{|b_i|}{16}\left|\left(\frac{\cos(\gamma_1r)}{\cosh(r/2)}\right)'\right|.
$$

A midpoint action ball plus cell half-width times this bound encloses
the whole cell. The action balls already include both omitted signed
action tails beyond cutoff 5; the tail is not inferred from the nominal
quadrature tolerance. The direct calculation uses the same 128 cells on
$[0,5/2]$, folded density and support-gap rows as the profile inputs.

## Whole spatial exterior

Reuse the supplied constants $C_0,C_2$ with
$|\Phi^{(j)}(r)|\le C_j e^{(9/2+2j)r-\pi e^{2r}}$ for $r\ge0$.
Put $S_x=5/2$, $A=4\pi^2-6\pi>0$, and write $T_p(S_x)$ for the
existing `exponential_integral_upper(p, pi, exp(2*S_x))` supplier.
It bounds $\int_{S_x}^\infty e^{(2p+1)r-\pi e^{2r}}dr$.
The exterior mass allowance is

$$
M=4C_0T_2(S_x)\ge\nu(|x|>S_x).
$$

The profile squared-source allowance and critical squared-source
allowance are

$$
H_i=2e^{-5R_i}T_2(\pi e^{-2R_i},S_x),
\qquad
V=\frac{8C_0}{64^2}
\left[\left(\frac{C_2}{A}\right)^2T_6(S_x)+\frac{T_2(S_x)}{16}\right],
$$

where $T_2(a,S_x)$ denotes the same supplier with rate $a$.
The positive first theta term bounds $\Phi$ below and gives the $V$
estimate. Three-term Cauchy therefore bounds the exterior source square by

$$
\int_{|x|>S_x}|f_i|^2d\nu
\le3[\Delta_iH_i+a_i^2V+c_i^2M].
$$

The weighted source-L1 tail separately includes the profile tail,
$|a_i|(C_2T_4+C_0T_2/4)/64$ and $|c_i|C_0T_2$, with the original
folded factor four. From $|Bf_i|\le(|f_i|+M_{1,i})/2$ and
$|\cos(\gamma_1x)/\cosh(x/2)|\le1$, the whole residual exterior is
bounded by

$$
E_i=3[\Delta_iH_i+a_i^2V+c_i^2M]
+M_{1,i}^2M+2b_i^2M/16^2.
$$

This pays the source growth, transport offset and dual tail. The exterior
Gram is positive, so its operator norm is bounded by
$\tau=\sum_iE_i$. Both scenarios have $\tau<6.272\times10^{-73}$.

## Positive joint Gram and directed allowances

The signed products $g_i(r)g_j(r)$ are enclosed on each shared cell
and integrated against $4\Phi(r)\cosh(r/2)$. Let $A_{ij}$ be the exact
point-dyadic midpoint of each interior Gram ball and $r_{ij}$ bound
its distance to both exported endpoints. With
$d_i\ge\sum_jr_{ij}$, Hermitian error obeys

$$
|z^*Ez|\le\sum_i d_i|z_i|^2\qquad(z\in\mathbb C^2).
$$

This follows from $2|z_i||z_j|\le|z_i|^2+|z_j|^2$ for the symmetric
entry radii. Consequently an upward-rounded point matrix

$$
G=A+\operatorname{diag}(d_1,d_2)+\tau I
$$

dominates the whole true Gram. The exported row inflation pays endpoint
serialization distances as well as ball uncertainty. Strictly positive
LDL pivots and the directed two-by-two eigenvalue formula certify the
positive upper matrix. One common complex vector is retained throughout;
separate scalar residual norms are not substituted for this Gram.

The [direct result](theta-corrected-profile-gram-result.json) gives:

| Scenario | Directed upper allowance, approximate | Strict public cap |
|---|---:|---:|
| Offset-centered zero control | $0.001522919404333620$ | $0.001523$ |
| Offset-centered nonzero correction | $0.0009801449562955543$ | $0.000981$ |

For orientation, the corrected upper matrix is approximately

$$
G_{\mathrm{corrected}}\approx
\begin{pmatrix}
0.00002016385254&-0.00000153931460\\
-0.00000153931460&0.00098014248803
\end{pmatrix}.
$$

Only the exact dyadic entries in the result carry the calculation.
The row inflations are approximately $0.00002010652411$ and
$0.0006380574907$; full-cell transport remains the dominant allowance.
The ratio of the directed corrected and control quantities is
approximately $0.6435961$, below $0.65$. This is a reduction of the
computed upper allowance, without a lower bound on the true zero-control
residual or an optimality statement.

With the inherited $b_0=1/100$, the existing metric inverse gives, for
this subblock only,

$$
\left\|\sum_i z_i(\mathcal R e_i-\eta_i)\right\|_2
\le b_0^{-1}\sqrt{\|G_{\mathrm{corrected}}\|}\,\|z\|_2
<3.133\|z\|_2.
$$

For a coefficient map with bound $Q$, this contributes at most
$3.133Q$. It is not the full J5 allowance: the remaining columns,
J4 approximation error, infinite principal contribution and required
common-sequence conditions must still be controlled.

## Reproduction, source contract and reuse boundary

The [shared producer](theta_shared_witness_gram.py) acquires fresh
critical witness actions on the identical profile grid; the direct
producer then reuses those rows. They resolve definition dependencies
relative to their source files and expose the normalization denominators,
individual zero index, coefficient precision and supplied profile family.
At least 128-bit precision and a complete ordered common grid are required.
The retained result uses Python 3.13.12, python-flint 0.9.0 and 192 bits:

```sh
uv run --offline --no-project --python 3.13 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/theta_shared_witness_gram.py --profiles docs/reports/theta-mixed-matrix/theta-profile-residual-gram-result.json --output /tmp/theta-shared-witness-gram.json
uv run --offline --no-project --python 3.13 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/theta_corrected_profile_gram.py --profiles docs/reports/theta-mixed-matrix/theta-profile-residual-gram-result.json --basis /tmp/theta-shared-witness-gram.json --output /tmp/theta-corrected-profile-gram.json
```

The declared offline runtime must be installed or cached. Source and
supplier hashes, complete matching cells, positive pivots and exact
coefficients are retained. Source-contract validation does not prove
arbitrary supplied row values: certified profile and witness rows remain
premises. Different parameters require their corresponding legitimate
membership and numerical premises.

An exact rational check verifies exported endpoint row sums, upward
diagonal inflation, positive pivot lower endpoints, congruence entries,
both norm caps and the inverse conversion. On the local macOS host,
running the two new entry points from `/tmp`, with source, dependency,
input and output paths containing spaces and no shell startup files,
reproduces both result files byte for byte. Static source review is
separate from this reproduction and supplies no independent numerical
acquisition or Lean verification.

Existing critical/dual memberships, the actual-action definition,
derivative transport, exponential-integral supplier and J5 conversion
are reused within their stated scope. Earlier quadratic, derivative,
translation and matrix grid producers are not executed or counted as
new work. The new acquisition covers the selected shared witness and
its interface to these two profiles. The full growing column family
and signs on one original common cofinal sequence remain unresolved.
