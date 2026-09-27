# Constant survival barriers leave a structural gap

For every pair of finite constants \(C_4,C_5\ge0\), the complete
cell-cost comparison from
[profile43](43-complete-cell-costs-strengthen-whole-hinge-survival.md),
with its numerator comparisons and modeled mass interval unchanged,
requires a combined bound of at least

\[
K_*=
\frac{1208994069650187954348450703035483220540461139}
 {2367081918117057277892487238031745380160000}
=510.75294876651606\ldots>403.
\tag{1}
\]

This constrains the **bound expression produced by this comparison
family**. It is not a lower bound for actual congruence families. In
particular, it does not assert that the relaxed control vertex or its
endpoint \(S=D\) is attained by an actual forbidden family. The
unrestricted odd covering problem remains open.

No continuous optimizer, attainment, numerical LP or finite search range
is needed for(1). One control vertex and a uniform comparison of costs
suffice. Increasing or continuously tuning these two constants cannot
reach the negative-\(Q\) criterion, even before its positive complete-core
error is added.

## 1. The comparison family for arbitrary finite barriers

Use the actual source data, independent original labels and full
cell-cost operator \(F_\theta\) of profiles42–43. Put

\[
h_t(v)=(v-t)_+,\qquad
\chi_{t,C}(v)=\min(C,h_t(v))=h_t(v)-h_{t+C}(v).
\]

For a shallow mixed7 root/cell choice \((r,j)\), set

\[
\omega_l^{r,j}=\frac{1_{\operatorname{ROOT}(l)=r}+1_{l=j}}5,
\qquad
g_{t,C,l}^{r,j}=\psi_t-\omega_l^{r,j}\chi_{t,C}.
\]

The original zero7 source cost \(\psi_t\) contains
\((29/35)h_t\). Thus

\[
g_{t,C,l}^{r,j}
=(29/35-\omega_l^{r,j})h_t
 +\omega_l^{r,j}h_{t+C}
 +\sum_{n\ge2}\frac{p_{7,n}}n
       [h_t(nv)-h_t(n)]
\]

is nonnegative, increasing and convex for every finite \(C\ge0\).
The coefficient budget is \(29/35-\omega_l\ge3/7\); it does not impose
an upper bound on \(C\). All costs have linear tails, so the complete
operator and its geometric tail identities remain applicable.

The identity

\[
\psi_t(v)+\omega_l(C-h_t(v))_+
 =C\omega_l+g_{t,C,l}(v)
\]

absorbs the same two original mixed7 cofactors as profile42. Each
remaining deletion integrand is bounded by \(C\). With the unchanged
complete positive7 complement \(P_t\), the resulting exact margin is

\[
m_{t,C}(\theta)=Cs-P_t-CT_{\rm rest}
 -\max_{r,j}\left[\frac C5(n_r+n_j)+F_\theta(g_{t,C}^{r,j})\right].
\tag{2}
\]

Retaining profile41's fixed \(h_{5/2}\) margin, the denominator used by
this family at \(D\le S\le s\) is

\[
\mathcal D_{C_4,C_5}(S)=
\left(\frac{193}{231}-\frac{C_4}6-\frac{4C_5}{33}\right)S
 +\frac{m_{25}}{22}+\frac{m_{4,C_4}}6+\frac{4m_{5,C_5}}{33}.
\tag{3}
\]

The constants are charged once in(3). Numerator margins, original
residues and the underlying actual source law are unchanged.

## 2. A uniform lower comparison for the full source cost

Define a comparison function, not an infinite choice of barrier,

\[
g_{t,*,l}=\psi_t-\omega_lh_t.
\]

It is nonnegative increasing convex, vanishes at1, and has eventual
slope \(1-\omega_l\). For every finite \(C\ge0\),

\[
g_{t,C,l}=g_{t,*,l}+\delta_l,
\qquad \delta_l=\omega_lh_{t+C}.
\tag{4}
\]

The signed centering in \(F\) requires more than pointwise ordering.
For any increasing convex increment \(\delta\) with \(\delta(1)=0\),
write

\[
q_{n,\delta}(v)=\frac{\delta(nv)-\delta(n)}n,
\quad
\overline\delta(v)=\sum_{n\ge2}\frac4{5^n}q_{n,\delta}(v)
                       -\frac{\delta(v)}5.
\]

For integer \(v\ge1\), discrete convexity gives

\[
\Delta q_{n,\delta}(v)
 =\frac1n\sum_{i=0}^{n-1}\Delta\delta(nv+i)
 \ge\Delta\delta(v).
\]

Both centered functions vanish at1, hence \(q_{n,\delta}\ge\delta\ge0\).
Since \(\sum_{n\ge2}4/5^n=1/5\), also

\[
\Delta\overline\delta\ge0,
\qquad \overline\delta(1)=0,
\qquad \overline\delta\ge0.
\tag{5}
\]

Every term of the full operator now increases under(4):

- Initial terms increase by
  \(n_l\delta_l(b_l)+\eta_l\overline\delta_l(b_l)\ge0\).
- Combined deep increments increase by
  \(\Delta(d_l\delta_l+\overline\delta_l)\ge0\).
- Positive5 constants increase by
  \(\sum_l\eta_l\delta_l(n)\ge0\).
- Each centered pure-cost initial value and deep increment increases,
  so its maximum \(P_\eta(q_n)\) increases.

The infinite sums have nonnegative coefficients and convergent geometric
tails. Consequently

\[
F_\theta(g_{t,C})\ge F_\theta(g_{t,*})
\quad\text{for every finite }C\ge0.
\tag{6}
\]

This proves monotonicity along the specified convex increment. It does
not assert that signed centering preserves arbitrary pointwise cost
ordering.

## 3. Cancel the barrier constants at a maximum-mass carrier

Choose \((r,j)\) with \(n_r+n_j=R(n)+\max_l n_l\). The deletion cap
identity is

\[
D=s-T_{\rm rest}-\frac{R(n)+\max_l n_l}{5}.
\]

Select this one carrier inside the maximum in(2), then apply(6):

\[
m_{t,C}\le CD-P_t-F_\theta(g_{t,*}^{r,j}).
\tag{7}
\]

Thus all occurrences of \(C_4,C_5\) cancel in the upper bound for(3)
at \(S=D\):

\[
\mathcal D_{C_4,C_5}(D)\le
B:=\frac{193}{231}D+\frac{m_{25}}{22}
 -\frac{P_4+F_\theta(g_{4,*})}{6}
 -\frac4{33}[P_5+F_\theta(g_{5,*})].
\tag{8}
\]

If a proposed pair has a nonpositive denominator, it is inadmissible for
this ratio certificate. Otherwise, for the unchanged positive combined
numerator \(N_D\),

\[
C_0+\frac{N_D}{\mathcal D_{C_4,C_5}(D)}
\ge C_0+\frac{N_D}{B}.
\tag{9}
\]

Using the \(s\) endpoint for a negative target coefficient cannot bypass
this necessary inequality: a bound for the modeled interval must also
hold at \(D\). This argument does not require any actual family to
attain \(D\).

## 4. Exact control402 values

At vertex402,

\[
\begin{aligned}
d&=(3/4,3/4,1/4,1/2,1/2),\\
n&=(1/24,1/12,1/72,1/18,1/18),\\
\eta&=(1/18,1/9,1/9,1/9,1/9),\\
s&=1/4,\quad D=3/20,\quad m_{25}=68963/441000.
\end{aligned}
\]

Both root masses equal \(1/8\); cell1 has largest mass \(1/12\).
The choice \((r,j)=(0,1)\) gives
\(\omega=(1/5,2/5,0,0,0)\) and \(T_{\rm rest}=7/120\).
The complete costs are

| Cost | \(t=4\) | \(t=5\) |
|---|---:|---:|
| \(P_t\) | \(2377/34300\) | \(137251/2401000\) |
| \(F_\theta(g_{t,*})\) | \(2295623/15435000\) | \(22423351/202584375\) |
| Their sum | \(3365273/15435000\) | \(272031233/1620675000\) |

These give

\[
B=\frac{2025618599}{26741137500},\qquad
C_0=\frac{185694867601}{8599322160},
\]

\[
N_D=
\frac{235676572069506444982211913251473065480803}
 {6360462916399256045941092769236000000000}.
\]

Substitution into(9) proves(1), with exact positive gap

\[
K_*-403=
\frac{255060056649013871357778346108689832335981139}
 {2367081918117057277892487238031745380160000}
=107.75294876651607\ldots.
\]

Compared with profile43's combined bound, all possible changes of these
two constant barriers together can save at most
\(0.18185698908432985\ldots\). This is a bound on optimization headroom,
not a claim that the endpoint is attained.

## 5. Reproducible arithmetic and inherited numerator

The standalone checker is
[`frontier/cover-geometry/absorbed_barrier_boundary.py`](../../frontier/cover-geometry/absorbed_barrier_boundary.py).
It has no scratch-data dependency and is read-only by default:

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/absorbed_barrier_boundary.py
```

An optional `--output PATH` writes its exact rational JSON result.
The checker pins the logical profile41/profile43 certificates and every
direct source file it reads. It reconstructs only control402:

1. Profile41 supplies \(m_{25}\); profile43 supplies its full \(m_4,m_5\).
   These reconstruct the positive denominator \(\Delta_{43}\).
2. Profile43 certifies402 as a \(D\)-endpoint maximizer of \(J\).
   Therefore the fixed numerator is recovered exactly as
   \(N_J=(J_{43}-C_0)\Delta_{43}\).
3. The checker recomputes the100 original square-source layout values.
   Vertex402 is outside the six specially refined rows, so its inherited
   barrier45 margin is \(m_G=m_{G,\mathrm{old}}+(45-G)D\).
4. Complete source formulas directly compute
   \(N_T=A_{81}D+\operatorname{Raw}_{81}-c_Gm_G\), and
   \(N_D=N_J+N_T\) is checked against the rational above.

This uses an already certified numerator and its unchanged comparison
formula; it does not use the new lower bound to establish that input.
The starred cell costs are evaluated as positive hinge measures. Their
ternary tails use closed hinge formulas, and the complete positive5 tails
retain each cell's slope \(1-\omega_l\). Both zero-weight specializations
exactly reconstruct the published scalar source values.

The remaining gap requires a stronger source/deletion comparison, a
sharper numerator bound, or another proof mechanism. This result rules
out closing it by tuning only \(C_4,C_5\) in the present family.

## 6. The boundary extends to five cell-dependent barriers

The same stopping value holds when each t=4,5 is allowed an arbitrary
finite nonnegative vector C_t=(C_(t,l)) on the five cells. This extension
keeps the old numerator and old m25 fixed and uses the complete weighted
cylinder-cap relaxation below. It also permits a common shallow-carrier
mixture and aggregation of the remaining caps after each test is clipped.
Additional actual-source constraints or conditional numerator information
change this model.

Let S_l be the actual raw357 surviving mass in cell l; thus
0<=S_l<=n_l and sum S_l=S. For any nonnegative cell weights C, the
complete remaining-cofactor cap is

    R(C)=max_l(d_l*C_l)/90+sum_l eta_l*C_l/20
         +max_r sum_(ROOT(l)=r)eta_l*C_l/20
         +max_l eta_l*C_l/20+max_l C_l/360.          (V1)

The five terms account respectively for pure3 depths a>=3, positive5
cofactors at old3 depths0,1,2, and positive5 cofactors at old3 depths>=3.
They use the same full tails sum3^-a=1/18, sum5^-b=1/4, and normalized
positive7 cap sum1/5. In particular R(1)=Trest. Its first term requires
the actual pointwise density bound, not just the five marginal masses.

For the common shallow-carrier mixture pi of profile46 put
omega_bar=sum_c pi_c*omega_c. Fix one original test A_t, with its own
original zero7 load Z_t. The signed identity and A_t>=Z_t give

    mu[(h_t(A_t)-C_(t,l))*1_V]
      <= integral_Lambda psi_t(Z_t)+P_t-C_t.n
         +mu[(C_(t,l)-h_t(Z_t))_+*1_(V^c)],

where mu=Lambda tensor normalized pure7. Apply the deletion caps only
to the nonnegative clip. The shallow term is at most
integral_Lambda omega_bar_l*(C_(t,l)-h_t(Z_t))_+; the remaining term
is at most R(C_t). Pointwise absorption gives

    psi_t(v)+omega_bar_l*(C_(t,l)-h_t(v))_+
      =omega_bar_l*C_(t,l)+g_(t,l)(v),
    g_(t,l)=psi_t-omega_bar_l*min(C_(t,l),h_t).

This is an admissible convex source cost: its native h_t coefficient
is29/35-omega_bar_l>=3/7 and its other coefficients are nonnegative.
Therefore, with the same actual S_l,

    mu[h_t(A_t)*1_V]<=C_t.S-m_t(C_t,pi),
    m_t(C_t,pi)=C_t.n-C_t.(omega_bar*n)
                   -P_t-R(C_t)-F_theta(g_t).       (V2)

The source functional is convex in its cost argument: each of its
branches is linear in that argument and each outer sum of maxima
has nonnegative coefficients. Hence the carrier-linear bound
m_t(C_t,pi)>=sum_c pi_c*m_t(C_t,c) also holds. The test loads and
source maximizations remain independent for different t.

There is a stronger valid way to combine the remaining caps. Write
alpha4=1/6, alpha5=4/33 and Cbar=alpha4*C4+alpha5*C5. The individual
nonnegative clips u_t satisfy sum_t alpha_t*u_t<=Cbar_l, so the
common remaining deletion union can be charged R(Cbar), rather than
sum_t alpha_t*R(C_t). The source terms still have separate F_theta
values. This aggregates already clipped terms and does not replace
them by a clip of one fictitious common load.

### A single vector satisfies every inherited weighted mass cut

The support function R is the Minkowski sum of the fixed vector
eta/20 and four simplex hulls: the root-restricted eta/20 vectors,
the vectors eta_l*e_l/20, d_l*e_l/90, and e_l/360. Include zero in
each simplex for missing labels. Assigning actual deleted points to
their original cofactor families gives a safe mass relaxation

    0<=S_l<=n_l,
    n_l-S_l<=n_l*omega_bar_l+r_l

for some r in this support set. Downward closure accommodates overlap.
In particular all nonnegative weighted cuts are

    C.(n-S)<=C.(omega_bar*n)+R(C), C>=0.            (V3)

This relaxation keeps the weighted first-order cylinder caps. It does
not enforce compatibility of the actual source or mixed7 residues.

At control402 choose the concentrated carrier(0,1), so
omega=(1/5,2/5,0,0,0), and choose the following point of the support set:

    r=eta/20+(eta restricted to root1)/20
             +eta_1*e_1/20+d_0*e_0/90+e_1/360
      =(1/90,1/72,1/90,1/90,1/90).

Its total is7/120=Trest. The surviving vector

    S*=n-omega*n-r
      =(1/45,13/360,1/360,2/45,2/45)               (V4)

has all coordinates in(0,n_l] and total3/20=D. It satisfies(V3)
for every C>=0, because C.r<=R(C) by the support-set membership.
Thus adding more weighted cuts from these same caps cannot exclude
this one vector. No actual forbidden family is claimed to realize it.

### Every finite barrier cancels at the same vector

At this fixed carrier, let g_star,l=psi_t-omega_l*h_t. For every
finite C_(t,l)>=0,

    g_(t,l)-g_star,l=omega_l*h_(t+C_(t,l)).

The difference is nonnegative increasing convex in each cell. The
convex-increment argument of section2 applies cell by cell and proves
F_theta(g_t)>=F_theta(g_star). In particular the signed centering does
not require general pointwise monotonicity of F_theta.

Use the stronger after-clipping remainder R(Cbar) in the survival
expression, and substitute n-S*=omega*n+r. Its value is at most

    (193/231)*D+m25/22+Cbar.r-R(Cbar)
                 -sum_(t=4,5)alpha_t*[P_t+F_theta(g_t)]
      <=(193/231)*D+m25/22
                 -sum_(t=4,5)alpha_t*[P_t+F_theta(g_star)]
       =2025618599/26741137500.                    (V5)

All ten independent barrier coordinates disappear from(V5). The
same relaxed vector and concentrated mixture work for every choice,
so taking a supremum over barriers or a finite menu cannot evade
this ceiling. The unchanged numerator at sum S*=D is exactly N_D
from section4. Thus every positive-denominator certificate uniform
over this relaxation has the same lower bound

    K_certificate>=510.75294876651606...>403,

or its denominator is inadmissible at(V4).

The [cellwise checker](../../frontier/cover-geometry/cellwise_barrier_boundary.py) reconstructs
the complete source and numerator constants using the pinned earlier
checker, verifies the support-set decomposition and every vector identity,
and exits zero. It does not sample barriers as a substitute for(V5).

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/cellwise_barrier_boundary.py
```

The new [actual-source constraint](48-actual-source-compatibility-excludes-a-relaxed-mass-endpoint.md)
requires liminf S>=139/900 at this source parameter. It therefore excludes
(V4), whose total is3/20. This identifies a concrete difference between
weighted cylinder caps and additional original-source compatibility.
The stopping statement is preserved for its specified relaxation; it is
not an obstruction after that relaxation or the numerator is strengthened.
