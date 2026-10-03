# A BBMST endpoint-cap adapter must charge singleton columns

[Index](../../../marked_head_profile.md) · [Source-global collision moment](../350-399/388-source-global-substitution-collision-moment.md) · [Collision cofactor packing](../600-649/844-collision-moment-needs-cofactor-packing.md)

The source-global substitution in report 844 gives a common source on which
the full pair count of repeated output numerical moduli is positive. This
report isolates a further necessary condition for one explicit class of
BBMST-style endpoint adapters. Under the hypotheses below, charges supported
only on originals that participate in a collision cannot pay for the complete
labelled-pair count. On a source event of mass \(>2/7\), a successful adapter
must obtain a strictly positive amount from originals that are singleton in
their current output column.

This is a boundary theorem for the stated adapter class. It supplies neither
the missing cofactor-packing inequality nor a global budget below one, and it
does not prove or refute unrestricted Erdős #7.

## 1. Common-source hypotheses

Use the \(r=5,s=7\) common source from report 844. Write each original
modulus as

\[
 d=5^a7^bm,\qquad \gcd(m,35)=1,
\]

and let the source outcome be \(\omega\). A surviving original in column
\((b,m)\) has output numerical modulus

\[
 n_{b,m}=5^bm.
\]

The safe \(5\)-coordinate removes the pure \(5\)-power classes, so every
surviving output modulus is a nonunit. Let

\[
 k_{b,m}(\omega)=\#\{\text{surviving labelled originals in column }(b,m)\},
\]

\[
 N_{b,m}(\omega)=\binom{k_{b,m}(\omega)}2,
 \qquad
 N(\omega)=\sum_{b,m}N_{b,m}(\omega).
\]

The only source facts used here are the two conclusions of report 844:

\[
 N(\omega)\ge 1\quad\text{for every }\omega,
 \tag{E1}
\]

and, for every fixed column,

\[
 \mathbb E_\mu N_{b,m}
 <\frac5{12}\left(\frac57\right)^b.
 \tag{E2}
\]

All labels and their original phases remain distinct. A pair in one column
is a labelled pair even when other columns have the same source event.

## 2. A positive-mass event with no small collision column

Define

\[
 N_{<9}(\omega)=
 \sum_{1<5^bm<9}N_{b,m}(\omega),
 \qquad
 F=\{\omega:N_{<9}(\omega)=0\}.
\]

The only possible odd output moduli strictly between \(1\) and \(9\) are
\(3,5,7\). The form \(5^bm\) with \(\gcd(m,35)=1\) excludes \(7\), leaving
the columns \((0,3)\) and \((1,1)\). Therefore (E2) gives

\[
 \mathbb E_\mu N_{<9}
 <\frac5{12}+\frac5{12}\frac57
 =\frac57.
\]

Since \(N_{<9}\) is a nonnegative integer,

\[
 \mu(F)=1-\mu(N_{<9}\ge1)
 \ge 1-\mathbb E_\mu N_{<9}
 >\frac27.
 \tag{1}
\]

On every \(\omega\in F\), (E1) supplies a collision and every column with a
collision has numerical modulus at least \(9\).

## 3. The endpoint adapter class

Let \(L\) be a common multiple of all output moduli and let

\[
 V\sim\operatorname{Unif}(\mathbb Z/L\mathbb Z)
\]

be one common auxiliary Haar coordinate, independent of the source outcome.
For a surviving original \(h\), write \(c_h(\omega)\pmod {n_h}\) for its
literal output phase. Consider arbitrary nonnegative charges satisfying

\[
 0\le Q_h(\omega,V)
 \le C_*\,\mathbf 1_{\{V\equiv c_h(\omega)\pmod {n_h}\}},
 \tag{2}
\]

where the BBMST reuse constant is

\[
 C_*:=\sum_{\ell=2}^{\infty}2^{-\ell/4}
 =\frac1{\sqrt2-2^{1/4}}.
 \tag{3}
\]

Condition (2) permits arbitrary fractional splitting and pooling between
pairs and cofactor columns. It only requires that the total charge attributed
to one original is supported on that original's literal output class and is
bounded by \(C_*\). This is a definition of the tested adapter class, not a
claim that report 844 or BBMST already supplies such charges.

Let \(J(\omega)\) be the surviving originals in columns with
\(k_{b,m}(\omega)\ge2\). These are precisely the collision endpoints.

## 4. Collision endpoints alone have insufficient capacity

For each \(h\), (2) and Haar measure give

\[
 \mathbb E_V[Q_h\mid\omega]\le\frac{C_*}{n_h}.
 \tag{4}
\]

For \(\omega\in F\), every \(h\in J(\omega)\) has \(n_h\ge9\). Hence

\[
\begin{aligned}
 \mathbb E_V\!\left[\sum_{h\in J}Q_h\mid\omega\right]
 &\le C_*\sum_{k_{b,m}\ge2}\frac{k_{b,m}}{n_{b,m}}\\
 &\le \frac{C_*}{9}\sum_{k_{b,m}\ge2}k_{b,m}\\
 &\le \frac{2C_*}{9}\sum_{b,m}\binom{k_{b,m}}2
 =\frac{2C_*}{9}N(\omega).
\end{aligned}
 \tag{5}
\]

The third inequality uses \(k\le2\binom{k}{2}\) for \(k\ge2\). The constant
is strictly below one after the pair normalization:

\[
 C_*<\frac{40}{9},
 \qquad
 \frac{2C_*}{9}<\frac{80}{81}<1.
 \tag{6}
\]

For an exact rational check of the first inequality, put \(t=2^{1/4}\).
The claim \(t^2-t>9/40\) reduces, after squaring positive quantities, to

\[
 3281^2-2\cdot2320^2=161>0.
\]

Combining (5) and (6), no adapter in this class that charges only \(J\) can
satisfy the conditional full-pair requirement

\[
 \mathbb E_V\!\left[\sum_{h\in J}Q_h\mid\omega\right]
 \ge N(\omega)
 \tag{7}
\]

on \(F\). This conclusion allows complete pooling between every collision
column; it is not a two-endpoint or pair-by-pair obstruction.

## 5. Quantified singleton requirement

Let \(S(\omega)\) be the surviving originals that are the sole member of
their output column. If the adapter is allowed to use all survivors and
satisfies

\[
 \mathbb E_V\!\left[\sum_{h\in J\cup S}Q_h\mid\omega\right]
 \ge N(\omega),
 \tag{8}
\]

then (5) implies, on \(F\),

\[
 \mathbb E_V\!\left[\sum_{h\in S}Q_h\mid\omega\right]
 >\frac1{81}N(\omega).
 \tag{9}
\]

Using \(N\ge1\) and (1), the required singleton contribution has the
source-averaged lower bound

\[
 \boxed{
 \mathbb E_{\mu,V}\!\left[
 \mathbf1_F(\omega)\sum_{h\in S(\omega)}Q_h(\omega,V)
 \right]>\frac2{567}.}
 \tag{10}
\]

Thus a conditionally faithful adapter with the endpoint cap (2) must pay from
non-collision originals on a positive-mass part of the one common source. A
construction confined to the collision incidence graph is impossible within
this class.

## 6. Exact scalar relaxation and the remaining packing obligation

For one source outcome define the total endpoint capacity

\[
 W(\omega)=\sum_{\text{surviving }h}\frac1{n_h}.
 \tag{11}
\]

If all survivors are eligible and we ignore tree incidences, the relaxed
conditional accounting problem under (2) is feasible exactly when

\[
 \boxed{N(\omega)\le C_*W(\omega).}
 \tag{12}
\]

Necessity follows by summing (4). Conversely, when (12) holds, \(W>0\) by
(E1), and the explicit choice

\[
 Q_h(\omega,V)=
 \frac{N(\omega)}{W(\omega)}
 \mathbf1_{\{V\equiv c_h(\omega)\pmod {n_h}\}}
\]

has conditional total expectation \(N(\omega)\) and obeys (2). This is only
a scalar relaxation: it supplies no BBMST tree representation, no genuine
depth or support-rank assignment, and no strict global budget.

Consequently, the next precise test for a broader endpoint adapter is whether
the actual EB1 common source forces (12) on every outcome. If an admissible
configuration violates it, all conditionally faithful literal-endpoint
adapters with cap \(C_*\) are excluded. If it holds, the tree incidences and
the global charge estimate still require proof.

## 7. The two moment summaries alone do not imply scalar capacity

The source facts (E1)--(E2) cannot by themselves prove (12). Consider the
finite probability space \(\Omega=\{1,2,3\}\) with the uniform law. Use the
three columns

\[
 (b,m)=(0,9),(0,11),(0,13).
\]

At outcome \(j\), put \(k_{0,m}=2\) in the \(j\)-th column and put all other
\(k_{b,m}=0\). Then \(N(\omega)=1\) at every outcome, while for each of the
three columns

\[
 \mathbb E_\mu N_{0,m}=\frac13<\frac5{12},
\]

so (E1)--(E2) hold exactly. The two labels in the active column can be given
distinct phases, so this toy law also retains the collision-versus-duplicate
distinction. Its endpoint capacity is \(W(\omega)=2/m\), and

\[
 C_*W(\omega)=\frac{2C_*}{m}<1=N(\omega)
 \qquad(m\in\{9,11,13\}).
\]

This is deliberately not a whole-cover construction and makes no claim about
an admissible original family. It proves a narrower but necessary point:
the scalar packing obligation requires the whole-cover, original-phase, and
EB1 structure in addition to the two recorded moment summaries. A proof that
uses only (E1)--(E2) cannot close the endpoint adapter.

## 8. A positive reduction that does not close the adapter

The capacity obstruction is not caused by a lack of a bare injective depth
routing. For a labelled pair

\[
 (5^a7^bm,5^{a'}7^bm),\qquad a<a',
\]

assign it to the deeper original, to the length-\(a\) prefix on the single
complete \(5\)-prefix tree, with residual depth \(a'-a\). Positive pair
events force compatible prefixes, so the common safe-coordinate path visits
the assigned node. For a fixed deeper original the residual depths are
distinct, and

\[
 \sum_{P\text{ assigned to }h}\theta^{d(P)}
 \le\sum_{j=1}^{a'}\theta^j
 <\frac{\theta}{1-\theta}
 \qquad(0<\theta<1).
 \tag{13}
\]

This is only a routing skeleton. Its nodes need not be the globally
DFS-first representatives used by BBMST, and it does not establish the
support-rank conditions or the BaseCaps estimate. In particular, cofactor
digits absent from the common source cannot be counted as depth merely because
they occur in an original modulus.

## 9. Scope

The result assumes conditional accounting at each common-source outcome, the
full labelled-pair count \(N\), literal output endpoint support, one common
Haar coordinate, and the aggregate per-original cap (2). It leaves open
adapters using another justified law, a different resource, amplified
coefficients, a collision selector or union functional, or compensation across
source outcomes. The lower bound (10) is not by itself a global deficit.

The unrestricted odd distinct-modulus covering problem therefore remains open.
The new obligation is concrete: any successful continuation of the §844 route
must either justify a source-preserving charge from singleton columns and then
prove the global budget, or replace the endpoint-cap interface with a different
fully quantified resource while retaining all original phases and the one
common source.
