[Index](../../../../Problems/erdos-7-odd-covering-systems.md)

<a id="laminar-prefix-conflicts-under-actual-conditioning"></a>
# Residue conflicts give query bounds under the actual survivor law

The conflict graph of literal prime-power prefix cylinders can be used
directly under an actual conditioned product law. It need not be
interpreted as the graph of a resampling algorithm. The product structure
required here is independence between complete prime coordinates;
different digits within one prime coordinate may be dependent.

More precisely, let \(\lambda\) be a product law on finitely many finite
coordinate spaces, and let the bad events and a query \(E\) be rectangles
whose sets in each coordinate belong to one laminar family. Join two bad
events when their coordinate requirements are incompatible. If valid
event caps lie in the full strict Shearer region of this conflict graph,
then the actual law \(\mu\) conditioned on avoiding all the bad events
satisfies
\[
 \mu(E)\le\lambda(E)
       \frac{Z_{I\setminus N(E)}(w)}{Z_I(w)}.
 \tag{LC1}
\]
Here \(I\) indexes the bad events, \(N(E)\) consists of those incompatible
with the query, and \(Z_U(w)\) is the signed independence polynomial of
the graph induced on \(U\), defined below.

This is an ordinary mathematical specialization of Scott–Sokal's
lopsided conditional avoidance theorem. The coupling which checks its
hypothesis is given explicitly below. It is not a new external theorem
or a Lean-certified result. It connects residue conflicts to the actual
conditional kernels used in
[Chapter 23](23-conditional-kernels-and-recursive-block-noncoverage.md);
it does not establish a uniform six-prime-block fee or unrestricted
Erdős #7.

## 1. Complete coordinates, literal events, and the strict-region premise

Let \(\mathcal Q\) be a finite coordinate index set, with finite spaces
\(X_q\) and probability laws \(\lambda_q\). Set
\[
 X=\prod_{q\in\mathcal Q}X_q,\qquad
 \lambda=\bigotimes_{q\in\mathcal Q}\lambda_q.
 \tag{LC2}
\]
For each \(q\), fix a laminar family \(\mathcal L_q\) of subsets of
\(X_q\), including \(X_q\): any two members are disjoint or one contains
the other. Let the finite bad-event family be
\[
 A_i=\prod_q A_{i,q},\qquad A_{i,q}\in\mathcal L_q,
 \qquad i\in I.
 \tag{LC3}
\]
The query is another such rectangle
\(E=\prod_q E_q\), with \(E_q\in\mathcal L_q\). An unrestricted
coordinate has factor \(X_q\).

In the AP application, \(X_q=\mathbb Z/q^{h_q}\mathbb Z\) is the
complete original prime-power coordinate. The laminar family consists
of the cylinders
\[
 \{x_q:x_q\equiv r\pmod{q^a}\},\qquad 0\le a\le h_q.
\]
Two such cylinders are disjoint or nested. An arbitrary nonempty actual
domain \(V_q\subseteq X_q\) is allowed through
\(\lambda_q=H_q(\cdot\mid V_q)\). This law need not factor into
independent digits. Zero-mass coordinate values are permitted.

The conflict graph \(G\) has vertex set \(I\), no loops, and edges
\[
 ij\in E(G)
 \quad\Longleftrightarrow\quad
 A_{i,q}\cap A_{j,q}=\varnothing\text{ for some }q.
 \tag{LC4}
\]
For original AP events this is exactly incompatibility of their residue
requirements under CRT. Compatible events may share several prime
coordinates. Define the query neighborhood by the same rule:
\[
 N(E)=\{i\in I:E_q\cap A_{i,q}=\varnothing
                         \text{ for some }q\}.
\]
Edges refer to these coordinate sets, without replacing a literal class
by its prime-divisor projections or by a union of other classes.

Choose caps \(w_i\in[0,1]\) with \(\lambda(A_i)\le w_i\). For
\(U\subseteq I\), put
\[
 Z_U(w)=\sum_{\substack{J\subseteq U\\J\text{ independent in }G}}
                  (-1)^{|J|}\prod_{j\in J}w_j,
 \qquad Z_\varnothing(w)=1.
 \tag{LC5}
\]
The required hypothesis is
\[
 Z_U(w)>0\qquad\text{for every }U\subseteq I.
 \tag{LC6}
\]
This is the full strict Shearer condition. Positivity of only
\(Z_I(w)\) does not suffice. The weights may be actual probabilities or
larger certified caps; condition (LC6) must hold for the chosen weights.

## 2. A coupling which preserves every compatible event

Fix a positive-probability rectangle \(A=\prod_q A_q\) of the stated
form. Draw \(X\) with law \(\lambda\). Independently for each coordinate,
draw \(Y_q\) with law \(\lambda_q(\cdot\mid A_q)\), independently of
\(X\), and set
\[
 T_q=\begin{cases}
 X_q,&X_q\in A_q,\\
 Y_q,&X_q\notin A_q.
 \end{cases}
 \tag{LC7}
\]
All these conditional laws exist because \(\lambda(A)>0\). For any
\(D\subseteq X_q\),
\[
 \begin{aligned}
 \Pr(T_q\in D)
 &=\lambda_q(D\cap A_q)
   +(1-\lambda_q(A_q))
                   \frac{\lambda_q(D\cap A_q)}{\lambda_q(A_q)}\\
 &=\lambda_q(D\mid A_q).
 \end{aligned}
\]
The coordinates \(T_q\) are independent, so \(T=(T_q)_q\) has law
\(\lambda(\cdot\mid A)\).

Let \(B=\prod_q B_q\) be compatible with \(A\). If \(X\in B\), then
\(T\in B\): for each coordinate, laminarity gives either
\(B_q\subseteq A_q\), in which case the point \(X_q\in B_q\) is
unchanged, or \(A_q\subseteq B_q\), in which case the output lies in
\(A_q\subseteq B_q\). Thus the coupling preserves the truth of every
compatible event simultaneously.

Let \(U\) be any family of events compatible with \(A\), and write
\(R_U=\bigcap_{i\in U}A_i^c\). The events within \(U\) need not be
mutually compatible. The pointwise implication just proved gives
\[
 \mathbf1_{R_U}(T)\le\mathbf1_{R_U}(X),\qquad
 \lambda(R_U\mid A)\le\lambda(R_U).
 \tag{LC8}
\]
Consequently, whenever \(\lambda(R_U)>0\), Bayes' identity yields
\[
 \lambda(A\mid R_U)\le\lambda(A).
 \tag{LC9}
\]
If \(\lambda(A)=0\), the same conclusion is immediate without defining
the coupling. Equivalently, including zero-probability conditioning
events, the unconditional inequality is
\(\lambda(A\cap R_U)\le\lambda(A)\lambda(R_U)\).

Apply this to each \(A_i\) and any
\(U\subseteq I\setminus(N_G(i)\cup\{i\})\). We obtain
\[
 \lambda(A_i\mid R_U)\le\lambda(A_i)\le w_i
 \tag{LC10}
\]
whenever the conditional probability is defined. This is precisely the
lopsided nonneighbor hypothesis of Scott–Sokal, equation (4.1).
Independence between complete coordinates suffices throughout this
argument; no step splits a prime coordinate into independent digits.

## 3. The actual survivor query ratio

The external probability input is
[Scott–Sokal](../../../../Library/Arith/scottsokal2003repulsive.md),
arXiv:cond-mat/0309352v2, Theorem 4.1(a), equations (4.1)–(4.3).
The theorem requires a graph satisfying the lopsided hypothesis; it does
not require an ordinary dependency graph. Its conditional conclusion is
an inequality in the same original probability space.

By (LC6) and (LC10), this theorem gives
\[
 \lambda(R_I)\ge Z_I(w)>0,
 \qquad \mu=\lambda(\cdot\mid R_I).
 \tag{LC11}
\]
This defines one actual survivor law for all queries. In particular it is
not the terminal law of a resampling process.

If \(\lambda(E)=0\), (LC1) follows immediately. Otherwise adjoin an
independent Bernoulli\((\varepsilon)\) coordinate and the event
\[
 Q=E\cap\{\mathrm{coin}=1\},\qquad
 w_Q=\varepsilon\lambda(E),\qquad \varepsilon>0.
 \tag{LC12}
\]
Old events leave the coin unrestricted. The enlarged family is again
made of rectangles in coordinatewise laminar families, so the preceding
coupling verifies the lopsided hypothesis for every old event and for
\(Q\). Its old neighbors are exactly \(N(E)\).

For every \(U\subseteq I\), the enlarged induced polynomial containing
the query vertex is
\[
 Z_U(w)-\varepsilon\lambda(E)Z_{U\setminus N(E)}(w).
 \tag{LC13}
\]
There are finitely many such inequalities. All the old induced
polynomials are strictly positive, so a sufficiently small
\(0<\varepsilon<1\) makes every expression in (LC13) strictly positive
as well.

Apply Scott–Sokal's conditional avoidance inequality (4.3) with the new
event as the avoided query and all old events as the conditioning set.
Writing \(\widehat\lambda\) for the product extension by the coin gives
\[
 \widehat\lambda(Q^c\mid R_I)
 \ge
 \frac{Z_I(w)-\varepsilon\lambda(E)Z_{I\setminus N(E)}(w)}
      {Z_I(w)}.
\]
The coin remains independent after conditioning on \(R_I\), so the
left side equals \(1-\varepsilon\mu(E)\). Rearranging and cancelling
the positive \(\varepsilon\) proves
\[
 \boxed{\mu(E)\le\lambda(E)
                 \frac{Z_{I\setminus N(E)}(w)}{Z_I(w)}.
 \tag{LC14}
\]
No limit and no identification of different output laws is needed. The
same \(\mu\) satisfies this bound for every query rectangle meeting the
stated laminar condition.

## 4. Interface with actual parent-conditioned block kernels

In the setting of Chapter 23, fix the actual child domains and their
product law \(\lambda\). For each complete parent word \(x\), retain
the literal old internal classes and the literal shallow crossing
classes whose parent prefixes match \(x\). They are rectangles of the
form (LC3), even when the child-domain restrictions create dependence
between digits within one coordinate.

If caps for this particular event family satisfy (LC6) in its residue
conflict graph, (LC14) applies directly to its actual conditional law
\(\mu_x\). The query may be a literal deep child cylinder. This gives a
legitimate way to use residue incompatibilities in an actual-survivor
cylinder estimate.

There is also a direct comparison with an available ordinary dependency
certificate on the same literal events. Let \(G_{\rm sup}\) join events
sharing a complete coordinate, and let \(G_{\rm conf}\) be their conflict
graph. Their query neighborhoods satisfy
\(N_{\rm conf}(E)\subseteq N_{\rm sup}(E)\). For a graph \(K\), write
\[
 \Psi(K,w,N)=\frac{Z^K_{I\setminus N}(w)}{Z^K_I(w)}.
\]
The graph-polynomial comparison
[(H8) in Chapter 16](16-canonical-conflict-resampling-and-the-exact-shearer-query-ratio.md#conflict-certificates-dominate-the-hls-matching-reduction),
with empty matching and unchanged weights, gives the following: if
\(w\) is strictly Shearer for \(G_{\rm sup}\), it is strictly Shearer
for \(G_{\rm conf}\), and
\[
 \mu(E)
 \le\lambda(E)\Psi(G_{\rm conf},w,N_{\rm conf}(E))
 \le\lambda(E)\Psi(G_{\rm sup},w,N_{\rm sup}(E)).
 \tag{LC15}
\]
This reuses a graph-polynomial result, independently of its former
terminal-law application. Equation (LC14) now applies the comparison to
one actual conditioned law. It preserves the available shared-coordinate
bound and can make it strictly smaller, as the control below demonstrates.

It does not by itself provide uniform strict-region certificates or
uniform query costs over all parent words, allocations, residues, and
original exponent ranges. Those are additional obligations before this
interface can strengthen a whole-block estimate. In particular, no
improved uniform six-prime-block fee is asserted here.

The graph vertices in this argument are literal rectangles. An arbitrary
union of original classes on one support need not have the laminar
preservation property. Replacing the literal vertices by such groups
requires its own lopsided-hypothesis proof; the support-union grouping of
Chapter 23 cannot simply be assigned the smaller conflict graph.

## 5. An exact original-label control with dependent digits

Take complete child coordinates modulo \(25,7,11\), and the actual
domains
\[
 V_5=\{x\in\mathbb Z/25\mathbb Z:x\not\equiv0\pmod5,\ x\ne1\},
 \quad V_7=\{1,\ldots,6\},\quad V_{11}=\{1,\ldots,10\}.
 \tag{LC16}
\]
They avoid the original pure classes \(0\pmod5\), \(1\pmod{25}\),
\(0\pmod7\), and \(0\pmod{11}\). Let \(\lambda\) be the product of
the uniform laws on these three domains. The source contains
\(19\cdot6\cdot10=1140\) child words in period \(1925\).

The two base-5 digits are dependent. The low-digit counts in \(V_5\)
are \((0,4,5,5,5)\). More explicitly, the low digit equals 1 with
probability \(4/19\), and the high digit equals 0 with probability
\(3/19\), but their joint occurrence has probability zero. Independence
of these digits would give \(12/361>0\).

At the actual parent prefix \(0\pmod3\), use the following five
literal child events and original crossing classes. Table entries specify
a residue followed by its modulus.

| Child event | Original crossing class |
| --- | --- |
| \(7\pmod{25}\) | \(57\pmod{75}\) |
| \(16\pmod{35}\) | \(51\pmod{105}\) |
| \(36\pmod{55}\) | \(36\pmod{165}\) |
| \(60\pmod{77}\) | \(60\pmod{231}\) |
| \(1233\pmod{1925}\) | \(1233\pmod{5775}\) |

Together with the four pure classes, these are nine original classes
with distinct odd moduli. Their original common period is \(5775\).
Under \(\lambda\), the five child-event probabilities, in table order,
are
\[
 w=\left(\frac1{19},\frac2{57},\frac2{95},
         \frac1{60},\frac1{1140}\right).
 \tag{LC17}
\]
Use these exact probabilities as the event weights. Both the conflict
graph and the ordinary shared-coordinate graph satisfy the full strict
region condition. Avoiding the five events leaves exactly 1001 of the
1140 source words, defining one actual law \(\mu\).

For the query \(E=\{x:x\equiv1\pmod5\}\), the exact comparison is
\[
 \lambda(E)=\frac4{19},\qquad
 \mu(E)=\frac{16}{91}
 \le\frac{80396}{360221}
 <\frac{236}{997}.
 \tag{LC18}
\]
The middle fraction is (LC14) with the conflict graph. The last fraction
is the conditional query bound with the ordinary shared-coordinate
graph, under the same \(\lambda\) and \(\mu\). Their difference is
\[
 \frac{236}{997}-\frac{80396}{360221}
 =\frac{4857344}{359140337}>0.
\]
Thus residue compatibility gives a strictly smaller bound in this finite
example without changing the actual survivor law. This is not a
uniform fee improvement for a class of blocks.

The standard-library program
[laminar_conflict_conditioning_control.py](../frontier/cover-geometry/laminar_conflict_conditioning_control.py)
and its [exact data](../frontier/cover-geometry/laminar_conflict_conditioning_control.json)
retain every original label and the complete coordinate domains. They
check the 32 induced polynomials of each graph by both deletion
recurrence and direct independent-set summation, and check every old
event's conditional nonneighbor inequality in this example. They also
test all 2975 literal queries \(r\pmod d\) with \(d>1\) dividing 1925
and \(0\le r<d\), comparing actual conditional probabilities against
both graph bounds, including zero-probability queries. A direct sieve
of the original period 5775 verifies the same survivors in the parent
prefix \(0\pmod3\).

The program requires Python 3.10 or later and rejects optimized `-O`
execution. From the repository root, reproduce its exact data with

```sh
python3 -I docs/reports/erdos7-odd-covering/frontier/cover-geometry/laminar_conflict_conditioning_control.py --output /tmp/laminar-conflict-conditioning-control.json
```

## 6. Source scope and retained boundaries

The mathematical verification is the coordinate coupling (LC7)–(LC10)
and a direct application of the already cited conditional avoidance
theorem. These steps apply to all finite coordinate spaces and all
weights satisfying the stated hypotheses; a finite AP control does not
replace them.

[Chapter 16](16-canonical-conflict-resampling-and-the-exact-shearer-query-ratio.md)
proves a conflict-graph query inequality for a fixed canonical resampling
terminal law. Equation (LC14) concerns the actual law conditioned on
avoiding the original bad events. The similar polynomial expression does
not identify those laws. The present argument supplies a separate
justification for actual conditioning under the broader complete-coordinate
product hypothesis.

The conflict-Shearer star obstruction retained in Chapter 16 also remains
in force: an arbitrary original AP family need not satisfy the strict
region premise at its natural event charges. A failed certificate is not
a covering construction, and the conditional theorem does not remove
that obstruction.

This result is a repository application of known lopsided Shearer theory,
not a literature-priority claim. It contains no Lean certification. The
uniform statements needed for unrestricted odd-covering noncoverage, and
for a general dense six-prime-block fee, remain unproved here.
