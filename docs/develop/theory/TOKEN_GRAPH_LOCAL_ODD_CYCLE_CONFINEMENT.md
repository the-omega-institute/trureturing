# Token-graph confinement with locally odd-cycle neighborhoods

## 17. Original-carrier confinement for the local odd-cycle class

**定义 17.1（The graph class and the unchanged Boolean carrier）。**
Let $H$ be a finite connected simple graph with unit edge weights and
an even number $m\geq2$ of vertices. For every $p\in V(H)$ require
that the entire induced open neighborhood

$$
G_p=H[N_H(p)]
\tag{17.1}
$$

is bipartite or is one simple odd cycle $C_n$, where $n\geq3$ is
arbitrary. The bipartite alternative permits disconnected graphs,
isolated vertices and edgeless graphs. The cycle alternative is an
assertion about all of $G_p$, not a cycle selected from it.

Use the conventions of the owning volume,
[Token-graph blow-ups and a full-state defect certificate,
Definitions 1.1–1.2](TOKEN_GRAPH_BLOWUP_DEFECT_DECOMPOSITION.md).
In particular $B_i=\{i\}\times[2]$, $\Omega=\bigsqcup_iB_i$,
$H[\mathrm{empty}_2]=H[\overline{K_2}]$, and $\mathcal H_m$ is the
entire complex space with orthonormal basis the $m$-subsets of
$\Omega$. The positive ordinary adjacency $K$ has coefficient one
exactly for a single token moved along an edge of this blow-up.
Let $P_i$ be the original within-fibre symmetric projection and put

$$
P=\prod_iP_i,\qquad E=\min\operatorname{spec}K,
\qquad \mathcal N=\ker P.
\tag{17.2}
$$

The minimum is taken over all of $\mathcal H_m$, with only the
global occupancy constraint $k=m$.

**定理 17.2（Every ground vector for locally bipartite or odd-cycle
neighborhoods）。** For every $H$ in Definition 17.1,

$$
\ker(K-EI)\subseteq\operatorname{ran}P.
\tag{17.3}
$$

The space $\mathcal N$ is nonzero and reduces $K$. With precisely
the original $E$ in (17.2),

$$
\begin{aligned}
g&=\min\operatorname{spec}(K|_{\mathcal N})-E>0,\\
K-EI&\succeq g(I-P),\\
\|(I-P)\phi\|^2
&\leq\frac{\langle\phi,K\phi\rangle-E}{g}
\qquad(\phi\in\mathcal H_m,\ \|\phi\|=1).
\end{aligned}
\tag{17.4}
$$

These are whole-space assertions for arbitrary complex states,
including every feasible weight, all sector components and their
superpositions, and arbitrary entanglement.

Proof. Consume the complete Boolean chain representation in the
owning volume, (6.6)–(6.12), specialized in (13.4)–(13.5) and
(16.2). To fix all normalizations, its one-fibre orthonormal vectors
are

$$
\begin{aligned}
|1,-1\rangle&=|\varnothing\rangle,&
|1,0\rangle&=\frac{|\{1\}\rangle+|\{2\}\rangle}{\sqrt2},&
|1,1\rangle&=|\{1,2\}\rangle,\\
\chi=|0,0\rangle&=\frac{|\{1\}\rangle-|\{2\}\rangle}{\sqrt2}.
\end{aligned}
\tag{17.5}
$$

The triplet is the symmetric subspace $V_1$ and the singlet is
$V_0=\mathbb C\chi$. Both multiplicities are one. On these spaces
$n_i=I+Z_i$, the ladders $J_i^\pm=L_i^{\ast},L_i$ annihilate
$\chi$, and their spin-one coefficients are
$\sqrt{(1\mp x)(2\pm x)}$ for the move $x\mapsto x\pm1$.
The representation gives the orthogonal reducing decomposition

$$
\begin{aligned}
\mathcal H_m&\cong
\bigoplus_{\boldsymbol J\in\{0,1\}^m}
\left(\bigotimes_iV_{J_i}\right)_{\sum_iZ_i=0},\\
K_{\boldsymbol J}
&=\sum_{\{i,j\}\in E(H)}
 (J_i^+J_j^-+J_i^-J_j^+).
\end{aligned}
\tag{17.6}
$$

The summand for $\boldsymbol J$ includes every configuration
$|x_i|\leq J_i$, $\sum_i x_i=0$, with all complex coefficients.
Each summand is nonempty because each integer spin has weight zero.
The projection $P$ selects exactly $\boldsymbol J=(1,\ldots,1)$.
Thus no input symmetry has been assumed.

The primary representation parameters are Srinivasan,
[Theorem 1.2 and pp. 3–5](https://arxiv.org/pdf/1001.0280v2),
Boolean rank $2$, starting rank $t_i=1-J_i$ and up operator $L_i^*$;
and Feinsilver,
[§§3–4, Proposition 4.3 and §4.2.2](https://arxiv.org/pdf/1102.0368v2),
principal number $2-2t_i=2J_i$, $T=L_i^*$, $T^*=L_i$.
The two-letter counts $(2-n_i,n_i)$ in the complete
[OccupancyWordSectors supplier](../../../D5/S3/Quantum/Entanglement/OccupancyWordSectors.lean),
including sector_words_card_multinomial, its counting recurrences
and sector_gram, and its
[Scribe](../../../Blueprint/D5/S3/Quantum/Entanglement/OccupancyWordSectors.scribe.cs)
give the normalizations in (17.5), including occupancies zero and two.
For the [collective-oscillator supplier](AURIC_COLLECTIVE_OSCILLATORS_AND_RECORD_CAPACITY.md),
the algebraic map is $d=m$, $N=2$, $g=0$, $e=1$, $B=A(H)$,
$a_i=L_i/\sqrt2$ and $H_2=\hbar K/2$; no excitation truncation
is made. The singleton-difference definition in
[TokenGraphLaplacianRadiusRefutation](../../../D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.lean)
and its
[Scribe](../../../Blueprint/D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.scribe.cs)
gives exactly the coefficient-one moves in (17.6).
In Apte–Parekh–Sud,
[v3, Definition 1 and Fact 2](https://arxiv.org/html/2506.03441v3),
the blow-up has $2m$ vertices and the token number is $m$.
The shifted XY block $WI/2-K$ in that Fact is a different operator.
Neither refutation conclusion is used to infer confinement.

Suppose a summand of (17.6) with at least one $J_i=0$ attains $E$.
Choose a unit ground vector in it and fix one such site $p$.
At every other zero-spin site replace its factor $\chi$ by
$|1,0\rangle$, keeping the remaining vector unchanged. Each such
factor is initially one-dimensional, so this operation is defined
even when all other sites are entangled. Both factors have weight
zero and zero expectation of every spin component. The original
operator has no intrafibre term; all incident edge expectations
are consequently zero before and after this replacement.
Its total weight and energy expectation therefore stay zero and
$E$, respectively. Since $K-EI\succeq0$ on the whole original
carrier, a unit vector of expectation $E$ is an actual ground vector:
expand it in an orthonormal eigenbasis and use the nonnegativity of
every eigenvalue minus $E$. Repeat at all the other zero-spin sites.

This is only the nonstrict $0\to1$ comparison already used in
(7.4)–(7.5), (13.6) and the proof of Theorem 16.3. Its general
bilinear-spin source is Ghassemi Tabrizi–Henderson–Kühne–Scuseria,
[Appendix A4, (A34)–(A54) and the concluding fixed-magnetization
paragraph](https://pmc.ncbi.nlm.nih.gov/articles/PMC12613319/#app1-sec4),
DOI [10.1021/acs.jctc.5c01412](https://doi.org/10.1021/acs.jctc.5c01412).
Here maximal spin $s_i=1$, variable spin $t_i=J_i$, total
magnetization $M=0$, and the coupling tensor is
$\operatorname{diag}(2a_{ij},2a_{ij},0)$, where $a=A(H)$.
That existence/nonstrict comparison alone does not give (17.3).

We have obtained a unit actual ground vector
$\Psi=\chi_p\otimes f$ with spin one at every site other than $p$.
It satisfies $K_{H-p}f=Ef$ and $\sum_{i\ne p}Z_if=0$.
Write

$$
A=N_H(p),\quad R=V(H)\setminus(\{p\}\cup A),\quad
B_A^\pm=\sum_{i\in A}J_i^\pm,\quad Z_A=\sum_{i\in A}Z_i.
\tag{17.7}
$$

Connectedness and $m\geq2$ imply $A\ne\varnothing$.
Replace $\chi_p$ by $|1,0\rangle_p$. The same expectation argument
makes the result an actual ground vector at the same $E$.
Its eigenvector equation, resolved into the orthogonal local
weights $1,0,-1$ at $p$, gives

$$
0=\sqrt2\,|1,1\rangle_p\otimes B_A^-f
 +\sqrt2\,|1,-1\rangle_p\otimes B_A^+f,
\qquad B_A^-f=B_A^+f=0.
\tag{17.8}
$$

Since $[B_A^+,B_A^-]=2Z_A$, also $Z_Af=0$.
The spin-chain coefficients, or the Casimir identity, imply that
$f$ lies in the entire total-singlet subspace on $A$ tensored with
the space on $R$. All singlet multiplicity spaces are retained.
The original total-weight constraint then implies $Z_Rf=0$.

Let $\Pi_A$ be the projection onto that whole singlet subspace.
For any $i\in A$,

$$
\Pi_A X_i\Pi_A=\Pi_A Y_i\Pi_A=\Pi_A Z_i\Pi_A=0.
\tag{17.9}
$$

Indeed, simultaneous rotations of $A$ act as the identity on every
singlet copy. Rotation by $\pi$ about an orthogonal axis changes
the sign of the chosen component; sandwiching by $\Pi_A$ therefore
equates the operator to its negative. Thus (17.9) applies to
entangled vectors in the entire singlet tensor spectator space.
In particular all edges from $A$ to $R$ have zero expectation in
$f$. Set

$$
\rho_R=\operatorname{tr}_A|f\rangle\langle f|,\qquad
a=\langle f,K_Af\rangle,\qquad
b=\operatorname{tr}(\rho_RK_R),\qquad E=a+b.
\tag{17.10}
$$

Here $K_U$ denotes the sum of (17.6)'s actual edges with both
endpoints in $U$, on the spin-one factors there. The density
$\rho_R$ has trace one and is supported on $Z_R=0$.
If $R=\varnothing$, use its factor $\mathbb C$, $\rho_R=1$,
$K_R=0$, $b=0$. No local minimum has replaced the whole-space $E$.

First suppose $G_p$ is bipartite or $C_5$.
The owning volume supplies a unit zero-weight ground vector $u_A$
of $K_A$ that is not annihilated by both $B_A^+$ and $B_A^-$.
For bipartite graphs this is the complete local argument
(7.6)–(7.10), consumed at spin $S=1$; it includes disconnected
and edgeless neighborhoods. For $C_5$ it is the local argument in
the proof of Theorem 15.2, (15.4)–(15.8), also at $S=1$.
Precisely, a singlet ground energy would satisfy
$-12<e_A<-8$ by (15.8), while simultaneous rotations of its
eigenvector equation give $T_z u=(e_A/4)u$ with
$T_z=\sum_{\{i,j\}\in E(C_5)}Z_iZ_j$ integer diagonal.
Thus $e_A\in4\mathbb Z$, a contradiction. These are supplied
local results, not a new local spectral theorem.

Let $e_A$ be this zero-weight ground energy. Since $Z_Af=0$,
$a\geq e_A$. On the original carrier consider

$$
\rho=|\chi_p\rangle\langle\chi_p|\otimes
 |u_A\rangle\langle u_A|\otimes\rho_R.
\tag{17.11}
$$

Its total weight is zero. Each $\langle u_A,J_i^\pm u_A\rangle=0$
because the ladders change total weight. All crossing edges and
all edges incident to $p$ therefore have zero expectation.
The variational principle on the full carrier gives
$E\leq\operatorname{tr}(K\rho)=e_A+b\leq a+b=E$.
Diagonalize this same $\rho_R$ into unit weight-zero vectors $h_c$
with positive weights. Each
$\chi_p\otimes u_A\otimes h_c$ has expectation at least $E$;
their average is $E$, so each is an actual ground vector.
Release $p$ in any one of them. Equation (17.8) now forces
$(B_A^-u_A)\otimes h_c=(B_A^+u_A)\otimes h_c=0$,
contradicting the choice of $u_A$.

It remains to treat the cycle alternatives $C_3$ and odd $C_n$
with $n\geq7$. Put $D=\{p\}\cup A$; its induced graph is the
actual wheel $K_1\vee C_n$, including $K_4$ when $n=3$.
We use supplied singlet estimates and supplied trial vectors on
this induced graph, at exactly spin one and total weight zero.

For $n=3$, on the singlet subspace of the three spin-one sites,

$$
0=\left(\sum_{i\in A}\boldsymbol J_i\right)^2
=6I+2\sum_{\{i,j\}\subseteq A}\boldsymbol J_i\cdot\boldsymbol J_j.
\tag{17.12}
$$

Rotations equate the three same-axis expectations. Since
$K_A=2\sum_{\{i,j\}\subseteq A}(X_iX_j+Y_iY_j)$, they give
$a=-4$. These identities hold for any density supported on the
singlet space, including the reduced density of our $f$.
The owning volume's actual four-site trial (13.13)–(13.14) is

$$
d_1=\frac{|1,-1\rangle-|0,0\rangle+|-1,1\rangle}{\sqrt3},
\qquad v_D=(d_1)_{p,a_1}\otimes(d_1)_{a_2,a_3},
\qquad \langle v_D,K_Dv_D\rangle=-\frac{16}{3}<-4.
\tag{17.13}
$$

Here $A=\{a_1,a_2,a_3\}$ and the two coordinates in each ket of
$d_1$ are magnetic weights of two actual triplet sites, not Boolean
coordinates. This is the classical spin-one pair singlet,
[NIST DLMF (34.1.1), (34.3.1)](https://dlmf.nist.gov/34.3#E1),
with coupled spin zero. Its pair edge has expectation $-8/3$;
the four edges joining different pairs have expectation zero.
In particular $v_D$ is normalized and has total weight zero.

For odd $n\geq7$, consume the singlet estimate (16.15)–(16.16)
on the whole cycle. Its coupling parameters are three spins one:
the two neighbors have spin $q=0,1,2$, and coupling to the central
spin one gives $l=|q-1|,\ldots,q+1$.
The Casimir eigenvalue
$\{l(l+1)-2-q(q+1)\}/2$ is at least $-3$.
Summing these local operators counts each isotropic cycle edge
twice and gives $H_{\rm iso}\succeq-3nI/2$.
On a singlet, rotation equates the three same-axis expectations,
so $\langle K_A\rangle=(4/3)\langle H_{\rm iso}\rangle\geq-2n$.
These are the triangle and coupling rules of
[DLMF §§34.1–34.3](https://dlmf.nist.gov/34.1), used at their
spin-one hypotheses in the owning volume. By linearity the same
bound holds for any singlet-supported density. Consequently

$$
a\geq-2n.
\tag{17.14}
$$

The supplied trial in (16.4)–(16.10), with the strict comparison
(16.11)–(16.12), is an actual normalized vector on these $n+1$
original two-coordinate fibres. In explicit parameters, let
$r=(n-1)/2$, $u_j=e^{2\pi\mathrm i rj/n}$, and put

$$
w_p=-1,\qquad w_j=\frac{u_j+1/10}{1+u_j/10},\qquad
v_D(T)=\binom{2(n+1)}{n+1}^{-1/2}
 \prod_{(i,c)\in T}w_i\quad(|T|=n+1).
\tag{17.15}
$$

Each phase has modulus one, so $v_D$ has norm one. It is
within-fibre invariant, hence belongs to the actual spin-one
factors, and has total weight zero. The supplied estimate is

$$
\langle v_D,K_Dv_D\rangle
\leq-\frac{4n(n+1)}{2n+1}
 \left(\frac{49}{50}\cos\frac\pi n+\frac7{100}\right)
<-2n\leq a.
\tag{17.16}
$$

This use is of the explicit trial, not of a minimum over a
symmetric-input carrier. Its subset phase count is the intermediate
in the owning volume (3.5)–(3.7) and (16.9)–(16.10), with parameters
$N_D=2(n+1)$, $k_D=n+1$, $s=2$.
The complete count, including private proof-local counting_identity,
W_move, phi40_norm, phi40_energy and choose_ratio40 in
[CutBoundRefutation](../../../D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.lean)
and its
[Scribe](../../../Blueprint/D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.scribe.cs),
supplies this counting mechanism; its fixed instance has $N=200$,
$k=100$, $s=40$, and its refutation is not used as a confinement
premise. The classical fixed-magnetization trial in
Bärwinkel–Schmidt–Schnack,
[§§2.2–2.3, (14)–(21)](https://arxiv.org/pdf/cond-mat/0210458v2),
assumes cyclic coupling. Here the consumed bound is the explicit
wheel calculation of Section 16, not a generalization of those
classical bounds beyond their hypotheses.

For either cycle case form the density on the entire original carrier

$$
\widetilde\rho=|v_D\rangle\langle v_D|\otimes\rho_R.
\tag{17.17}
$$

It has global weight zero. Every one-site ladder expectation of
$v_D$ is zero, since $v_D$ has definite total weight zero.
Thus every actual edge between $D$ and $R$ has zero expectation
in (17.17). In the old state, the edges from $p$ have zero
expectation because it is a singlet, and those from $A$ to $R$
have zero expectation by (17.9). The same outside marginal
$\rho_R$ retains exactly the energy $b$ of all edges within $R$.
No edge or attachment has been removed. Equations (17.13) or
(17.16) consequently imply

$$
\operatorname{tr}(K\widetilde\rho)
=\langle v_D,K_Dv_D\rangle+b<a+b=E,
\tag{17.18}
$$

contrary to the whole-carrier variational principle.
The local weight-zero factors in this trial were available because
(17.8) forced the singlet condition on the supposed ground vector;
no separate-filling premise was placed on that vector or on the
original carrier.

The supplied same-state replacement arguments (13.9)–(13.14),
(15.10)–(15.13) and (16.17)–(16.18) underlie this comparison.
Their two-auxiliary precedent is Benassi–Lees–Ueltschi,
[v3, §4.3, Lemma 9 and (4.12)–(4.17)](https://arxiv.org/pdf/1510.03215v3),
DOI [10.1007/s10955-016-1580-2](https://doi.org/10.1007/s10955-016-1580-2).
Their $R^i$ is the sum of two spin-half operators. Their strictness
uses a negative Hamiltonian and nonnegative product couplings in
directions 1 and 3; that statement is not applied to positive
adjacency on the present nonbipartite bases.
The additional graph-domain inference here is that the supplied
wheel trials may be used on $H[\{p\}\cup N_H(p)]$ while keeping
this same outside marginal. Together with the supplied bipartite
and five-cycle obstructions, this excludes every deficient sector
for the entire class (17.1), with arbitrary legal attachments.
It does not assert a new representation theorem, isolated-wheel
theorem or classical local spectral package.

Every deficient summand of (17.6) has now been excluded from the
actual eigenvalue $E$. An arbitrary complex ground vector decomposes
into these orthogonal reducing summands, and any nonzero component
would itself be an $E$-ground vector. Hence it lies entirely in the
all-spin-one summand, proving (17.3) with all superpositions and
entanglement retained.

The original vector $\chi_p\otimes\bigotimes_{i\ne p}|1,0\rangle_i$
has exactly $m$ particles and is a nonzero vector in $\mathcal N$.
All fibre permutations commute with $K$, so $P$ commutes with $K$
and $\mathcal N$ reduces it. Its spectrum is finite and nonempty,
and (17.3) excludes $E$ from that spectrum. Since $E$ was the
whole-space minimum, $g>0$. On $\operatorname{ran}P$,
$K-EI\succeq0$; on $\mathcal N$, $K-EI\succeq gI$.
Adding the two reducing quadratic forms proves (17.4), and taking
a normalized complex-vector expectation gives its mass inequality.
This is the finite-spectrum consequence already used in (13.3),
(15.2) and (16.14); it yields no exact value of $E$, numerical
lower bound for $g$ or rate. $\square$

**推论 17.3（The same graph class at every equal even fibre size）。**
For precisely the graphs $H$ of Definition 17.1 and every integer
$S\geq1$, put $s=2S$, $\Omega_s=V(H)\times[s]$ and
$k_s=mS=ms/2$. On the entire original complex Boolean carrier
$\mathcal H_{k_s}$ of $H[\mathrm{empty}_s]$, let $K_s$ be positive
ordinary adjacency and $P_s$ the product of the original symmetric
fibre projections. With

$$
E_s=\min\operatorname{spec}K_s,\qquad
\mathcal N_s=\ker P_s,
\tag{17.19}
$$

one has $\ker(K_s-E_sI)\subseteq\operatorname{ran}P_s$.
The space $\mathcal N_s$ is nonzero and reduces $K_s$, and

$$
\begin{aligned}
g_s&=\min\operatorname{spec}(K_s|_{\mathcal N_s})-E_s>0,\\
K_s-E_sI&\succeq g_s(I-P_s),\\
\|(I-P_s)\phi\|^2
&\leq\frac{\langle\phi,K_s\phi\rangle-E_s}{g_s}
\qquad(\phi\in\mathcal H_{k_s},\ \|\phi\|=1).
\end{aligned}
\tag{17.20}
$$

Each $E_s$ is its own actual whole-space minimum; each $g_s$ is
defined relative to that same $E_s$.

Proof. At $S=1$ use Theorem 17.2. At $S\geq2$ consume Theorem 15.2
of the owning volume at its condition (b), whose exact scale
hypothesis is $s=2S\geq4$. To check this condition, every odd cycle
$C_n$ in (17.1) has the orthogonal Fourier basis
$z^{(j)}_a=e^{2\pi\mathrm i ja/n}$, $0\leq j,a<n$.
A geometric sum proves orthogonality, and cycle adjacency gives
eigenvalues $2\cos(2\pi j/n)$. The angles nearest $\pi$ give the
least eigenvalue $-2\cos(\pi/n)$, attained at
$j=(n-1)/2,(n+1)/2$. Each such vector has modulus-one coordinates.
This includes $n=3,5$ and every longer odd cycle. The cycle has
an edge; the bipartite alternative of condition (b) imposes no
connectedness or nonempty-edge requirement. Thus every vertex
satisfies its exact condition.

The cited theorem acts on the full carrier in (17.19), including
all spins $J_i=S-t_i$, $0\leq t_i\leq S$, all multiplicity copies
$r_{2S}(t_i)=\binom{2S}{t_i}-\binom{2S}{t_i-1}$ and all feasible
global weights $\sum_i x_i=0$, $|x_i|\leq J_i$.
Its representation-source map is Boolean rank $2S$, starting rank
$t_i$, principal number $2S-2t_i$, and ladders $L_i^*,L_i$.
No assertion at $S=1$ is extracted from condition (b).

For the nonzero-complement endpoint explicitly, choose a nonconstant
one-particle vector in one fibre, an occupancy-$(2S-1)$ vector in a
second fibre, and occupancy-$S$ vectors in all remaining fibres.
Their product is killed by $P_s$ and has total occupancy
$1+(2S-1)+(m-2)S=mS$. It exists also when $m=2,S=1$.
Commutation with all fibre permutations gives reduction, and the
same finite-spectrum argument proves (17.20).
Thus the additional scale endpoint is $s=2$ for the graph class
(17.1); the larger even scales are exactly the stated application
of Section 15. Arbitrary connected even-order bases outside the
stated neighborhood alternatives remain unresolved here.
These conclusions supply no necessity criterion, weighted or
unequal or odd-fibre statement, other filling, changed-sign operator,
physical realization, exact energy or quantitative gap estimate.
$\square$

## 18. An interacting family with two shared-edge wheel regions

**定义 18.1（Two odd rims sharing one actual edge）。**
Choose arbitrary integers $r,t\geq3$ and put $n_1=2r+1$,
$n_2=2t+1$. Start with hubs $h_1,h_2$ and rims
$(v_{a,j})_{j\in\mathbb Z/n_a\mathbb Z}$, $a=1,2$.
Identify only $v_{1,0}=v_{2,0}=u$ and
$v_{1,1}=v_{2,1}=v$. Include all rim edges and all spokes
$h_av_{a,j}$, counting the common rim edge $uv$ only once.
Add two distinct vertices $\ell_1,\ell_2$, each with the unique
neighbor $v_{1,3}$. There are no other identifications or edges.
Call this simple unit-weight graph $H_{r,t}$ and write
$W_a=\{h_a\}\cup\{v_{a,j}:j\in\mathbb Z/n_a\mathbb Z\}$.

**命题 18.2（Legality, interaction and separation from the supplied
graph domains）。** Every $H_{r,t}$ is a connected even-order graph
in Definition 17.1. Hence it satisfies (17.3)–(17.4) and, for every
equal even fibre size, (17.19)–(17.20), on the original global
half-filled carrier. Its two longer-odd-cycle wheel regions share
actual fibres and permit transfer of occupancy between regions.
It lies outside every sufficient whole-graph $s=2$ confinement
domain stated through Section 16 of the owning volume.

Proof. Each wheel is connected and they share the edge $uv$;
the leaves preserve connectedness. The core has
$(n_1+1)+(n_2+1)-2=n_1+n_2$ vertices, so the full order is
$m=n_1+n_2+2$, even and at least $16$.
The following are the entire induced open neighborhoods.
At $h_a$ it is exactly the cycle $C_{n_a}$.
At a private rim vertex it is the path through its own hub between
its two rim neighbors. At $v_{1,3}$ the two leaves add two isolated
vertices to that path. At either leaf it is a single vertex.
At the shared vertices the neighborhoods are exactly the paths

$$
\begin{aligned}
G_u:&\quad
v_{1,n_1-1}-h_1-v-h_2-v_{2,n_2-1},\\
G_v:&\quad
v_{1,2}-h_1-u-h_2-v_{2,2}.
\end{aligned}
\tag{18.1}
$$

Indeed there is no edge between private vertices of different rims;
the spokes and the two incident rim edges give exactly the displayed
adjacencies. The inequalities $n_a\geq7$ preclude additional rim
adjacencies among the listed vertices. Each listed path, isolated
vertex and union of them is bipartite. Thus (17.1) holds at every
vertex, with two genuinely longer odd cycles as hub neighborhoods.
Theorem 17.2 and Corollary 17.3 apply with no extra filling condition.

To verify interaction on the original carrier, fix any even $s\geq2$
and put $k=ms/2$. Define the regional occupancy
$M_a=\sum_{i\in W_a}n_i$ there. The sets $W_1,W_2$ share the
actual base vertices $u,v$, hence their same Boolean fibres and
the actual edge $uv$; they are not disjoint tensor factors.
Choose one coordinate $x\in B_u$ and one $y\in B_{h_2}$.
There exists a $k$-subset $T$ with $x\in T$, $y\notin T$:
choose its other $k-1$ coordinates from the remaining $ms-2$,
which is possible because $1\leq k\leq ms-1$.
Let $T'=T\setminus\{x\}\cup\{y\}$. The spoke $uh_2$ makes
$\langle T'|K_s|T\rangle=1$, while $h_2\notin W_1$ and
$u\in W_1$. Consequently

$$
\langle T'|[M_1,K_s]|T\rangle
=(M_1(T')-M_1(T))\langle T'|K_s|T\rangle=-1.
\tag{18.2}
$$

Using $y\in B_{h_1}$ instead proves $[M_2,K_s]\ne0$.
Thus neither region has separately conserved occupancy under the
original global half-filling dynamics. These are overlapping
interacting regions, not independent half-filled single wheels.

We check noncoverage against the exact sufficient hypotheses of
the owning volume. Each hub has just one neighborhood component,
namely the nonbipartite cycle $C_{n_a}$, $n_a\geq7$.
Thus Section 7's wholly bipartite-neighborhood condition fails,
and Definition 14.1's requirement of at least one bipartite
component in each neighborhood also fails. The same hub contradicts
Definition 15.1(a), bipartite-or-$C_5$.
Definition 15.1(b) does hold, as in Corollary 17.3, but its
confinement theorem assumes $s\geq4$ and supplies no $s=2$ conclusion.

The core obtained by deleting the two leaves is two-connected.
Each wheel remains connected after deleting any one of its vertices:
a deleted hub leaves a cycle, and a deleted rim vertex leaves its
hub joined to all vertices of a path. After deleting any vertex
of the union, the two surviving wheels still share at least one
of $u,v$. Their union therefore stays connected. A pendant vertex
cannot belong to any two-connected subgraph, so this core is a
maximal two-connected block of $H_{r,t}$. It is not a clique:
$v_{1,0}$ and $v_{1,2}$ are not adjacent. Hence the block-graph
hypotheses of Sections 12–13 fail, including the all-even
block-graph consequence.

The graph is not complete multipartite. The vertex $v_{1,0}$ is
nonadjacent to both $v_{1,2}$ and $v_{1,3}$, whereas the latter
two are adjacent. In a complete multipartite graph distinct
nonadjacent vertices must lie in one independent part, which
these three relations make impossible. Thus neither the balanced
nor the dominant-part domains of Sections 10–11, nor their
combined complete-multipartite conclusion, apply.

The global flat least-mode assumption of Sections 3–6 also fails.
Let $\lambda=\min\operatorname{spec}A(H_{r,t})$.
A least Fourier vector on the first induced rim, extended by zero
at every other vertex, has Rayleigh quotient
$-2\cos(\pi/n_1)<-1$. Edges to vertices with zero coordinates
contribute zero. Therefore
$\lambda\leq-2\cos(\pi/n_1)<-1$.
If a modulus-one vector $z$ satisfied $A(H_{r,t})z=\lambda z$,
the equation at either leaf would give
$\lambda z_{\ell_i}=z_{v_{1,3}}$. Taking moduli forces
$|\lambda|=1$, a contradiction. The general full-state defect
certificate of Section 2 imposes no such graph condition, but is
a lower bound and does not itself assert exact every-ground
confinement at $s=2$. Section 6 also has a larger-scale requirement.

The individual-wheel domain of Definition 16.1 does not contain
$H_{r,t}$: an individual wheel there has no degree-one vertex,
whereas $H_{r,t}$ has two. Nor is it the five-rim-with-leaves
family of Proposition 15.3. Removing all degree-one vertices from
that family leaves a six-vertex wheel, while here it leaves the
core of order $n_1+n_2\geq14$ just described. Proposition 15.4
concerns individual wheels at $s\geq4$, except for its already
supplied five-rim endpoint. Finally, the odd-fibre domains of
Sections 8–9 do not include $s=2$.

This exhausts the stated sufficient graph domains through Section 16.
The separation is relative to those exact source hypotheses;
it is not a claim that confinement fails elsewhere, a necessity
result or a priority assertion. The new consumer is the entire
family $r,t\geq3$, with the interaction (18.2) on its original
carrier. $\square$

## 追加锚（本行以下为增补区）

## 19. Necessary singlet ground spaces on the actual neighborhood components

**定义 19.1（The original carrier and the local component spaces）。**
Let $H$ be finite, connected, simple and unit-weight, with even order
$m\geq2$. Fix any integer $S\geq1$ and put $s=2S$,
$B_i=\{i\}\times[2S]$ and $\Omega_s=\bigsqcup_i B_i$.
Use the entire complex Boolean space

$$
\mathcal H_{mS}=\operatorname{span}_{\mathbb C}
 \{|T\rangle:T\subseteq\Omega_s,\ |T|=mS\}.
\tag{19.1}
$$

Its orthonormal basis is indexed by actual subsets. The operator $K_s$
is positive ordinary token adjacency on $H[\overline{K_{2S}}]$:
its entry is one exactly for a single token moved along an actual
blow-up edge. Let $P_i$ be the orthogonal projection invariant under
all original permutations of $B_i$, and put

$$
P_s=\prod_iP_i,\qquad E_s=\min\operatorname{spec}K_s.
\tag{19.2}
$$

These are the definitions of the
[owning volume, Definitions 1.1–1.2](TOKEN_GRAPH_BLOWUP_DEFECT_DECOMPOSITION.md).
Only the global occupancy $mS$ is imposed.

For a subset $U\subseteq V(H)$, write $V_S^{\otimes U}$ for the tensor
product of the actual symmetric spin-$S$ fibre spaces, and define

$$
\begin{aligned}
Z_U&=\sum_{i\in U}Z_i,& B_U^\pm&=\sum_{i\in U}J_i^\pm,\\
K_U&=\sum_{\{i,j\}\in E(H[U])}
 (J_i^+J_j^-+J_i^-J_j^+),&
\mathcal V_U(0)&=\ker Z_U\subseteq V_S^{\otimes U},\\
e_U(0)&=\min\operatorname{spec}(K_U|_{\mathcal V_U(0)}),&
\mathcal G_U(0)&=\ker(K_U-e_U(0)I)\cap\mathcal V_U(0),\\
\mathcal S_U&=\ker B_U^+\cap\ker B_U^-.
\end{aligned}
\tag{19.3}
$$

Here $Z_i=n_i-SI$, $J_i^+=L_i^\ast$ and $J_i^-=L_i$ on a symmetric
fibre. The common ladder kernel $\mathcal S_U$ is the entire total-spin
singlet space, with all its multiplicities. Each $\mathcal V_U(0)$
is nonempty: it contains $\bigotimes_{i\in U}|S,0\rangle_i$.
For an empty tensor product use $\mathbb C$, zero operators and minimum
zero. A reduced density on $U$ is the actual partial trace over the
complementary original coordinates; no independent filling is part of
this definition.

**定理 19.2（A deficient minimum forces separate component singlet ground
spaces）。** Suppose that an original reducing spin sector with
$J_p<S$ at a specified vertex $p$ attains the actual $E_s$ of (19.2).
There exists a normalized original $E_s$-ground vector $\Psi$ whose spin
at $p$ is this same $J_p$ and whose spin is $S$ at every $i\ne p$.
For every actual connected component $C$ of $H[N_H(p)]$, this
realization satisfies

$$
\begin{aligned}
B_C^\pm\Psi&=0,\qquad Z_C\Psi=0,\\
\operatorname{ran}\rho_C&\subseteq\mathcal G_C(0),
 \qquad \rho_C=\operatorname{tr}_{V(H)\setminus C}
                         |\Psi\rangle\langle\Psi|,\\
\mathcal G_C(0)&\subseteq\mathcal S_C.
\end{aligned}
\tag{19.4}
$$

In particular, every vector in the local zero-weight ground space is
a total singlet, not only the vectors in the support of $\rho_C$.
This is an existence statement for a minimizing realization. It does
not assert that all marginals of an initially chosen deficient ground
vector are preserved.

Proof. The complete orthogonal Boolean-chain representation of the
[owning volume, (6.6)–(6.12)](TOKEN_GRAPH_BLOWUP_DEFECT_DECOMPOSITION.md)
gives, on the unchanged space (19.1),

$$
\begin{aligned}
\mathcal H_{mS}&\cong
\bigoplus_{\substack{0\leq t_i\leq S\\
                     1\leq a_i\leq r_{2S}(t_i)}}
 \left(\bigotimes_iV_{S-t_i}\right)_{\sum_iZ_i=0},\\
r_{2S}(t)&=\binom{2S}{t}-\binom{2S}{t-1},\qquad \binom{2S}{-1}=0,\\
J_i^\pm|J_i,x\rangle
 &=\sqrt{(J_i\mp x)(J_i\pm x+1)}\,|J_i,x\pm1\rangle,
 \qquad -J_i\leq x\leq J_i,\\
K_{\boldsymbol J}&=\sum_{\{i,j\}\in E(H)}
 (J_i^+J_j^-+J_i^-J_j^+)
 =2\sum_{\{i,j\}\in E(H)}(X_iX_j+Y_iY_j),
\end{aligned}
\tag{19.5}
$$

where $J_i=S-t_i$, $X_i=(J_i^++J_i^-)/2$ and
$Y_i=(J_i^+-J_i^-)/(2\mathrm i)$. The occupancy is $S+x$.
Every summand retains all weights $|x_i|\leq J_i$ with
$\sum_i x_i=0$, all complex coefficients, and arbitrary entanglement.
The index $a_i$ retains every multiplicity copy. Endpoint ladder
coefficients are zero. The projection $P_s$ selects precisely $t_i=0$
for all $i$.

The primary parameter map in this representation is Srinivasan,
[Theorem 1.2](https://arxiv.org/html/1001.0280v2), Boolean rank $2S$,
starting rank $t_i$, up operator $L_i^\ast$ and layer index
$u=S+x$: its coefficient
$\sqrt{(u+1-t_i)(2S-t_i-u)}$ is the raising coefficient in (19.5).
Feinsilver,
[§3, (8)–(10), §4, (16), Proposition 4.3 and §4.2.2](https://arxiv.org/html/1102.0368v2),
has $T=L_i^\ast$, $T^\ast=L_i$, principal number
$2S-2t_i=2J_i$, chain index $J_i+x$ and grading operator $-2Z_i$.
Its vacuum count is exactly $r_{2S}(t_i)$ and its orthogonality
includes all copies. These are consumed representation results.
The complete
[OccupancyWordSectors](../../../D5/S3/Quantum/Entanglement/OccupancyWordSectors.lean)
and its [Scribe](../../../Blueprint/D5/S3/Quantum/Entanglement/OccupancyWordSectors.scribe.cs),
including the counting recurrences, `sector_words_card_multinomial`
and `sector_gram`, normalize the symmetric vectors by the two-letter
counts $(2S-n_i,n_i)$, including $n_i=0,2S$.
The [collective-oscillator volume](AURIC_COLLECTIVE_OSCILLATORS_AND_RECORD_CAPACITY.md)
has algebraic parameters $d=m$, $N=2S$, $g=0$, $e=1$,
$B=A(H)$, $a_i=L_i/\sqrt{2S}$ and
$H_{2S}=\hbar K_s/(2S)$; no fixed-excitation approximation is used.
The singleton-difference definition in the complete
[TokenGraphLaplacianRadiusRefutation](../../../D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.lean)
and its [Scribe](../../../Blueprint/D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.scribe.cs)
is exactly the move defining $K_s$. The primary normalization is
Apte–Parekh–Sud,
[v3, Definition 1 and Fact 2](https://arxiv.org/html/2506.03441v3),
with $2mS$ vertices, $mS$ tokens and edge weights one. Their shifted
operator $WI/2-K_s$ is a different operator. No refutation conclusion
is used as a confinement premise.

First use the nonstrict spin comparison of the
[owning volume, (7.4)–(7.5)](TOKEN_GRAPH_BLOWUP_DEFECT_DECOMPOSITION.md).
Its primary source is Ghassemi Tabrizi–Henderson–Kühne–Scuseria,
[Appendix A4, (A34)–(A54) and its final fixed-magnetization paragraph](https://pmc.ncbi.nlm.nih.gov/articles/PMC12613319/#app1-sec4),
DOI [10.1021/acs.jctc.5c01412](https://doi.org/10.1021/acs.jctc.5c01412).
The maximal local spin there is $s_i=S$, the variable spin is
$t_i=J_i$, the magnetization is $M=0$, and the bilinear coupling is
$D_{ij}=\operatorname{diag}(2a_{ij},2a_{ij},0)$, $a=A(H)$.
Only its nonstrict existence conclusion is consumed. In the explicit
fixed-weight proof, the upper-spin projection of
$|j,x\rangle\otimes|1,0\rangle$ has squared norm

$$
\frac{(j+1)^2-x^2}{(j+1)(2j+1)}>0
\qquad(-j\leq x\leq j),
\tag{19.6}
$$

including $j=0$ and $x=\pm j$. The pair has zero Cartesian spin
expectations, so the trial keeps the energy and total weight.
For completeness, let $\eta_j$ be the minimum with this one
local spin $j$, all other spins fixed, and total weight zero.
The trial is a ground vector for $\eta_j$ tensored with the
weight-zero triplet. For $j=0$ it lies entirely in spin one,
so $\eta_1\leq\eta_0$. For $j\geq1$, decompose it into the
spins $j+1,j,j-1$ of $j\otimes1$. If induction gives
$\eta_{j-1}\geq\eta_j$, the two lower-spin projected energies
are at least $\eta_j$. Their average with the nonzero upper-spin
contribution is $\eta_j$. Thus the upper contribution has energy
at most $\eta_j$ and $\eta_{j+1}\leq\eta_j$. Distinct $x$ have orthogonal projected images, so
(19.6) remains nonzero for an arbitrary entangled input. Increase
each spin other than the specified $J_p$ to $S$. Every resulting
sector occurs in (19.5) and has minimum at least $E_s$; the comparison
gives at most $E_s$. Consequently it still attains precisely $E_s$.

Realize the spin $J_p$ on $2J_p$ symmetric original coordinates in
$B_p$, together with $S-J_p\geq1$ actual singlet pairs. Each pair
contains one particle and is annihilated by its collective spin.
At weight $x_p$ the occupancy is
$(J_p+x_p)+(S-J_p)=S+x_p$, so this is an actual copy inside the
original fibre. Since collective spin acts identically on all
multiplicity copies, transferring a minimizing vector to this copy
preserves its energy. Select one pair and write the resulting unit
ground vector as

$$
\Psi=\chi\otimes f,\qquad
\chi=\frac{|10\rangle-|01\rangle}{\sqrt2}.
\tag{19.7}
$$

All remaining coordinates, including the remaining coordinates at
$p$, stay in $f$. Set $A=N_H(p)$,
$R=V(H)\setminus(\{p\}\cup A)$ and let $Q$ denote those remaining
coordinates at $p$ together with $R$. Set $Z_Q=\sum_{u\in Q}(n_u-\tfrac12 I)$ on those actual
coordinates and $\mathcal Q(0)=\ker Z_Q$. Since the selected
pair has weight zero, $(Z_A+Z_Q)f=0$. The set $A$ is nonempty by
connectedness and $m\geq2$.

Replace $\chi$ by $\tau=(|10\rangle+|01\rangle)/\sqrt2=|1,0\rangle$.
Both states have weight zero and zero expectations of all three
collective Cartesian components. There is no intrafibre term in
$K_s$. Hence $\tau\otimes f$ has the same original occupancy and
energy expectation $E_s$. Since $K_s-E_sI\succeq0$ on (19.1),
a unit vector with this expectation is a ground eigenvector:
in a spectral expansion all terms
$(\theta-E_s)|c_\theta|^2$ are nonnegative and their sum is zero.
The equation for $\chi\otimes f$ first gives
$K^{\mathrm{rem}}f=E_sf$, where $K^{\mathrm{rem}}$ omits just the
selected pair. The equation after replacement then gives

$$
0=\sqrt2\,|1,1\rangle\otimes B_A^-f
  +\sqrt2\,|1,-1\rangle\otimes B_A^+f.
\tag{19.8}
$$

The pair weights are orthogonal, so $B_A^-f=B_A^+f=0$.
Their commutator is $[B_A^+,B_A^-]=2Z_A$, so $Z_Af=0$.
The ladder coefficients in each total-spin chain show that their
common kernel consists exactly of spin-zero chains. Thus
$f\in\mathcal S_A\otimes\mathcal Q(0)$, with the full singlet
multiplicity space and all allowed spectators retained.

If $\Pi_A$ projects onto $\mathcal S_A$, then, for every $i\in A$,

$$
\Pi_A X_i\Pi_A=\Pi_A Y_i\Pi_A=\Pi_A Z_i\Pi_A=0.
\tag{19.9}
$$

Indeed a simultaneous rotation of $A$ fixes every vector in every
singlet copy. Rotation by $\pi$ about an orthogonal axis reverses
the specified Cartesian component; sandwiching equates the operator
to its negative. Tensoring (19.9) with any operator on $Q$ proves
that all $A$–$Q$ edge expectations vanish even in the entangled
$f$. There are no $p$–$R$ edges. If
$\rho_Q=\operatorname{tr}_A|f\rangle\langle f|$, then

$$
a=\langle f,K_Af\rangle,\qquad
b=\operatorname{tr}(\rho_QK_R),\qquad E_s=a+b.
\tag{19.10}
$$

The density $\rho_Q$ has trace one and support of joint weight zero;
it is not replaced by a minimizing density on $Q$.

Choose any unit $u\in\mathcal G_A(0)$. The density

$$
\sigma_u=|\chi\rangle\langle\chi|\otimes
 |u\rangle\langle u|\otimes\rho_Q
\tag{19.11}
$$

belongs to the unchanged original globally half-filled carrier.
Every one-site expectation $\langle u,J_i^\pm u\rangle$ is zero
because $u$ has definite total weight. All crossing expectations
therefore vanish in this product density, including those with the
remaining coordinates at $p$. Since $f$ also has $A$-weight zero,

$$
E_s\leq\operatorname{tr}(K_s\sigma_u)
=e_A(0)+b\leq a+b=E_s.
\tag{19.12}
$$

Consequently $a=e_A(0)$ and the actual $A$ reduced density is
supported on $\mathcal G_A(0)$: diagonalize the positive operator
$K_A-e_A(0)I$ on $\mathcal V_A(0)$, whose expectation is zero.
This conclusion does not require that $K_A$ preserve the singlet
space.

Moreover, (19.12) holds for every chosen unit $u$ in that ground
space. Diagonalize $\rho_Q=\sum_c w_c|h_c\rangle\langle h_c|$ with
$w_c>0$ and unit zero-weight $h_c$. Each
$\chi\otimes u\otimes h_c$ has energy at least $E_s$; their
weighted average is $E_s$, so each is an actual ground eigenvector.
Release its selected pair as in (19.8). It follows that
$B_A^\pm u=0$. We have proved the universal inclusion

$$
\mathcal G_A(0)\subseteq\mathcal S_A.
\tag{19.13}
$$

We now separate the actual connected components, without prescribing
their fillings. For any such component $C$, $K_A$ commutes with
$Z_C$, because no edge of $H[A]$ joins $C$ to its complement in
$A$. If $u\in\mathcal G_A(0)$ and a weight projection
$v=\mathbf1_{Z_C=q}u$ is nonzero, then $v\in\mathcal G_A(0)$.
By (19.13), $v$ is a total singlet on $A$. A simultaneous rotation
of $A$ by $\pi$ about the $x$ axis reverses $Z_C$ while fixing $v$.
Thus

$$
q\|v\|^2=\langle v,Z_Cv\rangle
=-\langle v,Z_Cv\rangle=0,
\tag{19.14}
$$

and $q=0$. Every component weight of every $u\in\mathcal G_A(0)$
is therefore zero. Using $B_A^\pm u=0$ and $Z_Cu=0$ gives

$$
0=[Z_C,B_A^\pm]u=\pm B_C^\pm u.
\tag{19.15}
$$

Hence every such $u$ is separately a singlet on every actual
component. This step uses the independent weight conservation of
actual components; it does not select a cycle or other proper
subgraph from a component.

On $\bigotimes_C\mathcal V_C(0)$ the operator $K_A$ is the sum of
the component operators. A unit $u\in\mathcal G_A(0)$ lies in this
space by (19.14), so $e_A(0)\geq\sum_C e_C(0)$. Conversely, a
product of unit vectors from all $\mathcal G_C(0)$ has total
weight zero and energy $\sum_C e_C(0)$, proving

$$
e_A(0)=\sum_C e_C(0).
\tag{19.16}
$$

The actual $A$ reduced density is supported in all component
zero-weight spaces, and its expectation of the sum of the positive
operators $K_C-e_C(0)I$ is zero. Each expectation is nonnegative,
so each vanishes. Partial trace and the spectral equality argument
therefore give $\operatorname{ran}\rho_C\subseteq\mathcal G_C(0)$.
Finally choose any unit $u_C\in\mathcal G_C(0)$ and any ground
vector on each other component. Their product belongs to
$\mathcal G_A(0)$ by (19.16). Equation (19.15) applied to it gives
$B_C^\pm u_C=0$. This proves the last inclusion of (19.4) for
every vector in that space, and the same equations applied to the
support of the actual density prove the first line of (19.4).
All arguments allow $R=\varnothing$; an empty spectator is
$\mathbb C$ with zero operator. The constructed vector is the
required minimizing realization, with no assertion of unchanged
marginals for every original deficient vector. $\square$

## 20. The whole-fibre cone equality at spin one

**定理 20.1（A necessary original-cone equality, only at $S=1$）。**
Use Definition 19.1 at $S=1$. Suppose an original sector deficient
at $p$ attains $E_2$. For every actual connected component $C$ of
$H[N_H(p)]$, set $D=\{p\}\cup C$ and let
$\varepsilon_D(0)$ be the minimum of positive token adjacency on

$$
\operatorname{span}_{\mathbb C}
\{|T\rangle:T\subseteq D\times[2],\ |T|=|D|\}
\tag{20.1}
$$

for the actual induced cone $H[D]=K_1\vee H[C]$. The carrier in
(20.1) is the entire original Boolean zero-weight carrier, with
all spin-zero and spin-one choices and all feasible component
weights. Then necessarily

$$
\varepsilon_D(0)=e_C(0),
\tag{20.2}
$$

where $e_C(0)$ is the uniform-spin-one zero-weight minimum in
(19.3). This is a necessary condition for the stated deficient
minimum, not a sufficient condition or an equivalence.

Proof. At $S=1$ the deficient spin is $J_p=0$. Theorem 19.2
provides a unit actual ground vector $\Psi=\chi_p\otimes f$ with
all other spins one, and each actual component is separately a
singlet with reduced support on its local zero-weight ground
space. Thus $D$ has total weight zero and
$\langle\Psi,K_D\Psi\rangle=e_C(0)$; all spokes vanish because
$p$ is spin zero. Put $O=V(H)\setminus D$ and
$\rho_O=\operatorname{tr}_D|\Psi\rangle\langle\Psi|$.
It has joint weight zero. Every crossing edge incident to $p$
has zero expectation, and every crossing edge incident to $C$
has zero expectation by the component version of (19.9). Hence,
with $b_O=\operatorname{tr}(\rho_OK_O)$,

$$
E_2=e_C(0)+b_O.
\tag{20.3}
$$

Choose any normalized minimizer $v_D$ on the entire carrier
(20.1), with no local-spin restriction. Its one-site ladder
expectations vanish because its total weight is zero. The product
density $|v_D\rangle\langle v_D|\otimes\rho_O$ belongs to the
original whole-graph half-filled carrier; each crossing edge
has zero expectation. The whole-space variational principle gives

$$
e_C(0)+b_O=E_2\leq\varepsilon_D(0)+b_O.
\tag{20.4}
$$

On the other hand, for any unit $u_C\in\mathcal G_C(0)$,
$\chi_p\otimes u_C$ is an actual normalized vector in (20.1)
with energy $e_C(0)$. Thus $\varepsilon_D(0)\leq e_C(0)$.
Together with (20.4) this proves equality. If $O=\varnothing$,
use $\rho_O=1$ and $b_O=0$ and the proof is unchanged.
The same actual outside density is retained throughout; no
independently minimized outside energy is substituted.

The spin-one hypothesis is used because the selected singlet pair
is the entire fibre at $p$. For $S\geq2$, a deficient spin can
leave nonzero spin on the remaining coordinates at $p$, and those
coordinates can remain entangled with the outside. Theorem 19.2
does not remove that whole fibre. No whole-fibre cone equality
at those scales follows from this argument or is asserted here.
$\square$

## 21. One bipartite or odd-cycle component at every vertex

**定义 21.1（Class $\mathcal C$）。** In Definition 19.1 let
$H\in\mathcal C$ mean that for every vertex $p$, at least one
actual connected component of $H[N_H(p)]$ is bipartite or is a
simple odd cycle $C_n$, $n\geq3$. A singleton component is
bipartite. All other neighborhood components are unrestricted.

**定理 21.2（Every ground vector and the same-minimum spectral
consequences at all even scales）。** For every $H\in\mathcal C$
and every integer $S\geq1$, with exactly the $K_s,P_s,E_s$ of
(19.1)–(19.2), $s=2S$, one has

$$
\ker(K_s-E_sI)\subseteq\operatorname{ran}P_s.
\tag{21.1}
$$

The original nonsymmetric space $\mathcal N_s=\ker P_s$ is
nonzero and reduces $K_s$. With this same actual whole-space
minimum $E_s$,

$$
\begin{aligned}
g_s&=\min\operatorname{spec}(K_s|_{\mathcal N_s})-E_s>0,\\
K_s-E_sI&\succeq g_s(I-P_s),\\
\|(I-P_s)\phi\|^2
&\leq\frac{\langle\phi,(K_s-E_sI)\phi\rangle}{g_s}
\qquad(\phi\in\mathcal H_{mS},\ \|\phi\|=1).
\end{aligned}
\tag{21.2}
$$

In particular energy excess at most $\delta\geq0$ bounds this
mass by $\delta/g_s$. These statements include all local-spin
sectors and copies, feasible weights, complex superpositions and
entanglement. No numerical or scale-uniform gap is asserted.

Proof. Suppose a deficient sector attains $E_s$ and choose a
deficient site $p$. Theorem 19.2 applies to each actual component
at this site. Let $C$ be a component satisfying Definition 21.1.
Its conclusion requires every member of $\mathcal G_C(0)$ to be
a total singlet.

If $C$ is bipartite, consume the complete local obstruction in the
[owning volume, (7.6)–(7.10)](TOKEN_GRAPH_BLOWUP_DEFECT_DECOMPOSITION.md),
at the present integer spin $S\geq1$. Its hypotheses are a nonempty
finite bipartite graph, equal integer spins $S$, positive operator
$\sum_{\{i,j\}}(J_i^+J_j^-+J_i^-J_j^+)$, and its full total-zero
space. It provides a zero-weight ground vector which is not a total
singlet. In the one-vertex case there are no edges and the choice is
$|S,0\rangle$, with $\|J^+|S,0\rangle\|^2=S(S+1)>0$.
For a component with an edge, the supplied proof conjugates adjacency
to its negative by a bipartition sign, uses the connected fixed-token
configuration graph and Perron–Frobenius to obtain a ground vector
with all weight coordinates nonzero, and uses the singlet identity
$T_zv=(e_C(0)/4)v$. The zero configuration and the configuration
$1,-1$ on an edge give the incompatible diagonal values $0,-1$.
These are precisely the zero and $\pm1$ weights allowed for all
integer $S\geq1$, including $S=1$. Thus the cited obstruction has
no lost endpoint or extra filling assumption. It contradicts (19.4).

Now let $C=C_n$ be a simple odd cycle. For clarity, the relevant
local estimates of the owning volume can be consumed with their
exact parameters as follows. Its adjacency has the orthogonal
Fourier eigenvectors $z^{(j)}_a=e^{2\pi\mathrm i ja/n}$ and
eigenvalues $2\cos(2\pi j/n)$. Orthogonality follows from the
finite geometric sum. The least eigenvalue is

$$
\lambda=-2\cos(\pi/n)<0,
\qquad z_a=e^{2\pi\mathrm i (n-1)a/(2n)},\qquad |z_a|=1.
\tag{21.3}
$$

For any unit total singlet $v$ on these $n$ spin-$S$ sites,
rotation equates its same-axis pair expectations. Put
$F_\alpha=\sum_{i\in C}e_i\otimes J_i^\alpha v$ for
$\alpha=x,y,z$. The spectral quadratic form and the local
Casimir give exactly

$$
\begin{aligned}
\langle v,K_Cv\rangle
 &=\frac23\sum_\alpha
  \langle F_\alpha,(A(C_n)\otimes I)F_\alpha\rangle\\
 &\geq\frac23\lambda\sum_{i,\alpha}\|J_i^\alpha v\|^2
 =\frac23\lambda nS(S+1).
\end{aligned}
\tag{21.4}
$$

The factor $2/3$ accounts for both orientations in the adjacency
quadratic form and the two transverse axes in $K_C$.
For a competing vector on the same uniform-spin-$S$ zero-weight
space, use

$$
\Phi(T)=\binom{2nS}{nS}^{-1/2}
 \prod_{(i,c)\in T}z_i,
\qquad T\subseteq C\times[2S],\quad |T|=nS.
\tag{21.5}
$$

It is normalized and constant within each fibre-occupancy orbit,
so it belongs to the spin-$S$ tensor space. For an ordered pair of
distinct Boolean coordinates, exactly $\binom{2nS-2}{nS-1}$
subsets contain the first and omit the second. Counting both
orientations of the actual edges therefore yields

$$
e_C(0)\leq\langle\Phi,K_C\Phi\rangle
 =\lambda nS^2\frac{2nS}{2nS-1}.
\tag{21.6}
$$

These are the supplied intermediates (15.4)–(15.6), not new
representation or trial theorems. The complete phase-count bodies
in [CutBoundRefutation](../../../D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.lean)
and its [Scribe](../../../Blueprint/D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.scribe.cs),
including `Test.move`, `Test.toNbr_bij`, `Test.token_energy`,
`counting_identity`, `W_move`, `phi40_norm`, `phi40_energy` and
`choose_ratio40`, supply this subset-counting mechanism. Their
fixed parameters are $N=200,k=100,s=40$; the count used here has
$N=2nS,k=nS,s=2S$. The real/complex Rayleigh comparison applies
to arbitrary complex phases. Neither the cut-bound refutation nor
the Laplacian-radius refutation is a spectral-confinement premise.

For $S\geq2$, the comparison in the owning volume (15.7) is

$$
S^2\frac{2nS}{2nS-1}-\frac23S(S+1)
=\frac{2S\{nS(S-2)+S+1\}}{3(2nS-1)}>0.
\tag{21.7}
$$

Since $\lambda n<0$, (21.6) is strictly below (21.4).
Thus no vector in $\mathcal G_C(0)$ is a singlet, contradicting
Theorem 19.2. The numerator remains positive at $S=2$.

At $S=1,n=5$, the exact supplied value is
$\lambda=-\varphi$, $\varphi=(1+\sqrt5)/2$. If a singlet were a
zero-weight ground vector of energy $e_C(0)$, (21.4) and (21.6)
would give

$$
-\frac{20\varphi}{3}\leq e_C(0)
 \leq-\frac{50\varphi}{9},\qquad -12<e_C(0)<-8.
\tag{21.8}
$$

The last strict bounds follow from $3/2<\varphi<9/5$.
Write $T_\alpha=\sum_{\{i,j\}\in E(C_5)}J_i^\alpha J_j^\alpha$.
Rotate the singlet equation $2(T_x+T_y)v=e_C(0)v$ to obtain
also the $x,z$ and $y,z$ equations. Adding these latter equations
and subtracting the former gives $T_zv=(e_C(0)/4)v$.
In the spin-one weight basis $T_z$ is integer diagonal, so a
nonzero coordinate forces $e_C(0)\in4\mathbb Z$. This is
incompatible with (21.8). This is the local five-cycle obstruction
of (15.8), with no extrapolation to another cycle length.

For the remaining $S=1$ cases use Theorem 20.1 on the actual cone
$D=\{p\}\cup C$. At $n=3$, every unit total singlet on $C$ has

$$
0=\left(\sum_{i\in C}\boldsymbol J_i\right)^2
 =6I+2\sum_{\{i,j\}\in E(C_3)}\boldsymbol J_i\cdot\boldsymbol J_j
\quad\hbox{on that singlet space}.
\tag{21.9}
$$

Rotation equates the same-axis expectations, giving
$\langle K_C\rangle=-4$. By (19.4) its local ground energy must
therefore be $e_C(0)=-4$. The actual cone is $K_4$ and has the
supplied zero-weight trial of (13.13)–(13.14): pair its four
actual spin-one fibres, and on each pair use

$$
d=\frac{|1,-1\rangle-|0,0\rangle+|-1,1\rangle}{\sqrt3}.
\tag{21.10}
$$

Here each ket entry is the weight of one entire symmetric
spin-one fibre. The vector is a pair singlet, as follows from
its ladders or from
[DLMF (34.3.1)](https://dlmf.nist.gov/34.3.E1) with coupled spins
$1,1$ and total spin zero. Its one-site spin expectations vanish,
and its pair edge expectation is $-8/3$. The product of the two
pair singlets is an actual normalized Boolean zero-weight vector.
The four interpair edges have zero expectation, so
$\varepsilon_D(0)\leq-16/3<-4=e_C(0)$, contrary to (20.2).

Finally let $S=1$ and odd $n\geq7$. The supplied singlet estimate
(16.15)–(16.16) has the following exact coupling map. Couple the
two spin-one neighbors of a cycle vertex to spin $q=0,1,2$,
then couple them to that vertex's spin one, with
$l=|q-1|,\ldots,q+1$. The triangle condition is
[DLMF (34.2.1)](https://dlmf.nist.gov/34.2.E1); it includes
the degenerate endpoints. The local operator
$\boldsymbol J_i\cdot(\boldsymbol J_{i-1}+\boldsymbol J_{i+1})$
has eigenvalues

$$
\frac{l(l+1)-2-q(q+1)}2\geq-3.
\tag{21.11}
$$

Indeed its minimum is $0,-2,-3$ for $q=0,1,2$ respectively.
Summing the local operators counts each isotropic cycle edge
twice, so $H_{\rm iso}=\sum_i\boldsymbol J_i\cdot\boldsymbol J_{i+1}
\succeq-3nI/2$. On a total singlet,
$\langle K_C\rangle=(4/3)\langle H_{\rm iso}\rangle\geq-2n$.
Theorem 19.2 consequently implies $e_C(0)\geq-2n$.

The actual cone is the spin-one wheel of the
[owning volume, Definition 16.1 and Theorem 16.2](TOKEN_GRAPH_BLOWUP_DEFECT_DECOMPOSITION.md).
That theorem supplies a normalized vector in its original Boolean
zero-weight carrier, and hence gives a bound for precisely
$\varepsilon_D(0)$, not a minimum over a proxy sector. Its trial
has local parameters $N_D=2(n+1)$ and $k_D=n+1$; writing
$r=(n-1)/2$ and $u_j=e^{2\pi\mathrm i rj/n}$, its phases are
$w_p=-1$ and $w_j=(u_j+1/10)/(1+u_j/10)$.
They have modulus one, and its coefficient on a subset $T$ is
$\binom{2(n+1)}{n+1}^{-1/2}\prod_{(i,c)\in T}w_i$.
The complete wheel calculation (16.4)–(16.12) proves

$$
\varepsilon_D(0)
\leq-\frac{4n(n+1)}{2n+1}
 \left(\frac{49}{50}\cos\frac\pi n+\frac7{100}\right)
<-2n\leq e_C(0).
\tag{21.12}
$$

The strict inequality holds for every odd $n\geq7$, including
$n=7$, at these exact parameters. This is a direct consumption
of that supplied trial and its full estimate. It contradicts the
necessary equality (20.2). It uses no whole-fibre cone claim
for $S\geq2$.

Every alternative for the selected component has contradicted
attainment of $E_s$ by the deficient sector. In (19.5), any
nonzero component of an arbitrary complex ground vector in a
reducing summand is itself an $E_s$-ground vector. Hence no
deficient component can occur, proving (21.1) for every copy,
weight and superposition.

For the spectral assertions, every original fibre permutation
commutes with $K_s$, so $P_s$ commutes with $K_s$ and its kernel
reduces it. This kernel is nonzero even at $m=2,S=1$:
choose a nonconstant one-particle vector orthogonal to constants
in one fibre, an occupancy-$(2S-1)$ vector in a second fibre,
and occupancy-$S$ vectors in every remaining fibre. Their
nonzero product is killed by $P_s$ and has occupancy
$1+(2S-1)+(m-2)S=mS$. The finite nonempty spectrum on this kernel
contains only eigenvalues at least $E_s$, and (21.1) excludes
equality. Thus its minimum minus this same $E_s$ is $g_s>0$.
On $\operatorname{ran}P_s$, $K_s-E_sI\succeq0$; on its
orthogonal complement it is at least $g_sI$. Adding the two
reducing quadratic forms proves the whole-space operator
inequality, and its normalized expectation proves the mass
bound and its $\delta\geq0$ consequence. $\square$

**命题 21.3（Relation to the stated neighborhood classes）。**
Within the common connected even-order domain, class $\mathcal C$
contains both the class with a bipartite component in every
neighborhood in the owning volume's Definition 14.1 and the
whole-neighborhood bipartite-or-odd-cycle class of Definition 17.1.
It does not contain every sufficient confinement domain in the
owning volume.

Proof. A bipartite component is itself a permitted component.
If an entire nonempty neighborhood is bipartite, each of its
components is bipartite; if it is one odd cycle, that whole cycle
is a permitted component. Neighborhoods are nonempty by
connectedness and $m\geq2$. Thus both inclusions follow with all
even scales retained by Theorem 21.2. For the last assertion,
$K_6$ has every neighborhood $K_5$, which is connected,
nonbipartite and not a simple cycle, so $K_6\notin\mathcal C$.
It is a balanced complete multipartite graph with six singleton
parts and is therefore in the owning volume's Theorem 10.2 at
every even scale. No inclusion of that entire domain in
$\mathcal C$ is asserted. $\square$

## 22. A wheel and clique wing sharing an original fibre

**定义 22.1（An infinite family with an unrestricted neighborhood
component）。** For every odd integer $n\geq7$, define $F_n$ on
the distinct vertices

$$
\{p\}\ \sqcup\ \{v_j:j\in\mathbb Z/n\mathbb Z\}
\ \sqcup\ \{c_1,c_2,c_3,c_4\}
\ \sqcup\ \{\ell_1,\ell_2,\ell_3,\ell_4\}.
\tag{22.1}
$$

Include the rim edges $v_jv_{j+1}$, all spokes $pv_j$, all edges
$pc_i$, all edges $c_ic_j$ for $i\ne j$, and the four edges
$c_i\ell_i$. There are no other edges. Write
$W=\{p\}\cup\{v_j\}$ and
$Q=\{p,c_1,c_2,c_3,c_4,\ell_1,\ell_2,\ell_3,\ell_4\}$
for its two overlapping regions.

**命题 22.2（All-scale confinement, actual interaction and structural
separation）。** The graphs $F_n$, odd $n\geq7$, form an infinite
family of connected even-order simple unit-weight graphs in
$\mathcal C$. They satisfy (21.1)–(21.2) on their entire original
half-filled carriers for every even $s\geq2$. At each such scale,
the original regional occupancies of both $W$ and $Q$ fail to
commute with $K_s$. At every such scale this family is outside
every sufficient whole-graph confinement domain in the owning
volume through Section 16 and in Sections 17–18 here.

Proof. The wheel and the clique on $p,c_1,c_2,c_3,c_4$ are
connected and share $p$. Each leaf is attached to this connected
union. The order is $m=n+9$, even and at least $16$; differing
$n$ give differing orders. The entire induced neighborhoods are

$$
\begin{aligned}
H[N(p)]&=C_n\sqcup K_4,\\
H[N(v_j)]&=v_{j-1}-p-v_{j+1},\\
H[N(c_i)]&=K_4[\{p\}\cup\{c_j:j\ne i\}]\sqcup\{\ell_i\},\\
H[N(\ell_i)]&=\{c_i\}.
\end{aligned}
\tag{22.2}
$$

Here $H=F_n$ in the displayed notation. The absence of an edge
between $v_{j-1}$ and $v_{j+1}$ follows from $n\geq7$; a leaf
has no neighbor besides its specified $c_i$. There is no edge
between any rim vertex and any $c_i$. These observations verify
both the asserted edges and the absence of extra edges in each
entire neighborhood. At $p$ the actual cycle component qualifies;
at each $c_i$ the isolated leaf component qualifies; at a rim
vertex and a leaf the whole neighborhood is bipartite. Thus
$F_n\in\mathcal C$, with its $K_4$ components left unrestricted,
and Theorem 21.2 applies at every asserted scale.

For interaction, fix any $s=2S\geq2$, $k=ms/2$ and actual original
occupancy operators $M_W=\sum_{i\in W}n_i$ and
$M_Q=\sum_{i\in Q}n_i$. These regions share the same Boolean
fibre $B_p$, not two copies of it. Choose $x\in B_p$ and
$y\in B_{c_1}$. There is a $k$-subset $T$ with $x\in T$ and
$y\notin T$: choose $k-1$ coordinates from the other $ms-2$,
which is possible since $1\leq k\leq ms-1$. Put
$T'=T\setminus\{x\}\cup\{y\}$. The actual edge $pc_1$ gives
$\langle T'|K_s|T\rangle=1$, while $M_W(T')-M_W(T)=-1$.
Consequently

$$
\langle T'|[M_W,K_s]|T\rangle=-1.
\tag{22.3}
$$

Choosing instead $y\in B_{v_0}$ uses the actual spoke $pv_0$
and gives the same nonzero commutator entry for $M_Q$.
In fact a token can pass from the rim to the clique through $p$:
choose a $k$-subset containing a coordinate of $B_{v_0}$ and
omitting specified coordinates of $B_p$ and $B_{c_1}$, and move
it successively along $v_0p$ and $pc_1$. Such a subset exists
because $k-1\leq ms-3$ at the present $m\geq16,s\geq2$.
Both moves have coefficient one in the unchanged original carrier.
Thus the wheel and clique wing are interacting regions with
actual occupancy transfer, with no separately fixed regional
filling or independent regional minimization.

It remains to check the exact sufficient domains. At $p$, the
neighborhood has the two nonbipartite actual components $C_n$
and $K_4$. It is not bipartite and has no bipartite component.
This excludes the wholly bipartite-neighborhood domain of
Section 7 and the component-bipartite domain of Section 14,
including their stated consumers. It is neither bipartite nor
$C_5$, excluding Definition 15.1(a). It is also neither
bipartite nor one simple odd cycle, excluding Definition 17.1
and therefore its Section 18 family.

Definition 15.1(b) requires a flat least mode of the entire
neighborhood when it is nonbipartite. This fails at $p$.
The least eigenvalue on $C_n$ is $-2\cos(\pi/n)<-1$, whereas
$A(K_4)=\boldsymbol1\boldsymbol1^{\mathsf T}-I$ has eigenvalues
$3,-1,-1,-1$. The adjacency of $C_n\sqcup K_4$ is their direct
sum. Every eigenvector for its least eigenvalue consequently
vanishes on the $K_4$ coordinates, and cannot have modulus one
at every coordinate. Thus condition (b) fails structurally at
all scales, including those $s\geq4$ where its theorem applies.
This is not a failure of an estimate being used to assert
noncoverage; it is failure of the stated eigenvector hypothesis.

The wheel $F_n[W]$ is a nonclique maximal two-connected block.
Deleting its hub leaves its rim cycle; deleting a rim vertex
leaves a hub joined to the remaining rim path, so deleting any
one vertex leaves it connected. Its rim vertices have no edges
to the clique wing or its leaves. A subgraph containing one of
these rim vertices and a vertex outside $W$ would have $p$ as
a separating vertex, so cannot enlarge this two-connected block.
It is not a clique since $v_0$ and $v_2$ are nonadjacent.
The block-graph domains of Sections 12–13, including their
all-even conclusion, therefore fail.

The graph is not complete multipartite: $v_0$ is nonadjacent to
both $v_2$ and $v_3$, but $v_2v_3$ is an edge. Distinct
nonadjacent vertices in a complete multipartite graph belong to
the same independent part, so these three relations are
incompatible with that graph class. This excludes all balanced,
dominant-part and combined complete-multipartite domains of
Sections 10–11 at every scale.

The global flat least-mode assumption of Sections 3–6 also fails.
Extend a least Fourier vector of the induced rim by zero at all
other vertices. Its adjacency Rayleigh quotient in $F_n$ is
$-2\cos(\pi/n)<-1$, since all edges with an outside endpoint
contribute zero. Thus the whole-graph least eigenvalue $\lambda_H$
satisfies $\lambda_H<-1$. A modulus-one least eigenvector $z$
would, at a leaf, satisfy
$\lambda_H z_{\ell_i}=z_{c_i}$. Taking moduli would give
$|\lambda_H|=1$, a contradiction. In particular the larger-scale
flat-mode confinement theorem of Section 6 supplies no scale of
this family. Section 2's general defect certificate is a lower
bound, not a sufficient every-ground confinement theorem.

The individual-wheel domain of Section 16 has no degree-one
vertices, whereas $F_n$ has four. The individual wheels in
Proposition 15.4 are excluded for the same reason. The five-rim
wheel with rim leaves in Proposition 15.3 has a six-vertex core
after deleting all degree-one vertices; here that deletion leaves
$n+5\geq12$ vertices. It cannot be one of those graphs. Likewise
the two-shared-edge-wheel family of Section 18 has all its
neighborhoods bipartite or one odd cycle, a condition already
excluded at $p$ by (22.2). Sections 8–9 concern odd fibre sizes
and give no conclusion at any of the even scales asserted here.
The collective-oscillator and three Lean/Scribe suppliers provide
the stated representations, counting and refutation conclusions;
they add no sufficient whole-graph confinement domain containing
this family. These exclusions exhaust the sufficient domains
of those supplied results, without claiming confinement fails
outside them. $\square$

**定义 22.3（The remaining graph-domain question）。** For arbitrary
finite connected simple unit-weight $H$ of even order $m\geq2$
outside the sufficient classes stated here and in the owning
volume, the every-ground confinement assertion on the entire
complex Boolean carrier at every equal even fibre size remains
unresolved here. The necessary component inclusions (19.4) and
the spin-one cone equalities (20.2) are not a complete
if-and-only-if criterion. They do not supply an actual
original-$E_s$ nonsymmetric ground counterexample. All conclusions
above concern precisely positive coefficient-one adjacency,
equal even fibres and global half filling; they assert nothing
about other signs, weights, unequal or odd fibres, other filling,
physical realization or worldwide priority.

## 追加锚（本行以下为增补区）
## 23. Four equal integer spins on a diamond

**定义 23.1（The complete local zero-weight space）。** Let $D$ be the
simple diamond with vertices $1,2,3,4$ and edges
$12,13,14,23,24$. Its central vertices are $1,2$ and its nonadjacent
tips are $3,4$. For an integer $S\geq1$, put one spin $S$ at each
vertex, with the normalized weights and ladders in (19.5). On the
entire complex tensor product $V_S^{\otimes4}$ put

$$
\begin{aligned}
T_\alpha&=\sum_{ij\in E(D)}J_i^\alpha J_j^\alpha
\quad(\alpha=x,y,z),&
I_D&=T_x+T_y+T_z,\\
K_D&=\sum_{ij\in E(D)}(J_i^+J_j^-+J_i^-J_j^+)
       =2(T_x+T_y),&
\mathcal V_D(0)&=\ker\sum_{i=1}^4Z_i,\\
e_D(0)&=\min\operatorname{spec}(K_D|_{\mathcal V_D(0)}),&
\mathcal G_D(0)&=\ker(K_D-e_D(0)I)\cap\mathcal V_D(0),\\
\mathcal S_D&=\ker\sum_iJ_i^+\cap\ker\sum_iJ_i^-,&
L_S&=-4S^2-\frac83S.
\end{aligned}
\tag{23.1}
$$

Every edge in $K_D$ has the positive coefficient one. The space
$\mathcal S_D$ is the full total-singlet space, including all
coupling multiplicities. Only the total weight, rather than any
pair weight or individual weight, is fixed in $\mathcal V_D(0)$.

**定理 23.2（The diamond has no singlet zero-weight ground vector）。**
For every integer $S\geq1$ in Definition 23.1,

$$
\langle v,K_Dv\rangle\geq L_S
\quad(v\in\mathcal S_D,\ \|v\|=1),\qquad
 e_D(0)<L_S,\qquad
\mathcal G_D(0)\cap\mathcal S_D=\{0\}.
\tag{23.2}
$$

Proof. Use the classical addition of two angular momenta. Its triangle
range and normalization are
[DLMF (34.2.1)](https://dlmf.nist.gov/34.2.E1),
[(34.1.1)](https://dlmf.nist.gov/34.1.E1) and the orthogonality and
completeness relations
[(34.3.16)](https://dlmf.nist.gov/34.3.E16) and
[(34.3.17)](https://dlmf.nist.gov/34.3.E17).
For $S\otimes S$ the coupled spins are exactly $q=0,1,\ldots,2S$;
the pair Casimir on spin $q$ is $q(q+1)$. These are classical
intermediates, used with both endpoints included.

Write $c=S(S+1)$, $B=\boldsymbol J_1+\boldsymbol J_2$ and
$A=\boldsymbol J_3+\boldsymbol J_4$. The five actual diamond edges
give

$$
I_D=\boldsymbol J_1\cdot\boldsymbol J_2+B\cdot A,
\qquad
\boldsymbol J_1\cdot\boldsymbol J_2=\tfrac12(B^2-2cI).
\tag{23.3}
$$

A total singlet $v$ satisfies $(A+B)_\alpha v=0$ for every
Cartesian component $\alpha$. Since each $A_\alpha$ commutes with
each $B_\beta$, this gives $B\cdot Av=-B^2v$ and hence
$I_Dv=-cv-\tfrac12B^2v$. Simultaneous rotations of all four spins
fix every vector in every singlet copy. Such rotations interchange
the same-axis products, so
$\langle v,T_xv\rangle=\langle v,T_yv\rangle
=\langle v,T_zv\rangle$. Consequently, for every unit singlet,

$$
\begin{aligned}
\langle v,K_Dv\rangle
 &=\frac43\langle v,I_Dv\rangle
 =-\frac43c-\frac23\langle v,B^2v\rangle\\
 &\geq-\frac43S(S+1)-\frac23(2S)(2S+1)
 =L_S.
\end{aligned}
\tag{23.4}
$$

This bound uses the entire pair-spin spectrum. It imposes no
particular pair coupling on the singlet being bounded and applies
to arbitrary complex superpositions of its multiplicity copies.

For a competing vector, take the actual maximal-spin subspace
$q=2S$ of each pair $12$ and $34$. Couple these two spin-$q$
spaces to their normalized singlet

$$
w=\frac1{\sqrt{2q+1}}
 \sum_{M=-q}^{q}(-1)^{q-M}|q,M\rangle_{12}|q,-M\rangle_{34},
\qquad q=2S.
\tag{23.5}
$$

The coefficient is precisely
[DLMF (34.3.1)](https://dlmf.nist.gov/34.3.E1), with
$j_1=j_2=q$, total spin zero and weights $M,-M$, in the convention
of (34.1.1). Thus $w$ is a unit total singlet and belongs to the
same $\mathcal V_D(0)$. Also $B^2w=q(q+1)w$, so (23.4) is an
equality for this vector:

$$
\langle w,K_Dw\rangle=L_S<0.
\tag{23.6}
$$

We show that this Rayleigh value is not an eigenvalue attained by
$w$. If a total singlet $u$ satisfies $K_Du=e u$, rotate that
vector equation to interchange the coordinate axes. Since each
rotation fixes $u$, the resulting three equations are

$$
2(T_x+T_y)u=e u,\qquad
2(T_y+T_z)u=e u,\qquad
2(T_x+T_z)u=e u.
\tag{23.7}
$$

Adding the last two and subtracting the first gives
$T_zu=(e/4)u$. In the original four-site weight basis,

$$
T_z|x_1,x_2,x_3,x_4\rangle
=\{x_1x_2+(x_1+x_2)(x_3+x_4)\}
 |x_1,x_2,x_3,x_4\rangle.
\tag{23.8}
$$

Its diagonal value at $(0,0,0,0)$ is zero. This coordinate exists
for every integer $S\geq1$ and has a nonzero coefficient in $w$.
To see the coefficient without any cancellation assumption, realize
each spin $S$ as the symmetric space on $2S$ Boolean coordinates.
The maximal pair spin $2S$ is the symmetric space on their $4S$
coordinates. The normalized weight-zero vectors therefore satisfy

$$
\langle S,0;S,0\mid 2S,0\rangle
 =\frac{\binom{2S}{S}}{\sqrt{\binom{4S}{2S}}}>0.
\tag{23.9}
$$

This is the normalized Dicke count: the product of the two
weight-zero vectors has $\binom{2S}{S}^2$ Boolean terms, and the
weight-zero vector on $4S$ coordinates has $\binom{4S}{2S}$ terms.
The Boolean normalization is the classical symmetric-chain
normalization of Srinivasan,
[Theorem 1.2](https://arxiv.org/html/1001.0280v2), and Feinsilver,
[§3.1, (10), and §4.2.2](https://arxiv.org/html/1102.0368v2).
Only $M=0$ in (23.5) contributes to the four-site zero coordinate.
Since $q=2S$ is even, its coefficient is

$$
\langle0,0,0,0\mid w\rangle
=\frac1{\sqrt{4S+1}}
 \frac{\binom{2S}{S}^{\!2}}{\binom{4S}{2S}}>0.
\tag{23.10}
$$

Here each zero in the bra denotes the weight of an entire spin-$S$
site. If $K_Dw=L_Sw$, (23.7)–(23.8) at this coordinate would give
$0=(L_S/4)\langle0,0,0,0\mid w\rangle$, contradicting
(23.6) and (23.10). Thus $w$ is not an eigenvector.

The operator $K_D$ preserves total weight. Its finite Hermitian
restriction to $\mathcal V_D(0)$ has minimum at most $L_S$ by
(23.6). If that minimum equalled $L_S$, expand $w$ in an
orthonormal eigenbasis of this restriction. The equality
$\sum_\theta(\theta-L_S)|w_\theta|^2=0$, with all summands
nonnegative, would force $K_Dw=L_Sw$. This has just been excluded.
Therefore $e_D(0)<L_S$. The lower bound for every singlet in
(23.4) now excludes every nonzero singlet from its ground space.
The argument includes $S=1$ and uses no limiting spin estimate.
$\square$

## 24. Diamond components and the unchanged original carrier

**定义 24.1（Class $\mathcal C_{\diamond}$）。** Let $H$ be a finite
connected simple unit-weight graph of even order $m\geq2$. Say that
$H\in\mathcal C_{\diamond}$ if, for every $p\in V(H)$, at least
one actual connected component of the induced open neighborhood
$H[N_H(p)]$ is bipartite, a simple odd cycle $C_n$ with $n\geq3$,
or a diamond. A singleton component is bipartite. Other actual
components, their sizes and their edges are unrestricted, as are
all attachments outside the selected neighborhood component.

For every integer $S\geq1$, set $s=2S$ and use exactly Definition
19.1:

$$
\begin{aligned}
\Omega&=V(H)\times[2S],&
\mathcal H_{mS}
 &=\operatorname{span}_{\mathbb C}
       \{|T\rangle:T\subseteq\Omega,\ |T|=mS\},\\
K_s&=A(F_{mS}(H[\mathrm{empty}_{2S}])),&
P_s&=\prod_{i\in V(H)}P_i,&
E_s&=\min\operatorname{spec}(K_s|_{\mathcal H_{mS}}).
\end{aligned}
\tag{24.1}
$$

Here $F_{mS}$ denotes the ordinary token graph, every allowed move
has coefficient one, and $P_i$ is invariance under all permutations
of the original $2S$ coordinates at $i$. Only global half filling
is imposed. In particular $E_s$ is the minimum on the entire
original carrier, before imposing any fibre symmetry.

**定理 24.2（Every original ground vector at every even scale）。**
For every $H\in\mathcal C_{\diamond}$ and every integer $S\geq1$,

$$
\ker(K_s-E_sI)\subseteq\operatorname{ran}P_s.
\tag{24.2}
$$

This includes every original local-spin sector, multiplicity copy,
feasible weight, complex superposition and entangled vector.

Proof. The representation and minimizing-realization input is the
complete Theorem 19.2, including its component conclusion (19.4).
The companion source versions for this proof are Git
`e45f5aa2928bfa0d3239246268831d37a4146425`: the
[owning volume](TOKEN_GRAPH_BLOWUP_DEFECT_DECOMPOSITION.md), the
[collective-oscillator volume](AURIC_COLLECTIVE_OSCILLATORS_AND_RECORD_CAPACITY.md),
the three Lean sources and three Scribes cited below, and §§1–22
of this volume. Their roles and parameters are as follows.

The orthogonal Boolean-chain decomposition in the owning volume,
(6.6)–(6.12), and here (19.5), is on the whole space (24.1):

$$
\mathcal H_{mS}\cong
\bigoplus_{\substack{0\leq t_i\leq S\\
               1\leq a_i\leq r_{2S}(t_i)}}
 \left(\bigotimes_i V_{S-t_i}\right)_{\sum_i x_i=0},
\qquad
r_{2S}(t)=\binom{2S}{t}-\binom{2S}{t-1}.
\tag{24.3}
$$

The convention is $\binom{2S}{-1}=0$. The weights are all
$-J_i\leq x_i\leq J_i$, with $J_i=S-t_i$, and original occupancy
$S+x_i$. No other filling is fixed. Each $a_i$ is a separate
orthogonal multiplicity copy; collective spin acts identically on
all these copies. The original $P_s$ selects exactly $t_i=0$
for every $i$.

The primary representation parameters are Srinivasan,
[Theorem 1.2](https://arxiv.org/html/1001.0280v2), Boolean rank
$n=2S$, starting rank $t_i$, layer $u=S+x_i$ and up operator
$L_i^\ast$. Its normalized raising coefficient is
$\sqrt{(u+1-t_i)(2S-t_i-u)}$, precisely (19.5).
Feinsilver,
[§§3–4, (8)–(10), (16), Proposition 4.3 and §4.2.2](https://arxiv.org/html/1102.0368v2),
has $T=L_i^\ast$, $T^\ast=L_i$, principal number
$2S-2t_i=2J_i$, chain index $J_i+x_i$ and grading $-2Z_i$.
The vacuum count and orthogonality there give exactly the
multiplicities and orthogonal copies in (24.3), including the
spin-zero endpoint. These are consumed representation results.

The full counting recurrences and theorems
`sector_words_card_multinomial` and `sector_gram` in
[OccupancyWordSectors](../../../D5/S3/Quantum/Entanglement/OccupancyWordSectors.lean)
and its
[Scribe](../../../Blueprint/D5/S3/Quantum/Entanglement/OccupancyWordSectors.scribe.cs)
normalize the symmetric fibre vectors by two-letter counts
$(2S-n_i,n_i)$, including $n_i=0,2S$; for (23.9), the combined
pair uses length $4S$ and counts $(2S,2S)$. These word-count
statements alone do not assert a whole-carrier ground theorem.
The collective-oscillator volume has the exact algebraic map
$d=m$, $N=2S$, $g=0$, $e=1$, $B=A(H)$,
$a_i=L_i/\sqrt{2S}$ and $H_{2S}=\hbar K_s/(2S)$ on the chosen
two-state code. Its symmetric-code calculation is not substituted
for the complete decomposition (24.3), and no low-excitation
approximation is used.

The singleton-difference definition in the complete
[TokenGraphLaplacianRadiusRefutation](../../../D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.lean)
and its
[Scribe](../../../Blueprint/D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.scribe.cs)
is the move defining $K_s$ in (24.1). The primary convention is
Apte–Parekh–Sud,
[v3, Definition 1 and Fact 2](https://arxiv.org/html/2506.03441v3),
with $2mS$ original vertices, $mS$ tokens and edge weights one.
Their shifted block $WI/2-K_s$ is a different operator. Their
Definition 1 has $1\leq k<N$; the present $k=mS$, $N=2mS$
always lies in that range.

For the phase trials used in the odd-cycle inputs, the complete
private and proof-local bodies `Test.move`, `Test.toNbr_bij`,
`Test.token_energy`, `counting_identity`, `W_move`, `phi40_norm`,
`phi40_energy` and `choose_ratio40` in
[CutBoundRefutation](../../../D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.lean)
and the full
[Scribe](../../../Blueprint/D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.scribe.cs)
supply the coefficient and ordered-move counting mechanism. Their
fixed refutation has $N=200$, $k=100$, $s=40$; the general
phase-count identity is consumed through the owning volume's
(3.5)–(3.7) and the local consequences (21.5)–(21.6), with
$N=2nS$, $k=nS$, $s=2S$ on a cycle. Neither supplied refutation
is a premise for spectral confinement.

Theorem 19.2 uses only the nonstrict fixed-weight spin comparison
from Ghassemi Tabrizi–Henderson–Kühne–Scuseria,
[Appendix A4, (A34)–(A54) and its final fixed-magnetization paragraph](https://pmc.ncbi.nlm.nih.gov/articles/PMC12613319/#app1-sec4),
DOI [10.1021/acs.jctc.5c01412](https://doi.org/10.1021/acs.jctc.5c01412).
The map is maximal local spin $s_i=S$, variable spin $t_i=J_i$,
magnetization $M=0$ and bilinear coupling
$D_{ij}=\operatorname{diag}(2a_{ij},2a_{ij},0)$ for $a=A(H)$.
This supplies existence of a maximal-spin minimizing choice, not
strictness or an assertion about every original ground vector.
The selected-pair replacement and actual-component separation in
Theorem 19.2 supply the stronger necessary condition used here.
In particular, no strictness is imported from that primary
nonstrict result.

Now suppose that a reducing summand of (24.3), deficient at a
vertex $p$ with $J_p<S$, attains the actual $E_s$. Theorem 19.2
provides a minimizing realization with all other spins $S$ and,
for every actual component $C$ of $H[N_H(p)]$, requires

$$
\operatorname{ran}\rho_C\subseteq\mathcal G_C(0),\qquad
\mathcal G_C(0)\subseteq\mathcal S_C.
\tag{24.4}
$$

Here the local spaces and energies are exactly (19.3), and
$\mathcal G_C(0)$ is nonzero because the zero-weight space is
finite and nonempty. The zero weights and separate singlets in
(24.4) are conclusions of that theorem on actual components.
They are not independent restrictions on the original carrier.
No marginal of every initially chosen deficient vector is assumed
to be unchanged.

Choose an actual component qualifying in Definition 24.1. If it
is a diamond, Theorem 23.2 contradicts (24.4) at this exact spin
$S$, including $S=1$.

If it is bipartite, use the full local obstruction in the owning
volume's (7.6)–(7.10), as consumed in Theorem 21.2: a nonempty
bipartite graph with equal integer spins $S\geq1$ has a
zero-weight ground vector which is not a total singlet. The
operator there is precisely positive
$\sum_{ij}(J_i^+J_j^-+J_i^-J_j^+)$ on the entire zero-weight
space. For a singleton the vector is $|S,0\rangle$, and
$\|J^+|S,0\rangle\|^2=S(S+1)>0$. For a connected component
with an edge the supplied bipartition conjugation and
Perron–Frobenius argument uses all allowed zero-total-weight
configurations. Its incompatible diagonal values at the zero
configuration and the configuration with weights $1,-1$ on an
edge are $0$ and $-1$. Those weights exist also at $S=1$.
Thus the cited obstruction retains the endpoint and contradicts
the universal inclusion in (24.4).

If the selected component is $C_n$ with odd $n\geq3$, consume
the componentwise odd-cycle argument of Theorem 21.2. Its four
cases depend only on the one actual component, (24.4), and,
when $S=1$, the necessary cone equality of Theorem 20.1. They
do not require that other vertices of $H$ satisfy Definition
21.1. The exact estimates are the following.

For $S\geq2$, cycle adjacency has the flat least eigenvalue
$\lambda=-2\cos(\pi/n)<0$. Equations (21.4) and (21.6) give,
for every unit total singlet $v$ on the cycle,

$$
\langle v,K_Cv\rangle\geq\frac23\lambda nS(S+1),\qquad
 e_C(0)\leq\lambda nS^2\frac{2nS}{2nS-1}.
\tag{24.5}
$$

The competing vector is the normalized phase product on the
actual $nS$-subsets of $C\times[2S]$, constant within each
fibre-occupancy orbit. It is in the symmetric spin-$S$ tensor
space with only total weight zero. The exact strict comparison
(21.7) is

$$
S^2\frac{2nS}{2nS-1}-\frac23S(S+1)
=\frac{2S\{nS(S-2)+S+1\}}{3(2nS-1)}>0.
\tag{24.6}
$$

Since $\lambda n<0$, the upper bound in (24.5) is strictly
below the singlet lower bound, also at $S=2$ and $n=3$.
This contradicts (24.4).

For $S=1,n=5$, (21.8) gives $-12<e_C(0)<-8$ if a singlet is
a local ground vector. Rotating its eigenvector equation as in
(23.7) gives $T_zv=(e_C(0)/4)v$. The operator $T_z$ is integer
diagonal in the spin-one weight basis, so any nonzero coordinate
forces $e_C(0)\in4\mathbb Z$. No such integer multiple lies
strictly between $-12$ and $-8$. This is exactly the supplied
five-cycle obstruction.

For $S=1,n=3$, the singlet Casimir identity (21.9) gives
$\langle K_C\rangle=-4$ for every unit singlet. Thus (24.4)
would imply $e_C(0)=-4$. Theorem 20.1 at this deficient vertex
requires $\varepsilon_{\{p\}\cup C}(0)=e_C(0)$ on the entire
original Boolean carrier of the actual cone. This cone is $K_4$.
The product of the two pair singlets (21.10), each on two actual
spin-one fibres, has energy $-16/3$ there. Consequently
$\varepsilon_{\{p\}\cup C}(0)\leq-16/3<-4$, a contradiction.

For $S=1$ and odd $n\geq7$, (21.11) gives the isotropic cycle
bound $H_{\rm iso}\succeq-3nI/2$. Rotational invariance on a
singlet gives $\langle K_C\rangle\geq-2n$, hence (24.4)
requires $e_C(0)\geq-2n$. The actual cone is the wheel
$K_1\vee C_n$. The complete normalized original-carrier trial
and strict estimate from the owning volume's Theorem 16.2,
consumed as (21.12), give

$$
\varepsilon_{\{p\}\cup C}(0)
\leq-\frac{4n(n+1)}{2n+1}
 \left(\frac{49}{50}\cos\frac\pi n+\frac7{100}\right)
<-2n\leq e_C(0).
\tag{24.7}
$$

Its parameters are $N_D=2(n+1)$, $k_D=n+1$, central phase $-1$
and rim phases $(u_j+1/10)/(1+u_j/10)$, with
$u_j=e^{2\pi\mathrm i (n-1)j/(2n)}$. The supplied strict bound
includes $n=7$. It is a trial on the entire original zero-weight
cone carrier, not an independently prescribed local-spin minimum.
It contradicts Theorem 20.1. This cone equality is used only at
$S=1$; no whole-fibre removal for larger $S$ is inferred.

Every possible qualifying component has contradicted attainment
of $E_s$ by the deficient summand. Each summand of (24.3) reduces
$K_s$. Projecting an arbitrary complex $E_s$-ground vector onto
one of these summands therefore gives either zero or an
$E_s$-ground vector in that summand. All deficient projections
must vanish. The remaining summands have all $t_i=0$ and are
exactly $\operatorname{ran}P_s$. This proves (24.2) with every
copy, feasible weight and superposition retained. $\square$

**推论 24.3（A qualitative gap at the same actual minimum）。** For
every $H\in\mathcal C_{\diamond}$ and every integer $S\geq1$,
the original space $\mathcal N_s=\ker P_s$ is nonzero and reduces
$K_s$. With exactly the $E_s$ of (24.1),

$$
\begin{aligned}
g_s&=\min\operatorname{spec}(K_s|_{\mathcal N_s})-E_s>0,\\
K_s-E_sI&\succeq g_s(I-P_s),\\
\|(I-P_s)\phi\|^2
 &\leq\frac{\langle\phi,K_s\phi\rangle-E_s}{g_s}
 \qquad(\phi\in\mathcal H_{mS},\ \|\phi\|=1).
\end{aligned}
\tag{24.8}
$$

In particular energy excess at most any $\delta\geq0$ bounds the
same mass by $\delta/g_s$. Positivity is qualitative; no numerical
value or uniform-in-$S$ lower bound for $g_s$ is asserted.

Proof. Each original fibre permutation commutes with $K_s$, so its
invariant projection $P_i$, their commuting product $P_s$ and
$I-P_s$ commute with $K_s$. Their ranges are reducing. Choose a
nonzero one-particle vector orthogonal to constants in one fibre;
this is possible because $2S\geq2$. Tensor it with an
occupancy-$(2S-1)$ vector in a second fibre and occupancy-$S$
vectors in all remaining fibres. This nonzero product is killed
by $P_s$ and has total occupancy
$1+(2S-1)+(m-2)S=mS$. Thus $\mathcal N_s\ne\{0\}$, including
$m=2,S=1$.

Its finite nonempty spectrum has every eigenvalue at least $E_s$.
Theorem 24.2 excludes equality for every eigenvector in
$\mathcal N_s$, so its least eigenvalue exceeds this same $E_s$.
On $\operatorname{ran}P_s$, $K_s-E_sI\succeq0$; on
$\mathcal N_s$, $K_s-E_sI\succeq g_sI$. Add the two reducing
quadratic forms to obtain the operator inequality in (24.8).
Its expectation in any unit complex vector gives the displayed
mass estimate. No symmetric-space substitute for $E_s$ enters
this argument. $\square$

## 25. A six-vertex graph requiring the diamond alternative

**定义 25.1（The graph $Q$）。** Take six distinct vertices
$\{a,b,u,v,w,\ell\}$. On the five-vertex set
$\{a,b,u,v,w\}$ include every edge except $ab$, and add the
single edge $a\ell$. There are no other edges. Give every edge
weight one. Write $W=\{u,v,w\}$ for the three mutually adjacent
vertices of the core.

**命题 25.2（An actual consumer outside every prior sufficient domain）。**
The graph $Q$ is finite, connected, simple and of even order six.
It belongs to $\mathcal C_{\diamond}$. At every integer $S\geq1$,
all conclusions (24.2) and (24.8) hold for the entire original
complex $6S$-subset carrier of $Q[\mathrm{empty}_{2S}]$, with
its original $K_s,P_s,E_s$. At every one of these even scales it
is outside every sufficient whole-graph confinement domain in the
nine sources specified in the proof of Theorem 24.2.

Proof. The core is connected, and $\ell$ is attached to $a$.
The complete induced neighborhoods, with no omitted edges or
components, are

$$
\begin{aligned}
Q[N_Q(a)]&=K_3[W]\sqcup\{\ell\},\\
Q[N_Q(b)]&=K_3[W],\\
Q[N_Q(x)]&=K_4[\{a,b\}\cup(W\setminus\{x\})]-ab
                    &&(x\in W),\\
Q[N_Q(\ell)]&=\{a\}.
\end{aligned}
\tag{25.1}
$$

At $a$ the leaf is an isolated neighborhood component because it
has no other neighbor. At $b$ the whole neighborhood is the simple
odd cycle $C_3$. At $x\in W$ the sole component is a diamond,
with the two vertices of $W\setminus\{x\}$ central and $a,b$
the tips. At $\ell$ the neighborhood is a singleton. These
actual components verify Definition 24.1. Theorem 24.2 and
Corollary 24.3 apply at every $S\geq1$, with $N=12S$ and
$k=6S$. There is no separately imposed neighborhood filling.

We check the prior domains on this same graph. At any $x\in W$,
its diamond neighborhood is connected, contains a triangle and
has two vertices of degree three. It is nonbipartite and is not
a simple cycle of any length. Thus it has no bipartite component.
This excludes the owning volume's wholly bipartite-neighborhood
domain in §7, its bipartite-component domain in §14, its
bipartite-or-$C_5$ domain in Definition 15.1(a), the whole
bipartite-or-odd-cycle domain in Definition 17.1 here and the
actual-component class $\mathcal C$ of Definition 21.1. In
particular this excludes all their specific consumers, including
the corona families in §14, the shared-wheel family in §18 and
the family in §22. Theorem 21.2 cannot be applied to $Q$.

For the other neighborhood condition, the diamond has no complex
flat least mode. Label its two central coordinates by a common
value $c$ and its two tip coordinates by a common value $d$.
The central-antisymmetric subspace has eigenvalue $-1$, and the
tip-antisymmetric subspace has eigenvalue zero. On the remaining
constant-on-pairs subspace, adjacency acts by

$$
\begin{pmatrix}1&2\\2&0\end{pmatrix}
\begin{pmatrix}c\\d\end{pmatrix},
\qquad
\lambda_\pm=\frac{1\pm\sqrt{17}}2.
\tag{25.2}
$$

These four dimensions exhaust its adjacency space. Its least
eigenvalue is the simple $\lambda_-\in(-2,-1)$, so every least
eigenvector is of this constant-on-pairs form and satisfies
$\lambda_-d=2c$. If all four coordinates had modulus one,
this equation would force $|\lambda_-|=2$, a contradiction.
Thus the nonbipartite neighborhood at $x$ fails the precise
whole-neighborhood least-eigenvector condition in the owning
volume's Definition 15.1(b). Its theorem supplies no scale
$S\geq2$ for $Q$, and asserts no $S=1$ conclusion from that
condition.

The global flat least-mode hypothesis also fails. On the induced
diamond at $N_Q(x)$ take values $+1$ at its two central vertices
and $-1$ at its two tips, and extend by zero at the other two
vertices of $Q$. The central edge contributes $2$ and the four
central-tip edges contribute $-8$ to its adjacency quadratic form;
the squared norm is $4$. All other edges contribute zero. Hence

$$
\lambda_Q=\min\operatorname{spec}A(Q)\leq-\frac32<-1.
\tag{25.3}
$$

If $z$ were a modulus-one eigenvector for $\lambda_Q$, the leaf
equation would be $\lambda_Qz_\ell=z_a$. Its moduli would give
$|\lambda_Q|=1$, contrary to (25.3). This excludes Assumption
3.1 and all flat-global-mode sufficient gap regimes in the owning
volume's §6, at every even scale. Its general §2 defect identity
is a lower-bound certificate and supplies no separate sufficient
every-ground confinement domain for this graph.

The core $Q[\{a,b,u,v,w\}]=K_5-ab$ is a nonclique maximal
two-connected block. Deleting $a$ or $b$ leaves $K_4$; deleting
one of $u,v,w$ leaves $K_4-ab$, which is connected. Thus no
single core vertex separates the core. The only outside vertex
has degree one and cannot belong to any larger two-connected
subgraph. Since $a,b$ are nonadjacent, this block is not a
clique. The block-graph domains of the owning volume's §§12–13
therefore fail, including their spin-one endpoint conclusion and
clique-with-pendant-leaves consumers.

The graph is not complete multipartite. Its vertex $\ell$ is
nonadjacent to both $b$ and $u$, whereas $bu$ is an edge. In a
complete multipartite graph, distinct nonadjacent vertices must
lie in the same independent part. Those two nonadjacencies
would put $b$ and $u$ in the part containing $\ell$, contradicting
their edge. This excludes the balanced, dominant-part and combined
complete-multipartite domains in §§10–11, for every part-size
endpoint and every $S$.

The individual odd-rim wheels in Proposition 15.4 and §16 have
no degree-one vertices; $Q$ has exactly one. The five-rim wheel
with $2t$ rim leaves in Proposition 15.3 has a six-vertex core
after all degree-one vertices are removed, whereas removing the
unique leaf of $Q$ leaves a five-vertex core. Thus $Q$ is not
any graph in those specific families, including $t=0$. The
odd-fibre theorems in §§8–9 have a different fibre parity and
supply none of the present even scales.

The collective-oscillator volume and the three Lean/Scribe pairs
supply the algebra, word normalization, token conventions,
phase counts and refutations mapped in Theorem 24.2; none states
an additional sufficient whole-graph ground-confinement domain.
Together with the graph and scale exclusions above, this exhausts
the sufficient domains in all nine supplied sources. These are
failures of their exact hypotheses, not counterexamples to their
conclusions. The new conclusion on $Q$ is precisely the
original-model conclusion already obtained from its actual
diamond components. $\square$

## 26. The scale-dependent union and the remaining question

**定义 26.1（Sufficient domains at a fixed even scale）。** Work only
in the common domain of finite connected simple unit-weight
$H$ of even order $m\geq2$. Let $\mathcal M$ consist of complete
multipartite graphs with at least two nonempty parts, and let
$\mathcal B$ consist of block graphs. Let $\mathcal L$ be the
whole-neighborhood class in the owning volume's Definition
15.1(b): each actual neighborhood is bipartite or has a flat
least mode for its entire adjacency. Let $\mathcal C$ retain
exactly Definition 21.1.

For even $s=2S\geq2$, define $\mathcal F_s$ by the global
flat-least-mode hypothesis (3.1) of the owning volume, together
with a positive-gap regime of its Theorem 6.2. Explicitly, write
$\ell=-\lambda_{\min}(A(H))$, $\Delta=\max_i\deg_H(i)$,
$T=m+2$ and

$$
 s_H=2\left\lceil2^{18}(\Delta/\ell)^2T^3\right\rceil.
\tag{26.1}
$$

Require either $s\geq s_H$, or

$$
s\geq4T,\qquad
\ell s-64\Delta T^{3/2}\sqrt{s/2}-64\Delta T^2>0.
\tag{26.2}
$$

The second alternative includes the immediate strict-positive
application of that theorem's (6.3), without replacing the exact
finite-scale bound by its asymptotic size. Define
$\mathcal L_S=\mathcal L$ for $S\geq2$ and
$\mathcal L_1=\varnothing$, and put

$$
\mathcal U_s^{\rm old}
 =\mathcal M\cup\mathcal B\cup\mathcal C
       \cup\mathcal L_S\cup\mathcal F_s,
\qquad
\mathcal U_s^{\rm diamond}
 =\mathcal U_s^{\rm old}\cup\mathcal C_{\diamond}.
\tag{26.3}
$$

All sets here are restricted to the stated common domain. The
remaining original-model question at scale $s$ is every-ground
confinement for $H\notin\mathcal U_s^{\rm diamond}$. Its
simultaneous all-even version asks for every integer $S\geq1$,
retaining the separate union (26.3) at each scale. The component
inclusions (19.4) and the $S=1$ whole-cone equalities (20.2)
remain necessary conditions, not an if-and-only-if criterion.
No arbitrary-$H$ conclusion or actual original-$E_s$
nonsymmetric-ground counterexample is specified outside this
union.

**命题 26.2（Preserved old domains and a strict addition）。** The
sufficient graph/scale domains of the nine sources in Theorem
24.2, including the direct positive-bound consequence (26.2),
have union $\mathcal U_s^{\rm old}$ within this common even-scale
domain. Every $H\in\mathcal U_s^{\rm diamond}$ satisfies
(24.2) and (24.8) on its full original carrier at that scale.
The graph $Q$ of Definition 25.1 belongs to
$\mathcal U_s^{\rm diamond}\setminus\mathcal U_s^{\rm old}$
for every even $s\geq2$. The new component class does not contain
all the old sufficient classes.

Proof. The owning volume's Corollary 11.3 covers exactly the
complete-multipartite domain $\mathcal M$ at every even scale,
including both the balanced and dominant-part regimes and the
two- and three-part cases. Corollary 13.3 supplies all of
$\mathcal B$, including $S=1$. Definition 15.1(b) and Theorem
15.2 supply $\mathcal L_S$ with exactly the endpoint $S\geq2$.
The global flat-mode sufficient regimes in Theorem 6.2 are those
in $\mathcal F_s$, with (26.2) read directly from (6.3).

The remaining all-even neighborhood domains are contained in
$\mathcal C$: this includes wholly bipartite neighborhoods,
a bipartite actual component at every vertex, whole
bipartite-or-$C_5$ neighborhoods and whole
bipartite-or-odd-cycle neighborhoods. These inclusions are the
ones proved in Proposition 21.3 or follow by selecting their
stated actual component. The individual odd-rim wheels and all
the particular consumers in §§15–18 and §22 satisfy these
conditions; the pendant-core consumers of §§12 and 14 are already
in $\mathcal B$ or $\mathcal C$. Theorem 21.2 supplies all of
$\mathcal C$. The odd-fibre statements supply no even scale.
The representation and refutation suppliers have no further
whole-graph confinement domain. This proves the asserted old
union while preserving each graph and scale hypothesis.

Every member of $\mathcal C$ is in $\mathcal C_{\diamond}$.
Theorem 24.2 and Corollary 24.3 therefore supply the new domain,
and the cited old conclusions supply each other member of the
union. Proposition 25.2 proves $Q\in\mathcal C_{\diamond}$ and
excludes it from every old member at every stated scale.
For noncontainment in the other direction, $K_6$ belongs to
$\mathcal M$ and $\mathcal B$ and has all-even confinement by
the cited results. Its neighborhood at every vertex is $K_5$,
one connected component which is nonbipartite, not a simple odd
cycle and not a diamond. Thus $K_6\notin\mathcal C_{\diamond}$.

The additional mathematical inference is the all-integer-spin
diamond obstruction of Theorem 23.2 and its insertion into the
actual-component conclusion of Theorem 19.2. Angular-momentum
addition, Boolean-chain representation, nonstrict spin comparison,
the bipartite and odd-cycle obstructions, and the finite-spectrum
gap implication are the cited intermediates. The statements
preserve positive coefficient-one adjacency, equal even fibres,
the entire complex globally half-filled carrier and the same
actual $E_s$. They give neither an exact $E_s$ nor a numerical or
scale-uniform gap, and make no extension to other signs,
weights, fibre sizes or fillings, physical realization or
worldwide priority. The question in Definition 26.1 outside the
stated scale-dependent union remains unresolved here. $\square$

## 追加锚（本行以下为增补区）

## 27. The complete multipartite local obstruction and its sole exception

**定义 27.1（Local spaces and the singlet threshold）。** Let
$G=K_{p_1,\ldots,p_q}$, where $q\geq2$ and every $p_a$ is a
positive integer. No parity condition is imposed on
$n=\sum_a p_a$. For an integer $S\geq1$, put the same spin $S$
at each vertex, with the normalized ladders of (19.5), and set

$$
\begin{aligned}
K_G&=\sum_{ij\in E(G)}(J_i^+J_j^-+J_i^-J_j^+),&
\mathcal V_G(0)&=\ker\sum_i Z_i,\\
\mathcal S_G&=\ker\sum_iJ_i^+\cap\ker\sum_iJ_i^-,&
e_G(0)&=\min\operatorname{spec}(K_G|_{\mathcal V_G(0)}),\\
\mathcal G_G(0)&=\ker(K_G-e_G(0)I)\cap\mathcal V_G(0),&
L_a&=p_aS.
\end{aligned}
\tag{27.1}
$$

All spaces are complex subspaces of $V_S^{\otimes n}$; in
particular $\mathcal S_G$ includes every total-singlet copy.
Let $\boldsymbol T_a$ be the sum of the site spins in part $a$.
Define a list $j_a^*$ and a positive number $C_*$ as follows:

$$
\begin{aligned}
2\max_aL_a\leq\sum_aL_a:quad&j_a^*=L_a\quad\hbox{for all }a;\\
L_d>R:=\sum_{a\ne d}L_a:\quad&j_d^*=R,\quad
 j_a^*=L_a\quad(a\ne d);\\
C_*&=\sum_a j_a^*(j_a^*+1),\qquad b_G=-\frac23 C_*.
\end{aligned}
\tag{27.2}
$$

The two alternatives are exhaustive, and $d$ in the second is
unique. Equality in the first alternative is included there.
Every $j_a^*$ is a positive integer, including $q=2$.

**定理 27.2（Strict local separation, with the exact singlet minimum）。**
For every graph and spin in Definition 27.1 the singlet space is
nonzero and

$$
\min_{\substack{v\in\mathcal S_G\\\|v\|=1}}
 \langle v,K_Gv\rangle=b_G.
\tag{27.3}
$$

The minimum is attained precisely on the total-singlet subspace
with part spins $j_a^*$, retaining all its internal and coupling
multiplicities. Unless $G=K_3$ and $S=1$,

$$
e_G(0)<b_G,\qquad \mathcal G_G(0)\cap\mathcal S_G=\{0\}.
\tag{27.4}
$$

At that sole exception,

$$
e_{K_3}(0)=-4=b_{K_3},\qquad
\mathcal G_{K_3}(0)=\mathcal S_{K_3}=\mathbb C z,
\quad
z=\frac1{\sqrt6}\sum_{\pi\in\mathfrak S_3}
 \operatorname{sgn}(\pi)|\pi(1,0,-1)\rangle.
\tag{27.5}
$$

In fact the least eigenvalue on the whole $V_1^{\otimes3}$ is
also $-4$, with this same one-dimensional ground space.

Proof. The singlet threshold calculation is the collective-part
Casimir and coupling calculation in the
[owning volume, (10.7)–(10.10) and (11.6)](TOKEN_GRAPH_BLOWUP_DEFECT_DECOMPOSITION.md).
The clique calculation there, (12.4)–(12.7), the bipartite case,
and the diamond calculation (23.3)–(23.6) are its special
instances. We use these as the singlet bounds and attaining
trials inside the local obstruction, with their complete
parameter ranges verified below.
The classical addition rule and its coefficient convention are
[NIST DLMF (34.1.1), (34.2.1), (34.3.16)–(34.3.17)](https://dlmf.nist.gov/34.1).
For nonnegative integer spins $u,v$, every spin
$|u-v|,|u-v|+1,\ldots,u+v$ occurs in $V_u\otimes V_v$,
with both endpoints. Iteration gives exactly the interval
$[\max(0,2M-U),U]$ for a list with sum $U$ and maximum $M$,
as proved in the owning volume's (10.8).

A part with $p_a=1$ has only spin $S$. A part with $p_a\geq2$
has every integer spin from $0$ through $L_a=p_aS$, by this
interval rule. Fix all part Casimirs and a multiplicity copy,
and denote its part spins by $j_1,\ldots,j_q$. Such a copy
contains a total singlet exactly when
$2\max_a j_a\leq\sum_a j_a$. On any total singlet, rotations
interchange the three Cartesian axes and leave the vector fixed.
Writing $\boldsymbol T=\sum_a\boldsymbol T_a$ therefore gives,
for every unit singlet, including a superposition of these copies,

$$
\begin{aligned}
\langle K_G\rangle
 &=\frac43\sum_{a<b}\langle\boldsymbol T_a\cdot\boldsymbol T_b\rangle
 =-\frac23\sum_a\langle\boldsymbol T_a^2\rangle.
\end{aligned}
\tag{27.6}
$$

The part Casimirs commute with total spin, so the singlet space
has the same orthogonal decomposition into their eigenspaces.
On one of them (27.6) is $-\frac23\sum_a j_a(j_a+1)$.
In the balanced case each $j_a\leq L_a$, and the simultaneous
maximal list is feasible. In the dominant case, on every
singlet copy,

$$
j_d\leq\sum_{a\ne d}j_a\leq R,\qquad j_a\leq L_a\ (a\ne d).
\tag{27.7}
$$

The dominant part has at least two vertices: $p_d=1$ would give
$L_d=S\leq\sum_{a\ne d}p_aS$. Thus its spin $R$ really occurs,
and the list $(R,(L_a)_{a\ne d})$ is feasible. Since $x(x+1)$
is strictly increasing for nonnegative integers, these bounds
prove (27.3), its attainment and its equality characterization
on the entire singlet space. They also include two or three
parts and a dominant part of either parity; none of the parity
or whole-graph hypotheses of the original applications is
needed for this local Casimir calculation.

We next prove strictness. Choose actual part-spin subspaces with
the positive spins $j_a=j_a^*$, and put

$$
C=\sum_a j_a(j_a+1)=C_*,\qquad
Q=\sum_a(T_a^z)^2.
$$

On a singlet $w$ in their tensor product the complete cross-part
edge set gives the vector identity

$$
K_Gw=(Q-CI)w,\qquad \langle w,Qw\rangle=C/3
\quad(\|w\|=1).
\tag{27.8}
$$

Indeed, on the whole tensor product,
$K_G=\boldsymbol T^2-(T^z)^2-\sum_a\boldsymbol T_a^2+Q$.
Both total-spin terms vanish on a singlet. The second identity
follows by rotating each part's squared components and using its
Casimir. Consequently it suffices to find a singlet $w$ which
is not an eigenvector of the diagonal operator $Q$. Then it has
Rayleigh quotient $b_G$ but is not a $K_G$ eigenvector. If the
minimum on the finite space $\mathcal V_G(0)$ were $b_G$, equality
in its spectral Rayleigh bound would make every such attaining
vector an eigenvector. Thus that one $w$ proves $e_G(0)<b_G$.

Here are the required coefficient facts, with their endpoints.
An integer-spin list $(h_1,\ldots,h_t)$ of even sum $U$ with
$2\max h_i\leq U$ has a singlet whose all-zero weight
coordinate is nonzero. Zero spins may be deleted. To prove the
claim by induction, merge two positive spins $a,b$, letting $R$
and $M$ be the sum and maximum of the remaining spins. If the
list has two factors, the polygon condition says $a=b$ and the
pair singlet has nonzero zero coordinate. Otherwise choose an integer $c$ of parity $a+b$ in

$$
\max\{|a-b|,2M-R\}\leq c\leq\min\{a+b,R\}.
\tag{27.9}
$$

This interval is nonempty. The original polygon inequalities
imply $|a-b|\leq R$ and $2M-R\leq a+b$, while $M\leq R$
gives $2M-R\leq R$. Its lower endpoints have parity $a+b$
because $U$ is even, as do $a+b$ and $R$. The new list consisting
of $c$ and the remaining spins again has even sum and satisfies
the polygon inequalities. Its positive length decreases, so
induction applies. The coefficient coupling $|a,0;b,0\rangle$
to $|c,0\rangle$ is nonzero throughout this chosen parity range:
with $g=(a+b+c)/2$ the primary all-zero formula is

$$
\begin{pmatrix}a&b&c\\0&0&0\end{pmatrix}
=(-1)^g\frac{g!}{(g-a)!(g-b)!(g-c)!}
 \sqrt{\frac{(2g-2a)!(2g-2b)!(2g-2c)!}{(2g+1)!}}\ne0.
\tag{27.10}
$$

This is [DLMF (34.3.5)](https://dlmf.nist.gov/34.3.E5), with
(34.1.1) converting to the Clebsch–Gordan coefficient. All
factorial arguments are nonnegative, including at equality in
any triangle inequality and at $c=0$. Embedding the inductively
chosen singlet through this coupling preserves a nonzero
all-zero coefficient, proving the claim.

A second fact will handle an odd sum. If $a,b\geq1$, the spin
$c=a+b-1$ in $V_a\otimes V_b$ has a nonzero coefficient at
$(1,-1)$ in its weight-zero vector. For a direct ladder
verification put $J=a+b$ and start its highest vector at

$$
h=\sqrt b\,|a,a-1;b,b\rangle
       -\sqrt a\,|a,a;b,b-1\rangle.
\tag{27.11}
$$

It is nonzero, has weight $J-1$ and is killed by the total raising
operator. Thus it generates that spin-$J-1$ chain. Expand
$(J_a^-+J_b^-)^{J-1}h$ by the binomial theorem. At the allowed
coordinate $(t,-t)$, $|t|\leq\min(a,b)$, the two terms have,
after factoring out

$$
F_t=(J-1)!
 \sqrt{\binom{2a}{a+t}\binom{2b}{b-t}}>0,
$$

the respective factors
$\sqrt{b/(2a)}(a-t)$ and
$-\sqrt{a/(2b)}(b+t)$. Their sum is
$-Jt/\sqrt{2ab}$. A term requiring a negative number of lowerings
is absent and its displayed linear factor is zero. This includes
$a=1$ or $b=1$ at $t=1$. The coefficient at $t=1$ is therefore
nonzero. Normalizing the chain multiplies it by a nonzero common
scalar. This calculation uses exactly the ladders of (19.5).

For $q=2$, feasibility forces $j_1=j_2=j\geq1$.
The pair singlet
$\sum_{t=-j}^j(-1)^{j-t}|j,t;j,-t\rangle/\sqrt{2j+1}$
has nonzero coordinates at $t=0,1$, with distinct $Q$ values
$0,2$. Its normalization is
[DLMF (34.3.1)](https://dlmf.nist.gov/34.3.E1).

For $q=3$, order the spins $a\geq b\geq c\geq1$ and put
$d=b+c-a\geq0$. There is one singlet copy. Its coordinates at

$$
(a,t,-a-t),\qquad t=-b,-b+1,\ldots,c-a,
\tag{27.12}
$$

are all nonzero. In the factorial expression
[DLMF (34.2.4)–(34.2.5)](https://dlmf.nist.gov/34.2.E4)
for the corresponding $3j$ coefficient, $m_1=a$ forces the
summation index to zero; every remaining factorial is nonnegative
precisely on this interval. The triangle factor is positive.
If $d\geq2$, its $d+1\geq3$ consecutive coordinates cannot all
have the same value of the quadratic polynomial
$a^2+t^2+(a+t)^2$. If $d=0$, the extreme coordinate has
$Q=a^2+b^2+c^2>C/3$, because
$3(a^2+b^2+c^2)-C=\sum_{j\in\{a,b,c\}}j(2j-1)>0$.
It therefore contradicts the eigenvalue $C/3$ required by (27.8).
If $d=1$, the two endpoint $Q$ values differ unless
$a=2b-1$, which together with $a=b+c-1$ says $b=c=u$,
$a=2u-1$. In this last case $C=6u^2$ and the extreme value is
$6u^2-6u+2$. Its difference from $C/3$ is
$2(2u-1)(u-1)>0$ for $u\geq2$. Only $(a,b,c)=(1,1,1)$
remains.

For $q\geq4$, put $U=\sum_a j_a$. If $U$ is even, the
all-zero construction (27.9)–(27.10) gives a nonzero coordinate
with $Q=0<C/3$. If $U$ is odd, choose two smallest spins $a,b$
and set $c=a+b-1$. The sum $R$ of the other spins satisfies
$a+b\leq R$, and each other spin is at most $(U-1)/2$ by the
original polygon inequality and odd parity. Hence the list
consisting of $c$ and the other spins has even sum $U-1$ and
satisfies the polygon inequality: $c\leq R$, and every other
spin is at most $(c+R)/2$. Its all-zero singlet coordinate is
nonzero by (27.10). Embed its spin $c$ into the two chosen
factors by (27.11). The resulting singlet has nonzero coordinate
$(1,-1,0,\ldots,0)$, so $Q=2$ there. But
$C/3\geq2q/3>2$. In both parities (27.8) again excludes a
$Q$ eigenvector. This proves strictness for every positive
feasible list except the three spins $(1,1,1)$.

For the optimizing lists (27.2), that remaining list can arise
only in the balanced case with $q=3$, $p_1=p_2=p_3=1$, $S=1$.
In a dominant three-part case $j_d^*=R\geq2$; two-part and
at-least-four-part lists were already treated. Thus the exception
is exactly the one specified in the theorem, as a graph as well
as a spin value.

To settle it completely, in the spin-one triangle the zero-weight
basis is $|0,0,0\rangle$ and the six permutations of $(1,0,-1)$.
The ladder coefficient on every permitted move is $2$. On those
six permutations the moves exchanging adjacent values $1,0$ or
$0,-1$ form a six-cycle; each permutation is also connected to
$|0,0,0\rangle$ with coefficient $2$. The operator on the rim
is $2A(C_6)$. Its nonconstant Fourier modes have eigenvalues
$2,2,-2,-2,-4$, and are orthogonal to the hub coupling. The
constant rim mode and the hub have the matrix

$$
\begin{pmatrix}4&2\sqrt6\\2\sqrt6&0\end{pmatrix},
\qquad\operatorname{spec}=\{2-2\sqrt7,2+2\sqrt7\}.
\tag{27.13}
$$

Since $\sqrt7<3$, both eigenvalues exceed $-4$. The $-4$ mode
is the alternating rim vector $z$ in (27.5), and is simple.
The total ladders annihilate $z$ by cancellation of the two
permutations contributing to every output coordinate. The
addition rule also says the singlet has multiplicity one: the
first two spins must couple to spin one to couple with the third
to zero, and each of those couplings has multiplicity one.
This proves (27.5).

For completeness, the other weight sectors cannot supply another
whole-tensor ground vector. At total weights $\pm3$ the operator
is zero. At $\pm2$ it is $2A(K_3)$, with eigenvalues $4,-2,-2$.
At weight $1$ use the triples $A_i$ with a single $1$ at $i$
and zeros elsewhere and $B_i$ with a single $-1$ at $i$ and
ones elsewhere. With $D=2(\boldsymbol1\boldsymbol1^{\mathsf T}-I_3)$,
the matrix is

$$
\begin{pmatrix}D&D\\D&0\end{pmatrix}.
\tag{27.14}
$$

The eigenvalues of $D$ are $4,-2,-2$. Thus (27.14) has
$2\pm2\sqrt5$ once each and $-1\pm\sqrt5$ twice each.
All exceed $-4$, since $\sqrt5<3$. Reversing all weights is a
unitary equivalence with weight $-1$. These sectors exhaust the
whole tensor product, proving its asserted ground classification.
Finally (27.3) and the strict Rayleigh comparison exclude every
nonzero singlet from $\mathcal G_G(0)$ in all other cases.
No restriction to real coefficients, to a single part multiplicity,
or to a prescribed part weight has entered any lower bound.
$\square$

## 28. Multipartite components in the original globally half-filled model

**定义 28.1（Class $\mathcal C_{\mathrm{mp}}$）。** In the common
domain of finite connected simple unit-weight graphs $H$ of even
order $m\geq2$, let $H\in\mathcal C_{\mathrm{mp}}$ mean that
for each vertex $p$, at least one actual connected component of
$H[N_H(p)]$ is either a singleton or a connected complete
multipartite graph with at least two positive parts. The other
actual components and every attachment outside the selected
component are unrestricted.
For every integer $S\geq1$ put $s=2S$ and retain exactly the
original objects (19.1)–(19.2):

$$
\begin{aligned}
\Omega_s&=V(H)\times[2S],&
\mathcal H_{mS}&=\operatorname{span}_{\mathbb C}
 \{|T\rangle:T\subseteq\Omega_s,\ |T|=mS\},\\
K_s&=A(F_{mS}(H[\overline{K_{2S}}])),&
P_s&=\prod_iP_i,& E_s&=\min\operatorname{spec}K_s.
\end{aligned}
\tag{28.1}
$$

In particular $E_s$ is the actual entire-carrier minimum,
without a symmetry restriction, and every allowed token move
has coefficient one. Only global half filling is prescribed.

**定理 28.2（Every original ground vector at every even scale）。**
For every $H\in\mathcal C_{\mathrm{mp}}$ and every integer
$S\geq1$,

$$
\ker(K_s-E_sI)\subseteq\operatorname{ran}P_s.
\tag{28.2}
$$

This includes every local-spin sector, every multiplicity copy,
every feasible weight, and arbitrary complex superpositions and
entanglement on (28.1).

Proof. The representation, actual-component transfer and
spin-one cone results consumed here are the complete
Theorems 19.2 and 20.1. The supplier versions are Git
`6e666c2d731da9f46b20322bc85fee74063d9b97`: §§1–26 here,
the [owning volume](TOKEN_GRAPH_BLOWUP_DEFECT_DECOMPOSITION.md),
the [collective-oscillator volume](AURIC_COLLECTIVE_OSCILLATORS_AND_RECORD_CAPACITY.md),
and the three source/Scribe pairs specified below. The new
component inference uses (27.4) and the exact endpoint (27.5),
rather than any strictness assumption on the spin comparison.

The complete orthogonal Boolean representation is

$$
\begin{aligned}
\mathcal H_{mS}&\cong
 \bigoplus_{\substack{0\leq t_i\leq S\\
                      1\leq a_i\leq r_{2S}(t_i)}}
 \left(\bigotimes_i V_{S-t_i}\right)_{\sum_i x_i=0},\\
r_{2S}(t)&=\binom{2S}{t}-\binom{2S}{t-1},\quad\binom{2S}{-1}=0,\\
J_i&=S-t_i,\qquad -J_i\leq x_i\leq J_i,\qquad n_i=S+x_i.
\end{aligned}
\tag{28.3}
$$

Every $a_i$ is a separate orthogonal copy. The original adjacency
on it is exactly the sum of ladders in (19.5), with the endpoint
zeros retained, and $P_s$ selects exactly all $t_i=0$.
The primary map to Srinivasan,
[Theorem 1.2 and its representation derivation](https://arxiv.org/pdf/1001.0280v2),
is Boolean rank $n=2S$, starting rank $t_i$, layer $u=S+x_i$,
and up operator $L_i^\ast$. Its normalized coefficient is
$\sqrt{(u+1-t_i)(2S-t_i-u)}$.
Feinsilver,
[§§3–4, (8)–(10), Proposition 4.3 and §4.2.2](https://arxiv.org/pdf/1102.0368v2),
has $T=L_i^\ast$, $T^\ast=L_i$, principal number $2J_i$,
chain index $J_i+x_i$ and grading $-2Z_i$. These give both
the multiplicities in (28.3) and the full orthogonality, including
spin zero. The owning volume's (6.6)–(6.12) supplies their
explicit whole-Boolean construction; its use does not require a
flat eigenvector of $A(H)$.

The full word-cardinality and Gram identities
`sector_words_card_multinomial` and `sector_gram`, with their
private head-removal and factorial recurrences in
[OccupancyWordSectors](../../../D5/S3/Quantum/Entanglement/OccupancyWordSectors.lean)
and its [Scribe](../../../Blueprint/D5/S3/Quantum/Entanglement/OccupancyWordSectors.scribe.cs),
use two-letter occupation counts $(2S-n_i,n_i)$ and length $2S$.
They give the normalized symmetric weight vectors, including
$n_i=0,2S$. The collective-oscillator algebra has parameters
$d=m$, $N=2S$, $g=0$, $e=1$, $B=A(H)$,
$a_i=L_i/\sqrt{2S}$ and $H_{2S}=\hbar K_s/(2S)$ on the
two-state code. Its symmetric-code statement is used only with
this map; a fixed-excitation oscillator approximation is not a
statement on the growing half-filled carrier.

The actual singleton-difference move is the definition `tokenGraph`
in [TokenGraphLaplacianRadiusRefutation](../../../D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.lean)
and its [Scribe](../../../Blueprint/D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.scribe.cs).
The private and proof-local `Test.move`, `Test.adj_mem`,
`Test.move_injective`, `Test.toNbr_bij` and `Test.token_energy`
in [CutBoundRefutation](../../../D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.lean)
and the full [Scribe](../../../Blueprint/D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.scribe.cs)
identify the same coefficient-one adjacency with the ordered
lowering/raising sum. Their `counting_identity`, `W_move`,
`phi40_norm`, `phi40_energy` and `choose_ratio40` give the
phase-count support consumed in the older odd-cycle domains;
their fixed parameters are $200$ vertices, $100$ tokens and
fibre size $40$, not an assumption here. The present argument
requires none of their cut or Laplacian refutation conclusions.
Their private real/complex Rayleigh identities use the same
Hermitian complex inner product as (27.3).
The primary convention is Apte–Parekh–Sud,
[v3, Definition 1, §3.2 and Fact 2](https://arxiv.org/pdf/2506.03441v3),
with $N=2mS$, $k=mS$ and unit edge weights. In their notation
this is $A(F_k(G_s))$ itself, while $W(G_s)I/2-K_s$ is their
shifted XY block. Here $1\leq k<N$ at every endpoint in scope.

The nonstrict primary comparison is Ghassemi
Tabrizi–Henderson–Kühne–Scuseria,
[Appendix A4, (A34)–(A54) and its final fixed-magnetization paragraph](https://pmc.ncbi.nlm.nih.gov/articles/PMC12613319/#app1-sec4),
DOI [10.1021/acs.jctc.5c01412](https://doi.org/10.1021/acs.jctc.5c01412).
Its maximal local spin is $s_i=S$, variable spin $t_i=J_i$,
fixed magnetization $M=0$, and bilinear coupling
$D_{ij}=\operatorname{diag}(2a_{ij},2a_{ij},0)$,
$a=A(H)$. Only existence of a maximal-spin minimizing choice
is taken from that result. In the fixed-weight argument the
triplet has weight zero, and the upper-spin projection has
squared norm $((j+1)^2-x^2)/((j+1)(2j+1))>0$ for every
$-j\leq x\leq j$, including $j=0$ and both endpoints.
As in (19.6), distinct weights have orthogonal projected images,
so the step also applies to entangled vectors. It does not assert
that every original ground vector has maximal spin.

Suppose now that a summand of (28.3), deficient at $p$, attains
this actual $E_s$. Theorem 19.2 supplies a minimizing realization
with all other spins $S$. For every actual connected component
$C$ of $H[N_H(p)]$ it forces

$$
\mathcal G_C(0)\subseteq\mathcal S_C.
\tag{28.4}
$$

Its proof first releases one original singlet pair at $p$ into
its zero-weight triplet. Equality at the actual whole-space
minimum makes the released vector a ground eigenvector; its two
orthogonal pair weights force the neighborhood ladders to vanish.
The actual-component weight projections then force zero weight
on each component, and their commutators with the total ladders
force separate singlets. The replacement by any local ground
vector, with the same actual outside density, gives the universal
inclusion (28.4). Thus this step is about the whole nonzero local
ground space, not only a chosen vector in one marginal. It uses
actual components, whose weights are conserved by the neighborhood
operator. It imposes no independent regional filling on the
initial original state and requires no condition on other components
or on crossing attachments.

Choose the component allowed by Definition 28.1. A singleton has
$K_C=0$ and zero-weight vector $|S,0\rangle$; it is not a
singlet because $\|J^+|S,0\rangle\|^2=S(S+1)>0$.
This contradicts (28.4). For a complete multipartite component,
(27.4) contradicts it unless $C=K_3$, $S=1$.
At that exception (27.5) says precisely $e_C(0)=-4$ and that its
whole ground space is the one-dimensional singlet. Use Theorem
20.1 at this same deficient vertex. Since $S=1$, deficiency
means $J_p=0$, and it forces
$\varepsilon_{\{p\}\cup C}(0)=e_C(0)=-4$ on the entire actual
Boolean zero-weight cone. The cone is $K_4$. On its four actual
spin-one fibres take the product of two normalized pair singlets

$$
d_1=\frac{|1,-1\rangle-|0,0\rangle+|-1,1\rangle}{\sqrt3}.
\tag{28.5}
$$

Each pair has isotropic edge expectation $-2$ and therefore XY
expectation $-8/3$; every cross-pair edge has expectation zero
because each one-site spin expectation vanishes. This actual
cone vector has total weight zero and energy $-16/3$.
It is the supplied pair-singlet trial (21.10), also used
in §24, with no change of the cone's original fibres. Thus
$\varepsilon_{\{p\}\cup C}(0)\leq-16/3<-4$, the required
contradiction. The whole-fibre cone assertion is used only at
$S=1$; no such removal is assumed at larger spins.

Every deficient summand is now excluded from the actual minimum.
Each summand reduces $K_s$. The projection of an arbitrary complex
$E_s$ eigenvector onto one is zero or another $E_s$ eigenvector.
All deficient projections vanish; the remaining summands are
exactly $\operatorname{ran}P_s$. This proves (28.2) for all
copies and their superpositions. $\square$

**推论 28.3（The same-minimum qualitative spectral and mass bounds）。**
For every $H\in\mathcal C_{\mathrm{mp}}$, $S\geq1$, the space
$\mathcal N_s=\ker P_s$ is nonzero and reducing. With the same
actual $E_s$ as in (28.1),

$$
\begin{aligned}
g_s&=\min\operatorname{spec}(K_s|_{\mathcal N_s})-E_s>0,\\
K_s-E_sI&\succeq g_s(I-P_s),\\
\|(I-P_s)\phi\|^2
 &\leq\frac{\langle\phi,K_s\phi\rangle-E_s}{g_s}
 \quad(\phi\in\mathcal H_{mS},\ \|\phi\|=1).
\end{aligned}
\tag{28.6}
$$

In particular an energy excess at most $\delta\geq0$ bounds this
mass by $\delta/g_s$. No numerical or scale-uniform gap is asserted.

Proof. This is the finite-spectrum implication of (28.2), with
exactly the same hypotheses as the supplied Corollary 24.3.
Original fibre permutations commute with $K_s$; consequently the
orthogonal projections $P_s,I-P_s$ commute with it and their
ranges reduce it. In one fibre choose a nonzero one-particle
vector orthogonal to constants. Tensor it with any nonzero
occupancy-$(2S-1)$ vector in a second fibre and occupancy-$S$
vectors in all other fibres. Its occupancy is
$1+(2S-1)+(m-2)S=mS$, and $P_s$ kills it. This proves
$\mathcal N_s\ne0$ also at $m=2,S=1$.
Every eigenvalue on this finite nonzero space is at least $E_s$.
Equality would give a nonsymmetric $E_s$ eigenvector, excluded
by (28.2), so $g_s>0$. The quadratic form of $K_s-E_sI$ is
nonnegative on $\operatorname{ran}P_s$ and at least $g_s$ times
the squared norm on $\mathcal N_s$. Add these two reducing
forms to obtain (28.6), then take its expectation in any unit
complex vector. This uses no symmetric-space substitute for
$E_s$ and gives no estimate uniform in $S$. $\square$

## 29. An infinite family with two large interacting parts

**定义 29.1（The graphs $X_r$）。** For each integer $r\geq2$,
take disjoint sets $A,B$ of size $r$, two further vertices $u,v$,
and two leaves $\ell_1,\ell_2$. On $A\sqcup B\sqcup\{u\}\sqcup\{v\}$
put the complete multipartite graph $K_{r,r,1,1}$, choose a vertex
$a\in A$, and add exactly the edges $a\ell_1,a\ell_2$.
There are no other edges; every edge has weight one.

**命题 29.2（Confinement beyond every published Section 26 domain）。**
The graphs $X_r$ form an infinite family of connected interacting
simple graphs of even order $m=2r+4$ and belong to
$\mathcal C_{\mathrm{mp}}$. For every $r\geq2$, $S\geq1$,
all conclusions (28.2) and (28.6) hold on their entire original
complex carrier with $N=2(2r+4)S$, $k=(2r+4)S$.
For every even scale $s=2S$,

$$
X_r\notin\mathcal U_s^{\rm diamond}
 =\mathcal M\cup\mathcal B\cup\mathcal C
       \cup\mathcal L_S\cup\mathcal F_s\cup\mathcal C_{\diamond},
\tag{29.1}
$$

with exactly the domains and both alternatives for $\mathcal F_s$
in Definition 26.1.

Proof. The core is connected, and both added vertices are leaves
at $a$. The order is $2r+4$ and the edge count is $r^2+4r+3$;
the $r^2$ edges between $A$ and $B$ belong to the same connected
core as all the other edges. Different $r$ give different orders.
Thus this family adds interacting core vertices rather than
disjoint spectator factors. Its complete induced neighborhoods
are

$$
\begin{aligned}
X_r[N(a)]&=K_{r,1,1}[B,\{u\},\{v\}]
                      \sqcup\{\ell_1\}\sqcup\{\ell_2\},\\
X_r[N(x)]&=K_{r,1,1}[B,\{u\},\{v\}]
                                      &&(x\in A\setminus\{a\}),\\
X_r[N(y)]&=K_{r,1,1}[A,\{u\},\{v\}]
                                      &&(y\in B),\\
X_r[N(u)]&=K_{r,r,1}[A,B,\{v\}],&
X_r[N(v)]&=K_{r,r,1}[A,B,\{u\}],\\
X_r[N(\ell_i)]&=\{a\} &&(i=1,2).
\end{aligned}
\tag{29.2}
$$

All displayed components are actual components, and the list
includes every edge of every neighborhood. The leaves are
isolated within $N(a)$ because their only neighbor is $a$.
All non-singleton entries are connected complete multipartite
graphs. This proves membership in Definition 28.1 and the stated
original-model conclusions.

At $u$ the sole neighborhood component is $K_{r,r,1}$. It contains
a triangle, has $2r+1\geq5$ vertices, and its singleton-part
vertex has degree $2r\geq4$. Hence it is not bipartite, not a
simple odd cycle and not a diamond. It has no other component.
This excludes $\mathcal C$ and $\mathcal C_{\diamond}$.
It also has no flat least adjacency mode, as follows. The
subspaces summing to zero inside either size-$r$ part have
eigenvalue zero. On constant-on-parts vectors the antisymmetric
choice $(c,-c,0)$ has eigenvalue $-r$. The symmetric choices
$(c,c,d)$ have the two eigenvalues of

$$
\begin{pmatrix}r&1\\2r&0\end{pmatrix},\qquad
\lambda_\pm=\frac{r\pm\sqrt{r^2+8r}}2.
\tag{29.3}
$$

These subspaces exhaust the $2r+1$ dimensions. Since $r>1$,
$\sqrt{r^2+8r}<3r$, so $\lambda_->-r$. Thus the least
eigenvalue is the simple $-r$; every vector in its complex
eigenspace vanishes at the singleton-part vertex. It cannot
have modulus one at every coordinate. The whole-neighborhood
condition $\mathcal L$ therefore fails at $u$. This excludes
$\mathcal L_S$ for every $S\geq2$; $\mathcal L_1$ is empty
by its definition.

The global flat least-mode hypothesis also fails independently
of scale. Put $+1$ on $A$, $-1$ on $B$, and zero elsewhere.
Its adjacency quadratic form is $-2r^2$, its squared norm is
$2r$, and all edges with a zero endpoint contribute zero. Thus

$$
\lambda_{\min}(A(X_r))\leq-r\leq-2.
\tag{29.4}
$$

A modulus-one eigenvector $z$ for this least eigenvalue would,
at a leaf, satisfy $\lambda_{\min}z_{\ell_i}=z_a$.
Taking absolute values would force $|\lambda_{\min}|=1$,
contradicting (29.4). Since global flatness is required before
either positive-gap alternative defining $\mathcal F_s$ can
apply, $X_r\notin\mathcal F_s$ for every even $s$, including
both the $s\geq s_H$ alternative and the direct strictly
positive finite-scale expression (26.2).

The graph is not complete multipartite. A leaf is nonadjacent
to $b\in B$ and to $u$, while $bu$ is an edge. In a complete
multipartite graph distinct nonadjacent vertices belong to the
same independent part, so these three relations are impossible.
This excludes all of $\mathcal M$, with its balanced and
dominant-part regimes and all part-number endpoints.

The core $K_{r,r,1,1}$ is a maximal two-connected nonclique block.
Deleting any one core vertex leaves a connected complete
multipartite graph with at least three nonempty parts. A leaf
cannot belong to a two-connected enlargement. Two distinct
vertices of $A$ are nonadjacent, so this maximal block is not
a clique. Therefore $X_r\notin\mathcal B$.

These exclusions prove (29.1). Proposition 26.2 identifies the
exact old domains, including all their specific consumers, and
Definition 26.1 includes the diamond addition. Consequently the
family is outside every one of those sufficient graph/scale
domains, rather than outside only a particular asymptotic bound.
The six-vertex graph of §25 has different order from every
$X_r$, whose order is at least eight; the earlier consumers lie
in the excluded union. The assertion here concerns the original
interacting graphs $X_r$ and their actual $E_s$, not separate
minimization of the regions in (29.2). $\square$

## 30. The enlarged exact union and its unresolved complement

**定义 30.1（The preserved scale-dependent union）。** In the common
domain of Definition 26.1, retain its sets $\mathcal M$,
$\mathcal B$, $\mathcal C$, $\mathcal L_S$, $\mathcal F_s$ and
$\mathcal C_{\diamond}$ without altering any of their graph
or scale hypotheses. In particular $\mathcal L_1=\varnothing$
and $\mathcal L_S=\mathcal L$ for $S\geq2$. For the global
flat-least-mode graph in $\mathcal F_s$, write
$\ell=-\lambda_{\min}(A(H))$, $\Delta=\max_i\deg_H(i)$,
$T=m+2$, and

$$
s_H=2\left\lceil2^{18}(\Delta/\ell)^2T^3\right\rceil.
$$

Both original scale alternatives remain: either $s\geq s_H$,
or simultaneously

$$
s\geq4T,\qquad
\ell s-64\Delta T^{3/2}\sqrt{s/2}-64\Delta T^2>0.
\tag{30.1}
$$

With $\mathcal C_{\mathrm{mp}}$ exactly as in Definition 28.1,
put

$$
\begin{aligned}
\mathcal U_s^{\rm mp}
 &=\mathcal U_s^{\rm diamond}\cup\mathcal C_{\mathrm{mp}}\\
 &=\mathcal M\cup\mathcal B\cup\mathcal C\cup\mathcal L_S
    \cup\mathcal F_s\cup\mathcal C_{\diamond}
    \cup\mathcal C_{\mathrm{mp}},\qquad s=2S\geq2.
\end{aligned}
\tag{30.2}
$$

**定理 30.2（Coverage with the original quantifiers）。** For every
integer $S\geq1$ and every $H\in\mathcal U_s^{\rm mp}$,
every ground vector on (28.1) is fibre symmetric and all the
qualitative spectral, operator and mass conclusions (28.6) hold
at the same actual whole-space $E_s$. The inclusion
$\mathcal U_s^{\rm diamond}\subsetneq\mathcal U_s^{\rm mp}$
is strict at every even scale, witnessed by all $X_r$, $r\geq2$.

Proof. Proposition 26.2 supplies the unchanged conclusions for
$\mathcal U_s^{\rm diamond}$ with exactly the two flat-mode
regimes and the separate $S=1$ neighborhood endpoint stated
there. Theorem 28.2 and Corollary 28.3 supply the added class.
Taking their union proves the first assertion without intersecting
the old domains with the new condition. Proposition 29.2 gives
both membership and nonmembership needed for strictness at every
scale. The singlet thresholds, classical coupling, clique,
bipartite and diamond calculations are the attributed support
within Theorem 27.2; the additional local inference is its strict
zero-weight separation for arbitrary complete multipartite
components and the exact exceptional ground classification.
Its insertion into the supplied actual-component condition, with
the supplied spin-one actual-cone comparison at the exception,
gives the original-model extension and its infinite consumer.

For an arbitrary connected even-order $H$ outside (30.2),
every-ground confinement remains unresolved here at that scale.
The simultaneous all-even question retains this union separately
for every $S\geq1$; a scale-dependent sufficient hypothesis is
not silently promoted to an all-scale graph hypothesis.
The component inclusions (19.4) and spin-one cone equalities
(20.2) remain necessary conditions, not an if-and-only-if test.
In particular the local strict comparisons do not construct an
actual original-$E_s$ nonsymmetric ground counterexample.
All assertions retain simple unit-weight graphs, positive
coefficient-one adjacency, equal even fibres, global half filling,
and the full complex carrier. They determine neither the exact
original $E_s$ nor a numerical or scale-uniform gap, and give
no extension to other signs, weights, fibres or fillings.
$\square$

## 追加锚（本行以下为增补区）

## 31. Joint equality spaces and the actual crossing incidence

**定义 31.1（One deficient fibre and the original minimum）。**
Let $H$ be any finite connected simple unit-weight graph of even
order $m\geq2$, let $S\geq1$ be an integer and put $s=2S$.
Retain exactly the complex carrier, coefficient-one adjacency,
fibre projection and entire-carrier minimum
$\mathcal H_{mS},K_s,P_s,E_s$ of (19.1)–(19.2).
Write $V_J^{(a)}$ for an actual spin-$J$ copy in an original
$2S$-coordinate fibre. Its multiplicity is

$$
r_{2S}(S-J)=\binom{2S}{S-J}-\binom{2S}{S-J-1},
\qquad J=0,1,\ldots,S.
\tag{31.1}
$$

For a vertex $p$, let $K^{p,J}$ be the restriction to the
zero-total-weight space with spin $J$ at $p$ and spin $S$
at every other vertex. Its matrix is the same on each actual
multiplicity copy. Put

$$
\begin{aligned}
j&=S-1,&
\mu_p(J)&=\min\operatorname{spec}K^{p,J},&
\Delta_p&=\mu_p(j)-E_s,\\
g_s&=\min\operatorname{spec}(K_s|_{\ker P_s})-E_s.
\end{aligned}
\tag{31.2}
$$

These are minima on nonzero finite spaces. The exact gap
reduction is $g_s=\min_p\Delta_p$, with $\Delta_p\geq0$;
the reduction follows from the supplied nonstrict local-spin
comparison and is justified below. Thus $\Delta_p=0$ means
attainment of the actual $E_s$ by this original deficient
sector, including the endpoint $j=0$.

**定义 31.2（Regional ground spaces and real ladder relations）。**
Fix $p$ and set

$$
A=N_H(p),\qquad R=V(H)\setminus(\{p\}\cup A).
\tag{31.3}
$$

All factors in $A$ and $R$ are the actual maximal-spin-$S$
factors. For $X\subseteq A\cup R$ use the operators $K_X,Z_X$
and $B_X^\pm$ of (19.3). For every integer $q$ with
$\mathcal V_R(q):=\ker(Z_R-qI)\ne0$, define

$$
\begin{aligned}
e_A&=\min\operatorname{spec}(K_A|_{\ker Z_A}),&
U&=\mathcal G_A(0),\\
e_R(q)&=\min\operatorname{spec}(K_R|_{\mathcal V_R(q)}),&
W_q&=\ker(K_R-e_R(q)I)\cap\mathcal V_R(q),\\
\mathcal Q_t&=\{q\in\mathbb Z:\mathcal V_R(q)\ne0,\ |q|\leq t\},&
\eta&=\min_{q\in\mathcal Q_{S-1}}e_R(q),\\
M_{ir}&=\mathbf1_{\{i,r\}\in E(H)}\quad(i\in A,r\in R),&
V_{AR}&=\sum_{i\in A,r\in R}M_{ir}
 (J_i^+J_r^-+J_i^-J_r^+).
\end{aligned}
\tag{31.4}
$$

Here $U$ and each $W_q$ are their entire complex eigenspaces.
The set $\mathcal Q_{S-1}$ is nonempty since it contains zero.
For $R=\varnothing$ there is only $q=0$, with
$\mathcal V_R(0)=W_0=\mathbb C$, $K_R=Z_R=0$ and
$e_R(0)=\eta=0$; $M$ then has no columns and $V_{AR}=0$.
A regional weight slice reduces its own regional operator,
because $[K_X,Z_X]=0$. No invariance of a regional weight
slice under the coupled operator $K_s$ is part of this definition.

For any finite set $X$ of positive-spin-$S$ factors and any
nonzero complex subspace $W\subseteq V_S^{\otimes X}$, put

$$
\begin{aligned}
T_X^\pm(c)&=\sum_{x\in X}c_xJ_x^\pm,\\
L(W)&=\{c\in\mathbb R^X:T_X^+(c)W=T_X^-(c)W=0\}.
\end{aligned}
\tag{31.5}
$$

The equality to zero means annihilation of every vector of $W$.
A coordinate is active if some element of $L(W)$ is nonzero
there; otherwise it is inactive. A signed indicator on a set
$B\subseteq X$ is a vector $\sigma\in\mathbb R^X$ with
$\sigma_x\in\{1,-1\}$ on $B$ and zero outside $B$.
For $X=\varnothing$ use $\mathbb R^X=\{0\}$ and the same
empty-tensor convention as above.

**定理 31.3（Joint necessary equality and incidence theorem）。**
With Definitions 31.1–31.2, suppose $\Delta_p=0$.
Then the following conclusions hold simultaneously.

(a) The regional minima satisfy

$$
E_s=e_A+\eta,\qquad
\min_{q\in\mathcal Q_S}e_R(q)=\eta.
\tag{31.6}
$$

In particular at least one minimizing exterior weight belongs
to $\mathcal Q_{S-1}$. For every $q\in\mathcal Q_S$ with
$e_R(q)=\eta$, every integer $J$ with $|q|\leq J\leq S$,
and every actual spin-$J$ multiplicity copy $a$ at $p$,

$$
\begin{aligned}
|J,-q\rangle_p^{(a)}\otimes U\otimes W_q
 &\subseteq\ker(K_s-E_sI),\\
V_{AR}(U\otimes W_q)&=0.
\end{aligned}
\tag{31.7}
$$

The first line is an inclusion of entire complex subspaces in
the original carrier, and includes their superpositions across
weights, spins and copies whenever those summands occur.

(b) The real relation space used here has the following
finite-spin description, also for every general $W$ in (31.5).
There are pairwise disjoint active blocks $B_b$, each of size
at least two, and signed indicators $\sigma_b$ on them such that

$$
L(W)=\bigoplus_b\mathbb R\sigma_b.
\tag{31.8}
$$

All coordinates outside their union are inactive.
For every block, $Z_{B_b}W=0$. Simultaneously rotating the
negative-sign sites of all $\sigma_b$ by $\pi$ about the
$z$ axis makes $W$ separately singlet on every $B_b$.
The empty block family and $L(W)=0$ are included. This is the
collective-singlet and finite-dimensional algebra description
used in the joint theorem; it asserts no tensor factorization
of $W$.

For the actual $U$ there is a partition of all of $A$ into
blocks $A_b$ of size at least two, refining the actual connected
components of $H[A]$, such that

$$
L(U)=\bigoplus_b\mathbb R\mathbf1_{A_b}.
\tag{31.9}
$$

No factorization of $U$ across the $A_b$ is asserted.

(c) For every minimizing $q$ in (a), with the same actual
matrix $M$ and the same partition (31.9), one has the equivalence

$$
V_{AR}(U\otimes W_q)=0
\quad\Longleftrightarrow\quad
M_{i,\bullet}-M_{i',\bullet}\in L(W_q)
\quad\text{whenever }i,i'\in A_b.
\tag{31.10}
$$

In fact the equivalence uses only the indicated weight of
$W_q$ and (31.9), not a converse ground-state assumption.
Under $\Delta_p=0$ its left side holds for every such $q$,
so all the row conditions hold simultaneously.

(d) Apply (31.8) to each such $W_q$, allowing its blocks and
signs to depend on $q$. Every row difference in (31.10) has
its unique expression

$$
M_{i,\bullet}-M_{i',\bullet}
   =\sum_d\varepsilon_d\sigma_d,
\qquad \varepsilon_d\in\{-1,0,1\}.
\tag{31.11}
$$

It is zero on inactive coordinates. Its nonzero support is a
union of whole active blocks and cannot be a singleton.
If all exterior coordinates are active for $W_q$, then $q=0$.
This includes the empty exterior. Failure of a required row
condition excludes $\Delta_p=0$ at this $p$.

These are necessary consequences of equality at the actual
entire-carrier minimum. The equivalence (31.10) concerns boundary
annihilation only. It supplies neither universal strictness
nor a sufficient condition for a product space to attain $E_s$.
The arbitrary-$H$ confinement question outside (30.2), and the
requirement that a nonsymmetric counterexample attain the actual
original $E_s$, remain as in Theorem 30.2.

Proof. First recall the precise representation and minimum
comparison being consumed. The full orthogonal decomposition
(19.5), or the [owning volume's (6.6)–(6.12)](TOKEN_GRAPH_BLOWUP_DEFECT_DECOMPOSITION.md),
is

$$
\mathcal H_{mS}\cong
\bigoplus_{\substack{J_i\in\{0,\ldots,S\}\\
             1\leq a_i\leq r_{2S}(S-J_i)}}
 \left(\bigotimes_i V_{J_i}^{(a_i)}\right)_{\sum_i Z_i=0}.
\tag{31.12}
$$

Each summand reduces $K_s$, whose restriction is
$\sum_{\{i,k\}\in E(H)}(J_i^+J_k^-+J_i^-J_k^+)$ with
exactly the ladders in (19.5). Its weight $x_i$ has original
occupancy $S+x_i$, including both endpoints.
For Srinivasan, [Theorem 1.2 and the representation construction](https://arxiv.org/pdf/1001.0280v2),
the parameters are Boolean rank $2S$, starting rank $S-J_i$
and layer $u=S+x_i$. His up operator is $L_i^\ast$ and its
coefficient is
$\sqrt{(u+1-(S-J_i))(2S-(S-J_i)-u)}$.
For Feinsilver, [§§3–4, Proposition 4.3 and §4.2.2](https://arxiv.org/pdf/1102.0368v2),
the principal number is $2J_i$, the chain index is $J_i+x_i$,
$T=L_i^\ast$, $T^\ast=L_i$ and the grading is $-2Z_i$.
Thus (31.12) retains the spin-zero chains and every multiplicity.

The normalized maximal-spin weights are the actual two-letter
occupation vectors with counts $(2S-n_i,n_i)$ and length $2S$.
The cardinality and Gram formulas are
`sector_words_card_multinomial` and `sector_gram` in
[OccupancyWordSectors](../../../D5/S3/Quantum/Entanglement/OccupancyWordSectors.lean)
and its [Scribe](../../../Blueprint/D5/S3/Quantum/Entanglement/OccupancyWordSectors.scribe.cs);
the head-removal and factorial recurrences give the same formulas
when either count is zero. Equivalently, (O.2), (O.8)–(O.9) of
the [collective-oscillator volume](AURIC_COLLECTIVE_OSCILLATORS_AND_RECORD_CAPACITY.md)
have parameters $d=m$, $N=2S$, $g=0$, $e=1$ and
$a_i=L_i/\sqrt{2S}$. With its matrix $B=A(H)$ its finite
operator is $H_{2S}=\hbar K_s/(2S)$ on the two-state code.
Only these exact finite identities are used, not a fixed-excitation
approximation at the growing excitation $mS$.

The singleton differences in `tokenGraph` in
[TokenGraphLaplacianRadiusRefutation](../../../D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.lean)
and its [Scribe](../../../Blueprint/D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.scribe.cs)
give one removed and one inserted original coordinate for every
allowed move. The full `Test.move`, `Test.adj_mem`,
`Test.move_injective`, `Test.toNbr_bij` and `Test.token_energy`
arguments in [CutBoundRefutation](../../../D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.lean)
and its [Scribe](../../../Blueprint/D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.scribe.cs)
identify that move sum with coefficient-one adjacency.
In particular, summing $L_i^\ast L_k$ over ordered adjacent
fibre indices gives the two ladder terms for each unordered edge,
with no extra factor or diagonal shift. The primary convention
is [Apte–Parekh–Sud v3, Definition 1 and Fact 2](https://arxiv.org/pdf/2506.03441v3),
with $N=2mS$, $k=mS$ and all edge weights one.
Their shifted operator $W(G_s)I/2-K_s$ is different from $K_s$.
The real/complex Rayleigh identities in the same complete
CutBoundRefutation source justify the identical complex Rayleigh
minimum. None of its cut, phase-trial or Laplacian refutations
is a premise about the present ground space.

The nonstrict fixed-zero-weight comparison in (19.6) and the
owning volume's (7.4)–(7.5) is the result of Ghassemi
Tabrizi–Henderson–Kühne–Scuseria,
[Appendix A4, (A34)–(A54) and its final fixed-magnetization paragraph](https://pmc.ncbi.nlm.nih.gov/articles/PMC12613319/#app1-sec4),
DOI [10.1021/acs.jctc.5c01412](https://doi.org/10.1021/acs.jctc.5c01412).
The source's maximal spins are $s_i=S$, its variable spins
are $t_i=J_i$, its magnetization is $M=0$, and
$D_{ik}=\operatorname{diag}(2A(H)_{ik},2A(H)_{ik},0)$.
It gives nonincrease of the minimum when one local spin is
increased by one. The weight-zero triplet used there preserves
total weight, and its upper-spin projection has squared norm
$((J+1)^2-x^2)/((J+1)(2J+1))>0$ for every $|x|\leq J$,
including $J=0$ and both endpoints. Orthogonality of different
weights preserves nonvanishing for entangled inputs. Only this
nonstrict comparison, not an every-vector exclusion, is used.

To verify the reduction in (31.2), take any deficient summand of
(31.12). At some $p$ its spin is at most $S-1$. Increase that
spin to $S-1$ and every other spin to $S$. The comparison shows
that its minimum is at least $\mu_p(S-1)$. Conversely each
sector defining $\mu_p(S-1)$ is an actual deficient summand in
$\ker P_s$. Taking both minima proves
$g_s=\min_p(\mu_p(S-1)-E_s)$.
All original sector energies are at least $E_s$, so
$\Delta_p\geq0$. This proves the claimed exact reduction.

Now $\Delta_p=0$ supplies an original ground vector in the
sector with spin $j=S-1$ at $p$ and spin $S$ elsewhere.
Apply the complete necessary-ground-space result of Theorem
19.2, including (19.12)–(19.16). It gives

$$
\begin{aligned}
U&\subseteq\mathcal S_A,&
B_C^\pm U&=0,& Z_CU&=0
   \quad(C\text{ an actual component of }H[A]),\\
e_A&=\sum_Ce_C(0),&
0\ne\Psi&\in V_j\otimes U\otimes V_S^{\otimes R},&
(Z_p+Z_R)\Psi&=0,qquad K_s\Psi=E_s\Psi.
\end{aligned}
\tag{31.13}
$$

Here $\Psi$ can be normalized. To spell out the use of its
component conclusion, the support of each component marginal
lies in $\mathcal G_C(0)$. For its orthogonal projection $Q_C$
this says $\|(I-Q_C)\Psi\|^2=0$.
The commuting component projections therefore put $\Psi$ in
the tensor product of those component ground spaces. The sum
$K_A=\sum_CK_C$ acts there by $\sum_Ce_C(0)=e_A$, proving
the asserted $U$ support without claiming a product vector.
The universal inclusion of the *whole* $U$ in the singlet space
is (19.13), not an inference from just that marginal support.
It is obtained there by replacing the neighborhood with any
zero-weight local ground vector and releasing an original
singlet pair at $p$; the two orthogonal triplet outputs force
both neighborhood ladders to vanish. Thus the hypothesis is
attainment of the same actual $E_s$, as required here.

Let $\Pi_A$ be the projector onto the full $A$ singlet space.
Simultaneous rotations fix each of its vectors and reverse a
specified one-site Cartesian component under a $\pi$ rotation
about an orthogonal axis. Hence
$\Pi_AJ_i^\pm\Pi_A=0$ for $i\in A$, as in (19.9).
The $p$–$A$ terms also annihilate $V_J\otimes U$, since
they are $J_p^+B_A^-+J_p^-B_A^+$.
There are no $p$–$R$ edges. Consequently, on the vector in
(31.13), all crossing expectations vanish and

$$
E_s=e_A+\langle\Psi,K_R\Psi\rangle.
\tag{31.14}
$$

This compression identity also holds with arbitrary operators
on the spectator tensor factors; it does not require an
unentangled $\Psi$.

Decompose only by the $p$ weight and the exterior weight:

$$
\Psi=\sum_{q\in\mathcal Q_j}|j,-q\rangle_p\otimes f_q,
\qquad f_q\in U\otimes\mathcal V_R(q),\qquad
\sum_q\|f_q\|^2=1.
\tag{31.15}
$$

Since $K_R$ preserves its own weight spaces, (31.14) gives

$$
E_s\geq e_A+\sum_{q\in\mathcal Q_j}e_R(q)\|f_q\|^2
\geq e_A+\eta.
\tag{31.16}
$$

Choose a minimizing $q_0\in\mathcal Q_j$, any unit $u\in U$
and any unit $w\in W_{q_0}$. The actual original vector
$|j,-q_0\rangle_p\otimes u\otimes w$ has total weight zero
and Rayleigh quotient $e_A+\eta$: the $p$–$A$ term is zero,
and the $A$–$R$ expectation is zero by the preceding singlet
compression. The variational principle on the whole original
carrier gives the reverse of (31.16), so $E_s=e_A+\eta$.
No regional slice was assumed to reduce $K_s$ in this argument.

For any $q\in\mathcal Q_S$ the same trial using spin $S$
at $p$ gives $E_s\leq e_A+e_R(q)$. Thus $e_R(q)\geq\eta$
for every such $q$, while $q_0$ attains $\eta$ and belongs to
$\mathcal Q_{S-1}\subseteq\mathcal Q_S$. This proves all of
(31.6), also when $S=1$ and $\mathcal Q_j=\{0\}$.

Fix any $q\in\mathcal Q_S$ with $e_R(q)=\eta$ and any
$|q|\leq J\leq S$. Every actual copy of $V_J$ occurs with
the multiplicity (31.1). For unit $u\in U,w\in W_q$, the
same calculation on that copy gives Rayleigh quotient $E_s$
to $|J,-q\rangle_p^{(a)}\otimes u\otimes w$.
For a finite Hermitian operator whose entire-carrier minimum
is $E_s$, zero expectation of $K_s-E_sI\succeq0$ implies
membership in its kernel: in an orthonormal eigenbasis the
expectation is a sum of nonnegative numbers
$(\theta-E_s)|c_\theta|^2$, each of which must vanish.
Thus every such product is an original ground vector.
Its internal terms already act by $e_A+\eta=E_s$, and its
$p$–$A$ term is zero. Subtracting those terms from the ground
equation leaves

$$
|J,-q\rangle_p^{(a)}\otimes V_{AR}(u\otimes w)=0.
\tag{31.17}
$$

The nonzero first factor proves the boundary annihilation for
all $u,w$. Product vectors span $U\otimes W_q$ over
$\mathbb C$; linearity proves (31.7) on the whole space and
on all stated superpositions, including entanglement within
and between its regions. No choice of one minimizing weight,
one local ground vector or one multiplicity copy is retained.

We next establish the finite-spin algebra needed to interpret
this boundary equation. The collective singlet condition is
annihilation by the three total spin components, equivalently
by both total ladders. This is the trivial spin summand in
angular-momentum addition; see [DLMF §§34.1–34.3](https://dlmf.nist.gov/34.1).
Diagonal collective stabilizers and their disjoint spin blocks
are classical representation-theoretic structures; for the
spin-$\tfrac12$ setting see Lyons–Walck,
[*Multiparty quantum states stabilized by the diagonal subgroup
of the local unitary group*, introduction (1)–(2)](https://arxiv.org/pdf/0808.2989v2),
and Lyons–Skelton–Walck,
[*Werner State Structure and Entanglement Classification*, §3](https://arxiv.org/pdf/1109.6063v2).
Only the collective-singlet and elementary finite-dimensional
algebra facts are used here. The following argument gives their
needed real-coefficient, common-subspace form directly, without
assuming a classification of positive-integer-spin graph ground
spaces from those qubit results.

For the arbitrary nonzero $W$ of (31.5), abbreviate
$T_X^\pm(c)$ to $T^\pm(c)$ and put
$D(c)=\sum_xc_xZ_x$. Products of coefficient vectors in this
paragraph are coordinatewise. The spin commutation relations give

$$
[T^+(c),T^-(d)]=2D(cd),\qquad
[D(cd),T^\pm(e)]=\pm T^\pm(cde).
\tag{31.18}
$$

If two operators annihilate $W$ pointwise, their commutator
does too. Therefore, for $c,d,e\in L(W)$,
$D(cd)W=0$ and $cde\in L(W)$.
In particular every odd coordinatewise power $a^{2k+1}$ of
an $a\in L(W)$ belongs to $L(W)$, by induction using the
ternary product with $a,a$.

For an active coordinate $x$, let $\lambda_x$ be the nonzero
real linear functional $c\mapsto c_x$ on $L(W)$.
Partition the active coordinates by
$x\sim y$ if $\lambda_x=\lambda_y$ or
$\lambda_x=-\lambda_y$. This is an equivalence relation.
Choose a representative $x_b$ of each class $B_b$ and signs
$\sigma_b(x)$ so that
$\lambda_x=\sigma_b(x)\lambda_{x_b}$ on $B_b$.
Every $c\in L(W)$ is then constant up to those signs on a
class and is zero at inactive coordinates.

There exists $a\in L(W)$ for which all $a_{x_b}$ are nonzero
and their squares are pairwise distinct. Indeed the excluded
conditions are the kernels of finitely many nonzero real
linear forms $\lambda_{x_b}$ and
$\lambda_{x_b}\pm\lambda_{x_d}$ for distinct classes.
Their product is a nonzero polynomial on the finite-dimensional
real vector space $L(W)$, so it cannot vanish everywhere.
Write $v_b=a_{x_b}$ and extend each $\sigma_b$ by zero outside
its class. If there are $h$ classes, the $h$ vectors
$a,a^3,\ldots,a^{2h-1}$ have the expansions

$$
a^{2k+1}=\sum_{b=1}^h v_b^{2k+1}\sigma_b,
\qquad 0\leq k<h.
\tag{31.19}
$$

The coefficient matrix is invertible: its determinant, up to
ordering, is
$\prod_bv_b\prod_{b<d}(v_d^2-v_b^2)\ne0$.
Thus every $\sigma_b$ is in $L(W)$. Conversely the functional
relations defining the classes already put every element of
$L(W)$ in their span. Disjoint nonempty supports make the sum
direct, proving (31.8). If there are no active coordinates,
$L(W)=0$ and the assertion holds with no blocks; this also
covers $X=\varnothing$.

Apply (31.18) with $c=d=\sigma_b$ to get
$Z_{B_b}W=0$. Let

$$
\mathcal R_\sigma=
 \prod_{\substack{b,\ x\in B_b\\\sigma_b(x)=-1}}
 e^{-\mathrm i\pi Z_x}.
\tag{31.20}
$$

Conjugating a local ladder by this rotation changes its sign
exactly at the negative-sign sites and leaves each $Z_x$
unchanged. Hence both unweighted ladders on $B_b$ annihilate
$\mathcal R_\sigma W$, as does $Z_{B_b}$.
Their three Cartesian generators consequently fix this entire
space under every simultaneous block rotation: every vector
is a singlet on that block. If $B_b=\{x\}$, the same equations
would give $Z_xW=J_x^+W=J_x^-W=0$. For $0\ne w\in W$
the Casimir identity instead gives

$$
\|J_x^+w\|^2
 =\langle w,(S(S+1)I-Z_x(Z_x+I))w\rangle
 =S(S+1)\|w\|^2>0,
\tag{31.21}
$$

a contradiction. Every block therefore has size at least two.
These arguments apply to all vectors of $W$ simultaneously;
they do not select a basis vector or assume that $W$ factors.

For the actual $U$, (31.13) puts $\mathbf1_A$ in $L(U)$ and
also puts $\mathbf1_C$ in $L(U)$ for every actual component
$C$ of $H[A]$. Thus every coordinate of $A$ is active.
On any signed block of (31.8), an element of $L(U)$ is a
scalar multiple of its sign pattern. Since $\mathbf1_A$ has
value one everywhere, that pattern must be constant on the
block. Reversing an overall sign makes it $\mathbf1_{A_b}$.
Moreover $\mathbf1_C$ must be constant on each $A_b$;
therefore $A_b$ cannot meet both $C$ and its complement.
This proves (31.9) with refinement of actual components and
with the already proved exclusion of singleton blocks.
It proves only a relation-space partition, not factorization
of the complex space $U$.

For the boundary equivalence we need the full space of complex
relations among just one sign of the ladders on $U$.
Let $\alpha_i^\pm=J_i^\pm|_U$ be the corresponding linear maps.
Then

$$
\left\{c\in\mathbb C^A:\sum_i c_i\alpha_i^+=0\right\}
 =L(U)\otimes_{\mathbb R}\mathbb C
 =\left\{c\in\mathbb C^A:\sum_i c_i\alpha_i^-=0\right\}.
\tag{31.22}
$$

To prove this, a simultaneous rotation of $A$ by $\pi$ about
$x$ fixes every vector of $U\subseteq\mathcal S_A$ and
interchanges $J_i^+$ with $J_i^-$. Thus either one-sign
relation implies the other, with the same complex coefficients.
Write $c=a+\mathrm i b$ with $a,b\in\mathbb R^A$.
Both relations imply $X(a)+\mathrm iX(b)=0$ and
$Y(a)+\mathrm iY(b)=0$ on $U$, where
$X(a)=\sum_i a_iX_i$ and similarly for the other sums.
The self-adjoint operators $X(a),X(b)$ commute, since all
same-axis site operators commute. Thus for every $u\in U$,

$$
0=\|(X(a)+\mathrm iX(b))u\|^2
  =\|X(a)u\|^2+\|X(b)u\|^2.
\tag{31.22a}
$$

The cross term is zero because
$\langle X(a)u,X(b)u\rangle=\langle u,X(a)X(b)u\rangle$
is real. The same argument with $Y$ shows that all four real
sums annihilate $U$. Therefore $a,b\in L(U)$.
Conversely the complexification of $L(U)$ supplies both
relations by linearity. This proves (31.22) on the entire
complex subspace, without a reality assumption on its vectors.

For each block choose one representative $i_b\in A_b$.
By (31.9) and (31.22), for either fixed sign the only relations
among the $\alpha_i^\pm$ are the complex spans of
$\sum_{i\in A_b}\alpha_i^\pm=0$. It follows that
$\{\alpha_i^\pm:i\in A_b\setminus\{i_b\},\ b\}$ is linearly
independent: a relation among these maps would extend by zero
at each $i_b$ to an element constant on every block, hence to
zero everywhere. The same family spans all the maps since
$\alpha_{i_b}^\pm=-\sum_{i\in A_b\setminus\{i_b\}}\alpha_i^\pm$.

Fix a minimizing $q$ and write

$$
\beta_i^\pm=\left.\sum_{r\in R}M_{ir}J_r^\pm\right|_{W_q}.
\tag{31.23}
$$

These are maps from the whole $W_q$ into its exterior weight
$q\pm1$ space, with the zero space allowed at an endpoint.
On $U\otimes W_q$, the two signs of the boundary term have
$A$ weights $+1$ and $-1$, respectively. Their images are
orthogonal, so their sum vanishes if and only if

$$
\sum_i\alpha_i^+\otimes\beta_i^-=0,
\qquad
\sum_i\alpha_i^-\otimes\beta_i^+=0.
\tag{31.24}
$$

These are identities of maps on the entire tensor product.
The identification of tensor products of linear maps with maps
on tensor products is injective in these finite-dimensional
spaces, as is seen by using bases in their domain and range.
For either sign, eliminate the representative in each block
using the displayed relation among the $\alpha_i^\pm$.
For example the first identity becomes

$$
\sum_b\sum_{i\in A_b\setminus\{i_b\}}
 \alpha_i^+\otimes(\beta_i^--\beta_{i_b}^-)=0.
\tag{31.25}
$$

Linear independence, or application of the dual basis of the
span of the $\alpha_i^+$, says precisely that each map
$\beta_i^--\beta_{i_b}^-$ is zero. The second identity says
the same for the plus maps. Thus (31.24) is equivalent to
both exterior ladders with coefficients
$M_{i,\bullet}-M_{i',\bullet}$ annihilating $W_q$, for every
pair in a common $A_b$. Those coefficients are real, so this
is exactly membership in (31.5), proving (31.10).
The reasoning also proves the reverse implication without a
Rayleigh argument: constancy of both $\beta_i^\pm$ on a block
makes its contribution the zero map
$\sum_{i\in A_b}\alpha_i^\mp\otimes\beta_{i_b}^\pm$.
The partition belongs to $U$ alone and $M$ belongs to the
original graph alone. Neither can change when a different
minimizing exterior weight is chosen.

Finally let $d=M_{i,\bullet}-M_{i',\bullet}\in L(W_q)$.
Since $M$ is zero-one, every coordinate of $d$ belongs to
$\{-1,0,1\}$. On a block $B_h$ in (31.8), $d_r$ equals a single
coefficient times $\sigma_h(r)$; evaluating at any coordinate
of that block puts the coefficient itself in $\{-1,0,1\}$.
Disjoint supports give uniqueness and give zero outside the
active union. Every nonzero coefficient occupies the whole
block, whose size is at least two. This proves (31.11) and
the singleton exclusion. If all exterior coordinates are
active, their block weight identities add to $Z_RW_q=0$.
But $Z_RW_q=qW_q$ and $W_q\ne0$, whence $q=0$.
For $R=\varnothing$ both identities are zero and the only
feasible weight was already zero. The row-failure statement
is the contrapositive of (31.7) and (31.10), not a sufficiency
test for a ground state.

The energy step used the actual $E_s$ before any annihilation
or row equivalence was deduced. Conversely, a boundary equation
alone compares no other original spin sector or exterior weight
with a proposed energy. Thus it gives no global ground
certificate and no universal strictness outside the hypotheses
already supplying strictness in §§17–30. In particular all
component conditions (19.4) remain necessary only, and the
whole-fibre cone condition (20.2) is still used only at $S=1$.
The sufficient domains of (26.3), (29.1) and (30.2) retain their
original graph and scale hypotheses, including both alternatives
in (30.1) and the separate $\mathcal L_1=\varnothing$ endpoint.
No new sufficient class or nonsymmetric original-ground
counterexample follows from the present necessary theorem.
All conclusions use the original positive coefficient-one
operator, equal even fibres and global half filling. $\square$

## 追加锚（本行以下为增补区）

## 32. A dominating vertex in one actual neighborhood component

**定义 32.1（The class $\mathcal D$ on the original carrier）。**
Let $H$ be a finite connected simple unit-weight graph of even
order $m\geq2$. A vertex $p$ satisfies the dominating-component
condition if an actual connected component $C$ of $H[N_H(p)]$
contains a vertex $v$ adjacent to every vertex of $C\setminus\{v\}$.
The component may be a singleton. Let $\mathcal D$ consist of
exactly the graphs satisfying this condition at every vertex.
There is no condition on the other neighborhood components or
on edges from the chosen component to the exterior.

For every integer $S\geq1$, put $s=2S$ and retain

$$
\begin{aligned}
\Omega_s&=V(H)\times[2S],&
\mathcal H_{mS}&=\operatorname{span}_{\mathbb C}
 \{|T\rangle:T\subseteq\Omega_s,\ |T|=mS\},\\
K_s&=A(F_{mS}(H[\overline{K_{2S}}])),&
P_s&=\prod_iP_i,&
E_s&=\min\operatorname{spec}(K_s|_{\mathcal H_{mS}}).
\end{aligned}
\tag{32.1}
$$

Here $P_i$ is the original fibre-permutation projection.
The entries for allowed token moves in $K_s$ are positive one.
Use the actual sector minima $\mu_p(J)$ and
$\Delta_p=\mu_p(S-1)-E_s$ of Definition 31.1. All of these
minima refer to the same entire-carrier $E_s$ in (32.1).

**定理 32.2（Strict local separation at every even scale）。**
If $p$ satisfies Definition 32.1, then, for every integer $S\geq1$,

$$
\mu_p(S-1)>E_s,\qquad\Delta_p>0.
\tag{32.2}
$$

This includes the spin-zero deficiency at $S=1$, all actual
multiplicity copies and all feasible weights in the defining sector.

Proof. The representation, normalization and comparison inputs
are those of Theorems 19.2 and 31.3. Their source correspondence
is retained explicitly. The full Boolean decomposition is

$$
\mathcal H_{mS}\cong
\bigoplus_{\substack{0\leq t_i\leq S\\
 1\leq a_i\leq\binom{2S}{t_i}-\binom{2S}{t_i-1}}}
 \left(\bigotimes_i V_{S-t_i}^{(a_i)}\right)_{\sum_iZ_i=0},
\qquad \binom{2S}{-1}=0.
\tag{32.3}
$$

In each summand $J_i=S-t_i$, the original occupancy is $S+x_i$,
and

$$
\begin{aligned}
J_i^\pm|J_i,x_i\rangle
 &=\sqrt{(J_i\mp x_i)(J_i\pm x_i+1)}
       |J_i,x_i\pm1\rangle,\qquad |x_i|\leq J_i,\\
K_{\boldsymbol J}
 &=\sum_{\{i,h\}\in E(H)}
       (J_i^+J_h^-+J_i^-J_h^+).
\end{aligned}
\tag{32.4}
$$

The multiplicity count and normalized ladders are the classical
Boolean-chain facts in Srinivasan,
[Theorem 1.2 and its representation derivation](https://arxiv.org/html/1001.0280v2),
and Feinsilver,
[§3.1, (10), Proposition 4.3 and §4.2.2](https://arxiv.org/html/1102.0368v2),
consumed through the [owning volume, (6.6)–(6.12)](TOKEN_GRAPH_BLOWUP_DEFECT_DECOMPOSITION.md).
Srinivasan's parameters are Boolean rank $2S$, starting rank
$t_i$, layer $u=S+x_i$ and up operator $L_i^\ast$; his
$\sqrt{(u+1-t_i)(2S-t_i-u)}$ is exactly the raising coefficient.
Feinsilver's $T,T^\ast$ are $L_i^\ast,L_i$, his principal
number is $2J_i$, his chain index is $J_i+x_i$, and his grading
operator is $-2Z_i$. The length-one spin-zero chains and the
endpoint zero ladder coefficients remain in (32.3)–(32.4).

The full head-removal and factorial bodies and
`sector_words_card_multinomial`, `sector_gram` of
[OccupancyWordSectors](../../../D5/S3/Quantum/Entanglement/OccupancyWordSectors.lean)
and its [Scribe](../../../Blueprint/D5/S3/Quantum/Entanglement/OccupancyWordSectors.scribe.cs)
give the unit symmetric vectors with two-letter counts
$(2S-n_i,n_i)$, including zero counts. The exact finite identities
(O.2), (O.8)–(O.9) of the
[collective-oscillator volume](AURIC_COLLECTIVE_OSCILLATORS_AND_RECORD_CAPACITY.md)
have $d=m$, $N=2S$, $g=0$, $e=1$, $B=A(H)$,
$a_i=L_i/\sqrt{2S}$ and $H_{2S}=\hbar K_s/(2S)$ on the
two-letter code. No oscillator approximation is used at occupancy
$mS$, and that code calculation does not replace (32.3).

The singleton differences in
[TokenGraphLaplacianRadiusRefutation](../../../D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.lean)
and its [Scribe](../../../Blueprint/D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation.scribe.cs),
and the full `Test.move`, `Test.adj_mem`, `Test.move_injective`,
`Test.toNbr_bij`, `Test.token_energy` bodies in
[CutBoundRefutation](../../../D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.lean)
and its [Scribe](../../../Blueprint/D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation.scribe.cs)
identify exactly one removed and one inserted coordinate in each
move. Thus the two terms in (32.4) have coefficient one per
unordered edge. Apte–Parekh–Sud,
[v3, Definition 1 and Fact 2](https://arxiv.org/html/2506.03441v3),
have $N=2mS$, $k=mS$ and unit edge weights here; their shifted
operator $W(G_s)I/2-K_s$ is a different operator.
The complete `lambdaMin_quad`, `complex_real_energy`,
`complex_real_norm`, `complex_norm_pos` and
`real_complex_rayleigh` bodies give the same minimum for real
and arbitrary complex coordinates. Their fixed cut-bound
refutation and phase-product trials are not confinement premises.
These are the supplied sources at Git
`3ec6f28ef087bcfadf0336a5ca88253bd18ad8ec`.

The nonstrict local-spin comparison is the result of
Ghassemi Tabrizi–Henderson–Kühne–Scuseria,
[Appendix A4, (A34)–(A54) and the final fixed-magnetization paragraph](https://pmc.ncbi.nlm.nih.gov/articles/PMC12613319/#app1-sec4),
DOI [10.1021/acs.jctc.5c01412](https://doi.org/10.1021/acs.jctc.5c01412).
Its maximal spins are $s_i=S$, variable spins $t_i=J_i$,
magnetization $M=0$ and coupling matrices
$D_{ih}=\operatorname{diag}(2A(H)_{ih},2A(H)_{ih},0)$.
As in (19.6), the upper-spin projection has squared norm
$((J+1)^2-x^2)/((J+1)(2J+1))>0$ for every $|x|\leq J$.
Only nonincrease of the fixed-weight minimum is consumed;
strictness in (32.2) is not supplied by that comparison.

All sectors in (32.3) are actual subspaces of (32.1), so
$\Delta_p\geq0$. Suppose for contradiction that $\Delta_p=0$.
Write $j=S-1$, $A=N_H(p)$ and
$R=V(H)\setminus(\{p\}\cup A)$. Theorem 19.2 gives, for
every actual component $D$ of $H[A]$,

$$
\mathcal G_D(0)\subseteq\mathcal S_D,\qquad
 e_A(0)=\sum_D e_D(0).
\tag{32.5}
$$

In particular, every vector in each indicated ground space is
a singlet. For a singleton component this is already impossible:
its zero-weight ground space is $\mathbb C|S,0\rangle$, while
$\|J^+|S,0\rangle\|^2=S(S+1)>0$.
This handles a selected singleton, also when $m=2$.
We may therefore use a selected component $C$ with at least two
vertices and its dominating vertex $v$.

Use the exterior notation of Definition 31.2. By (31.6) there
exists an integer $q$ and a unit vector $w\in W_q$ such that

$$
|q|\leq S-1,\qquad e_R(q)=\eta,\qquad
E_s=e_A(0)+\eta.
\tag{32.6}
$$

No simplicity of any regional minimum is used. Choose any unit
$u\in\mathcal G_C(0)$ and any unit
$u_D\in\mathcal G_D(0)$ for every other component $D$.
Put $u_{\mathrm{other}}=\bigotimes_{D\ne C}u_D$ and
$e_{\mathrm{other}}=\sum_{D\ne C}e_D(0)$.
The empty product is one with energy zero. By (32.5), all these
vectors are singlets and
$e_A(0)=e_C(0)+e_{\mathrm{other}}$. Set $e=e_C(0)$.
Thus

$$
K_Cu=eu,\qquad B_C^\pm u=Z_Cu=0.
\tag{32.7}
$$

The singlet and rotation facts used next are classical
angular-momentum intermediates; the coupling and phase conventions
are those of [DLMF §§34.1–34.3](https://dlmf.nist.gov/34.1),
including [the singlet coefficient (34.3.1)](https://dlmf.nist.gov/34.3.E1).
Their needed normalization and operator consequences follow directly
as well. Since $B_C^\pm u=Z_Cu=0$, all simultaneous spin rotations
of $C$ fix $u$. Its reduced density $\rho_v$ consequently
commutes with every spin rotation at $v$. Commutation with $Z_v$
makes $\rho_v$ diagonal in the simple weight basis of $V_S$;
commutation with $J_v^+$ makes consecutive diagonal entries equal,
since all its interior raising coefficients are positive.
Its trace is one, so

$$
\rho_v=\frac{I_{V_S}}{2S+1},\qquad
c:=\langle u,Z_v^2u\rangle=\frac{S(S+1)}3>0,
\qquad
\langle Z_v\rangle_u=\langle Z_v^3\rangle_u=0.
\tag{32.8}
$$

For the second identity the three Cartesian second moments are
equal by rotations and their sum is the local Casimir $S(S+1)$.
The odd moments vanish by symmetry of the weights. This argument
allows arbitrary singlet multiplicity and complex coefficients.

Define two vectors in the actual maximal-spin tensor space on $C$:

$$
t_0=\frac{Z_vu}{\sqrt c},\qquad
 t_1=-\frac{J_v^+u}{\sqrt{2c}}.
\tag{32.9}
$$

The identity $J_v^-J_v^+=S(S+1)I-Z_v^2-Z_v$ and (32.8)
give $\|J_v^+u\|^2=2c$. Hence both vectors are unit, with
$C$ weights zero and one respectively, and are orthogonal.
Because $v$ is adjacent to every other vertex in $C$, writing
$D_0=C\setminus\{v\}$ gives the exact operator decomposition

$$
K_C=K_{D_0}+J_v^+B_{D_0}^-+J_v^-B_{D_0}^+,
\qquad B_{D_0}^\pm u=-J_v^\pm u.
\tag{32.10}
$$

There are no omitted incident edges or weights in this equality.
The spin commutation relations now give

$$
\begin{aligned}
[K_C,Z_v]u
 &=(-J_v^+B_{D_0}^-+J_v^-B_{D_0}^+)u
   =2Z_vu,\\
[K_C,J_v^+]u
 &=-2Z_vB_{D_0}^+u=2Z_vJ_v^+u.
\end{aligned}
\tag{32.11}
$$

It follows that $K_Ct_0=(e+2)t_0$.
For the other vector, the scalar marginal (32.8) and cyclicity
of finite trace give

$$
\begin{aligned}
\langle J_v^+u,Z_vJ_v^+u\rangle
 &=\frac{\operatorname{tr}(J_v^-Z_vJ_v^+)}{2S+1}
 =\frac{\operatorname{tr}(Z_vJ_v^+J_v^-)}{2S+1}\\
 &=\frac{\operatorname{tr}
   (Z_v(S(S+1)I-Z_v^2+Z_v))}{2S+1}=c.
\end{aligned}
\tag{32.12}
$$

Using (32.11) and $\|J_v^+u\|^2=2c$, this proves

$$
\langle t_0,K_Ct_0\rangle=e+2,\qquad
 \langle t_1,K_Ct_1\rangle=e+1.
\tag{32.13}
$$

Only the second expectation is needed; no eigenvector assertion
for $t_1$ is being made. The collective ladder relations are

$$
B_C^+t_0=\sqrt2\,t_1,\qquad
 B_C^-t_1=\sqrt2\,t_0.
\tag{32.14}
$$

Indeed $[B_C^+,Z_v]=-J_v^+$ and
$[B_C^-,J_v^+]=-2Z_v$, and $B_C^\pm u=0$.
These are the usual spin-one matrix elements obtained by applying
a local vector operator to a singlet; (32.8)–(32.14) derive
exactly the pieces needed here, without a new representation
assumption or a restriction on the remaining spin copies.

Choose the actual spin-$S$ fibre at $p$ and set

$$
\begin{aligned}
f_0&=|S,-q\rangle_p\otimes t_0
             \otimes u_{\mathrm{other}}\otimes w,\\
f_1&=|S,-q-1\rangle_p\otimes t_1
             \otimes u_{\mathrm{other}}\otimes w,\\
a&=\sqrt{2(S-q)(S+q+1)}.
\end{aligned}
\tag{32.15}
$$

Both magnetic weights at $p$ are feasible because
$-S+1\leq q\leq S-1$. The vectors are orthonormal and have
total weight zero. Thus they are actual vectors of (32.1),
with occupancies $S+x_i$ throughout, including any occurring
endpoint. In particular the second vector is legal at $S=1$,
$q=0$: its $p$ weight is $-1$ and its $C$ weight is $1$.

We compute the compression of the whole $K_s$ to their span.
On the $p,C$ factors the only added interaction is
$J_p^+B_C^-+J_p^-B_C^+$. Equations (32.4) and (32.14)
give its off-diagonal entry $a$, with positive sign and no
factor suppressed. Its diagonal entries vanish by weight.
The internal $C$ entries are (32.13); the other components
and $R$ contribute the common scalar
$e_{\mathrm{other}}+\eta$.

For completeness, all other edges have zero compressed matrix
elements. No edge joins $C$ to another component of $H[A]$,
and there are no $p$–$R$ edges. For every $r\in R$,
$\langle w,J_r^\pm w\rangle=0$ because $w$ has definite
$R$ weight $q$. Every $A$–$R$ edge therefore has zero
matrix element between either pair $f_i,f_h$: its exterior
factor is this same zero expectation, irrespective of the
matrix element on $C$. Edges from $p$ to the other components
annihilate their singlets by the summed ladders; their
individual one-site ladder expectations also vanish.
This lists every edge of $H$, and uses product vectors only
as legal variational trials, not as an assumption about an
original minimizing vector. Consequently

$$
\left(\langle f_i,K_sf_h\rangle\right)_{i,h=0,1}
 =E_sI_2+\begin{pmatrix}2&a\\a&1\end{pmatrix}.
\tag{32.16}
$$

No regional slice is claimed to reduce the coupled operator.
In particular leakage of $K_Ct_1$ out of this trial span is
irrelevant to its Rayleigh quotient.

Since $S-q\geq1$ and $S+q+1\geq2$, one has $a^2\geq4>2$.
The actual normalized whole-carrier vector

$$
\Phi=\frac{f_0-af_1}{\sqrt{1+a^2}}
\tag{32.17}
$$

therefore satisfies

$$
\langle\Phi,K_s\Phi\rangle
 =E_s+\frac{2-a^2}{1+a^2}<E_s.
\tag{32.18}
$$

This contradicts the definition of the entire-carrier minimum.
Thus equality $\Delta_p=0$ is impossible and (32.2) follows.
If $R=\varnothing$, the only exterior weight in (32.6) is zero,
$w=1$ and $\eta=0$; the same computation applies. Disconnected
neighborhoods enter only through their actual component factors.
Degenerate minima require no chosen basis or real-vector
restriction. The new inference is the dominating-vertex
commutator calculation and its insertion at the actual $E_s$
into the two-vector comparison (32.16)–(32.18); the Boolean
representation, singlet algebra, nonstrict spin comparison and
finite-dimensional variational principle are attributed
intermediates. Neither (19.4) nor (31.7) has been used conversely.
$\square$

**推论 32.3（Every-ground confinement on $\mathcal D$）。**
For every $H\in\mathcal D$ and integer $S\geq1$,

$$
\ker(K_s-E_sI)\subseteq\operatorname{ran}P_s.
\tag{32.19}
$$

With $\mathcal N_s=\ker P_s\subseteq\mathcal H_{mS}$, put
$g_s=\min\operatorname{spec}(K_s|_{\mathcal N_s})-E_s$.
Then $g_s>0$ and

$$
K_s-E_sI\succeq g_s(I-P_s),\qquad
\|(I-P_s)\phi\|^2\leq\frac{\delta}{g_s}
\tag{32.20}
$$

for every unit complex $\phi$ with
$\langle\phi,K_s\phi\rangle\leq E_s+\delta$, $\delta\geq0$.
No value or scale-uniform estimate of $g_s$ is asserted.

Proof. By the exact reduction in Definition 31.1 and its proof,
$g_s=\min_p\Delta_p$. Explicitly, any deficient summand in
(32.3) has some $J_p\leq S-1$. Increase this spin to $S-1$
and all other spins to $S$ using the supplied nonstrict
fixed-zero-weight comparison. Its minimum is at least
$\mu_p(S-1)$. Conversely each of the latter sectors is an
actual deficient summand, so the two minima agree.
Theorem 32.2 makes each of the finitely many $\Delta_p$
strictly positive.

The space $\mathcal N_s$ is nonzero: take a nonconstant
one-particle vector in one original fibre, an occupancy-$(2S-1)$
vector in a second fibre and occupancy-$S$ vectors in the other
fibres. Their tensor has occupancy $mS$ and is killed by $P_s$.
This construction includes $m=2,S=1$.
The operator $K_s$ commutes with each fibre permutation,
hence with $P_s$; both projection ranges reduce it.
Its form is at least $E_s$ on the symmetric range and at
least $E_s+g_s$ on $\mathcal N_s$. Adding these reducing
forms gives the operator inequality and then its expectation
bound. A ground vector has zero expectation on the left and
therefore no nonsymmetric component. Equivalently, decomposing
any complex ground vector into (32.3) cannot leave a nonzero
deficient component. Orthogonal sums across weights, sectors
and multiplicities, and all entanglement within them, are
included in this argument. $\square$

## 33. An infinite family outside the entire multipartite union

**定义 33.1（The graphs $Y_n$）。** For each integer $n\geq1$,
let $Q$ have $r=2n+1$ vertices and take five further distinct
vertices $u,v,z,\ell_1,\ell_2$. Make $Q\sqcup\{u,v\}$
a clique. Add exactly the four edges
$uz,vz,u\ell_1,u\ell_2$, and no other edges. All edge weights
are one. In particular $z$ has precisely the two neighbors
$u,v$, and each $\ell_i$ is a leaf at $u$.

**命题 33.2（All-scale confinement and exclusion of every old class）。**
The graphs $Y_n$ form an infinite family of connected interacting
simple graphs of even order $m=2n+6$. For every $n\geq1$,

$$
Y_n\in\mathcal D,\qquad
Y_n\notin\mathcal U_s^{\rm mp}quad\text{for every }s=2S\geq2.
\tag{33.1}
$$

All conclusions (32.19)–(32.20) consequently hold on their
original entire complex occupancy-$(2n+6)S$ carriers.

Proof. The clique has $r+2$ vertices and all its vertices
interact in the same connected component. The vertex $z$ is
attached to two clique vertices and the leaves to one.
Thus the graph is simple and connected, has $r+5=2n+6$
vertices and $\binom{r+2}{2}+4$ edges, and has no disconnected
spectator factors. The orders increase strictly with $n$.
Its complete induced open neighborhoods are

$$
\begin{aligned}
Y_n[N(u)]
 &=\bigl(K_{r+1}[Q\sqcup\{v\}]\text{ with a leaf }z
                      \text{ at }v\bigr)
               \sqcup\{\ell_1\}\sqcup\{\ell_2\},\\
Y_n[N(v)]
 &=K_{r+1}[Q\sqcup\{u\}]\text{ with a leaf }z
                      \text{ at }u,\\
Y_n[N(x)]&=K_{r+1}[(Q\setminus\{x\})\sqcup\{u,v\}]
                                      &&(x\in Q),\\
Y_n[N(z)]&=K_2[\{u,v\}],&
Y_n[N(\ell_i)]&=\{u\}\quad(i=1,2).
\end{aligned}
\tag{33.2}
$$

Every vertex and edge of every neighborhood is listed. The
nontrivial component at $u$ has dominating vertex $v$; the
component at $v$ has dominating vertex $u$. The clique
neighborhoods and $K_2$ have dominating vertices, and the
singleton neighborhoods qualify as well. This proves membership
in $\mathcal D$ using actual components.

Write $T=Y_n[N(v)]$. This neighborhood is connected, so it
has no alternative component for any component-based condition.
It contains a triangle in its clique, and therefore is not
bipartite. Its vertex $u$ has degree $r+1\geq4$, so $T$ is
not a simple odd cycle. Its order is $r+2\geq5$, so it is
not a diamond or singleton. Finally choose distinct
$x,y\in Q$. In $T$, the vertex $z$ is nonadjacent to both
$x,y$ while $xy$ is an edge. In a complete multipartite graph,
nonadjacency of distinct vertices means membership in a common
independent part. The indicated three relations are impossible.
Thus $T$ is not complete multipartite. Its sole component
excludes $Y_n$ from each of
$\mathcal C$, $\mathcal C_\diamond$ and $\mathcal C_{\rm mp}$.

This same $T$ excludes the entire-neighborhood class
$\mathcal L$. Its vertices $z,u,x$, for any $x\in Q$,
induce the path $z-u-x$. The vector equal to $1,-1,1$
on these three vertices and zero elsewhere has squared norm
$3$ and adjacency quadratic form $-4$. Hence

$$
\lambda_{\min}(A(T))\leq-\frac43<-1.
\tag{33.3}
$$

If a complex least eigenvector $b$ of $T$ had $|b_i|=1$
at every coordinate, its equation at the leaf $z$ would be
$\lambda_{\min}(A(T))b_z=b_u$. Absolute values would imply
$|\lambda_{\min}(A(T))|=1$, contrary to (33.3).
The nonbipartite $T$ therefore has no flat complex least mode.
This excludes $\mathcal L_S$ for every $S\geq2$;
$\mathcal L_1=\varnothing$ is already empty.

The global flatness hypothesis fails separately. The vertices
$\ell_1,u,z$ induce a path, so the same vector with entries
$1,-1,1$ gives

$$
\lambda_{\min}(A(Y_n))\leq-\frac43<-1.
\tag{33.4}
$$

At the global leaf $\ell_1$, any modulus-one complex
eigenvector for this least eigenvalue would force its absolute
value to be one. This contradicts (33.4). Thus $Y_n$ fails
the actual global complex-flat least-mode requirement of
$\mathcal F_s$ independently of scale. It is excluded before
either of the two positive-gap alternatives in Definition
30.1 is considered, so neither alternative restores membership.

The whole graph is not complete multipartite either: the leaf
$\ell_1$ is nonadjacent to $v$ and to $x\in Q$, whereas
$vx$ is an edge. The same independent-part argument excludes
all of $\mathcal M$, including every balanced or dominant-part
regime and every allowed number of parts.

To exclude $\mathcal B$, let $B=Q\sqcup\{u,v,z\}$.
The induced graph on $B$ is two-connected: deleting $u$ leaves
$z$ attached to $v$ and a connected clique; deleting $v$ is
the symmetric assertion; deleting $z$ leaves the clique;
deleting a vertex of $Q$ leaves that clique connected and
$z$ attached to both $u,v$. These exhaust all possible deletions,
and $|B|\geq5$. A leaf cannot lie in any two-connected
enlargement of $B$, so this is a maximal two-connected block
of $Y_n$. It is not a clique because $zx$ is absent for
$x\in Q$. Hence $Y_n$ is not a block graph.

These arguments exclude every term of (30.2), with their exact
graph and scale hypotheses, and prove (33.1). Theorem 32.2
and Corollary 32.3 now give the original-model conclusions
at every integer $S\geq1$. The use of zero-extended adjacency
vectors in (33.3)–(33.4) is a direct finite-dimensional Rayleigh
comparison; it makes no claim that the path is an actual
neighborhood component or that a regional energy is $E_s$.
$\square$

## 34. The extended union at each exact scale

**定义 34.1（The preserved union with dominating components）。**
In the common domain of Definition 32.1, retain every set in
Definition 30.1 unchanged and put

$$
\begin{aligned}
\mathcal V_s
 &=\mathcal U_s^{\rm mp}\cup\mathcal D\\
 &=\mathcal M\cup\mathcal B\cup\mathcal C\cup\mathcal L_S
   \cup\mathcal F_s\cup\mathcal C_\diamond
   \cup\mathcal C_{\rm mp}\cup\mathcal D,
\qquad s=2S,\ S\geq1.
\end{aligned}
\tag{34.1}
$$

In particular $\mathcal M$ still contains all complete
multipartite graphs with at least two nonempty parts, including
all part-size regimes. The endpoint is still
$\mathcal L_1=\varnothing$ and $\mathcal L_S=\mathcal L$
for $S\geq2$. The set $\mathcal F_s$ still requires a global
least adjacency eigenvector with every complex coordinate
of modulus one. With
$\ell=-\lambda_{\min}(A(H))$, $\Delta=\max_i\deg_H(i)$,
$T=m+2$ and
$s_H=2\lceil2^{18}(\Delta/\ell)^2T^3\rceil$,
its scale requirement is still either $s\geq s_H$, or both

$$
s\geq4T,\qquad
\ell s-64\Delta T^{3/2}\sqrt{s/2}-64\Delta T^2>0.
\tag{34.2}
$$

None of these sets is intersected with $\mathcal D$.

**定理 34.2（Strict extension of the entire prior union）。**
For every integer $S\geq1$, every graph $H\in\mathcal V_s$
has every original $E_s$-ground vector in $\operatorname{ran}P_s$,
and has the qualitative same-minimum inequalities (32.20).
At each such scale,

$$
\mathcal U_s^{\rm mp}\subsetneq\mathcal V_s,
\qquad
\{Y_n:n\geq1\}\subseteq
       \mathcal V_s\setminus\mathcal U_s^{\rm mp}.
\tag{34.3}
$$

Proof. Theorem 30.2 gives the conclusions on the entire
$\mathcal U_s^{\rm mp}$ with exactly its hypotheses and
endpoints. Corollary 32.3 gives them on $\mathcal D$ at
the same original minimum, so they hold on their union.
Proposition 33.2 supplies infinitely many connected interacting
graphs in the difference for every scale and proves strictness.
In particular, no previous sufficient theorem, example,
counterexample, exceptional local minimum or scale alternative
is removed or strengthened by (34.1).

The additional mathematical inference is (32.11)–(32.18):
the dominating vertex turns a component singlet ground vector
into normalized weight-zero and weight-one trials with energy
increments two and one, whose coupling to the actual spin-$S$
fibre at $p$ has a negative direction at every exterior weight
$|q|\leq S-1$. Equation (32.6), supplied by actual deficient
attainment, places that direction strictly below the same
whole-carrier $E_s$. The family (33.2) then separates this
sufficient condition from every part of (30.2).
The representation, singlet rotations, nonstrict comparison and
finite spectral principles remain their classical or supplied
intermediate results. This is an inference from those stated
inputs, with no assertion of literature priority.

For a connected even-order $H\notin\mathcal V_s$,
every-ground confinement at that scale remains unresolved here.
The all-even question retains (34.1) separately for every
$S\geq1$; a scale-dependent old hypothesis is not promoted
to an all-scale graph hypothesis. The joint equality and
incidence conditions of Theorem 31.3 and the component and
spin-one cone conditions of §§19–20 remain necessary conditions,
not converses. The strict local result provides neither an
actual nonsymmetric original-ground counterexample outside
(34.1) nor a general solution for arbitrary $H$.
All statements use simple unit-weight graphs, equal even fibres,
positive coefficient-one adjacency and only global half filling
on the entire complex carrier. They impose no product-state
restriction on ground vectors and supply no numerical or
scale-uniform global gap, other-weight or other-filling
extension, or physical-realization conclusion. $\square$

## 追加锚（本行以下为增补区）
