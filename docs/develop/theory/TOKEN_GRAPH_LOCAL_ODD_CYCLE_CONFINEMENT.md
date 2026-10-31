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
