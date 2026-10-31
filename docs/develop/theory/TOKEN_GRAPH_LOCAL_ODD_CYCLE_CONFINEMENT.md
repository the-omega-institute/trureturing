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
