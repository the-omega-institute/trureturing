# Nonconstant extremal words for quantum Černý complexity

## 1. Instances and word actions

**Definition 1.1 (Quantum Černý complexity).** Let $d$ be any positive integer and let
$\mathcal D_d$ be the set of positive semidefinite matrices in $M_d(\mathbb C)$
with trace one. An instance consists of two completely positive,
trace-preserving complex-linear maps
$A_0,A_1:M_d(\mathbb C)\longrightarrow M_d(\mathbb C)$ and a state
$\rho_0\in\mathcal D_d$. For $u=u_1\cdots u_k\in\{0,1\}^*$ put

$$
A_u=A_{u_k}\circ\cdots\circ A_{u_1},\qquad
A_{\varepsilon}=\operatorname{id},\qquad
R=\{A_u(\rho_0):u\in\{0,1\}^*\}.
$$

A word $w$ synchronizes this instance if there is a state
$\rho_1\in\mathcal D_d$ such that $A_w(\rho)=\rho_1$ for every $\rho\in R$.
It is the unique shortest synchronizing word if it synchronizes and every
$u\ne w$ with $|u|\le |w|$ fails to synchronize the same instance.
For nonempty $w$, $\operatorname{qc}(w)$ is the least positive dimension of
such an instance. The existence of a realizing dimension follows from the
construction in the proof of Theorem 2.1 below. These are the definitions of
[Lee, Lee and Kjos-Hanssen, *Quantum Černý complexity of binary words*,
arXiv:2609.40154v1, Definition 1.1](https://arxiv.org/html/2609.40154v1).

**Definition 1.2 (Extremal words).** For $m\ge1$ write

$$
Q_m=\max\{\operatorname{qc}(u):u\in\{0,1\}^m\},\qquad
\mathcal E_m=\{u\in\{0,1\}^m:\operatorname{qc}(u)=Q_m\}.
$$

The assertion in
[Lee, Lee and Kjos-Hanssen, Section 6, item 4](https://arxiv.org/html/2609.40154v1)
is that there exists an integer $M\ge1$ such that
$\mathcal E_m=\{0^m,1^m\}$ for every integer $m\ge M$.

## 2. Nonconstant maximizers at every length at least two

**Theorem 2.1.** For every integer $m\ge2$,

$$
\operatorname{qc}(0^{m-1}1)
=\operatorname{qc}(1^{m-1}0)
=\operatorname{qc}(0^m)
=\operatorname{qc}(1^m)
=Q_m
=\left\lceil\sqrt{m+1}\right\rceil.
$$

Consequently,

$$
\{0^m,1^m,0^{m-1}1,1^{m-1}0\}\subseteq\mathcal E_m
\qquad(m\ge2),
$$

and the eventual assertion in Definition 1.2 is false.

**Proof.** First record within this proof the linearization of
[Lee, Lee and Kjos-Hanssen, Proposition 2.1](https://arxiv.org/html/2609.40154v1).
For an arbitrary instance let

$$
H_d=\{X\in M_d(\mathbb C):X=X^*,\ \operatorname{tr}X=0\},\qquad
V=\operatorname{span}_{\mathbb R}\{\rho-\sigma:\rho,\sigma\in R\}.
$$

The real dimension of $H_d$ is $d^2-1$: a Hermitian matrix has $d$ real
diagonal entries and two real coordinates for each of the $d(d-1)/2$
off-diagonal pairs, and trace zero imposes one independent real equation.
Thus $n:=\dim_{\mathbb R}V\le d^2-1$.
Each channel preserves Hermitian matrices and trace. Moreover
$A_a(R)\subseteq R$, since $A_a(A_u(\rho_0))=A_{ua}(\rho_0)$.
Complex linearity therefore gives real-linear endomorphisms
$L_a=A_a|_V$ of this same $V$. For
$L_u=L_{u_k}\cdots L_{u_1}$, with $L_\varepsilon=\operatorname{id}_V$,

$$
A_u(\rho)-A_u(\sigma)=L_u(\rho-\sigma)\qquad(\rho,\sigma\in R).
$$

It follows in both directions that $u$ synchronizes if and only if
$L_u=0$ on $V$. In the reverse direction the common output is
$A_u(\rho_0)$, which is a density matrix and uses the start state of this
instance.

Now suppose $0^{m-1}1$ is the unique shortest synchronizing word of this
arbitrary instance, and put $S=L_0$ and $T=L_1$. The synchronizing word,
the shorter word $0^{m-2}1$, and the distinct word $0^m$ give, respectively,

$$
TS^{m-1}=0,\qquad TS^{m-2}\ne0,\qquad S^m\ne0.
$$

All three statements concern endomorphisms of the single space $V$ just
defined. Put $W_j=S^j(V)$ for $j\ge0$. Then
$W_{j+1}\subseteq W_j$ and $W_{j+1}=S(W_j)$.
The first two displayed relations imply that $T$ vanishes on $W_{m-1}$
but does not vanish on $W_{m-2}$, so
$W_{m-1}\subsetneq W_{m-2}$.
If $W_j=W_{j+1}$ held for some $0\le j\le m-2$, applying $S$ repeatedly
would give $W_{m-2}=W_{m-1}$. Hence every inclusion in

$$
V=W_0\supsetneq W_1\supsetneq\cdots\supsetneq W_{m-1}
$$

is strict. Also $S^m\ne0$ implies $W_m\ne\{0\}$, and thus
$W_{m-1}\ne\{0\}$. Counting these $m-1$ strict decreases above a nonzero
space yields

$$
m\le\dim_{\mathbb R}V\le d^2-1.
$$

Every realizing positive integer $d$ therefore satisfies
$d\ge\lceil\sqrt{m+1}\rceil$. This proves the required lower bound for
$0^{m-1}1$. At $m=2$ the shorter comparison word is $1$, and the same
argument has exactly one strict inclusion and a nonzero final space.

For completeness the constant-word lower bound is the nilpotency argument
of [Lee, Lee and Kjos-Hanssen, Theorem 3.1](https://arxiv.org/html/2609.40154v1).
If $0^m$ is uniquely shortest, then $S^m=0$ and $S^{m-1}\ne0$ on $V$.
Choose $x\in V$ with $S^{m-1}x\ne0$.
The vectors $x,Sx,\ldots,S^{m-1}x$ are independent: in any nonzero linear
relation choose its least index $j$ with nonzero coefficient and apply
$S^{m-1-j}$; all higher-index terms vanish and the remaining term is a
nonzero multiple of $S^{m-1}x$. Again $m\le\dim V\le d^2-1$.

We next use the general upper-bound construction of
[Lee, Lee and Kjos-Hanssen, Lemma 2.3 and Theorem 2.4](https://arxiv.org/html/2609.40154v1),
giving its realization on the full complex matrix algebra explicitly.
Fix any word $w$ of length $m\ge1$, and let
$d=\lceil\sqrt{m+1}\rceil$, so that $m\le d^2-1$.
Let $p_q$ denote the prefix of $w$ of length $q$, for $0\le q\le m$.
Use states $0,\ldots,m$, with $m$ absorbing. For $q<m$, define
$\delta_a(q)=m$ if $p_q a$ contains $w$ as a contiguous factor; otherwise
let $\delta_a(q)$ be the largest $r<m$ such that $p_r$ is a suffix of
$p_q a$. Extend the transitions to words in left-to-right order, and set
$\delta_a(m)=m$.

These transitions have the property

$$
\delta_v(q)=m
\quad\Longleftrightarrow\quad
p_qv\text{ contains }w\text{ as a factor}.
$$

Indeed, before an occurrence, maintain the longest prefix $p_r$ of $w$
that is a suffix of the input already read. Every other prefix of $w$
that is a suffix of that input has length at most $r$, and is a suffix
of $p_r$; conversely every prefix of $w$ that is a suffix of $p_r$ is a
suffix of that input. After a new letter $a$, a nonempty prefix $p_s$
is a suffix exactly when its last letter is $a$ and $p_{s-1}$ was a
suffix before that letter. This also detects a newly completed
occurrence by taking $s=m$. Thus the specified transition retains all
required suffix information, and induction proves the displayed
property, including the absorbing case. In particular,
$\delta_w(q)=m$ for every $q$, and
$\delta_v(0)=m$ precisely when $v$ contains $w$.

Choose real-linearly independent $g_0,\ldots,g_{m-1}\in H_d$ and put
$g_m=0$. Define real-linear maps $F_a:H_d\longrightarrow H_d$ by

$$
F_a(g_q)=g_{\delta_a(q)}\quad(0\le q<m),
$$

and by zero on a chosen linear complement of their span.
Consequently $F_v(g_q)=g_{\delta_v(q)}$ for every word $v$ and every
$q\in\{0,\ldots,m\}$. This is the prefix-automaton realization of
Theorem 2.4 of the cited paper.

Write $\tau=I_d/d$. Every traceless complex matrix has a unique expression
$H+iK$ with $H,K\in H_d$, obtained from its Hermitian and skew-Hermitian
parts. The extension
$\widetilde F_a(H+iK)=F_a(H)+iF_a(K)$ is complex-linear, preserves the
adjoint, and has traceless values. For a real parameter $t>0$ define
on all of $M_d(\mathbb C)$

$$
\Phi_a(X)=\operatorname{tr}(X)\tau+
 t\widetilde F_a\bigl(X-\operatorname{tr}(X)\tau\bigr).
$$

This is complex-linear, trace-preserving and adjoint-preserving.
To verify complete positivity, use the unnormalized Choi matrix

$$
J(\Phi_a)=\sum_{i,j=1}^d E_{ij}\otimes\Phi_a(E_{ij})
=\frac{1}{d}I_{d^2}+tC_a,
$$

where

$$
C_a=\sum_{i,j=1}^d E_{ij}\otimes
 \widetilde F_a\bigl(E_{ij}-\delta_{ij}\tau\bigr)
$$

is Hermitian. The unnormalized convention here gives $I_{d^2}/d$ for
the completely depolarizing map; the normalized convention gives
$I_{d^2}/d^2$. Choose

$$
0<t<\frac{1}{d(1+\|C_0\|_{\mathrm{op}}+\|C_1\|_{\mathrm{op}})}.
$$

For either letter,
$J(\Phi_a)\succeq(1/d-t\|C_a\|_{\mathrm{op}})I_{d^2}\succ0$.
Here the Choi implication can be seen directly: factor a positive Choi
matrix as $\sum_\ell v_\ell v_\ell^*$ and reshape each vector by
$(K_\ell)_{\alpha i}=(v_\ell)_{(i,\alpha)}$. Comparing the
$(i,\alpha),(j,\beta)$ entries gives
$\Phi_a(E_{ij})=\sum_\ell K_\ell E_{ij}K_\ell^*$, hence
$\Phi_a(X)=\sum_\ell K_\ell X K_\ell^*$ for all $X$.
For every positive integer $k$, its amplification sends a positive
matrix $Y$ to
$\sum_\ell(I_k\otimes K_\ell)Y(I_k\otimes K_\ell)^*\succeq0$.
Thus $\Phi_a$ is completely positive. Together with trace preservation
this gives two actual channels. This is the depolarizing perturbation
of the cited Lemma 2.3; the complex extension and unnormalized Choi
convention are also given in the authors'
[Complexification.lean](https://github.com/bjoernkjoshanssen/quantumcerny/blob/6690d5a19c3927be2625e0ec9d1f86ee2801cfb0/RequestProject/Complexification.lean),
[Choi.lean](https://github.com/bjoernkjoshanssen/quantumcerny/blob/6690d5a19c3927be2625e0ec9d1f86ee2801cfb0/RequestProject/Choi.lean)
and
[Depolarizing.lean](https://github.com/bjoernkjoshanssen/quantumcerny/blob/6690d5a19c3927be2625e0ec9d1f86ee2801cfb0/RequestProject/Depolarizing.lean).

Choose
$0<\eta<1/[d(1+\|g_0\|_{\mathrm{op}})]$ and set
$\rho_0=\tau+\eta g_0$. This is positive definite and has trace one.
For $x\in H_d$ and $c\in\mathbb R$,

$$
\Phi_a(\tau+cx)=\tau+tcF_a(x).
$$

Induction on $|u|$ gives the exact orbit formula for this pair of
channels and this start state:

$$
\Phi_u(\rho_0)=\tau+\eta t^{|u|}g_{\delta_u(0)}.
$$

In particular $\tau=\Phi_w(\rho_0)$ belongs to their reachable set
$R$, and both channels fix $\tau$.
If $v$ synchronizes on $R$, its common output must be $\tau$ because
$\tau\in R$. Evaluating also at $\rho_0\in R$ gives
$\eta t^{|v|}g_{\delta_v(0)}=0$.
Since $\eta t^{|v|}>0$ and $g_q\ne0$ for $q<m$, this implies
$\delta_v(0)=m$, so $v$ contains $w$.
Conversely, if $v$ contains $w$, then $\delta_v(q)=m$ for every $q$.
Applying the orbit formula first to $u$ and then to $v$ yields

$$
\Phi_v(\Phi_u(\rho_0))
=\tau+\eta t^{|u|+|v|}g_{\delta_v(\delta_u(0))}
=\tau
\qquad(u\in\{0,1\}^*).
$$

Thus $v$ synchronizes exactly when it contains $w$. The only such word
of length at most $m$ is $w$ itself. This proves existence and

$$
\operatorname{qc}(w)\le\left\lceil\sqrt{m+1}\right\rceil
\qquad(w\in\{0,1\}^m,\ m\ge1).
$$

Combining this upper bound with the two lower bounds proves the asserted
values for $0^{m-1}1$ and $0^m$ and their equality to $Q_m$.
Exchanging the labels of the two channels preserves the reachable set:
the set of all words is carried bijectively to itself by complementation.
It preserves all word lengths and the unique shortest property.
Therefore $\operatorname{qc}(\overline w)=\operatorname{qc}(w)$,
giving the stated values for $1^{m-1}0$ and $1^m$.

Finally, let any integer $M\ge1$ be given and take
$m=\max\{M,2\}$. The word $0^{m-1}1$ has length $m$, contains both
letters, and belongs to $\mathcal E_m$. Hence
$\mathcal E_m\ne\{0^m,1^m\}$ at this $m\ge M$.
As this applies to every $M$, no eventual threshold exists.
At the remaining endpoint $m=1$, the general upper bound gives dimension
two, while dimension one has only the state $[1]$, making the empty word
synchronize every instance. Thus $\operatorname{qc}(0)=\operatorname{qc}(1)=2$
and $\mathcal E_1=\{0,1\}$. $\square$

## 追加锚（本行以下为增补区）
