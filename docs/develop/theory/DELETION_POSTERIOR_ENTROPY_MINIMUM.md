# The finite binary deletion-posterior entropy minimum

## 1. Joint law and entropy

**Definition 1.1 (labelled deletion law).** Let $n,m$ be integers with
$0\le m\le n$, put $[n]=\{1,\ldots,n\}$ and $[0]=\varnothing$, and let
$\Sigma_\ell=\{0,1\}^{\ell}$. The set $\Sigma_0$ consists of the empty word.
Write $\mathcal S_{n,m}$ for the set of all labelled $m$-element subsets
of $[n]$, and put $C=\binom nm$ and $d=n-m$. Let $Y$ be uniform on
$\Sigma_n$, and let $S$ be independent of $Y$ and uniform on
$\mathcal S_{n,m}$. If $s=\{s_1<\cdots<s_m\}$, set
$y|_s=(y_{s_1},\ldots,y_{s_m})$, and define $X=Y|_S$.
Different subsets remain different masks even when they produce the same word.

For $x\in\Sigma_m$, write $p_x(y)=\Pr(Y=y\mid X=x)$ and
$H_{n,m}(x)=H(Y\mid X=x)$, where Shannon entropy is measured in bits:

$$
H_{n,m}(x)=-\sum_{y\in\Sigma_n}p_x(y)\log_2 p_x(y),
\qquad 0\log_2 0=0.
$$

The sum includes all words, including those of posterior probability zero.
The notation $0^m,1^m$ denotes the constant words; they coincide when $m=0$.
This is the uniform-prior, uniform-mask law of Atashpendar, Roscoe and Ryan,
[*Information Leakage due to Revealing Randomly Selected Bits*,
institutional author preprint](https://orbilu.uni.lu/bitstream/10993/21251/1/information_leakage_due_to_revealing_randomly_selected_bits_preprint.pdf),
Section 2, with its $k$ equal to $m$.

**Definition 1.2 (embedding multiplicity).** For $x\in\Sigma_m$ and
$y\in\Sigma_n$, define

$$
\omega_x(y)=\#\{s\in\mathcal S_{n,m}:y|_s=x\}.
$$

In particular, $\omega_{\varnothing}(y)=1$. This counts increasing index
embeddings with multiplicity, as in Section III of Atashpendar, Beunardeau,
Connolly, Géraud, Mestel, Roscoe and Ryan,
[*From Clustering Supersequences to Entropy Minimizing Subsequences for
Single and Double Deletions*, arXiv:1802.00703v2](https://arxiv.org/pdf/1802.00703v2).

## 2. Complete finite minimum and equality

**Theorem 2.1 (minimum and all equality cases).** Under Definition 1.1,
for every pair $0\le m\le n$ and every $x\in\Sigma_m$,

$$
H_{n,m}(x)\ge H_{n,m}(0^m)=H_{n,m}(1^m).
$$

If $1\le m<n$, equality holds if and only if $x$ is constant.
If $m=n$, then $H_{n,n}(x)=0$ for every $x$.
If $m=0$, the unique empty observation has entropy $H_{n,0}(\varnothing)=n$,
including $H_{0,0}(\varnothing)=0$. The minimum has the exact value

$$
H_{n,m}(0^m)
=d+\log_2\binom nm
-2^{-d}\sum_{j=0}^{d}\binom dj\log_2\binom{m+j}{m}.
\tag{2.1}
$$

The inequality is an application of classical spin alignment:
Alhejji and Knill,
[*Towards a Resolution of the Spin Alignment Problem*,
arXiv:2307.06894v3](https://arxiv.org/pdf/2307.06894v3),
Proposition IV.5 and its proof, pp. 19–21. The correspondence is local
dimension $2$, $n$ sites, $Q=I_2/2$,
$\mu_s=C^{-1}$ for $s\in\mathcal S_{n,m}$ and $\mu_s=0$ otherwise,
and the pure classical state on $s$ specified by the increasing word $x$.
Either binary basis vector may be the distinguished eigenvector of $Q$.
The proof below specializes that coordinate-alignment argument and supplies
the compatible-mask strictness argument needed for the equality classification.

The one- and two-deletion minimum cases are contained in
Atashpendar et al., arXiv:1802.00703v2, Section V.
For positive observed length in these cases, Singhvi, Sabary, Bar-Lev and Yaakobi,
[*Conditional Entropies of $k$-Deletion/Insertion Channels*,
arXiv:2407.10026v2](https://arxiv.org/pdf/2407.10026v2),
Theorems 6 and 9, give the single-run minimizers under uniform transmission;
their Remark 4 specifies the corrected two-deletion embedding characterization.
Their arbitrary-$k$ input-entropy theorem for insertion channels concerns a
different posterior direction. Atashpendar, Mestel, Roscoe and Ryan,
[*A Proof of Entropy Minimization for Outputs in Deletion Channels via
Hidden Word Statistics*, arXiv:1807.11609v1](https://arxiv.org/pdf/1807.11609v1),
Theorem IV.6, gives the minimum and constant-only equality for each fixed $m$
and sufficiently large $n$. These special-case and asymptotic results are not
premises for the finite proof.

*Proof.* For each fixed $s$, its $m$ selected fair bits have distribution
uniform on $\Sigma_m$. Consequently,

$$
\Pr(X=x\mid S=s)=2^{-m},\qquad
\Pr(X=x)=2^{-m},\qquad
\Pr(S=s\mid X=x)=C^{-1}.
\tag{2.2}
$$

Given $S=s$ and $X=x$, the bits at $s$ equal $x$ in increasing order;
the remaining $d$ bits are independent fair bits. Thus every observation
has positive probability and

$$
p_x(y)=\frac{\omega_x(y)}{C2^d},
\qquad
\sum_{y\in\Sigma_n}\omega_x(y)=C2^d.
\tag{2.3}
$$

If $m=0$, the observation imposes no constraint, so the posterior is uniform
on $\Sigma_n$ and has entropy $n$. If $m=n$, the only mask is $[n]$ and
$X=Y$, so each posterior is a point mass and has entropy zero. This also
handles $(n,m)=(0,0)$. For the comparison and its strictness, assume now
$1\le m<n$.

Within the coordinate-alignment proof, allow an auxiliary assignment
$a_s:s\to\{0,1\}$ for each $s\in\mathcal S_{n,m}$, and write

$$
p_a(y)=\frac1{C2^d}
\sum_{s\in\mathcal S_{n,m}}[\,y_j=a_s(j)\text{ for every }j\in s\,].
\tag{2.4}
$$

Here $[P]$ is $1$ when $P$ holds and $0$ otherwise.
The law $p_a$ is the average, over the $C$ masks, of the uniform laws on
their $2^d$ satisfying words. The actual posterior in (2.3)
is (2.4) with $a_s(s_k)=x_k$. These auxiliary assignments are only
intermediate points in the entropy comparison.

Fix $i\in[n]$. Align coordinate $i$ by replacing $a_s(i)$ by $0$ for every
mask containing $i$, leaving all other assigned coordinates intact.
For $z\in\{0,1\}^{[n]\setminus\{i\}}$, put
$E_s(z)=[\,z_j=a_s(j)\text{ for all }j\in s\setminus\{i\}\,]$ and
$\lambda=(C2^d)^{-1}$. Define the nonnegative quantities

$$
b=\lambda\sum_{s:i\notin s}E_s(z),\qquad
c=\lambda\sum_{s:i\in s,\ a_s(i)=0}E_s(z),\qquad
e=\lambda\sum_{s:i\in s,\ a_s(i)=1}E_s(z).
$$

The two probabilities for the words extending $z$ with bit $0$ or $1$
at $i$ therefore change as follows:

$$
(b+c,\ b+e)\longmapsto(b+c+e,\ b).
\tag{2.5}
$$

This is the binary, maximally mixed specialization of the transfers in
Alhejji–Knill, Equations (IV.11)–(IV.13).
For completeness, its entropy change, including zero probabilities, is
controlled directly by $f(t)=t\log_2t$ for $t>0$ and $f(0)=0$.
If $c>0$, the function $g_c(t)=f(t+c)-f(t)$ is continuous on
$[0,\infty)$ and satisfies

$$
g_c'(t)=\log_2(1+c/t)>0\qquad(t>0).
$$

It is strictly increasing also from $0$: for $t>0$,
$g_c(t)>g_c(t/2)\ge g_c(0)$ by monotonicity on the positive half-line
and continuity at $0$. Hence

$$
f(b+c+e)+f(b)-f(b+c)-f(b+e)\ge0,
\tag{2.6}
$$

with strict inequality exactly when $c>0$ and $e>0$.
Indeed, when both are positive the difference is
$g_c(b+e)-g_c(b)>0$; if either is zero it vanishes.
Summing over all outside words $z$ proves that each alignment
does not increase Shannon entropy, and strictly decreases it if some
$z$ has both $c,e>0$. Aligning all $n$ coordinates yields the assignments
$a_s(j)=0$ for all $j\in s$, hence precisely $p_{0^m}$.
This proves $H_{n,m}(x)\ge H_{n,m}(0^m)$.

Suppose $x$ is nonconstant. It has an adjacent transition
$x_r\ne x_{r+1}$ for some $1\le r<m$. Since $m+1\le n$, the masks

$$
s=[m+1]\setminus\{r\},\qquad
t=[m+1]\setminus\{r+2\},\qquad i=r+1
\tag{2.7}
$$

belong to $\mathcal S_{n,m}$ and both contain $i$.
The rank of $i$ is $r$ in $s$ and $r+1$ in $t$, so their assignments
at $i$ are opposite. Outside $i$, their common selected positions have
identical assignments. Explicitly, choose an outside word $z$ with

$$
\begin{aligned}
z_j&=x_j &&(1\le j\le r-1),\\
z_r&=x_r,&\qquad z_{r+2}&=x_{r+1},\\
z_j&=x_{j-1} &&(r+3\le j\le m+1),
\end{aligned}
\tag{2.8}
$$

and arbitrary bits at positions beyond $m+1$; empty index ranges impose
no conditions. The position $r$ is selected only by $t$, and $r+2$
only by $s$. Thus $E_s(z)=E_t(z)=1$ for the actual posterior assignments.
Their opposite bits at $i$ give $c\ge\lambda>0$ and $e\ge\lambda>0$.
Align coordinate $i$ first. By (2.6) this step strictly lowers entropy;
all subsequent alignments do not increase it. Therefore

$$
H_{n,m}(x)>H_{n,m}(0^m)
\quad\text{for every nonconstant }x,\quad 1\le m<n.
\tag{2.9}
$$

Bitwise complementation $y\mapsto\overline y$ is a bijection on $\Sigma_n$
and satisfies $\omega_{1^m}(\overline y)=\omega_{0^m}(y)$, since it keeps
each labelled mask. Thus the two constant posteriors have the same entropy.
Both constants attain the lower bound, and (2.9) excludes every other
equality case. When $m=1$ every binary observation is constant, in agreement
with this classification.

Finally, (2.1) is the constant-observation value of Atashpendar, Roscoe and
Ryan, institutional author preprint cited in Definition 1.1, Section 3.3,
Equation (12), reindexed by the number of additional zeros. That equation
evaluates the constant law; extremality follows here from the comparison
just proved. To check the correspondence, a word with $k$ zero bits has

$$
\omega_{0^m}(y)=\binom{k}{m},
$$

and there are $\binom nk$ such words. Terms with $k<m$ have zero posterior
probability. Substitution into (2.3) gives, for every $0\le m\le n$,

$$
H_{n,m}(0^m)=\log_2(C2^d)
-\frac1{C2^d}\sum_{k=m}^{n}
\binom nk\binom km\log_2\binom km.
$$

The factorial identity
$\binom nk\binom km=\binom nm\binom{n-m}{k-m}$ and the substitution
$j=k-m$ give (2.1). It yields $n$ at $m=0$ and $0$ at $m=n$,
as also proved directly above. $\square$

## 追加锚（本行以下为增补区）
