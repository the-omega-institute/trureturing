# Native regional rank on a bouquet

## 1. Definitions and the native map

Fix a natural number $k\ge2$ and a prime $p>k$. Let
$K=\operatorname{GaloisField}(p,2)$, and let
$$
D:\operatorname{Fin}(k)\times(\operatorname{Fin}(k)\times\operatorname{Fin}(2))\longrightarrow K
$$
be an arbitrary matrix. Its entries are written $D(i,(j,s))$, where
$i,j\in\operatorname{Fin}(k)$ and $s\in\operatorname{Fin}(2)$. The latent
space is $K^k\times K^k$: $\lambda\in K^k$ is the central coordinate and
$z\in K^k$ has one loop coordinate $z_j$ per $j$. Since $p>k\ge2$ and $p$ is
prime, $p\ge3$, so $2\cdot1_K\ne0$.

For $\lambda\in K^k$ put
$$
\begin{aligned}
a_j(\lambda)&=\sum_{i\in\operatorname{Fin}(k)}D(i,(j,0))\lambda_i,\\
b_j(\lambda)&=\sum_{i\in\operatorname{Fin}(k)}D(i,(j,1))\lambda_i.
\end{aligned}
$$
The actual four-leg map in loop $j$ is
$$
(a_j(\lambda)+z_j,\ a_j(\lambda)-z_j,\ b_j(\lambda)+z_j,\ b_j(\lambda)-z_j).
$$
For a region $R\subseteq\operatorname{Fin}(k)\times\operatorname{Fin}(4)$,
let
$$
R_j=\{\ell\in\operatorname{Fin}(4):(j,\ell)\in R\},\qquad
J=\{j:R_j\ne\varnothing\},\qquad H_R=|J|.
$$
The selected map $F_R:K^k\times K^k\to K^R$ is the restriction of the
displayed actual map to the coordinates in $R$; thus
$$
(F_R(\lambda,z))_{(j,\ell)}=
\begin{cases}
a_j(\lambda)+z_j,&\ell=0,\\
a_j(\lambda)-z_j,&\ell=1,\\
b_j(\lambda)+z_j,&\ell=2,\\
b_j(\lambda)-z_j,&\ell=3.
\end{cases}
$$

Define $V_R:K^k\to K^{2k}$ by giving two slots for every $j$ and padding
unused slots by zero. Its $j$-block is
$$
v_{R,j}(\lambda)=
\begin{cases}
(0,0),&|R_j|\le1,\\
(a_j(\lambda),0),&R_j=\{0,1\},\\
(b_j(\lambda),0),&R_j=\{2,3\},\\
(a_j(\lambda)-b_j(\lambda),0),&R_j=\{0,2\}\text{ or }R_j=\{1,3\},\\
(a_j(\lambda)+b_j(\lambda),0),&R_j=\{0,3\}\text{ or }R_j=\{1,2\},\\
(a_j(\lambda),b_j(\lambda)),&|R_j|\ge3.
\end{cases}
$$
The zero padding is part of the definition and does not change the rank of
the nonzero central slots.

**定理 1.1（任意系数与任意区域的本征区域秩恒等式）。** 对上述每个
$k,p,D$及每个区域 $R$，均有
$$
\operatorname{rank}_K(F_R)=H_R+\operatorname{rank}_K(V_R).
$$
这里的秩是相应有限维 $K$-线性映射像的 $K$-维数。该量词包括零矩阵、
任意相关的 $D$，以及空、满、单腿区域和 $k=2,p=3$；没有使用
MSRD、单射、秩或核等价、熵、RT 条件或目标结论作为假设。

Proof. Write
$$
\epsilon=(1,-1,1,-1),\qquad
c_j(\lambda)=(a_j(\lambda),a_j(\lambda),b_j(\lambda),b_j(\lambda)).
$$
The $(j,\ell)$ coordinate of the actual map is
$c_{j,\ell}(\lambda)+\epsilon_\ell z_j$. For each $j\in J$ choose one
actual selected anchor $\alpha_j\in R_j$, using only $R$ and before varying
$\lambda$ or $z$, and put
$$
T_j(\lambda)=\epsilon_{\alpha_j}c_{j,\alpha_j}(\lambda).
$$
Let $W_R:K^k\to K^R$ have rows
$$
(W_R(\lambda))_{(j,\ell)}
   =\epsilon_\ell c_{j,\ell}(\lambda)-T_j(\lambda)
   \qquad ((j,\ell)\in R).
$$
The anchor row is zero by definition. If $(\lambda,z)\in\ker F_R$, the anchor
equation in loop $j$ is $c_{j,\alpha_j}+\epsilon_{\alpha_j}z_j=0$, hence
$z_j=-T_j(\lambda)$. Multiplying every other selected equation by its
nonzero sign $\epsilon_\ell$ then gives precisely the corresponding row of
$W_R(\lambda)=0$. Conversely, if $\lambda\in\ker W_R$, set
$$
z_j=-T_j(\lambda)\quad(j\in J),
$$
and choose arbitrary $z_j\in K$ for $j\notin J$. For a selected row in a hit
loop, the equation multiplied by $\epsilon_\ell$ is the zero row of $W_R$;
multiplication by the same nonzero sign recovers the original equation. There
are no equations in an unhit loop. Thus the two maps
$$
\begin{aligned}
\ker F_R&\longrightarrow\ker W_R\times K^{\operatorname{Fin}(k)\setminus J},
 &(\lambda,z)&\longmapsto(\lambda,(z_j)_{j\notin J}),\\
\ker W_R\times K^{\operatorname{Fin}(k)\setminus J}&\longrightarrow\ker F_R,
 &(\lambda,u)&\longmapsto(\lambda,z),
\end{aligned}
$$
with $z_j=-T_j(\lambda)$ on $J$ and $z_j=u_j$ off $J$, are well-defined
linear inverses. This also covers the empty region: then $J=\varnothing$,
$W_R$ has no rows, and all $k$ loop coordinates are free.

It remains to identify the central kernel. The local rows of $W_R$ impose no
condition when $|R_j|\le1$. If $R_j=\{0,1\}$, the two signed central values
are $a_j$ and $-a_j$; after one is chosen as anchor the other row is
$\pm2a_j$, so its vanishing is equivalent to $a_j=0$. The same argument for
$R_j=\{2,3\}$ gives $b_j=0$. For $\{0,2\}$ and $\{1,3\}$ the remaining row
is a nonzero sign times $a_j-b_j$, while for $\{0,3\}$ and $\{1,2\}$ it is a
nonzero sign times $a_j+b_j$. The factor $2$ is nonzero by the displayed
conditions on $p$, so these equivalences hold also when $p=3$.

If $|R_j|\ge3$, at least one of the pairs $\{0,1\}$ and $\{2,3\}$ is fully
selected. The equations saying that all selected signed central values equal
the anchor value then give either $a_j=-a_j$ or $b_j=-b_j$, hence that whole
quantity is zero; a selected leg from the other pair then forces the other
quantity to be zero. Conversely $a_j=b_j=0$ makes every local residual zero.
Therefore, for every $j$, the local condition supplied by $W_R$ is exactly
the kernel condition of the corresponding padded block $v_{R,j}$ in the
definition of $V_R$. Since the blocks use disjoint coordinates,
$$
\ker W_R=\ker V_R.
$$

The inverse pair above gives
$$
\dim_K\ker F_R=\dim_K\ker V_R+(k-H_R).
$$
Rank-nullity on the actual latent domain $K^k\times K^k$, whose dimension is
$2k$, now yields
$$
\begin{aligned}
\operatorname{rank}_K(F_R)
 &=2k-\dim_K\ker F_R\\
 &=2k-\bigl(\dim_K\ker V_R+k-H_R\bigr)\\
 &=H_R+\bigl(k-\dim_K\ker V_R\bigr)\\
 &=H_R+\operatorname{rank}_K(V_R).
\end{aligned}
$$
This proves the identity. ∎

## 2. Scope boundary

The theorem is the arbitrary-$D$ inference that isolates the local elimination
step for this bouquet's actual four-leg map. It does not assert virtual-rank
saturation, an MSRD or lawful-collection extension, realization of every
region by a prescribed virtual collection, a support or entropy formula, or an
all-region RT equivalence or converse. Those statements concern additional
hypotheses and remain separate from this regional identity.

## 3. Source status

The exact correspondence between the same matrix $D$, the same selected region
$R$, the anchor elimination, and the padded native map $V_R$ is repo-derived.
The proof uses only finite-dimensional linear algebra, the displayed
characteristic-$p$ consequence, and rank-nullity; it makes no claim about an
external open problem or about originality of those standard ingredients.

## 追加锚（本行以下为增补区）
