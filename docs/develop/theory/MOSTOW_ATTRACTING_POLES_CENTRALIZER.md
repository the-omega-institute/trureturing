# Attracting poles and centralizers

This volume records a topological criterion for triviality of the centralizer
of a group action. Its hypotheses are explicit geometric obligations when the
space is intended to be an ideal boundary.

## 1. Dense attracting poles

**定理 1.1（稠密吸引极点的平凡中心化子）。** Let $G$ be a group and $X$ a Hausdorff
topological space in which, for any $b,c\in X$, there is a point distinct from
both. Let $\rho:G\to\operatorname{Homeo}(X)$ be a group homomorphism. Suppose the
set of points $a$ for which there are $g\in G$ and $b\in X$ with $a\ne b$ and

$$
\forall x\in X\setminus\{b\},\qquad \rho(g)^n(x)\longrightarrow a
\quad\text{as }n\longrightarrow\infty
$$

is dense in $X$. Then every homeomorphism commuting with every $\rho(g)$ is
the identity.

**证明。** Let $z$ commute with the image of $\rho$, and choose an attracting
pole $a$ with witness $(g,b)$. Choose $x$ distinct from both $b$ and
$z^{-1}(b)$; then $z(x)\ne b$. The orbit $\rho(g)^n(x)$ tends to $a$, so its
image under the continuous map $z$ tends to $z(a)$. Commutation gives
$z(\rho(g)^n(x))=\rho(g)^n(z(x))$ for every $n$, and the attracting-pole
hypothesis makes this latter sequence tend to $a$. Uniqueness of limits in a
Hausdorff space yields $z(a)=a$. Thus $z$ fixes a dense subset of $X$;
continuity makes it the identity everywhere.

## 2. Scope

The theorem assumes an action on a Hausdorff space with dense attracting
poles. It does not construct an ideal boundary, establish north-south
dynamics or density of poles for a lattice, prove faithfulness, or provide a
conjugator.

## 追加锚（本行以下为增补区）
