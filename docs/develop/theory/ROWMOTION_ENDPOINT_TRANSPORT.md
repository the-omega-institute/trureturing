# Rowmotion endpoint transport

Let $P$ be a finite poset and let $I\subseteq P$ be interval-closed: whenever
$u,v\in I$ and $u\le y\le v$, then $y\in I$.  For $x\in P$, write

$$
T_x(S)=
\begin{cases}
S\mathbin{\triangle}\{x\},&\text{if }S\mathbin{\triangle}\{x\}\text{ is interval-closed},\\
S,&\text{otherwise}.
\end{cases}
$$

If $x_1,\ldots,x_N$ is a complete reverse linear extension of $P$ (each point occurs exactly once and $x_i>x_j$ implies $i<j$), define $I_0=I$ and
$I_k=T_{x_k}(I_{k-1})$.  Put $J=I_N$.  For $S\subseteq P$, let
$\operatorname{Min}(S)$ and $\operatorname{Max}(S)$ denote extremal elements in the induced order, and let

$$
\uparrow I=\{x\in P:\exists a\in I,\ a\le x\},\qquad
\downarrow J=\{x\in P:\exists b\in J,\ x\le b\}.
$$

**命题 1.1（端点传输）。** 若 $m\in\operatorname{Min}(I)$、
$c\in\operatorname{Min}(\uparrow I\setminus I)$、且 $m<c$, 则

$$
c\in\operatorname{Max}(J)
\qquad\text{and}\qquad
m\in\operatorname{Max}(\downarrow J\setminus J).
$$

The statement uses the literal toggle trace above.  In particular, the endpoint conclusion is not a definition of a transition and does not assume a global rowmotion formula.  The proof must account for the processed/unprocessed membership at the exact step at which each point is toggled; the local alternatives are the interval-closed toggle conditions for an absent point and for a present point.

## 追加锚（本行以下为增补区）
