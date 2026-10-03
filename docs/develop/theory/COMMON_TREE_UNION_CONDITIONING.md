# 共同正则子树的并集条件化

## 1. 有限共同树与原前缀事件

**定义 1.1（全节点均匀树律）。** 固定整数 $2\le r<s$，记 $[s]=\{0,\ldots,s-1\}$，$\mathcal C_{r,s}=\{S\subseteq[s]:|S|=r\}$。对每个有限高度 $B\ge0$，令

$$
\Omega_0=\{\bullet\},\qquad
\Omega_{B+1}=\mathcal C_{r,s}\times\Omega_B^{[s]}.
$$

$\mathbb P_0$ 为点质量；$\mathbb P_{B+1}$ 是 $\mathcal C_{r,s}$ 上的均匀律与 $s$ 份 $\mathbb P_B$ 的独立乘积。因此所有深度小于 $B$ 的目标节点都有独立的均匀 $r$ 子集选择，包括未从根到达的节点。

**定义 1.2（采样叶与存活）。** 令 $T_\bullet=\{\varepsilon\}$。对 $\Theta=(S,(\Theta_a)_{a\in[s]})\in\Omega_{B+1}$，递归定义

$$
T_\Theta=\bigcup_{a\in S}\{av:v\in T_{\Theta_a}\}\subseteq[s]^{B+1}.
$$

对长度 $\ell\le B$ 的词 $w\in[s]^\ell$，记 $A_w=\{\Theta:\exists v\in T_\Theta,\ w\text{ 是 }v\text{ 的前缀}\}$。对任意集合 $F\subseteq[s]^B$，记 $H_F=\{\Theta:T_\Theta\cap F\ne\varnothing\}$。空词事件 $A_\varepsilon$ 是整个样本空间。所有事件均在同一个 $\Omega_B$ 上定义。

**定义 1.3（共同嵌入）。** 在每个被选节点，将其 $r$ 个已选目标孩子按自然顺序与 $[r]$ 对应。从根递归得到各层单射 $\theta_j:[r]^j\hookrightarrow[s]^j$。它们与截取前缀相容，且 $\operatorname{im}\theta_B=T_\Theta$。这一嵌入同时用于全部目标词。若 $\mathcal F$ 是长度不超过 $B$ 的有限前缀族，令 $F$ 为其中各词的全部深度 $B$ 扩张的并；则 $\bigcup_{v\in\mathcal F}A_v=H_F$，因为每个已到达的节点都有 $r\ge1$ 个后继。

## 2. 不随高度累乘的并集下界

**定理 2.1（实际共同树的并集条件化）。** 对任意整数 $2\le r<s$、有限高度 $B\ge0$、整数 $0\le\ell\le B$、词 $w\in[s]^\ell$ 和集合 $F\subseteq[s]^B$，在定义 1.1 的同一概率律下有

$$
r(s-1)\,\mathbb P_B(A_w\cap H_F)
\ \ge\ s(r-1)\,\mathbb P_B(A_w)\mathbb P_B(H_F).
$$

证明。置

$$
t=\frac rs,\qquad \kappa=\frac{s(r-1)}{r(s-1)}.
$$

由根的均匀子集计数，每个指定孩子被选中的概率为 $t$。沿词的独立节点选择相乘，$\mathbb P_B(A_w)=t^\ell>0$。于是所求不等式等价于 $\mathbb P_B(H_F\mid A_w)\ge\kappa\mathbb P_B(H_F)$。有 $0<t<1$ 与 $0<\kappa<1$。

先给出所需的不放回抽样比较。设有限载体 $V$ 至少有 $r$ 个元素。均匀选取 $r$ 子集 $S\subseteq V$，再从 $S$ 中均匀删除一个元素 $e$。任意固定的 $(r-1)$ 子集 $R$ 有恰好 $|V|-r+1$ 个逆像对 $(S,e)$，故 $S\setminus\{e\}$ 均匀分布于全部 $(r-1)$ 子集。对任意固定命中集 $D\subseteq V$，若 $S\cap D\ne\varnothing$，至少 $r-1$ 个删除选择仍保留命中：固定一个 $S\cap D$ 中的元素，删除其他元素均可。因此，均匀选取 $(r-1)$ 子集的命中概率至少为均匀选取 $r$ 子集命中概率的 $(r-1)/r$。命中集可以随机，只需它与子集选择独立；对其条件化后再平均即可。

现对高度 $B$ 归纳，命题同时量化全部合法长度、词和叶集合。若 $w$ 为空，条件事件必然发生，不等式由 $\kappa\le1$ 得到；这也包括高度零。非空时写 $w=iw'$，并记

$$
F_j=\{v:jv\in F\},\qquad
q_j=\mathbb P_{B-1}(H_{F_j}),\qquad
q_i'=\mathbb P_{B-1}(H_{F_i}\mid A_{w'}).
$$

归纳假设给出 $q_i'\ge\kappa q_i$。在其他 $s-1$ 个孩子中，令 $u$ 为均匀选择 $r-1$ 个孩子时其子树至少命中一个 $F_j$ 的概率，令 $v$ 为均匀选择 $r$ 个孩子时的相应概率。这里先抽取全部孩子的独立子树，再独立抽取孩子子集；随机命中集是 $\{j\ne i:T_{\Theta_j}\cap F_j\ne\varnothing\}$。上述删除比较适用，得到

$$
v\le\frac r{r-1}u.
$$

根子集条件于含 $i$ 时，其余部分是其他孩子的均匀 $(r-1)$ 子集；条件于不含 $i$ 时，它是均匀 $r$ 子集。根选择独立于全部子树，指定子树独立于其他子树，所以令 $q=\mathbb P_B(H_F)$，可得

$$
q=t\bigl[u+(1-u)q_i\bigr]+(1-t)v.
$$

条件事件 $A_w$ 等于根选中 $i$ 与第 $i$ 子树发生 $A_{w'}$ 的交。两个条件涉及独立坐标；其余子树的联合律不变。因此

$$
h:=\mathbb P_B(H_F\mid A_w)=u+(1-u)q_i'.
$$

利用 $t+(1-t)r/(r-1)=1/\kappa$、$0\le u\le1$ 和 $q_i\ge0$，有

$$
\begin{aligned}
\kappa q
&\le u+\kappa t(1-u)q_i\\
&\le u+\kappa(1-u)q_i\\
&\le u+(1-u)q_i'=h.
\end{aligned}
$$

归纳完成。乘回正数 $\mathbb P_B(A_w)$ 及 $r(s-1)$ 即为无除法陈述。$\square$

## 追加锚（本行以下为增补区）
