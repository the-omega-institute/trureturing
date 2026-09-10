# 受限像集探针: Q_m(Sym(p))

## 先纠正输入,再给判词

**判词: revise。像集可用已有定义精确表达;本席找到的有效低阶约束均有 bind-only 路径,不派独立实施席。完整的全阶实根机制仍未得到。**

三处必须先校准:

1. **Remark 5.5 的转述属实,但须点名 kernel。** 第 20 页说的是 Proposition 5.4 中的 `H_m[2,2 / (1-1/(2m)),(2+1/m)]`,以及其正 dilation。不是 Notation 5.1 的 `z_{2m}`:论文第 19 页反而明确说 `z_{2m}` 全实根。`Q_m(z_{2m})` 也不能与 Proposition 5.4 合并系数因子后的 kernel 混同。
2. **“#6433/#6450 尚未冻结”已过期。** 本树 `bc8d784d6a331a985c758bdbf6cf22bcd41ac873` 上已有这些模块的状态片。`git log` 定位到后续补冻提交 `11e09fb04011c40a1889c6006cf4813a687564d0`。下文用的是当前源码和状态片,不把旧报告或 issue 当冻结前提。本席没有执行冻结。
3. **研究席的 `(2)`、`R`、`H₀` 不是这篇论文的原生编号/记号。** `#6377` 第二轮评论的 `(2)` 是匹配恒等式的轮内标签。打开的 v2 全文中 `matching` 词界检索为 0;论文自己的有关系数编号是 (2.1)、(3.1)、(5.1)。本报告从这些原始定义明确重建 `R` 和矩阵归一化,不声称找到了论文中的 `H₀(R)`。

产地: `skill: consensus-rnd:sshx`; 单席 codex-cli; `repo-prior-exposed`。
输入为本席 brief、AGENTS.md、完整 CLAUDE.md、源码/状态片、实际下载的论文及公开 issue/PR。
零子席、零评审席、独立来源数 1;没有多模型共识或 orchestrator 本轮亲验主张。
先前 orchestrator 在 `m=2..11` 的核验是 brief 转述;下文同一区间的读数由本席重新独立计算。
任务是第三档研究线的有界判形探针。达到定义、约束和反例的可核对结算即停止,不把它扩成实施模块。

## Q1. 原文核实

实际打开: <https://arxiv.org/pdf/2502.00254v2>。
Jacob Campbell, Rafael Morales, Daniel Perales, *Even Hypergeometric Polynomials and Finite Free Commutators*。
下载文件为 33 页;PDF 物理页码与印刷页码相同。
PDF SHA-256: `2d8db91f7f43604bbf56672abf3f14035897444a9ce7204bb30d49b90470bfdd`。
首页印有 SIGMA 21 (2025), 108、DOI `10.3842/SIGMA.2025.108`;没有另行打开 DOI 页面。
以下引文恢复排版空格,数学公式转写为 LaTeX,不改文字或参数。

### Theorem 5.2, p.20

> **Theorem 5.2 ([10]).** Let A and B be normal n × n matrices with characteristic polynomials p(x) = χ(A) := det[xI − A] and q(x) = χ(B) := det[xI − B]. Then
>
> \[\mathbb E_U\chi[i(AUBU^*-UBU^*A)]=p(x)\mathbin{\square_n}q(x),\]
>
> where U is a random n × n unitary matrix.

这是期望特征多项式恒等式。它没有断言该期望全实根,也没有给 common interlacing。

### Conjecture 5.3, p.20

> **Conjecture 5.3.** For p, q ∈ P_n(R), we have p □_n q ∈ P_n(R).

量词覆盖所有次数 `n`,两个输入均首一、恰为 `n` 次、全部根实。
没有中心化、单根、非零根、偶数次数或 Theorem 5.6 因子分解假设。
论文随后为方便计算才限制 `n=2m`;这不是猜想的附加假设。

### Proposition 5.4, p.20

> **Proposition 5.4 (even part of commutator).** For p, q ∈ P_{2m}(R), we have
>
> \[Q_m(p\mathbin{\square_{2m}}q)=Q_m(\operatorname{Sym}(p))\boxtimes_m
> Q_m(\operatorname{Sym}(q))\boxtimes_m
> \operatorname{Dil}_{1/4}H_m\!\left[\begin{matrix}2,2\\1-\frac1{2m},\,2+\frac1m\end{matrix}\right].\]
>
> **Proof.** When one applies Q_m to the right-hand side of equation (5.1) and uses Proposition 3.9, one obtains the expression
>
> \[Q_m(\operatorname{Sym}(p))\boxtimes_m Q_m(\operatorname{Sym}(q))\boxtimes_m
> \operatorname{Dil}_{1/4}H_m\!\left[\begin{matrix}2,2,1-\frac1{2m}\\-\frac1{2m},-\frac1{2m},2+\frac1m\end{matrix}\right]
> \boxtimes_m H_m\!\left[\begin{matrix}-\frac1{2m}\\1-\frac1{2m}\end{matrix}\right]
> \boxtimes_m H_m\!\left[\begin{matrix}-\frac1{2m}\\1-\frac1{2m}\end{matrix}\right].\]
>
> By Theorem 2.18, the hypergeometric polynomials can be combined, and cancellation of parameters leaves \(H_m[2,2 / (1-1/(2m)),(2+1/m)]\), hence the claim.

这里 `H_m` 上排是 `b` 参数、下排是 `a` 参数;不是通常超几何级数参数的随意互换。
Definition 2.16, p.7 原式为
\[e_k(H_n[\mathbf b/\mathbf a])=\binom nk\frac{(n\mathbf b)_k}{(n\mathbf a)_k}.\]
本报告的 `(a)_k` 一律表示**下降**阶乘。

### Remark 5.5, p.20, 全文

> **Remark 5.5.** It is very important to notice that the polynomial \(H_m[2,2 / (1-1/(2m)),(2+1/m)]\), appearing in Proposition 5.4, does not belong to P_m(R_{≥0}).
>
> Actually, if this polynomial were to be in P_m(R_{≥0}), then Conjecture 5.3 would follow from part (3) of Theorem 2.12, after noticing that Q_m(Sym(p)) ∈ P_m(R_{≥0}) and Q_m(Sym(q)) ∈ P_m(R_{≥0}) by part (5) of Lemma 3.8.
>
> This means that to prove Conjecture 5.3, one must find some kind of “extra” real-rootedness in the symmetrizations Q_m(Sym(p)). It is unclear if this extra positivity holds in general. With this idea in mind, however, we can explicitly formulate a theorem that is similar to Conjecture 5.3, but requires an extra assumption.

所以原文确实定位了该直接套用路径的障碍。它不是“任何 Mathlib/冻结件组合都不可能解决”的元定理;`escapes` 仍须逐候选检查。
Remark 的无例外措辞须按非平凡次数读: `m=1` 时该 `H_1=Y-8/3`,确实在 `P_1(R_{≥0})`;本报告的 kernel 负性主张均限定 `m≥2`。

### Q_m、Sym 的精确定义

p.3 §2.1:

> We denote by P_n the set of monic polynomials (over the complex plane C) of degree n. To specify that all the roots of a polynomial belong to a specific region K ⊆ C, we use the notation P_n(K).

p.11 Notation 3.4:

> Define S_m : P_m → P^E_{2m} by S_m(p) = p(x²) for p ∈ P_m.

p.11 Notation 3.5:

> **Notation 3.5 (even and odd parts).** Define Q_m : P_{2m} → P_m as follows: for p ∈ P_{2m}, define Q_m(p) by the coefficients
>
> \[e_k(Q_m(p))=(-1)^k e_{2k}(p).\tag{3.1}\]

故 `Q_m` 对**任意**首一 `2m` 次多项式定义,丢弃奇次项并把 `X^{2j}` 改成 `Y^j`。
它不是“把任意多项式的全部根平方”;只有限制在偶多项式上才与 `S_m` 互逆。

p.11 Notation 3.7:

> For p ∈ P_n, the symmetrization of p is the polynomial Sym(p) := p ⊞_n (Dil_{−1} p).

`Sym` 是有限自由加法卷积;既不是普通偶部平均,也不是普通乘积。
p.11 Lemma 3.8 的有关原句:

> (3) Sym(Dil_α p) = Dil_α Sym(p);
> (4) Sym(p ⊞_n c_α) = Sym(p);
> (5) if p ∈ P_{2m}(R), then Q_m(Sym(p)) ∈ P_m(R_{≥0}).

p.6 Theorem 2.12 的实根保持条件原文:

> Let p, q ∈ P_n(R). Then
> (1) p ⊞_n q ∈ P_n(R);
> (2) if either p ∈ P_n(R_{≥0}) or q ∈ P_n(R_{≥0}), then p ⊠_n q ∈ P_n(R);
> (3) if both p, q ∈ P_n(R_{≥0}), then p ⊠_n q ∈ P_n(R_{≥0}).

## Q2. 仓内与论文对照

`F4` 以下指 `D5/S3/Zeros/Convolution/FiniteFreeCommutatorDegreeFour`。
这里的等同均限定论文要求的首一、恰好次数域;Lean 定义在域外仍然是总函数。

| 仓内声明 | 论文对象/原式 | 页码及边界 |
| --- | --- | --- |
| `F4.elementaryCoeff n p k` | Notation 2.1 的 `e_k(p)`; `p(X)=Σ_{k=0}^n X^{n-k}(-1)^k e_k(p)` | p.3; 只在 `k≤n` 对应。Lean 的自然数截断减法不提供论文域外的零延拓 |
| `F4.additiveConvolution n p q` | Definition 2.9 的 `p ⊞_n q`; `e_k=(n)_k Σ_{i+j=k} e_i(p)e_j(q)/((n)_i(n)_j)` | p.5; `descPochhammer` 是下降阶乘,不是上升阶乘 |
| `F4.dilate n α p` | Notation 2.2: `[Dil_α p](x)=α^n p(α^{-1}x)` | p.3; 论文明确 `α≠0`,Lean 没有这个参数前提;这里只用 `α=-1` |
| `F4.symmetrize n p` | Notation 3.7 的 `Sym(p)=p⊞_n Dil_{-1}p` | p.11; 不是普通偶部 |
| `FiniteConvolutionCoefficients.coeff_additiveConvolution` | Definition 2.9 的同一系数式,改为无符号的 `c_k=[X^{n-k}]p` | p.5; `k≤n` 是显式前提。论文没有这个 Lean 名称对应的独立定理 |
| `F4.multiplicativeConvolution n p q` | Definition 2.9 的 `⊠_n`; `e_k(p⊠q)=e_k(p)e_k(q)/binom(n,k)` | p.5 |
| `F4.commutatorKernel n` | Notation 5.1 的 `z_n` | p.19; **不等于** Proposition 5.4 的 `m` 次 kernel |
| `F4.square4` | Notation 5.1 的 `p□_4q` | p.19; 该声明只绑定 `n=4`;任意 `n` 可用已有两个乘法卷积定义复合写出 |
| Mathlib `Polynomial.contract 2` | Notation 3.5 的 `Q_m` | p.11; `coeff_contract` 给 `[Y^j]contract(2,p)=[X^{2j}]p`,次数上界取 `2m` |
| Mathlib `Polynomial.expand ℝ 2` | Notation 3.4 的 `S_m` | p.11; `contract_expand` 直接给 `Q_m S_m=id` |
| `MatchingPolynomial.matching_identity` | 本轮 `#6377` 的匹配式 `(2)` | **对不上论文中的一个同号声明**,不是论文原生式 (2) |
| `NewtonHankelRealRootCriterion.newtonHankel` | 本报告另定义的 `H₀(R)` 的归一化版本 | **对不上论文对象/页码**;该论文这些条目没有 `H₀` |

无符号转换明确为
\[c_k(p\boxplus_n q)=(n)_k\sum_{i=0}^k
\frac{c_i(p)c_{k-i}(q)}{(n)_i(n)_{k-i}}.\]
这是 `(-1)^k(-1)^i(-1)^{k-i}=1` 的规范化,不是另一种卷积。

为离线核对 `z_n` 与合并后 kernel 的区别,补录 p.19 Notation 5.1 的原式:

> **Notation 5.1.** Let
>
> \[z_n(x):=\sum_{k=0}^{\lfloor n/2\rfloor}x^{n-2k}(-1)^k\binom n{2k}
> \frac{(n)_k k!}{(2k)!}\frac{n+1-k}{n+1}\]
>
> and for polynomials p(x) and q(x) with degree n, write
>
> \[p\mathbin{\square_n}q:=\operatorname{Sym}(p)\boxtimes_n\operatorname{Sym}(q)\boxtimes_n z_n.\tag{5.1}\]

该页在 `n=2m` 的超几何表示后明确写道:

> By Theorem 2.12, it follows that \(z_{2m}\in P_n^E(\mathbb R)\).

引文保留原文的下标 `n`;此处 `n=2m`。

冻结状态以 `ls Golden/Frozen/state/D5/S3/Zeros/Convolution` 及指定 Constants 路径查询。
以下是实际状态片 `statement_id` 的值;它们是**模块状态片身份**,不冒充逐声明哈希。

| 模块简称 | 状态片 statement_id, 均带 `sha256:` 前缀 |
| --- | --- |
| F4 | `e4f15f5c0461a866887270b3ea9714ad3cb9c7bf4a40afe95cc84c3488442c13` |
| FiniteConvolutionCoefficients | `58abac734b6a8969c6215223633e21fea7d3901df1967f9531622190c058d12c` |
| MatchingFiber | `27c6df741461734d172135906b9c9ccd1b6f884b6c790ec3c657e3a10ddc17d5` |
| MatchingPolynomial | `0d50ff5c5d051bd02c1ec393dc881990d9a1a09874800f18261a2870fac80799` |
| SexticEnvelope | `33cfc49345ee9794259badf034e9f1f7eb39c5f7aa2b1e5a8f5a0687adb2b763` |
| FiniteAdditiveSymbol | `ac2cdc677a969d2ce1e3e0528f12bfac212e0c3f8f0cd30ff76dfdcd9b58b6fd` |
| EvenPolynomialRoots | `14f866e6a3bd58843fd91007d0c80166b260ae939cc2a77c2234c6ec00c3a871` |
| NewtonHankelRealRootCriterion | `18b030426106ba093ef4ec58fbba090c162f365f32ed6b291aaa0eeba9a358a9` |

PR API 读取确认 #6433 合并于 `f2fdfa60dacb42206031565186712b1fc247f329`,#6450 合并于 `219dea85e92cf760bb7e6b1459ca3ad63af5ba15`;其原 PR 没有冻结片与之后补冻并不矛盾。
钉版为 Lean `v4.33.0`,Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`。

## Q3. 可表达的像集与额外性质

### P0: 精确像集,定义层 bind-only

无需新增 `Q_m`、实根谓词、匹配或卷积 API:

```lean
def reducedSym (m : ℕ) (r : Fin (2 * m) → ℝ) : ℝ[X] :=
  Polynomial.contract 2 (symmetrize (2 * m) (rootPolynomial r))

def imageCone (m : ℕ) : Set ℝ[X] := Set.range (reducedSym m)
```

`rootPolynomial r=∏_i(X-C(r_i))` 来自冻结 `MatchingFiber`。
实根首一多项式恰可这样列出根,包括重根和零根。也可用
`∃ p, p.Monic ∧ p.natDegree=2*m ∧ p.Splits ∧ q=contract 2 (symmetrize (2*m) p)`。
后者与根列表形式的互换用 Mathlib 的实根分解/Vieta,不是缺少一个数学定义。

写 `Q=Y^m-b₁Y^{m-1}+b₂Y^{m-2}-...`,令 `b_k=e_k(Q)`。
直接实例化当前已冻结的 `matching_identity`,得到完整的同源系数见证:
\[ b_k=\frac{1}{(2m)_k}\sum_{M\in\mathrm{Match}(2m,k)}
\prod_{\{i,j\}\in M}(r_i-r_j)^2,\qquad 0\le k\le m.\tag{W}\]
**所有阶使用同一个 `r`**,不能按阶另选根或另选任意非负边权。
在 `Q.natDegree≤m` 的条件下,“存在这样的同一个 `r` 满足全部 (W)”反过来也充分,由系数外延性得到精确成员资格。
这是一个精确存在量词描述,尚不是消去 `r` 后的可用全阶不等式刻画。

### P1: 系数非负,bind-only,停手

由 (W)、`sq_nonneg`、`Finset.prod_nonneg`、`Finset.sum_nonneg`、`div_nonneg` 直接得到 `b_k≥0`。
于是 `a_k=λ_{2m,k}b_k c_k≥0` 也只是直接绑定,其中
\[\lambda_{n,k}=\frac{k!}{(n-k)_k}\frac{n+1-k}{n+1},\quad 2k\le n.\]
没有新模块的理由。这一性质**不排除** `(Y-1)^m`,单独作刻画太弱。

### P2: 平移不变与加权齐次,bind-only

由同一根差表达式直接规范化:
\[b_k(r+t)=b_k(r),\qquad b_k(\alpha r)=\alpha^{2k}b_k(r).\]
可以把根平移到均值零;这里是根列表的共同平移,不是额外假设。
因此“像锥”只作为**加权 dilation** 的简称使用。首一多项式集合不是普通线性锥,一般也不是系数凸集。
例如 `m=2`,`Y²` 与 `Y²-4Y+8/3` 都在像中,系数中点 `Y²-2Y+4/3` 违反下面的 `b₂≤b₁²/6`。
这些协变性质本身也不足以排除校准输入。

### P3: 任意偶次数的锐二阶界,bind-only 路径

设 `n=2m≥4`,中心化根为 `x_i=r_i-mean(r)`,`S_j=Σ_i x_i^j`。
只实例化冻结 `symmetrize_coefficient` 于 `k=1,2`,并用 Mathlib 的 Vieta 和 Newton identities 于阶 `2,4`,得
\[e_1(p)=0,\quad e_2(p)=-S_2/2,\quad e_4(p)=S_2^2/8-S_4/4,\]
\[ b_1=S_2,\qquad b_2=\frac{n^2-3n+3}{2n(n-1)}S_2^2-\frac12S_4.\]
具体是 `b₁=-2e₂(p)` 和
`b₂=2e₄(p)+(n-2)(n-3)e₂(p)²/(n(n-1))`;有限卷积和分别只有 3、5 个项。
然后直接实例化钉版 **全局命名空间**的 `sq_sum_le_card_mul_sum_sq` 于 `f_i=x_i²`:
\[S_2^2\le nS_4.\]
规范化给出
\[0\le b_2\le\beta_m b_1^2,\qquad
\beta_m=\frac{(m-1)^2}{m(2m-1)},\tag{B2}\]
以及精确余量
\[\beta_m b_1^2-b_2=\tfrac12(S_4-S_2^2/n)\ge0.\]
比一般 `P_m(R_{≥0})` 的 Newton 界 `(m-1)b₁²/(2m)` 严格。
`p=(X²-a²)^m` 取等号,故常数锐;`a=0` 也包括。

**判形边界:** 上面是完整的纸面绑定推导。Lean 档案核验了 `k=2,4` 的一般 Newton 实例、Cauchy 实例以及冻结四次界的直接投影。
没有把“任意根列表的平移、Vieta、两个卷积系数、(B2)”全部封装成一个端到端 Lean 定理;不冒领该封装已 kernel 验证。
这不产生数学 gap:所列步骤只需现有声明实例化和规范化。不得因尚未装配就把它判为 content 或派独立实施席。

### P4: 六次的第三阶相关界,bind-only

`m=3` 时,冻结 `SexticEnvelope.centered_real_sextic_envelope` 的最后一个合取为
`45 Z (8A²-B)≤4AB²`,其中 `A=b₁/2,B=5b₂/2,Z=b₃`。
直接投影和规范化给出
\[9b_3(4b_1^2-5b_2)\le5b_1b_2^2.\tag{B3-6}\]
探针只消耗这条冻结结论,不重跑它内部的排序根间隙证书。
这是六次专属约束;本席**没有主张**把下标 6 去掉仍成立。

### P5: 非负实根基本类,论文已知,当前直接绑定有条件

`C_m⊆P_m(R_{≥0})` 正是论文 Lemma 3.8(5),p.11;不是本席新发现。
仓内 `FiniteAdditiveSymbol.additive_splits` 明确要求 `hBB : FiniteSymbolCriterion`。
`EvenPolynomialRoots.nonnegative_roots_of_splits_expand_two` 是已冻结的根几何桥,但不会自行产生 `hBB`。
因此当前仅用钉版和冻结 API 的直接应用得到的是**条件式**,不能省掉前提。

出网实际读到 upstream `RealRooted/BorceaBranden/Applications/RealUnivariateSymbol.lean` 在提交
`acd0ec31118a155b083c8dd45af2015492ce0c10` 的 `finiteSymbolTheorem` 和 `finiteSymbol_preservesRealRootedUpTo`。
这次没有做跨项目兼容构建,故它**不是本树可直接 import 的已验前提**。
数学上没有未知猜想需要为 P5 单独研究;当前缺的是可消费的 BB 保持定理证据。P5 也完全不能排除 `(Y-1)^m`。

### P6: 输出首个 Hankel 主块,仍是 bind-only 后果

本节限定 `m≥2`。从 Proposition 5.4 重新定义
\[K_m=\operatorname{Dil}_{1/4}H_m[2,2/(1-1/(2m)),(2+1/m)],\]
\[R=Q\boxtimes_m T\boxtimes_m K_m
=Y^m-a_1Y^{m-1}+a_2Y^{m-2}-\cdots,\quad a_k=\lambda_{2m,k}b_k c_k.\tag{R}\]
Definition 2.16 与两个二项式除数的直接消去给
\[e_k(K_m)=\binom mk\frac{(2m)_k^2}{4^k(m-1/2)_k(2m+1)_k}
=\lambda_{2m,k}\binom mk^2.\]
把 (B2) 对 `Q,T` 的非负两边相乘,直接规范化:
\[(m-1)a_1^2-2ma_2\ge L_m b_1^2c_1^2,\]
\[L_m=\frac{2(m-1)(2m^3-3m^2-2m+1)}{m(2m-3)(2m-1)^2(2m+1)^2}>0.\]
分子中的立方因子在 `m=t+2` 时等于 `2t³+9t²+10t+1`;正性无新结构。
这只证明 `[[m,a₁],[a₁,a₁²-2a₂]]` 半正定,**不证明整个 `m×m` 矩阵半正定**。
`m≥3` 的高阶块仍包含未受这些界控制的系数相关性。

### 数值读数: P0-P6

用 SymPy 1.14.0 的精确有理算术,从输入根先乘成 `p`,按 Definition 2.9 求 `Sym`,再提取偶系数。
另用逐顶点匹配递推独立计算 (W),六例逐项相等。
每例还实际计算了根平移 `+7` 及缩放 `×3`:分别得到相同 `b` 和 `9^k b_k`。
根计数由 `Poly.count_roots(0,+∞)` 精确求出;表中的近似根只供读数,不承担判词。

| n | 输入根 | `(b₁,...,b_m)` | (B2) 余量 | `Q` 正根数 | `R=Q,Q` 正根数 | R 首个 2×2 主子式 |
| --- | --- | --- | --- | --- | --- | --- |
| 4 | `-2,-1,1,2` | `10,73/6` | `9/2` | 2 | 2 | `16013/45` |
| 6 | `-3,-2,-1,1,2,3` | `28,882/5,2452/15` | `98/3` | 3 | 3 | `347508/25` |
| 8 | `-4,-3,-2,-1,1,2,3,4` | `60,7197/7,5150,278169/70` | `129` | 4 | 4 | `138508744/735` |
| 4 | `(-1)×2,(1)×2` | `4,8/3` | 0 | 2 | 2 | `256/225` |
| 6 | `(-1)×3,(1)×3` | `6,48/5,16/5` | 0 | 3 | 3 | `12672/1225` |
| 8 | `(-1)×4,(1)×4` | `8,144/7,128/7,128/35` | 0 | 4 | 4 | `149504/6615` |

(B3-6) 的 `rhs-lhs` 在两例六次输入上分别为 `5201448/5` 和 `0`。
第一例 `Q` 的根约 `1.41763578996589,8.58236421003411`;其 `R` 系数为 `1,-80/3,5329/60`,根约 `3.90141353346697,22.7652531331997`。
八次非重根例的 `R` 系数为 `1,-3200/7,5755201/105,-5304500/3,8597554729/980`,四个正根约 `6.03437221,41.37828929,122.19490198,287.53529367`。
这些有限读数不证明任意次数保持性;`m=4` 一例尤其不是 degree-8 认证进展。

## Q4. 负校准通过,并给出第二个反例

### 指定校准: U=V=(X²-1)^m,只做 Sym 后的步骤

关键是 `Q_m(U)=(Y-1)^m`,恰为 `⊠_m` 的单位元。因此本校准的输出 `R` **就是 `K_m`**。
其 `a_k=λ_{2m,k}binom(m,k)²` 与上面的 kernel 系数完全一致。
这直接对齐了 Remark 5.5 与轮内 `D_m`,无需依赖研究席未恢复的符号。

若误称 `Q_m(U)∈C_m`,则 `b₁=m,b₂=m(m-1)/2` 必须满足 (B2)。但
\[b_2-\beta_m b_1^2=\frac{m(m-1)}{2(2m-1)}>0\quad(m\ge2).\]
所以这些 `U` **不能是某个合法输入的 Sym 输出**。注意作为 Sym **之前**的输入,同一个多项式完全合法:
例如 `m=2`,真正 `Q_2(Sym((X²-1)²))=Y²-4Y+8/3`,不是 `(Y-1)²`。

代入 kernel 系数的纯有理恒等式给
\[D_m=(m-1)a_1^2-2ma_2
=-\frac{m^3(m-1)(8m^3+4m-1)}{2(2m-3)(2m-1)^2(2m+1)^2}<0.\]
SymPy 对一般符号 `m` 化简“左式减右式”为 0;分母和除负号外的分子在 `m≥2` 均正。
重新计算的有理读数如下,不是引用 orchestrator 的旧表:

| m | D_m |
| --- | --- |
| 2 | `-284/225` |
| 3 | `-2043/1225` |
| 4 | `-16864/6615` |
| 5 | `-254750/68607` |
| 6 | `-105060/20449` |
| 7 | `-950453/139425` |
| 8 | `-7395584/845325` |
| 9 | `-5702724/521645` |
| 10 | `-4019500/300713` |
| 11 | `-71148605/4432491` |

`m=2` 具体为 `K₂=Y²-(16/15)Y+3/5`,判别式 `-284/225`。
因所有实根列表都满足 Cauchy 的 `mΣρ_i²-(Σρ_i)²≥0`,负 `D_m` 已反证 `K_m` 全实根。
这是使用实根的**必要条件做反驳**,没有用待证的 PSD 回证实根。

| 描述或约束 | 能否排除指定校准 |
| --- | --- |
| P0 的同一根列表精确见证 | 能,因它必推出 (B2) |
| P1 非负系数 / P5 非负实根 | 不能;`(Y-1)^m` 两者都满足,作为刻画太弱 |
| P2 平移不变和加权齐次 | 不能;这些是像的协变规律,不是单点成员测试 |
| P3 锐二阶界 | 能,上述显式正差对所有 `m≥2` 成立 |
| P4 六次第三阶界 | `m=3` 能,校准点的余量为 `-54`;其它 m 不适用 |
| P6 输出首个 Hankel 主块 | 能拒绝该输出的负子式,但未判整个矩阵 |

### 第二校准: (B2)+非负实根仍不足

先尝试把 P3、P5 绑定为 kernel 保持定理,但它们没有控制全部系数。
精确搜索在 `m=3` 找到
\[Q=T=(Y-1)^2(Y-4)=Y^3-6Y^2+9Y-4.\]
它非负实根,且 (B2) 余量为 `(4/15)·36-9=3/5>0`。
然而
\[Q\boxtimes_3Q\boxtimes_3K_3
=Y^3-\frac{216}{35}Y^2+\frac{135}{14}Y-\frac{64}{7},\]
\[\operatorname{disc}=-\frac{662940477}{600250}<0.\]
精确实根数 1;近似根为 `4.47245031684394` 和 `0.849489127292316 ± 1.15005631707377 i`。
首个 2×2 Hankel 主子式仍为 `22437/1225>0`。
所以“前两矩过关即足够”以及“P3+P5 是完整像刻画”均被处决。
本例又违反冻结的 (B3-6),余量 `-1134`,因此**没有**构造出 Conjecture 5.3 的反例。

### Hermite 归一化和循环边界

本报告 `H₀(R)_{ij}=s_{i+j}`,`s_j=Σ_{ell=1}^mρ_ell^j`,`s₀=m`,含重数,`0≤i,j<m`。
对实系数 `R` 的复根枚举,这些和为实数。冻结 `newtonHankel` 则使用
`rootPowerMoment roots j = (Σ roots^j).re / m`,所以 `H₀=m·newtonHankel`。
`m>0` 时只差正缩放;上面的 2×2 行列式是**未归一化**的版本。
冻结 iff 还显式要求根集合在复共轭下封闭。它的两个方向都不能提供此前没有的实根机制。
这里没有以 `H₀ PSD` 为假设证明 `R` 实根再把它包装为对 `H₀ PSD` 的证明。

## Q5. 六栏判形表

所有候选先走钉版 Mathlib 实例化、冻结投影、规范化尝试。P0-P4/P6 的成功绑定到此为止;不创建实施模块。
表中 `不能` 指当前可消费前提内未获得该结论,不是在 Lean 中证明了“所有可能证明均不存在”。

| from | steps | gap: 数学缺陷 | escapes | payoff | cost_shape |
| --- | --- | --- | --- | --- | --- |
| **P0 精确像定义/同源系数**: `contract`, `coeff_contract`, `contract_expand`; `MatchingFiber.rootPolynomial`; `MatchingPolynomial.matching_identity` | `Set.range`; 系数转换;同一 r 的 (W);系数外延 | 无;但存在量词未消去 | **能,bind-only**;系数绑定 Lean 已验 | 明确对象与真正相关性,消除缺定义误判 | 结构性的函数像;每阶一条冻结匹配式,零匹配单项式重展 |
| **P1 系数符号**: P0; `sq_nonneg`,有限积/和/商非负 | 平方→积→和→除以非负阶乘 | 无;不足以排除 Q4 | **能,bind-only**,Lean 已验 | 可作消费者的伴随结论,不是新的实根机制 | 符号有限和,不展开;每条边是 1 个平方 |
| **P2 平移/齐次**: (W),`sub_add_sub_cancel` 类改写,`mul_pow`,有限积规则 | 根差消共同平移;提取 `α^{2k}`;系数外延 | 无;协变本身不是成员充分条件 | **能,bind-only**;完整 Lean 装配未做 | 合法中心化;解释“锥”的加权含义 | 每边一次二项式改写,无 n 依赖巨型恒等式 |
| **P3 锐二阶界**: `symmetrize_coefficient`; Mathlib Vieta、`psum_eq_mul_esymm_sub_sum`, `sq_sum_le_card_mul_sum_sq`;F4 界 | `k=1,2`; Newton 阶 2,4; Cauchy 用 `x_i²`;规范化余量 | 无新数学缺口;全次数一体 Lean 封装未作 | **能,bind-only**;通用 Newton/Cauchy 和四次投影 Lean 已验 | 所有 `m≥2` 排除 Q4;锐界与方差余量 | 次数固定的 O(1) 规范化;卷积和/原始 Newton 和至多 **5 项**,中心矩余量 2 项;不展开 `Σx_i²` 的平方。未实测完整 Lean 装配的展开峰值 |
| **P4 六次第三阶界**: `SexticEnvelope.centered_real_sextic_envelope` | 投影最后合取;代 `A=b₁/2,B=5b₂/2,Z=b₃` | 无;域仅 m=3 | **能,bind-only**,投影规范化 Lean 已验 | 排除新增 `(1,1,4)` 外像点,显示第三阶相关性 | 原结论在 `A,B,Z` 中 3 个单项式,代入 `u,v,w,s` 后差式 7 项;不重算冻结包络的根间隙展开 |
| **P5 基本非负实根性**: `additive_splits hBB`;`EvenPolynomialRoots` 两个方向;论文 Lemma 3.8(5) | Sym 的加法保持→偶性→平方变量下降 | 直接应用缺无条件的 BB 稳定性保持证据;根几何桥不提供它。文献中此数学事实已知 | **有 hBB 时能,bind-only;当前无条件不能** | 只到基础类,仍容纳 Q4。不是新的研究实施靶 | 组合/稳定性结构;缺的是可消费定理,不是一个大型 ring 等式 |
| **P6 首个 Hankel 主块**: P1、P3;商非负/乘法单调;Newton 前两矩 | 两个 (B2) 相乘→`L_m` 下界→正首主元 | 无;高阶主子式未受控制 | **能,bind-only**;纸面规范化+精确符号复算,无端到端 Lean 主张 | 验证一块必要条件;不能解 m≥3 | `L_m` 分子展开 5 项,其中立方因子 4 项且 `m=t+2` 后仍 4 项;不展开矩阵行列式族 |
| **P7 外类保持假设**: P3+P5 ⇒ kernel 保持 | 尝试乘法实根保持,条件不匹配;随后做精确反例探针 | **陈述为假**: Q=(Y-1)²(Y-4) 已反驳 | **不能,但应 reject**,不得派实施去证明 | 处决“二阶界就是所缺结构”的路线 | 输入/输出各 4 个系数;三次判别式标准 5 项 |
| **P8 真正目标**: 同一 r,s 的 (W),Proposition 5.4 的 (R),冻结 Hermite iff | 必须独立控制全部高阶相关系数,或给 R 的实根/交错机制 | 尚无从这些相关性到 R 实根的论证;只知道每条边平方非负仍不足 | **不能,open**;这是保留的研究问题,尚无可执行实施方案 | 若完成可解偶数次数的 Conjecture 5.3 | 组合/结构,不是已找到的大恒等式。没有测得所需最大块,不沿用 2829 项外推 |

P5 的 `不能` 不构成新数学内容或单独派席理由;P7 是假命题;P8 才是未解的原目标。
没有任何 P0-P6 被本席重新标成逃逸见证。P8 的有限数值验证只覆盖上表六例;未验证全称命题。

## 检索、碰撞与验证收据

以下命令在仓根运行;命中数按**匹配行**计,不是定理数。阴性均配同样词界和分组选项的阳性对照。

| 命令 | 匹配行 | exit |
| --- | --- | --- |
| `git grep -n -P '\b(imageCone|image_cone|symmetrize_kurtosis|symmetrize_fourth_moment)\b' -- D5` | 0 | 1 |
| `git grep -n -P '\b(symmetrize|matching_identity|coeff_additiveConvolution)\b' -- D5` | 29 | 0 |
| `rg -n '\b(additiveConvolution|FiniteSymbolCriterion|finiteSymbolTheorem)\b' .lake/packages/mathlib/Mathlib` | 0 | 1 |
| `rg -n '\b(contract|psum_eq_mul_esymm_sub_sum|sq_sum_le_card_mul_sum_sq)\b' .lake/packages/mathlib/Mathlib` | 35 | 0 |
| `rg -n '\b(additiveConvolution|symmetrize|FiniteSymbolCriterion|finiteSymbolTheorem)\b' .lake/packages/mathlib/Mathlib` | 17 | 0 |
| `git grep -n -P '\b(FiniteSymbolCriterion|additive_splits)\b' -- D5` | 8 | 0 |
| `git grep -n -P '\b(newtonHankel_posSemidef_iff_roots_real|centered_quartic_invariant_bounds)\b' -- D5` | 9 | 0 |

17 个宽检索命中逐行检查:是 `SetRel.symmetrize`、uniformity 使用点和自然语言注释,与有限自由多项式不对应。
这些阴性只声明搜索范围内无该拼写命中;没有据此宣称 Mathlib 中不存在任何等价证明。
实际源码检查补足了否定的含义:`additive_splits` 的 `hBB` 参数仍在,不是因为名字未命中就认定缺定理。

碰撞终检:取到 `origin/dev=18f2f73fe95b2690e3838af754fe93362a6683fc` 后,把前两条 `git grep` 命令改为 `... '<pattern>' origin/dev -- D5`,仍为 **0/29**,exit **1/0**。
`git ls-tree -r --name-only origin/dev -- docs/reports/convolution/image-cone-probe-0909.md docs/reports/convolution/image-cone-probe-0909-snippets.lean` 返回 **0 路径**,exit 0。
不移动本席基线、不修改已有冻结件。最终新增数学事实模块 **0**;因当前任务就是尽早拒绝重复绑定,无需抢占新声明地址。

论文检索:对实际提取的 `cmp-v2.txt` 执行 `rg -a -n -i '\bmatching\b'` 为 **0**,exit 1;
同特性的 `rg -a -c -i '\bconvolution\b'` 为 **61**,exit 0。终检显式加 `-a`,避免 PDF 提取文本中 NUL 字符触发二进制文件模式;读数不变。页面全文确实已读取,不是搜索结果摘要。
检索中两个猜测的 Newton 文件路径不存在;随后用 `rg --files ... -g '*Newton*'` 找到实际的 `MvPolynomial/Symmetric/NewtonIdentities.lean` 和 `Constants/Moments/CoefficientNewtonSums.lean`。
初猜 upstream `RealRooted/BorceaBranden.lean` 返回 HTTP 404;读取该提交的 Git tree 后才打开上述真实文件。
这些路径失败没有被当成定理缺失证据。

Lean 验证只执行 `make lean`。临时探针在 `D5/S3/Zeros/Convolution/ImageConeProbe0909.lean` 被默认 glob 收入;验证后原样移为旁边的 `image-cone-probe-0909-snippets.lean`,不成为生产模块。
最终成功为 **exit 0**,`Built ... ImageConeProbe0909 (11s)`、`Build completed successfully (12635 jobs)`;后者含复用任务,不是本次新编译 12635 个模块。
缓存收据 `status=present`,Mathlib/项目 `olean_state=warm`。
没有裸 `lake` 调用,没有更改 `maxHeartbeats`、`maxRecDepth`、构建参数或任何常数。
前六次 `make lean` 为 exit 2:依次涉及全局定理名误加 `Finset`、antidiagonal 的 `Finset.Nat` 命名空间、有限 filter/sum 的显式规范化、`eval/aeval` 的表达式统一、平方嵌套的规范化。最终片段把 Cauchy 原式保留为 `(x²)²`,与 `x⁴` 的区别只是 `ring` 归一化。失败均保留日志,不作为数学反例。

一次性 worker 工件目录:
`/var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/image-cone-probe-0909/attempt-1`。
其中 `cmp-v2.pdf/txt` 为论文原料,`numeric_probe.py`、`numerics.json` 为计算及完整读数,`search_probe.py`、`searches.json` 为逐条检索,`lean-probe-7.log` 为成功日志,`lean-probe.log` 和 `lean-probe-2.log` 至 `-6.log` 为失败记录。
执行的精确算术命令为 `uv run --with sympy python <attempt>/numeric_probe.py`。以下小段可离线在 SymPy 1.14.0 重算两个负校准,无需论文或 GitHub:

```python
import sympy as s
y = s.Symbol('y')
def lam(m, k):
    return s.factorial(k) / s.ff(2*m-k, k) * s.Rational(2*m+1-k, 2*m+1)
for m in range(2, 12):
    a1 = lam(m, 1)*m**2
    a2 = lam(m, 2)*s.binomial(m, 2)**2
    D = s.factor((m-1)*a1**2-2*m*a2)
    expected = -s.Rational(m**3*(m-1)*(8*m**3+4*m-1),
                          2*(2*m-3)*(2*m-1)**2*(2*m+1)**2)
    assert D == expected and D < 0
    print(m, D)
b = [1, 6, 9, 4]
a = [lam(3,k)*b[k]**2 for k in range(4)]
R = s.Poly(sum((-1)**k*a[k]*y**(3-k) for k in range(4)), y)
assert s.Rational(4,15)*b[1]**2-b[2] == s.Rational(3,5)
assert s.discriminant(R) == -s.Rational(662940477,600250)
assert R.count_roots(-s.oo,s.oo) == 1
assert 5*b[1]*b[2]**2-9*b[3]*(4*b[1]**2-5*b[2]) == -1134
```

## 明确未主张

- 未证明 Conjecture 5.3 的任意次数版本,未证明一般 `R` 实根或完整 `H₀(R)` PSD。
- 未给出消去根参数后的完整 `C_m` 不等式/交错/全正性刻画。
- 未把 P1、P3 或 P3+P5 称为充分刻画;后一条已被本席精确反驳。
- 未把 PSD⇔实根这一双向判据当作新的实根机制;未把期望 Hermitian 特征多项式直接当作实根多项式。
- 未声称 `C_m` 是普通凸锥;未把 `z_{2m}`、`Q_m(z_{2m})` 与 `K_m` 混同。
- 未将纸面绑定推导、数值正例或已编译子片段冒充完整一般次数 Lean 定理。
- 未声称联网或仓内检索穷尽所有等价定理。upstream 与本 pin 的兼容性是 `ASSUMED-UNVERIFIED`,本次未构建。
- 未打开论文参考文献 [10]、[19]、[30]、[32] 的原文;涉及这些外部原著的独立核验均为 `ASSUMED-UNVERIFIED`,本报告只引用已打开 CMP 中的陈述。
- 未获得独立评审;本席判形和纸面推导是单席判断,不冒充评审共识。
- 未 deposit、未冻结、未修改 coverage、未开 PR。仅将报告和探针片段提交并推送本席分支;提交身份由 `result.json` 的 `pushed.commits` 给出。
