# 定义逃逸谱完备化
## Definition-Escape Spectrum Completion（DESC）

> **状态**：定义、定理骨架与反模型，v1.0，2026-08-24。  
> **写入纪律**：追加式演化；后续版本只在文末增订，不回写本文既有段落。  
> **母卷关系**：只引用 DECT v1.0 的 §5.3、§6.1、§6.2、§16.2 与 §17.2；本卷独立、结算独立，不回写 DEFINITION_ESCAPE_COMPLETION_THEORY.md。  
> **主张边界**：以下只给定义、定理骨架和显式反模型。测度自上连续、紧致开覆盖与 Szpilrajn 型延伸均借用成熟形状；未完成的解析估计、形式化实现或系统文献检索不标为已证。本卷整体为 suspected-novel。

## 0. 共同语义

令 \((X,\mathcal A)\) 为可测对象空间，\(q:X\to Q\) 为现行概念，\(T:X\to Y\) 为目标，\(\Gamma\) 为定义语言，\(c:\Gamma\to(0,\infty)\) 为有限单定义成本。令

\[
E:=\mathcal E(q;T)=\{(x,y):q(x)=q(y),\ T(x)\ne T(y)\},
\qquad 0<M_0:=\nu(E)<\infty .
\]

对 \(d\in\Gamma\)，令分离集与盲残差为

\[
U_d:=\{(x,y)\in E:d(x)\ne d(y)\},
\qquad
B:=\mathcal B_\Gamma(q;T)=E\cap\bigcap_{d\in\Gamma}\ker d .
\]

对有限族 \(S\Subset\Gamma\)，记

\[
E_S:=E\setminus\bigcup_{d\in S}U_d,
\qquad
C(S):=\sum_{d\in S}c(d),
\qquad
\mathscr F_L:=\{S\Subset\Gamma:C(S)\le L\}.
\]

这里的“有限”始终指有限定义族；不把点态无限联合偷换成有限预算。测度论陈述均在 \(E\) 的残差子空间上解释。

## T1. 预算包络恒等式

定义未归一化预算包络与逃逸谱

\[
M_\Gamma(L):=\inf_{S\in\mathscr F_L}\nu(E_S),
\qquad
\rho_\Gamma(L):=\frac{M_\Gamma(L)}{M_0}.
\]

**定理 T1（下确界包络）**。若每个 \(d\) 的成本有限，则

\[
\boxed{
\inf_{L\ge0}M_\Gamma(L)
=\lim_{L\to\infty}M_\Gamma(L)
=\inf_{S\Subset\Gamma}\nu(E_S)
}
\]

并且

\[
\boxed{
\inf_{L\ge0}\rho_\Gamma(L)
=\lim_{L\to\infty}\rho_\Gamma(L)
=\frac1{M_0}\inf_{S\Subset\Gamma}\nu(E_S).
}
\]

第一等号来自 \(L\mapsto M_\Gamma(L)\) 的单调性；第二等号来自每个有限 \(S\) 都落入某个有限预算层，而每个预算层都是有限族的子类。

**真残差一句**：尚未消去的质量不是某个任意预算点的读数，而是所有有限定义族残差质量的下确界。  
**结案判据一句**：给出任意 \(\varepsilon>0\) 的有限 \(S\) 使 \(\nu(E_S)\le\inf_{F\Subset\Gamma}\nu(E_F)+\varepsilon\)，即核验 T1 的预算包络结案。

## T2. 盲核地板的精确 iff

称 \(\Gamma\) **本质可数生成**，若存在 \(d_1,d_2,\ldots\in\Gamma\) 使

\[
\nu\!\left(\left(E\setminus\bigcup_{n\ge1}U_{d_n}\right)\setminus B\right)=0,
\quad\text{等价地}\quad
\nu\!\left(E\setminus\bigcup_{n\ge1}U_{d_n}\right)=\nu(B).
\]

称 \(\nu\) 在残差链上**自上连续**，若对每个递减可测链 \(A_1\supseteq A_2\supseteq\cdots\subseteq E\)，

\[
\nu(A_n)<\infty,\quad A_\infty:=\bigcap_nA_n
\quad\Longrightarrow\quad
\nu(A_n)\downarrow\nu(A_\infty).
\]

**定理 T2（盲核地板 iff）**。在 \(M_0<\infty\)、本质可数生成与上述自上连续前件下，以下命题等价：

\[
\begin{aligned}
\mathrm{(i)}\quad&\lim_{L\to\infty}\rho_\Gamma(L)=\frac{\nu(B)}{M_0};\\
\mathrm{(ii)}\quad&\forall\varepsilon>0\ \exists S\Subset\Gamma:
\nu(E_S\setminus B)<\varepsilon;\\
\mathrm{(iii)}\quad&\text{对某个本质生成序列 }(d_n),\quad
\nu\!\left(E\setminus\bigcup_{k\le n}U_{d_k}\right)\downarrow\nu(B).
\end{aligned}
\]

证明骨架：令 \(A_n=E_{\{d_1,\ldots,d_n\}}\)，则 \(A_n\downarrow A_\infty\) 且 \(\nu(A_\infty)=\nu(B)\)；自上连续给出 (iii)，T1 给出 (i)，而 (i) 与 (ii) 互相取下确界。反向若 (ii) 失败，则存在 \(\varepsilon_0>0\) 使一切有限 \(S\) 均有 \(\nu(E_S\setminus B)\ge\varepsilon_0\)，从而

\[
\lim_{L\to\infty}\rho_\Gamma(L)
\ge\frac{\nu(B)+\varepsilon_0}{M_0}>
\frac{\nu(B)}{M_0}.
\]

这就是 T4 两个边界反模型的对偶必要性：任一前件被删去，(i) 可能失效。

**真残差一句**：盲核 \(B\) 是无限预算下不可再切割的地板；地板以上的质量必须能由有限切割任意逼近，才不是隐藏的预算缺口。  
**结案判据一句**：下游证明本质生成序列、残差链极限与 (ii) 的有限逼近互相推出，即可判 T2；任一方向失败须给出正质量缺口反模型。

## T3. 有限完备化定理

令 \(E\) 带残差子空间拓扑。假设 \(E\) 紧致，\(B=\varnothing\)，且每个 \(U_d\) 在 \(E\) 中开。

**定理 T3（紧致残差有限完备化）**。存在有限 \(S\Subset\Gamma\) 与有限预算 \(L=C(S)\)，使

\[
E_S=\varnothing,
\qquad
\rho_\Gamma(L)=0.
\]

证明骨架：\(B=\varnothing\) 意味着 \(\{U_d:d\in\Gamma\}\) 覆盖 \(E\)；开性使其为开覆盖；紧致性给出 \(U_{d_1},\ldots,U_{d_m}\) 的有限子覆盖，取 \(S=\{d_1,\ldots,d_m\}\)。这里借用紧致覆盖的成熟定理形，不把解析紧致性或定义连续性冒领为仓库已证事实。

**真残差一句**：盲残差为空只说明逐点可分，紧致性才把逐点见证压成统一有限预算。  
**结案判据一句**：给出 \(E\) 的紧致性证书、各 \(U_d\) 的开性证书与 \(B=\varnothing\) 的覆盖证书，机器核验有限子覆盖及其成本和，即结案 T3。

## T4. 两个边界反模型

### T4(a) 删除可数性：单点切割反模型

取 \(X=[0,1]\times\{0,1\}\)，\(q(t,i)=t\)，\(T(t,i)=i\)。令双向残差边为

\[
e_t^+:=((t,0),(t,1)),\qquad e_t^-:=((t,1),(t,0)),
\qquad E=\{e_t^+,e_t^-:t\in[0,1]\},
\]

并以 Lebesgue 测度与双向均匀权重推前，故 \(M_0=1\)。对每个 \(t\in[0,1]\) 定义

\[
d_t(s,i):=\begin{cases}i,&s=t,\\0,&s\ne t.\end{cases}
\]

于是

\[
U_{d_t}=\{e_t^+,e_t^-\},
\qquad
B=E\setminus\bigcup_{t\in[0,1]}U_{d_t}=\varnothing,
\qquad
\nu(E_S)=1\quad(S\Subset\Gamma).
\]

令 \(c(d_t)=1\)。定义族不可数、测度有限，然而任一有限预算只含有限个单点切割，

\[
\rho_\Gamma(L)=1\quad(L<\infty),
\qquad
\lim_{L\to\infty}\rho_\Gamma(L)=1\ne0=\frac{\nu(B)}{M_0}.
\]

**真残差一句**：逐点没有盲核不等于有限预算能看见正测度的残差。  
**结案判据一句**：机器复现 \(U_{d_t}=\{e_t^+,e_t^-\}\)、有限并集零测与全族并集为 \(E\)，即判定“删可数性”反模型成立。

### T4(b) 删除自上连续：自由超滤权重反模型

取 \(X=\mathbb N\times\{0,1\}\)，令 \(q(n,i)=n\)、\(T(n,i)=i\)，并写 \(e_n^+=((n,0),(n,1))\)、\(e_n^-=((n,1),(n,0))\)。令

\[
d_n(k,i):=\begin{cases}i,&k\le n,\\0,&k>n,\end{cases}
\]

则

\[
E_{\{d_1,\ldots,d_n\}}=\{e_k^+,e_k^-:k>n\},
\qquad
\bigcap_{n\ge1}E_{\{d_1,\ldots,d_n\}}=\varnothing.
\]

令 \(\Gamma=\{d_n:n\ge1\}\)、\(c(d_n)=1\)，则 \(B=\varnothing\)，且任一有限定义族只留下某个尾残差。

取一个自由超滤 \(\mathcal U\) 于 \(\mathbb N\)，定义有限可加权重

\[
\nu(\{e_k^+,e_k^-:k\in A\})=
\begin{cases}
1,&A\in\mathcal U,\\
0,&A\notin\mathcal U.
\end{cases}
\]

每个尾集 \(\{k>n\}\) 属于 \(\mathcal U\)，故

\[
\nu(E_{\{d_1,\ldots,d_n\}})=1\quad(n\ge1),
\qquad
\nu(\varnothing)=0,
\qquad
\rho_\Gamma(L)=1\quad(L<\infty).
\]

这里交集为空而权重恒正，正是删去自上连续后的行为；该权重不是可数可加测度，因而不与 T2 前件冲突。

**真残差一句**：链的集合极限可以为空，而缺少自上连续时质量极限仍可停在正值。  
**结案判据一句**：机器核验尾集递减、交集为空、超滤权重恒为一，即判定“删测度连续性”反模型成立。

> **Lean 形状注（散文，不作代码指控）**：现役 `EscapeWeight` 的公理字段只有 `empty_mass` 与 `mass_nonnegative` 两律；这两律不足以排除 T4(b)。还需显式自上连续或等强的 \(\sigma\)-可加律，方可把该反模型挡在定理前件之外。

## T5. 三分型完备定理

在 T2 的前件下定义三类：

\[
\begin{aligned}
\mathsf{FiniteClosed}
&:\Longleftrightarrow
\exists S\Subset\Gamma,\ C(S)<\infty,\ \nu(E_S)=0;\\
\mathsf{AsymptoticClosed}
&:\Longleftrightarrow
\neg\mathsf{FiniteClosed}
\ \wedge\ \lim_{L\to\infty}\rho_\Gamma(L)=0;\\
\mathsf{StructurallyIncomplete}
&:\Longleftrightarrow
\lim_{L\to\infty}\rho_\Gamma(L)>0.
\end{aligned}
\]

**定理 T5（三分型）**。上述三类两两互斥且穷尽所有满足 T2 前件的 \((q,T,\Gamma,\nu,c)\)。更精确地，T2 给出

\[
\lim_{L\to\infty}\rho_\Gamma(L)=\frac{\nu(B)}{M_0};
\]

若 \(\nu(B)>0\)，则结构不完备；若 \(\nu(B)=0\)，则要么存在有限零残差族而为有限闭合，要么不存在而必为渐近闭合。有限闭合的定义使用“存在零残差见证”，避免把仅有下确界为零误报为有限达成；在预算最优值取到的模型中，它等价于某个 \(L\) 有 \(\rho_\Gamma(L)=0\)。

**真残差一句**：三类只由盲核地板与是否存在有限零残差见证决定，不把“预算尚未跑够”另立第四类。  
**结案判据一句**：机器给出 \(B\) 的质量、有限零残差见证或其不存在的证明，并核验三式之一且排除另外两式，即结案 T5。

## 结算承诺 \(K_n\)

循 DECT 第49部 \(K_n\) 的七元字段形状，固定本卷的冻结对象：

\[
\boxed{
K_n=(\operatorname{target\_chain},\operatorname{scope},\operatorname{comparator},
\operatorname{test\_plan},\operatorname{baseline},\operatorname{weight\_spec},
\operatorname{committed\_artifact}).
}
\]

\[
\begin{aligned}
\operatorname{target\_chain}
&=\text{GoalArtifact 持续正交产出}\to\text{DECT v1.0 §§5--6 缺口};\\
\operatorname{scope}
&=\text{有限/可数模型；排除次模贪心（#2904 在飞）、盲核阻断（#2938）、动态邻域（#3039），}\\
&\qquad\text{以及已吸收的反单调与 0--1 界};\\
\operatorname{comparator}
&=\text{本卷消化 atoms 由下游 prove/refute/statement-revise 结案，失败可判};\\
\operatorname{test\_plan}
&=\text{逐定理核验公式对、条件闭包、T4 机器反模型与 T5 终态互斥穷尽};\\
\operatorname{baseline}
&=\text{DECT v1.0 §§5.3、6.1、6.2 的缺口表述，不预记新定理为真};\\
\operatorname{weight\_spec}
&=\text{有限残差质量；T2 要求自上连续，T4(b) 明示违反该前件};\\
\operatorname{committed\_artifact}
&=\{T1,T2,T3,T4,T5\};\\
\operatorname{falsifiable\_prediction}
&=\text{五个定理中至少三个在不扩作用域下由 kernel 定理或机器反模型结案}.
\end{aligned}
\]

这里的“至少三个”以五个定理 (T1,T2,T3,T4,T5) 为结算单元；T4 的两个反模型均须进入同一 T4 atom 的证据闭包。下游必须给每单元唯一 atom 地址与终态；达到阈值前记 open，不把未结案写成通过。

## 新颖性与借用边界

测度的自上连续、紧致空间的有限开子覆盖、自由超滤产生的非可数可加权重与 Szpilrajn 型延伸，均只借用成熟理论形状；本卷把它们接到预算逃逸谱与盲核地板的组合是 suspected-novel，未作系统文献检索。T1--T5 是可形式化的定义/骨架；除显式前件下的集合与测度推理外，不声称已有 Lean 证明或具体解析估计。

# 追加账本

## v1.0 — 2026-08-24

首次存入：

- 预算包络的下确界恒等式与归一化残差质量；
- 本质可数生成、自上连续与盲核地板的精确 iff；
- 紧致残差子空间上的有限完备化定理；
- 删除可数性与删除自上连续的两个显式反模型；
- 有限闭合、渐近闭合、结构不完备的三分型定理；
- \(K_n\) 结算承诺、作用域排除与可证伪结案预测。

后续增订继续严格追加于本节之后。
