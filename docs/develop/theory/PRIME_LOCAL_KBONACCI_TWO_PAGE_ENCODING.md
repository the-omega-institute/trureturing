# 原子双页 (k)-bonacci 局域判素编码：有限最优性与自定界扩展

本文是 `docs/develop/theory/` 下的参考输入卷，记录一套在有限窗口和全体自然数上的二进制编码构造。Lean 内核代码才是本仓库的数学真值来源；本文没有宣称自身已经由 Lean 验证或冻结。

**来源与产地。** 作者类型：mixed（用户提供的数学草稿与 Codex 在会话 `01a0e7b7-2660-7eb0-9ab3-7f57b3643aff` 中的继续推理）；日期：2026-09-28。本文保留构造的假设、证明边界和未验证状态，不把外部运行读数当作内核证明。

## 1. 任务合同与合法词

固定 (Nge2)，令

$$
X_N={0,1,ldots,N},qquad
\chi_{\mathbb P}(n)=
\begin{cases}
1,&n\text{ 为素数},\\
0,&n\text{ 为非素数}.
\end{cases}
$$

置

$$
X_{N,b}=\{x_{b,0}<\cdots<x_{b,M_b-1}\},qquad
M_0=A_N,quad M_1=P_N,quad A_N+P_N=N+1.
$$

对 (Nge2)，有

$$
1le P_Nle A_N.
$$

证明是直接计数：除 (2) 外的素数全为奇数，所以
(P_Nle\lfloor(N+1)/2\rfloor)，从而 (A_Nge P_N)。

固定 (kge2)。定义整数权重

$$
G_j^{(k)}=2^jquad(0le j<k),qquad
G_j^{(k)}=\sum_{h=1}^{k}G_{j-h}^{(k)}quad(jge k).
$$

令 (mathcal W_m^{(k)}) 为长度恰为 (m)、不含 (1^k) 的二进制词。对高位在前的词 (w=b_{m-1}cdots b_0)，定义

$$
\operatorname{val}_k(w)=\sum_{j=0}^{m-1}b_jG_j^{(k)}.
$$

这采用仓内 [RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_RESOLUTION.md](RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_RESOLUTION.md) 的整数权重归一化；它不是 Perron 根的实数负幂展开。

## theorem 1.1: 合法词的区间双射

**Claim status: open.** 对每个 (mge0)，

$$
\operatorname{val}_k:\mathcal W_m^{(k)}
\overset{\sim}{\longrightarrow}
\{0,1,\ldots,G_m^{(k)}-1\}
$$

是双射，并保持字典序与整数大小顺序。

当 (m<k) 时这是固定长度二进制唯一性。(mge k) 时，每个合法词唯一写成 (1^j0v)，其中 (0le j<k)。令

$$
S_0=0,qquad S_j=\sum_{h=1}^{j}G_{m-h}^{(k)}.
$$

前缀 (1^j0) 的词恰好表示

$$
[S_j,S_{j+1})\cap\mathbb Z,
$$
因为 (S_{j+1}=S_j+G_{m-j-1}^{(k)})，而 (S_k=G_m^{(k)})。这些区间首尾相接且不交，给出双射和顺序保持性。

仓内已有同一整数区间结论的参考位置是 TM.374–TM.380；本卷不把它重复登记为已冻结 Lean 事实。

## proposition 1.2: 首位分支容量

**Claim status: open.** 令

$$
C_b(k,m)=|\{w\in\mathcal W_m^{(k)}:w_1=b\}|.
$$

对 (mge1)，有

$$
C_0(k,m)=G_{m-1}^{(k)},qquad
C_1(k,m)=G_m^{(k)}-G_{m-1}^{(k)}.
$$

并且

$$
 w_1=0\iff\operatorname{val}_k(w)<G_{m-1}^{(k)},qquad
 w_1=1\iff G_{m-1}^{(k)}le\operatorname{val}_k(w)<G_m^{(k)}.
$$

此外 (C_1(k,m)le C_0(k,m))，且对 (mge2)，

$$
C_1(k,m)ge G_{m-2}^{(k)}.
$$

前者来自把首位 (1) 改为 (0) 的单射；后者来自合法词族 (10u)。

## 2. 有限窗口的双页编码

定义可行码长为满足

$$
A_Nle G_{m-1}^{(k)},qquad
P_Nle G_m^{(k)}-G_{m-1}^{(k)}
$$
的 (mge1)。记最小可行码长为 (m_*(N,k))。

令 (Z_{k,m}) 为定理 1.1 的逆映射。对 (n=x_{b,r})，定义

$$
E_{N,k,m}(n)=Z_{k,m}\bigl(r+bG_{m-1}^{(k)}\bigr).
$$

## theorem 2.1: 有限双页编码的可逆性与局域判素

**Claim status: open.** 对每个可行的 (N,k,m)，(E_{N,k,m}) 是单射，码字属于 (mathcal W_m^{(k)})，且

$$
E_{N,k,m}(n)_1=\chi_{\mathbb P}(n).
$$

定义实际码集

$$
\mathcal C_{N,k,m}=E_{N,k,m}(X_N).
$$

对 (w\in\mathcal C_{N,k,m})，令 (t=\operatorname{val}_k(w))，并定义

$$
D_{N,k,m}(w)=
\begin{cases}
x_{0,t},&t<G_{m-1}^{(k)},\\
x_{1,t-G_{m-1}^{(k)}},&t\ge G_{m-1}^{(k)}.
\end{cases}
$$

超出实际分配范围的词必须拒绝。于是

$$
D_{N,k,m}\circ E_{N,k,m}=\operatorname{id}_{X_N},qquad
E_{N,k,m}\circ D_{N,k,m}=\operatorname{id}_{\mathcal C_{N,k,m}}.
$$

“读取一次即可判素”只在输入已承诺属于实际码集时成立；对任意收到的位串，还必须检查长度、禁串和实际序号范围。

## theorem 2.2: 固定宽度最优性

**Claim status: open.** 在首位必须等于素数指示值的固定长度合同下，长度 (m) 编码存在，当且仅当

$$
A_Nle C_0(k,m),qquad P_Nle C_1(k,m).
$$

因此

$$
\min_E|E|=m_*(N,k).
$$

必要性是两页分别需要占用不同合法词；充分性由定理 2.1 的地址分配给出。该最优性比较所有满足合同的编码，不限于类内递增的具体排列。

## corollary 2.3: 局域化最多增加一位

**Claim status: open.** 定义只保存完整身份的最小宽度

$$
 m_0(N,k)=\min\{m\ge0:G_m^{(k)}\ge N+1\}.
$$

则

$$
 m_0(N,k)le m_*(N,k)le m_0(N,k)+1.
$$

上界使用 (G_m^{(k)}le2G_{m-1}^{(k)}) 以及 (A_Nge P_N)。

## corollary 2.4: 精确二择一码长判据

**Claim status: open.** 对 (Nge2)，令 (m_0=m_0(N,k))。则

$$
 m_*(N,k)=
\begin{cases}
 m_0,&A_Nle G_{m_0-1}^{(k)} \text{且}\ P_Nle G_{m_0}^{(k)}-G_{m_0-1}^{(k)},\\
 m_0+1,&\text{否则}.
\end{cases}
$$

因此局域化的额外位数由身份最短宽度处的两页容量溢出完全决定。

## theorem 2.5: 判素读取次数下界

**Claim status: open.** 在确定性、零错误、按位读取且输入承诺属于实际码集的模型中，判素读取次数恰为一次。一次读取第一位足够；零次读取不可能，因为 (X_N) 同时包含 (2) 与 (0)，它们任务值不同。

## 3. 跨阶与全体二进制下界

令

$$
 m_{\mathrm{bin}}^*(N)=1+\lceil\log_2 A_N\rceil.
$$

## theorem 3.1: 跨所有阶数的固定宽度下界

**Claim status: open.** 有

$$
\min_{k\ge2}m_*(N,k)=m_{\mathrm{bin}}^*(N).
$$

下界来自每个 (k)-bonacci 码仍是二进制词。上界取任意 (k>m_{\mathrm{bin}}^*(N))，此时长度 (m_{\mathrm{bin}}^*(N)) 的词不可能含 (k) 个连续的 (1)，所以两个首位分支各有 (2^{m-1}) 个位置。

## proposition 3.2: 最小达到阶数的容量判据

**Claim status: open.** 有

$$
 k_{\min}(N)=
\min\left\{k\ge2:
 A_Nle G_{m_{\mathrm{bin}}^*(N)-1}^{(k)},\quad
 P_Nle G_{m_{\mathrm{bin}}^*(N)}^{(k)}-G_{m_{\mathrm{bin}}^*(N)-1}^{(k)}
\right\}.
$$

固定 (m) 时，随着 (k) 增大，合法词语言扩大，两个首位分支容量均不减，因此该集合是向上的。

## proposition 3.3: 同序号配对

**Claim status: open.** 对 (0le r<P_N)，有

$$
E_{N,k,m}(x_{0,r})=0Z_{k,m-1}(r),qquad
E_{N,k,m}(x_{1,r})=1Z_{k,m-1}(r),
$$

从而两码字的 Hamming 距离恰为 (1)。这里使用 (P_Nle C_1(k,m)) 和两个地址分支的共同尾码。

## 4. 全体自然数的自定界双页码

将非素数和素数分别递增枚举为 (a_0<a_1<cdots) 与 (p_0<p_1<cdots)。每个 (nin\mathbb N) 唯一写成 (n=a_r) 或 (n=p_r)，记页标为 (bin\{0,1\})。令

$$
\ell_k(r)=\min\{\ell\ge0:r<G_\ell^{(k)}\},qquad
z_k(r)=Z_{k,\ell_k(r)}(r).
$$

对正整数 (t)，写

$$
\operatorname{bin}(t)=1u,qquad q=\lfloor\log_2t\rfloor,qquad |u|=q.
$$

定义

$$
 h(0)=00,qquad h(1)=01,qquad
 \eta(t)=0^q1h(u).
$$

## theorem 4.1: 改进长度字段

**Claim status: open.** (eta) 是前缀自由编码，能唯一恢复 (t)，不含连续两个 (1)，且

$$
|\eta(t)|=3\lfloor\log_2t\rfloor+1.
$$

证明：先数前导零得到 (q)，再读标记 (1)，最后读取恰好 (q) 个二位块 (00) 或 (01)。标记 (1) 后的第一位必为 (0)，每个块内部也无 (11)，故不存在连续两个 (1)。

## theorem 4.2: 改进的全域帧

**Claim status: open.** 定义

$$
 E'_{\infty,k}(n)=b,0,\eta(\ell_k(r)+1),0,z_k(r).
$$

则该码集满足：

1. 每个码字不含 (1^k)；
2. 码集前缀自由并有唯一解码器；
3. 第一位等于 (\chi_{\mathbb P}(n))；
4. (a_r) 与 (p_r) 的码字只差第一位；
5. 码长为

$$
|E'_{\infty,k}(n)|
=\ell_k(r)+3\lfloor\log_2(\ell_k(r)+1)\rfloor+4.
$$

全域帧的解码顺序是：读取页标和重置零；解码 (eta(ell+1)) 得到 (ell)；读取第二个重置零；读取恰好 (ell) 位正文；检查正文合法且为最短长度；最后返回 (a_r) 或 (p_r)。

与使用 (h(\gamma(t))) 的旧长度字段相比，新帧逐码字缩短

$$
\lfloor\log_2(\ell_k(r)+1)\rfloor+1
$$
位。这里是帧格式的严格改进，不宣称所有变长前缀码中的全局最优性。

## proposition 4.3: 连续比特流的禁串保持

**Claim status: open.** 定义

$$
\widehat E'_{\infty,k}(n)=E'_{\infty,k}(n),0.
$$

任意有限或无限顺序拼接这些帧都不含 (1^k)，因为每帧末尾的固定零切断跨帧连续一。解码器读取一帧后跳过该固定零。

## 5. 语义运输的边界

## proposition 5.1: 窗口和阶数变化的语义兼容

**Claim status: open.** 若 (Nle M)，定义

$$
R_{N,k}^{M,\ell}=E_{M,\ell}\circ D_{N,k}.
$$

则

$$
D_{M,\ell}\circ R_{N,k}^{M,\ell}=D_{N,k},qquad
R_{N,k}^{M,\ell}(w)_1=w_1.
$$

若再有 (Mle L)，则

$$
R_{M,\ell}^{L,h}\circ R_{N,k}^{M,\ell}=R_{N,k}^{L,h}.
$$

这些是整数语义的兼容性，不是不同窗口之间的字面前缀包含关系。

## proposition 5.2: 指定运算的准确运输

**Claim status: open.** 对部分运算 (T:S\subseteq X_N^r\to X_N)，定义

$$
\widehat T(w_1,\ldots,w_r)=E_{N,k}\bigl(T(D_{N,k}(w_1),\ldots,D_{N,k}(w_r))\bigr).
$$

在解码后属于 (S) 的定义域上，

$$
D_{N,k}(\widehat T(w_1,\ldots,w_r))
=T(D_{N,k}(w_1),\ldots,D_{N,k}(w_r)).
$$

该命题只保证语义运输，不保证运算本身只访问第一位。

## proposition 5.3: 乘法原子页的分类解释

**Claim status: open.** 对正整数 (n)，唯一素因子分解给出

$$
\chi_{\mathbb P}(n)=1
\iff\sum_pv_p(n)=1.
$$

因此素数页可解释为乘法原子页；这个解释不扩展到 (n=0)，也不改变前述有限编码的地址语义。

## 6. 结论范围

本文建立的是“任务分类 (	o) 首位分支 (	o) 类内 (k)-bonacci 地址”的编码关系。有限部分的真值边界是首位合同、实际码集承诺和固定 (k)；全域部分的自定界帧是一个可逆构造，改进帧缩短了原长度字段但没有声称全局变长最优。

本文没有把编码生成成本、素数枚举成本或完整数值解码成本纳入码长目标；也没有把首位判素扩展成任意输入的有效性认证。文中所有 `Claim status: open` 均表示尚未由当前冻结账本给出 Lean 证明。

## 追加锚（本行以下为增补区）
