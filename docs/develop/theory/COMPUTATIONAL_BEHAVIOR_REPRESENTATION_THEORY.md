# 有限观察下的计算与行为表示理论

> 本卷按 `generic-v1` 的字节规则摄入。已有正文合入后保持不变；修正与扩充使用文末追加锚之后的新编号章节。本文只提供数学参考输入，形式化声明及其证明项不以本文编号作为权威地址。

## 1. 数学约定与证明来源

**约定 1.1（载体、动作与复合方向）。** 在 ZFC 中工作，全部载体均为集合。记 $\epsilon$ 为空词，$\Sigma^*$ 为字母表 $\Sigma$ 上的有限词集，$uv$ 为先读 $u$ 再读 $v$。状态更新按此顺序复合，即 $F_{uv}=F_v\circ F_u$。除明确增加的条件外，不预设状态有限、观察可计算、矩阵非负或动力学收缩。

**约定 1.2（出处与证明身份）。** 本卷使用仓库 `theory-volume-template` 的新卷结构。数学写作、来源核对及实施由本会话 ChatGPT 单席串行完成，复核为同席自查，没有独立模型评审。仓库来源固定于 `6009fa739f232152b73131c472f48c1e8c8b1886`。下文给出纸面证明；引用既有 Lean 声明只说明相应构件的来源，不构成本卷整体的 Lean 验证收据。形式化及冻结状态由仓库账本给出。文献支持与本卷推导的范围在第 7 节分别列明，不主张全球首创。

## 2. 全未来行为、最大不动点与最小表示

**定义 2.1（行为关系与精确表示）。** 给定非空状态集 $X$、总确定性更新 $F_a:X\to X$（$a\in\Sigma$）及观察 $o:X\to Y$，定义
\[
 B(x)(w)=o(F_wx),\qquad
 x\sim y\iff B(x)=B(y).
\]
对关系 $R\subseteq X^2$ 定义
\[
 \Phi(R)=\ker o\cap\bigcap_{a\in\Sigma}(F_a\times F_a)^{-1}(R).
\]
精确表示由 $r:X\to S$、$G_a:S_r\to S_r$ 及 $\bar o:S_r\to Y$ 构成，其中 $S_r=r[X]$，并要求
\[
 rF_a=G_ar,\qquad o=\bar o r.
\]
所有下降映射只在实际像上定义。

**定理 2.2（最大行为关系与最粗精确表示）。** 关系 $\sim$ 是 $\Phi$ 在关系包含序下的最大不动点，也是 $\ker o$ 内被全部 $F_a$ 保持的最大等价关系。商 $Q=X/{\sim}$ 携带唯一的更新及读出，使投影 $\pi:X\to Q$ 成为精确表示。对任意精确表示 $r$，存在唯一满射 $p:S_r\to Q$ 满足
\[
 \pi=pr,\qquad pG_a=\bar F_ap,\qquad \bar o_Qp=\bar o.
\]
因此若 $Q$ 有限，任何精确表示至少有 $|Q|$ 个实际状态；若内部存储为固定长度 $b$ 比特，则 $2^b\ge |Q|$。

**证明。** 由空词得到 $\sim\subseteq\ker o$。若 $x\sim y$，比较所有词 $aw$，即得 $F_ax\sim F_ay$。反之，当前观察相同且全部一步后继满足 $\sim$，便使空词及全部非空词的观察相同，故 $\sim=\Phi(\sim)$。

若任意关系 $R$ 满足 $R\subseteq\Phi(R)$，对词长归纳可得 $xRy$ 蕴含 $o(F_wx)=o(F_wy)$，于是 $R\subseteq\sim$。这同时证明最大不动点性质；$\sim$ 作为函数核本身是等价关系。

置 $\bar F_a([x])=[F_ax]$、$\bar o_Q([x])=o(x)$。前述保持性保证良定义。对于精确表示，$r(x)=r(y)$ 经任意动作词更新后仍相等，读出后得到 $x\sim y$。因此 $p(r(x))=[x]$ 与代表元无关。它满射、满足所列交换式，并由 $r$ 对 $S_r$ 的满射性唯一确定。有限基数及比特下界随即成立。这里关系的最大性对应商的最粗性，比较的对象和偏序不同。证毕。[^repo-behavior][^lit-rutten]

**定理 2.3（有限细化、区分词与显式比较界）。** 另设 $|X|=n<\infty$、$|\Sigma|=k<\infty$，令
\[
 R_0=\ker o,\qquad R_{h+1}=\Phi(R_h),\qquad c_0=|X/R_0|.
\]
则
\[
 xR_hy\iff \forall |w|\le h,\ o(F_wx)=o(F_wy).
\]
存在 $h_*\le n-c_0$ 使 $R_{h_*}=R_{h_*+1}=\sim$。任意不等价状态有长度至多 $n-c_0$ 的区分词。若状态及动作显式枚举，转移查表、观察值相等测试及类标号比较均为单位成本，按每轮签名
\[
 \bigl(o(x),([F_ax]_{R_h})_{a\in\Sigma}\bigr)
\]
逐对比较的算法，使用 $O((k+1)n^2(n-c_0+1))$ 次上述基本操作即可求出该商。

**证明。** 词长归纳给出 $R_h$ 的表达式。每个 $R_h$ 是等价关系，且 $R_{h+1}\subseteq R_h$。一次严格细化至少增加一个等价类，类数至多为 $n$。若某轮相等，则递推式使以后全部相等；稳定关系保持全部动作并包含全部未来要求，由定理 2.2 等于 $\sim$。故严格细化至多 $n-c_0$ 次。

区分词可随细化恢复：观察值不同使用空词；若某动作 $a$ 的后继在旧分区中不同，就在后继的旧区分词前加 $a$。因而第 $h$ 轮分开的状态有长度至多 $h$ 的证据。

一轮至多比较 $n^2$ 对、每对至多比较 $k+1$ 个签名坐标。加上检测最终稳定的一轮，总轮数至多 $n-c_0+1$；初始观察分区的比较也被所给量级覆盖。此界以声明的输入表示和基本操作为口径，不包含任意实数相等判定的实现成本。证毕。[^repo-closure]

## 3. 稀疏输入、相容性与转移一致的状态压缩

**定义 3.1（带承诺输入域及冲突图）。** 设非空 $D\subseteq\Sigma^*$，目标为 $f:D\to Y$。令
\[
 P=\operatorname{Pref}(D)=\{u:\exists v,\ uv\in D\}.
\]
在 $P$ 上定义无向冲突图：不同的 $u,v$ 相邻，当且仅当存在 $w$ 使 $uw,vw\in D$ 且 $f(uw)\ne f(vw)$。对于整数 $s\ge1$，称 $c:P\to\{1,\ldots,s\}$ 是转移一致的适当着色，若相邻顶点颜色不同，并且
\[
 c(u)=c(v),\ ua,va\in P\quad\Longrightarrow\quad c(ua)=c(va)
\]
对全部 $u,v,a$ 成立。域外词不带目标标签，也不被自动解释为拒绝。

**定理 3.2（带承诺域的精确状态刻画）。** 存在一个至多 $s$ 状态的总确定性输出自动机，在全部 $D$ 上输出 $f$，当且仅当冲突图存在至多 $s$ 色的转移一致适当着色。因此最少状态数等于最少转移一致颜色数；普通适当着色只给出必要条件。

**证明。** 给定自动机，将前缀映到读完此前缀所到的状态。相同状态经相同续接会产生相同输出，所以冲突前缀不能同色；确定性又保证所需的转移一致性。

反向，给定着色 $c$。对颜色 $i$ 和动作 $a$，若存在 $u\in P$ 满足 $c(u)=i$ 且 $ua\in P$，令 $\delta(i,a)=c(ua)$。一致性使取值与 $u$ 无关。若不存在此类前缀，任选一个颜色作为后继。对每个颜色 $i$，若有 $u\in D$ 且 $c(u)=i$，令输出为 $f(u)$；取两个这样的词并使用空续接，适当着色保证输出唯一。未出现目标标签的颜色，使用由 $D\ne\varnothing$ 得到的某个 $Y$ 元素。

以 $c(\epsilon)$ 为初态。对 $u\in P$ 的长度归纳，全部中间前缀均属于 $P$，故读完 $u$ 恰到 $c(u)$。于是对 $u\in D$ 输出正确。构造仅使用有限色集，但对任意无限 $D$ 不宣称着色可计算。证毕。

**命题 3.3（稀疏相容性可以不传递）。** 仅要求共同合法续接上的输出一致，不能一般地得到等价关系。

**证明。** 取字母表 $\{a,b,x,y,z\}$，令
\[
 D=\{xa,yb,za\},\qquad f(xa)=f(yb)=0,\quad f(za)=1.
\]
前缀 $x$ 的唯一合法续接为 $a$，$y$ 的为 $b$，$z$ 的为 $a$。因此 $x,y$ 没有共同合法续接，$y,z$ 也没有，二者分别相容；而 $x,z$ 在续接 $a$ 上冲突。这是定义 3.1 中同一个实际输入域的反例。证毕。

**定理 3.4（固定状态预算的有限反驳证据）。** 设 $\Sigma,Y$ 有限且 $Y\ne\varnothing$，固定 $s\ge1$。以下等价：存在至多 $s$ 状态的输出自动机在全部 $D$ 上正确；对每个有限 $E\subseteq D$，存在至多 $s$ 状态的输出自动机在 $E$ 上正确。特别地，若全部 $D$ 上不存在这样的自动机，则某个有限 $E\subseteq D$ 已经排除全部候选。

**证明。** 正向取限制。反向使用逆否命题。把不足 $s$ 状态的自动机补上不可达状态，全部候选均可写成固定状态集 $\{1,\ldots,s\}$ 上的表。候选数量至多为
\[
 s\,s^{s|\Sigma|}|Y|^s,
\]
分别选择初态、转移及输出。若每台候选都在 $D$ 上失败，为每台取一个失败词。有限多个失败词组成 $E$，任何候选都在 $E$ 上失败。

因此，一个忠实编码有限样本约束的 UNSAT 证据，只需另证样本属于 $D$、标签等于 $f$，即可给出全域的状态下界。某一个有限样本集上的 SAT 解只证明该样本集可满足。上述有限性证明没有给出有效的反例词长度界。证毕。[^lit-digits]

**命题 3.5（唯一续接区分族的字母表上界）。** 设有限指标集 $I$ 的前缀 $u_i$ 满足：每个 $u_i$ 至多有一个续接使 $u_iw\in D$；对于每个 $i\ne j$，存在共同合法续接 $w_{ij}$，使 $f(u_iw_{ij})\ne f(u_jw_{ij})$。则 $|I|\le |Y|$，其中 $Y$ 有限且非空。

**证明。** 若 $|I|\le1$，结论直接成立。否则固定不同的 $i_0,j_0$。唯一性先使同一 $i$ 所参与的全部 $w_{ij}$ 相等，再经共同端点 $i_0$ 使所有不同指标对的续接都等于同一个 $w$。此时 $i\mapsto f(u_iw)$ 单射，得到基数界。该假设要求所选全部前缀的全域续接唯一性；有限实验中观察到大量唯一续接不提供这一全称前提。证毕。[^repo-rigid]

## 4. 近似预测的静态下界与动态约束

**定义 4.1（有限窗口响应及静态编码）。** 设 $\Sigma$ 有限，$Y$ 为度量空间，$H\in\mathbb N$。定义
\[
 B_H(x)=\bigl(o(F_wx)\bigr)_{|w|\le H},\qquad
 d_H(x,y)=\max_{|w|\le H}d_Y(o(F_wx),o(F_wy)).
\]
一个静态 $\varepsilon$ 预测编码包括 $e:X\to C$ 及解码器 $D:C\times\Sigma^{\le H}\to Y$，并要求每个 $x,w$ 满足
\[
 d_Y(D(e(x),w),o(F_wx))\le\varepsilon.
\]
此定义不要求存在从 $e(x)$ 计算 $e(F_ax)$ 的更新。

**定理 4.2（打包下界与静态覆盖上界）。** 若有限集 $E\subseteq X$ 的不同元素满足 $d_H(x,y)>2\varepsilon$，则任何静态 $\varepsilon$ 预测编码都有 $|C|\ge |E|$。若响应集 $B_H[X]$ 在最大度量下有 $s$ 个半径 $\varepsilon$ 的覆盖球，球心属于 $Y^{\Sigma^{\le H}}$，则存在 $s$ 标签的静态 $\varepsilon$ 编码。

**证明。** 若 $e(x)=e(y)$，对每个 $w$，两个真实输出与同一个解码输出的距离均不超过 $\varepsilon$。三角不等式给 $d_H(x,y)\le2\varepsilon$，所以 $e$ 在 $E$ 上单射。对于上界，将 $x$ 编到一个覆盖 $B_H(x)$ 的球心编号，并在词 $w$ 处输出该球心的对应坐标即可。两个论证均只处理静态编码；球心覆盖没有提供动作更新的一致性。证毕。

**定理 4.3（延迟脉冲的静态与可更新记忆分离）。** 对 $m\in\mathbb N$，取
\[
 X=\mathbb N,\qquad F(n)=n+1,\qquad o_m(n)=\mathbf1_{\{n=m\}}\in\mathbb R.
\]
给定 $H\in\mathbb N$ 及 $0\le\varepsilon<1/2$，静态 $H$ 窗口 $\varepsilon$ 编码的最少标签数为
\[
 \min(H,m)+2.
\]
若要求一个固定有限状态更新器，从每个初态 $n$ 的编码出发，在任意后续时刻仍以误差至多 $\varepsilon$ 预测当前输出，则其最少状态数为 $m+2$。

**证明。** 对 $n$，窗口向量为 $(o_m(n+j))_{0\le j\le H}$。非零向量恰为单个 $1$ 出现在位置 $j=0,\ldots,\min(H,m)$ 的向量；此外有全零向量。因此共有 $\min(H,m)+2$ 种响应，任意两个的最大距离为 $1$。定理 4.2 给出相同数量的下界，直接存储响应类型达到上界。

对于可更新编码，考虑 $n=0,\ldots,m+1$。若 $i<j$ 被编码为同一内部状态，在继续 $m-i$ 步后，预测器内部状态仍相同，而真实输出分别为 $1$ 与 $0$。同一个预测值不能同时距两者小于 $1/2$，故这 $m+2$ 个初态必须分开。反向，使用状态 $0,\ldots,m$ 和一个吸收状态，将 $n\le m$ 编为自身、$n>m$ 编到吸收状态；逐步递增并从 $m$ 进入吸收状态，只在 $m$ 输出 $1$。该机器精确预测全部时刻。固定 $H$ 后令 $m$ 增大，得到任意大的状态数差距。证毕。

**定理 4.4（收缩动力学的有限状态近似上界）。** 设 $(X,d_X)$ 为度量空间，全部 $F_a$ 具有共同 Lipschitz 常数 $L\ge0$，观察 $o$ 的 Lipschitz 常数为 $M\ge0$。设点集 $z_1,\ldots,z_s\in X$ 及映射 $Q:X\to\{1,\ldots,s\}$ 满足
\[
 d_X(x,z_{Q(x)})\le\delta\quad\text{对全部 }x\in X.
\]
定义有限状态更新及输出
\[
 \widehat F_a(i)=Q(F_az_i),\qquad \widehat o(i)=o(z_i),
\]
初始状态取 $Q(x)$。对任意长度 $t$ 的动作词，输出误差至多为
\[
 M\delta\sum_{j=0}^{t}L^j.
\]
特别地，若 $L<1$，则全部时刻的误差一致不超过 $M\delta/(1-L)$。

**证明。** 令 $x_t$ 为真实轨道，$z_{i_t}$ 为近似轨道，$e_t=d_X(x_t,z_{i_t})$。初始 $e_0\le\delta$。对于实际执行的任意动作 $a_t$，有
\[
 e_{t+1}\le d_X(F_{a_t}x_t,F_{a_t}z_{i_t})
             +d_X(F_{a_t}z_{i_t},z_{Q(F_{a_t}z_{i_t})})
          \le Le_t+\delta.
\]
归纳得到 $e_t\le\delta\sum_{j=0}^tL^j$，再应用观察的 Lipschitz 界。收缩情形对几何级数求和。此构造给出数学上的有限状态表示；只有再给出 $Q(F_az_i)$ 和所需输出的有效求值条件，才能把它解释为可执行构造。证毕。

## 5. 行动词 Hankel 秩与有限维实现

**定义 5.1（词响应、残余空间及线性实现）。** 设 $K$ 为域，$\Sigma$ 有限，$f:\Sigma^*\to K$。定义
\[
 f_u(v)=f(uv),\qquad V_f=\operatorname{span}_K\{f_u:u\in\Sigma^*\},\qquad
 H_f(u,v)=f(uv).
\]
称 $f$ 具有有限 Hankel 秩 $r$，若 $V_f$ 有限维且 $\dim_K V_f=r$。一个 $d$ 维线性实现由行向量 $\alpha\in K^{1\times d}$、矩阵 $A_a\in K^{d\times d}$ 及列向量 $\beta\in K^{d\times1}$ 给出，满足
\[
 f(a_1\cdots a_t)=\alpha A_{a_1}\cdots A_{a_t}\beta.
\]
允许 $d=0$ 表示零响应。这里的维数不等同于有限自动机的离散状态基数，也不指定系数的存储精度。

**引理 5.2（有限评价分离）。** 若 $g_1,\ldots,g_r:T\to K$ 线性无关且 $r\ge1$，则存在 $t_1,\ldots,t_r\in T$，使矩阵 $(g_i(t_j))_{i,j=1}^r$ 可逆。

**证明。** 在 $W=\operatorname{span}\{g_i\}$ 上考虑评价泛函 $\operatorname{ev}_t$。若这些泛函的张成空间是 $W^*$ 的真子空间，有限维线性代数给出非零 $g\in W$ 被全部评价泛函消去，因而 $g(t)=0$ 对每个 $t$ 成立，与 $g\ne0$ 矛盾。因此评价泛函张成 $W^*$。从中选取 $r$ 个为基，其在 $g_i$ 基下的矩阵可逆。证毕。

**定理 5.3（有限 Hankel 秩等于最小线性维数）。** 响应 $f$ 存在有限维线性实现，当且仅当 $V_f$ 有限维；最小实现维数等于 $\dim_KV_f$。

**证明。** 若给定 $d$ 维实现，每个残余函数 $f_u$ 都形如 $v\mapsto\gamma A_v\beta$，其中 $\gamma=\alpha A_u$。映射 $\gamma\mapsto(v\mapsto\gamma A_v\beta)$ 是从 $K^{1\times d}$ 到函数空间的线性映射，故 $\dim V_f\le d$。

反向，在函数空间上定义线性算子
\[
 (T_ag)(v)=g(av).
\]
它满足 $T_af_u=f_{ua}$，因此保持 $V_f$。以 $f_\epsilon$ 为初态，以 $g\mapsto g(\epsilon)$ 为读出，在 $V_f$ 的一组基下使用行坐标，令 $A_a$ 表示 $T_a$。连续读入 $a_1,\ldots,a_t$ 后，状态是 $f_{a_1\cdots a_t}$，读出为 $f(a_1\cdots a_t)$。这构造一个 $\dim V_f$ 维实现。若 $V_f=\{0\}$，则 $f=0$，使用零维实现。结合前向下界得到最小性。证毕。[^lit-kiefer][^repo-hankel]

**定理 5.4（完整秩假设下的有限块恢复）。** 设 $\dim_KV_f=r\ge1$。若词族 $p_1,\ldots,p_r$ 与 $s_1,\ldots,s_r$ 使
\[
 H=(f(p_is_j))_{i,j}\in K^{r\times r}
\]
可逆，定义
\[
 H_a=(f(p_i a s_j))_{i,j},\qquad
 h=(f(s_1),\ldots,f(s_r)),\qquad
 b=(f(p_1),\ldots,f(p_r))^{\mathsf T}.
\]
则
\[
 \alpha=hH^{-1},\qquad A_a=H_aH^{-1},\qquad\beta=b
\]
给出对所有词正确的最小实现。这样的两组词总是存在。

**证明。** $H$ 可逆使 $f_{p_1},\ldots,f_{p_r}$ 线性无关；由全局维数假设，它们是 $V_f$ 的基。以此基写 $g$ 的行坐标为 $c$，则 $g$ 在 $s_j$ 上的评价向量为 $cH$。作用 $T_a$ 后评价向量为 $cH_a$，故新坐标为 $cH_aH^{-1}$。$f_\epsilon$ 的评价向量是 $h$，所以初始坐标为 $hH^{-1}$；在空词的评价列是 $b$。代入定理 5.3 的构造即得全部词上的公式。

为证明存在性，从残余生成族中选取 $r$ 个为基，再用引理 5.2 选择分离该基的 $r$ 个续接。这里 $H$ 的可逆性证明样本中的 $r$ 个残余独立；它没有单独证明全局秩至多 $r$。证毕。[^lit-kiefer]

**命题 5.5（任意有限数据不能单独确定全局秩）。** 在 $K=\mathbb Q$、$\Sigma=\{a\}$ 上，对每个 $N\in\mathbb N$ 都存在两个有限秩响应，在全部长度至多 $N$ 的词上相同，但最小线性维数不同。即使这些样本包含一个非零的一阶 Hankel 块，该结论仍成立。

**证明。** 取 $m>N$，令
\[
 f(a^n)=1,\qquad g(a^n)=1+\mathbf1_{\{n=m\}}.
\]
两者在指定样本上相等，且共同的 $f(\epsilon)=g(\epsilon)=1$ 给出可逆的一阶块。$f$ 的残余空间由常值 $1$ 生成，维数为 $1$。

对于 $g$，当 $n>m$ 时残余 $g_{a^n}$ 为常值 $1$；当 $0\le n\le m$ 时，它为常值 $1$ 加上在续接长度 $m-n$ 处的单位脉冲。因此 $V_g$ 由常值 $1$ 与位置 $0,\ldots,m$ 的 $m+1$ 个单位脉冲张成，并包含全部这些函数。它们线性无关：先在大于 $m$ 的位置评价，消去常值系数；再逐个评价位置 $0,\ldots,m$，消去脉冲系数。所以 $\dim V_g=m+2$。定理 5.3 给出所称的最小维数差异。证毕。

## 6. 有限观察完成的存在性与统一可计算界

**定义 6.1（紧致有限观察塔）。** 给定非空紧致空间 $X$、有限离散集 $Q_n$ 及连续满射 $q_n:X\to Q_n$，满足
\[
 q_n=p_nq_{n+1}.
\]
要求各纤维 $q_n^{-1}(\{z\})$ 合在一起形成 $X$ 的拓扑基。于是 $q_N(x)=q_N(y)$ 且 $N\ge n$ 蕴含 $q_n(x)=q_n(y)$。

**定理 6.2（连续有限读出的有限层因子化）。** 在定义 6.1 的条件下，若 $Y$ 是有限离散空间，$f:X\to Y$ 连续，则存在 $N$ 及唯一 $\bar f:Q_N\to Y$ 使 $f=\bar f q_N$。

**证明。** 对每个 $x$，开集 $f^{-1}(\{f(x)\})$ 含一个以 $x$ 为中心的观察纤维 $U_x=q_{n_x}^{-1}(\{q_{n_x}(x)\})$。紧致性给出有限子覆盖 $U_{x_1},\ldots,U_{x_t}$，令 $N=\max_i n_{x_i}$。若 $q_N(x)=q_N(y)$，取包含 $x$ 的某个 $U_{x_i}$，塔相容性使 $y$ 也在其中，故 $f(x)=f(y)$。于是 $\bar f(q_N(x))=f(x)$ 良定义，并由满射性唯一确定。证毕。[^repo-completion]

**推论 6.3（有限行动窗口具有有限观察层）。** 在定理 6.2 的条件下，另设 $\Sigma$ 有限、$F_a:X\to X$ 连续，且 $o:X\to Y$ 连续。对每个 $H\in\mathbb N$，存在 $N(H)$ 使
\[
 q_{N(H)}(x)=q_{N(H)}(y)
 \quad\Longrightarrow\quad
 \forall |w|\le H,\ o(F_wx)=o(F_wy).
\]

**证明。** 对每个有限词 $w$，复合 $oF_w$ 连续，由定理 6.2 经某层 $q_{N_w}$ 因子化。由于 $\Sigma$ 有限，长度至多 $H$ 的词只有有限多个，令 $N(H)=\max_{|w|\le H}N_w$ 即可。此证明给出每个窗口的存在性，没有提供有限观察塔、连续映射及有限子覆盖的有效表示。证毕。

**定理 6.4（各实例均有有限状态表示，仍可没有统一可计算界）。** 固定一种可有效模拟、停机问题不可判定的程序编号 $e\in\mathbb N$。令
\[
 b_e(n)=\mathbf1_{\{\text{程序 }e\text{ 首次在第 }n\text{ 步停机}\}}.
\]
则 $(e,n)\mapsto b_e(n)$ 是总可计算函数；每个序列 $b_e$ 均能由有限状态输出自动机在输入 $a^n$ 上产生。但不存在总可计算函数 $s(e)$，对每个 $e$ 上界该序列的最小状态数；也不存在总可计算函数 $N(e)$，对每个 $e$ 保证
\[
 \bigl(\forall n\le N(e),\ b_e(n)=0\bigr)
 \quad\Longrightarrow\quad
 \forall n,\ b_e(n)=0.
\]

**证明。** 模拟前 $n$ 步并记录首次停机时刻即可计算 $b_e(n)$。若程序永不停机，序列恒零，由一状态机器产生。若首次在 $t$ 停机，序列是延迟脉冲，定理 4.3 在误差 $0$ 下给出最小状态数 $t+2$，并给出达到此数的机器。因此每个实例确实存在有限表示。

若 $s(e)$ 是所称的可计算上界，任何会停机的程序都满足 $t+2\le s(e)$。计算 $s(e)$ 后模拟至该界，未停机者即可判定永不停机，与停机不可判定矛盾。若存在第二种 $N(e)$，计算该值并检验有限前缀；出现 $1$ 即停机，全零则由保证判定永不停机，同样矛盾。

该反例的输入是程序编号及其有限时间求值规则，没有提供显式的有限状态转移表，也没有提供定义 6.1 的有效紧致呈示。它不否定定理 2.3 在显式有限输入上的算法，也不否定在另外给出有效紧致性和可计算连续性数据后求取模数的结果。证毕。[^repo-rice][^lit-computable]

## 7. 证明引用与适用范围

**出处 7.1（经典结果与本卷推导）。** 定理 2.2 的行为核、商及不动点结构使用已有观察者理论和经典余代数背景。定理 5.3 的秩与最小性对应经典加权自动机结果；定理 5.4 使用行残余坐标推导有限块公式。定理 2.3、第 3 节、第 4 节、引理 5.2、命题 5.5 与第 6 节的具体陈述按正文证明列为 `repo-derived`，其中命题 3.5 已有直接源码构件。这个分类表示本卷的推导来源，不表示这些结果在文献中首次出现。以下文献列为 `literature-attested` 的范围限于各项注明的内容。

[^repo-behavior]: 固定源码：[ControlledBehaviorUniversality.lean](https://github.com/the-omega-institute/trureturing/blob/6009fa739f232152b73131c472f48c1e8c8b1886/D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.lean)，`controlled_behavior_universal_property` 给出有限载体上的受控行为商泛性质及基数界。另见 [StrictOneHoleContexts.lean](https://github.com/the-omega-institute/trureturing/blob/6009fa739f232152b73131c472f48c1e8c8b1886/D5/S3/ConceptDynamics/Observation/StrictOneHoleContexts.lean) 的 `contextual_equivalence_is_greatest`，其对象为带全部实际槽参数的严格部分操作；本文第 2 节采用总确定性动作。

[^repo-closure]: 固定理论来源：[OBSERVER_CLOSURE_SPECTRUM.md](https://github.com/the-omega-institute/trureturing/blob/6009fa739f232152b73131c472f48c1e8c8b1886/docs/develop/theory/OBSERVER_CLOSURE_SPECTRUM.md) 的未来核塔及有限稳定推导；[CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md](https://github.com/the-omega-institute/trureturing/blob/6009fa739f232152b73131c472f48c1e8c8b1886/docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md) 的有限细化与区分词。本文定理 2.3 另写明基本操作计费口径。

[^repo-rigid]: 固定源码：[DFAOStateLowerBound.lean](https://github.com/the-omega-institute/trureturing/blob/6009fa739f232152b73131c472f48c1e8c8b1886/D5/S0/Automata/DFAOStateLowerBound.lean)，`state_lower_bound_of_distinguishing_family`；[DistinguishingFamilyCardinalityBound.lean](https://github.com/the-omega-institute/trureturing/blob/6009fa739f232152b73131c472f48c1e8c8b1886/D5/S0/Automata/DistinguishingFamilyCardinalityBound.lean)，`card_le_card_output_of_rigid_continuations`。引用保留唯一续接的全称前提。

[^repo-hankel]: 固定源码：[SequenceHankelRealization.lean](https://github.com/the-omega-institute/trureturing/blob/6009fa739f232152b73131c472f48c1e8c8b1886/D5/S3/Observer/Hankel/SequenceHankelRealization.lean)，使用单时间索引尾空间构造实现；[ExecutableHoKalman.lean](https://github.com/the-omega-institute/trureturing/blob/6009fa739f232152b73131c472f48c1e8c8b1886/D5/S3/Observer/Hankel/ExecutableHoKalman.lean)，`run_exact_recovery` 要求固定阶数参考实现及样本匹配；[HoKalmanPredictionBudget.lean](https://github.com/the-omega-institute/trureturing/blob/6009fa739f232152b73131c472f48c1e8c8b1886/D5/S3/Observer/Hankel/HoKalmanPredictionBudget.lean)，`run_prediction_error_bound` 给出带前提的有限样本误差传播。本文第 5 节采用词索引，不把这些源码引用当作多动作版本已被形式化的证据。

[^repo-completion]: 固定理论来源：[RECURSIVE_RELATIONAL_OBSERVATION.md](https://github.com/the-omega-institute/trureturing/blob/6009fa739f232152b73131c472f48c1e8c8b1886/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md)，有限观察塔、真实像与完成空间的区分。本文定理 6.2 直接假设紧致载体以及观察纤维组成拓扑基，并在该假设下证明有限层因子化。

[^repo-rice]: 固定源码：[ClosureUndecidable.lean](https://github.com/the-omega-institute/trureturing/blob/6009fa739f232152b73131c472f48c1e8c8b1886/D5/S0/Computability/ClosureUndecidable.lean)，`closure_reading_unreachable` 是 Mathlib Rice 定理的明确封装。本文定理 6.4 独立写出延迟脉冲归约，不声称该具体归约已有 Lean 证明项。

[^lit-rutten]: J. J. M. M. Rutten，*Universal coalgebra: a theory of systems*，CWI Report CS-R9652，1996，[作者机构条目](https://ir.cwi.nl/pub/4802)。`literature-attested` 范围：状态系统、行为关系及余代数的经典框架。本文定理 2.2 给出所用确定性特例的完整证明，不借此引用推广到任意概率或非确定性语义。

[^lit-digits]: Aaron Barnoff、Curtis Bright、Jeffrey Shallit，*Using finite automata to compute the base-b representation of the golden ratio and other quadratic irrationals*，arXiv:2405.02727v1，2024，[原文](https://arxiv.org/html/2405.02727v1)。`literature-attested` 范围：算术编码上的输出自动机及部分实例的 SAT 最小性方法。本文第 3 节没有证明该论文任何尚未解决实例的最小状态数。

[^lit-kiefer]: Stefan Kiefer，*Notes on Equivalence and Minimization of Weighted Automata*，arXiv:2009.01217v1，2020，[第 3、4 节](https://arxiv.org/html/2009.01217v1)。`literature-attested` 范围：域上加权自动机的 Hankel 秩、最小性及 Hankel 实现。本文有限块公式按行残余坐标重新推导；未引入非负、随机或量子实现的约束。

[^lit-computable]: Vasco Brattka、Guido Gherardi，*Effective Choice and Boundedness Principles in Computable Analysis*，arXiv:0905.4685，[作者预印本](https://arxiv.org/abs/0905.4685)。`literature-attested` 范围：数学存在原理需要按输入输出表示区分计算内容。本文第 6 节不声称对所定义问题给出 Weihrauch 度分类，所用不可计算结论仅为正文证明的具体停机归约。

## 追加锚（本行以下为增补区）
