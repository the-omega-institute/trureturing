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

## 8. 增补一·可更新预测器的前向不变覆盖

**本批导航。** 本批接续 PR #8330 的 `ae239ec5cdd39f52889ab0a7d1f62eb3325a3456`，并核对 `dev` 的 `e984c77223b55a3cda565c7694098e436926183d`。第 8 节刻画可更新近似预测器所需的覆盖条件；第 9 节把第 4.3 条的有限窗口分离加强为无理旋转上的全未来分离，并给出黄金旋转的有限时间状态复杂度；第 10 节在收缩编码上给出达到下界的有限状态构造。第 11 节列本批证明来源。原有条目及其字节保持不变。

**定义 8.1（统一可更新预测与状态计费）。** 设 $X\ne\varnothing$，动作更新 $F_a:X\to X$ 总定义且确定，观察 $o:X\to Y$ 取值于度量空间。一个有限状态预测器由非空有限集 $S$、初始化 $e:X\to S$、总确定性更新 $G_a:S\to S$ 及输出 $h:S\to Y$ 组成。误差 $\varepsilon\ge0$ 的全未来要求为
\[
 d_Y\bigl(h(G_w(e(x))),o(F_w(x))\bigr)\le\varepsilon
 \quad(x\in X,\ w\in\Sigma^*).
\]
有限时间要求将词限制为 $|w|\le H$。初始化后只能接收动作，不能再次访问真实状态，也没有不计入 $S$ 的外部时钟、计数器或随机源；更新及输出均与时刻无关。预测器可以依赖预先给定的 $H$ 和 $\varepsilon$。所计资源是 $|S|$，或编码其当前标签的 $\lceil\log_2|S|\rceil$ 比特；转移表、输出常数、初始化算法及数值精度的存储成本另计。此定义允许 $G_we(x)\ne e(F_wx)$。

**定理 8.2（有限状态近似等价于确定性前向不变覆盖）。** 存在至多 $s\ge1$ 个状态、满足定义 8.1 全未来要求的预测器，当且仅当存在至多 $s$ 个非空集合 $C_i\subseteq X$ 覆盖 $X$，为每个 $i,a$ 指定唯一后继编号 $\delta(i,a)$，并存在 $y_i\in Y$，满足
\[
 F_a[C_i]\subseteq C_{\delta(i,a)},\qquad
 \sup_{x\in C_i}d_Y(o(x),y_i)\le\varepsilon.
\]
这些集合允许重叠。若定义
\[
 d_\infty(x,x')=\sup_{w\in\Sigma^*}d_Y(o(F_wx),o(F_wx'))\in[0,\infty],
\]
则每个 $C_i$ 的 $d_\infty$ 直径至多为 $2\varepsilon$。

**证明。** 给定预测器，对每个状态 $i$ 定义
\[
 C_i=\{F_wx:x\in X,\ w\in\Sigma^*,\ G_we(x)=i\}.
\]
删除空集合及其未到达状态。空词使剩余集合覆盖 $X$。若 $z=F_wx\in C_i$，则 $F_az=F_{wa}x\in C_{G_a(i)}$，故前向包含成立且后继集合非空。预测保证又给 $d_Y(o(z),h(i))\le\varepsilon$，可取 $y_i=h(i)$。同一真实状态可以由不同历史到达，因此这些 $C_i$ 没有被假定为初始化映射的纤维。

反向，对每个 $x$ 选择一个包含它的 $C_i$ 作为初始标签，并用 $\delta$ 更新。沿词长归纳，真实状态始终属于当前标签对应的集合，因而输出误差始终至多为 $\varepsilon$。对于同属 $C_i$ 的两个真实状态，执行同一个动作词后仍同属同一个后继集合；它们的观察各距同一 $y_j$ 至多 $\varepsilon$，故距离至多为 $2\varepsilon$。对所有词取上确界即可。这个证明只给同动作的一侧模拟，不附加未证明的双模拟或有效可计算性。证毕。[^tcs-symbolic]

## 9. 无理旋转的有限摘要、无限预测与算术状态界

**定义 9.1（圆周旋转及其预测复杂度）。** 令 $\mathbb T=\mathbb R/\mathbb Z$，$\alpha\in\mathbb R\setminus\mathbb Q$，唯一动作是
\[
 F_\alpha(x)=x+\alpha\pmod1,\qquad o(x)=\exp(2\pi i x)\in\mathbb C.
\]
输出度量为复数绝对值，允许预测输出位于整个 $\mathbb C$。对 $H\in\mathbb N$、$\varepsilon>0$，记 $S_{H,\varepsilon}(\alpha)$ 为同时对全部 $x\in\mathbb T$、$0\le n\le H$ 满足定义 8.1 的最少状态数。该最小值存在，例如将有限相位网格与长度 $H+1$ 的显式计时状态组合即可。对 $t\in\mathbb R$，记 $\|t\|_{\mathbb T}=\min_{k\in\mathbb Z}|t-k|$。

**定理 9.2（全未来可有限压缩与永久有限状态预测的分离）。** 此旋转系统满足
\[
 d_\infty(x,y)=|\exp(2\pi ix)-\exp(2\pi iy)|.
\]
因此对任意 $\varepsilon>0$，存在有限标签静态编码，以及接收标签和外部查询 $n$ 的解码器，使全部 $x,n$ 的预测误差不超过 $\varepsilon$。然而对任意固定初相位 $x$，任何有限状态自主预测器的全时间最坏误差均至少为 $1$；一状态、恒输出 $0$ 达到误差 $1$。特别地，$\varepsilon<1$ 时不存在定义 8.1 的全未来有限状态预测器，也不存在定理 8.2 的有限前向不变覆盖。

**证明。** 两个相位的后续复数输出共同乘上单位复数 $\exp(2\pi in\alpha)$，距离保持不变，给出 $d_\infty$ 的等式。取整数 $M\ge\pi/\varepsilon$，把 $x$ 编到最近的相位 $j/M$，并令
\[
 D(j,n)=\exp(2\pi i(j/M+n\alpha)).
\]
圆周相位误差至多 $1/(2M)$，故每个时刻的输出误差至多 $\pi/M\le\varepsilon$。该静态解码器读取外部 $n$，其计算资源没有被有限标签数约束。

对有限状态自主预测器，轨道在某个 $\mu\ge0$ 后以周期 $p\ge1$ 重复。在时刻 $\mu+kp$，预测输出恒为某个 $c\in\mathbb C$。由于 $p\alpha$ 无理，真实输出在单位圆上稠密；仓库的 `irrational_rotation_interval_sampling` 亦直接推出这个经典稠密性。连续性给出
\[
 \sup_{k\ge0}|\exp(2\pi i(x+(\mu+kp)\alpha))-c|
 =\sup_{|z|=1}|z-c|=1+|c|\ge1.
\]
最后，一状态输出 $0$ 与真实输出的距离恒为 $1$。定理 8.2 给出覆盖不存在的结论。证毕。[^tcs-rotation]

**定理 9.3（有限预测时间的算术下界）。** 设 $0<\varepsilon<1/2$，置
\[
 a_\varepsilon=\frac{\arcsin\varepsilon}{\pi},\qquad
 \Psi_\alpha(s)=\max_{1\le p\le s}\frac{p}{\|p\alpha\|_{\mathbb T}}.
\]
若一个 $s$ 状态自主预测器从某个固定初相位起，在 $0\le n\le H$ 内误差至多为 $\varepsilon$，则
\[
 H<s+a_\varepsilon\Psi_\alpha(s).
\]
若另有 $c>0$、$\nu\ge1$ 满足 $\|p\alpha\|_{\mathbb T}\ge c p^{-\nu}$ 对全部正整数 $p$ 成立，则
\[
 H<s+\frac{a_\varepsilon}{c}s^{\nu+1}.
\]
这些结论对允许任意复数输出常数的预测器仍成立。

**证明。** 若 $H<s$，结论立即成立。否则有限确定性轨道有 $\mu\ge0,p\ge1$ 满足 $\mu+p\le s$，并从时刻 $\mu$ 起周期为 $p$。令
\[
 K=\left\lfloor\frac{H-\mu}{p}\right\rfloor\ge1.
\]
时刻 $\mu,\mu+p,\ldots,\mu+Kp$ 的预测输出相同。把每个真实输出与时刻 $\mu$ 的真实输出比较，由三角不等式得到
\[
 |1-\exp(2\pi i k p\alpha)|\le2\varepsilon,
 \qquad \|kp\alpha\|_{\mathbb T}\le a_\varepsilon
 \quad(1\le k\le K).
\]
置 $\delta=\|p\alpha\|_{\mathbb T}>0$，首先有 $\delta\le a_\varepsilon$。若 $K\delta>a_\varepsilon$，取最小 $j\le K$ 使 $j\delta>a_\varepsilon$，则
\[
 a_\varepsilon<j\delta\le a_\varepsilon+\delta
 \le2a_\varepsilon<1-a_\varepsilon.
\]
这里 $a_\varepsilon<1/6$。由于 $p\alpha$ 模整数等于 $\delta$ 或 $-\delta$，上述区间迫使 $\|jp\alpha\|_{\mathbb T}>a_\varepsilon$，矛盾。因此 $K\delta\le a_\varepsilon$，从而
\[
 H<\mu+(K+1)p
 \le s+a_\varepsilon\frac{p}{\|p\alpha\|_{\mathbb T}}
 \le s+a_\varepsilon\Psi_\alpha(s).
\]
代入所给丢番图下界，并用 $p\le s$，即得第二个不等式。证毕。

**定理 9.4（有理相位时钟的构造上界）。** 对任意整数 $p$、正整数 $q$ 及 $H\ge0$，存在一个对全部初相位统一适用的 $q$ 状态预测器，其时间 $0\le n\le H$ 内的误差至多为
\[
 \frac{\pi}{q}+2\pi H\left|\alpha-\frac pq\right|.
\]

**证明。** 用 $\mathbb Z/q\mathbb Z$ 作状态集，更新 $j\mapsto j+p$，状态 $j$ 输出 $\exp(2\pi ij/q)$。把初相位 $x$ 编到最近的 $j/q$。真实相位与预测相位在第 $n$ 步的圆周距离至多为
\[
 \frac1{2q}+n\left|\alpha-\frac pq\right|.
\]
映射 $t\mapsto\exp(2\pi it)$ 对圆周距离的 Lipschitz 常数为 $2\pi$，得到所列界。更新表与输出表固定，不读取外部时刻。该构造无需假设 $p,q$ 互素。证毕。

**定理 9.5（黄金旋转的匹配平方根状态律）。** 令
\[
 \varphi=\frac{1+\sqrt5}{2},\qquad \alpha=\varphi^{-1},\qquad
 0<\varepsilon<1/2.
\]
对 $s=S_{H,\varepsilon}(\alpha)$ 有
\[
 H<s+3a_\varepsilon s^2,
\]
并且
\[
 s<2\max\left\{2,\frac{2\pi}{\varepsilon},
                      \sqrt{\frac{4\pi H}{\varepsilon}}\right\}.
\]
因此在固定 $\varepsilon$、$H\to\infty$ 的口径下，
\[
 S_{H,\varepsilon}(\varphi^{-1})=\Theta_\varepsilon(\sqrt H),\qquad
 \left\lceil\log_2 S_{H,\varepsilon}(\varphi^{-1})\right\rceil
 =\tfrac12\log_2 H+O_\varepsilon(1).
\]
这里的比特数仅指定义 8.1 中的当前内部状态。

**证明。** 对正整数 $q$，取距离 $q\alpha$ 最近的整数 $p$。因 $0<\alpha<1$，可取 $0\le p\le q$。利用 $\alpha$ 的共轭为 $-\varphi$，有
\[
 (p-q\alpha)(p+q\varphi)=p^2+pq-q^2\in\mathbb Z\setminus\{0\}.
\]
而 $0<p+q\varphi\le(1+\varphi)q<3q$，故
\[
 \|q\alpha\|_{\mathbb T}>\frac1{3q}.
\]
在定理 9.3 中取 $c=1/3,\nu=1$ 即得下界。

令 Fibonacci 数满足 $F_0=0,F_1=1,F_{n+2}=F_{n+1}+F_n$。由 $\alpha^2=1-\alpha$ 及递推归纳，
\[
 F_{n+1}\alpha-F_n=(-1)^n\alpha^{n+1}.
\]
另外 $F_k<\varphi^k$ 对全部 $k\ge0$ 成立，同样由递推归纳得到。因此对 $p=F_n,q=F_{n+1}$ 有
\[
 \left|\alpha-\frac pq\right|
 =\frac{\alpha^{n+1}}{q}<\frac1{q^2}.
\]
这些正分母趋于无穷，相邻分母比至多为 $2$。置
\[
 T=\max\left\{2,\frac{2\pi}{\varepsilon},
                  \sqrt{\frac{4\pi H}{\varepsilon}}\right\},
\]
选取第一个满足 $q\ge T$ 的 Fibonacci 分母，则 $q<2T$。定理 9.4 给出的误差小于或等于
\[
 \frac\pi q+\frac{2\pi H}{q^2}\le\frac\varepsilon2+\frac\varepsilon2.
\]
于是 $S_{H,\varepsilon}\le q<2T$。对固定 $\varepsilon$，上界为 $O_\varepsilon(\sqrt H)$；下界中 $s\ge1$ 使 $s+3a_\varepsilon s^2\le(1+3a_\varepsilon)s^2$，从而给出 $\Omega_\varepsilon(\sqrt H)$。取对数得到最后一个式子。证明同时给出可构造的时钟，没有从试验拟合渐近阶。证毕。[^tcs-golden]

**命题 9.6（有限线性维数不能替代有限离散状态数）。** 固定初相位 $0$，无理旋转的复数序列 $z_n=\exp(2\pi in\alpha)$ 在 $\mathbb C$ 上的 Hankel 秩及最小线性实现维数均为 $1$。把输出视为二维实向量 $(\operatorname{Re}z_n,\operatorname{Im}z_n)$，其最小实线性实现维数为 $2$。这两种精确有限维实现与定理 9.2 的有限状态障碍同时成立。

**证明。** 置 $\zeta=\exp(2\pi i\alpha)$。Hankel 矩阵为 $H(i,j)=\zeta^i\zeta^j$，它秩至多为 $1$，且 $H(0,0)=1$，故恰为 $1$。一个复寄存器按 $z\mapsto\zeta z$ 更新即可精确实现该序列。

在实数上，二维旋转矩阵及初始向量 $(1,0)$ 给出实现。第零与第一步的真实输出分别为 $(1,0)$ 及 $(\cos(2\pi\alpha),\sin(2\pi\alpha))$。无理性保证 $\sin(2\pi\alpha)\ne0$，两向量线性无关；一维实状态空间经固定线性读出所得的全部输出只能位于一条直线上，故不可能实现。有限维寄存器允许无穷多个取值，而定义 8.1 计数的是实际可区分的离散内部状态。上述维数结论不提供有限精度实现的永久误差保证。证毕。

## 10. 收缩编码的精确最小记忆与黄金特例

**定义 10.1（两分支收缩编码）。** 给定 $0<\lambda<1/2$，令
\[
 K_\lambda=\left\{(1-\lambda)\sum_{j=0}^\infty b_j\lambda^j:
                         b_j\in\{0,1\}\right\}\subseteq[0,1],
\]
动作及观察为
\[
 F_a(x)=(1-\lambda)a+\lambda x\quad(a\in\{0,1\}),\qquad o(x)=x\in\mathbb R.
\]
对 $\varepsilon>0$，记 $N_\varepsilon(\lambda)$ 为对全部初态及全部动作词、误差至多 $\varepsilon$ 的最少预测器状态数，采用定义 8.1 的计费口径。数字串按从当前最高权位到较低权位的顺序书写；执行动作 $a$ 把 $a$ 加到数字串开头。

**定理 10.2（收缩数字前缀达到状态下界）。** 对任意整数 $L\ge1$，若
\[
 \frac{\lambda^L}{2}\le\varepsilon
       <\frac{(1-\lambda)\lambda^{L-1}}2,
\]
则
\[
 N_\varepsilon(\lambda)=2^L.
\]
上界由保存前 $L$ 个数字、每步前插新动作并舍弃最后一位的确定性状态机达到。特别地，精度 $\varepsilon_L=\lambda^L/2$ 时恰好需要 $L$ 比特当前状态，且此保证覆盖任意长的动作序列。

**证明。** 数字编码唯一。事实上，若两条无限数字串首次在位置 $k$ 不同，最高差异项的绝对值为 $(1-\lambda)\lambda^k$，全部后续项差异的绝对值之和至多为 $\lambda^{k+1}$，净差至少为 $(1-2\lambda)\lambda^k>0$。

对 $u=(u_0,\ldots,u_{L-1})\in\{0,1\}^L$ 置
\[
 P(u)=(1-\lambda)\sum_{j=0}^{L-1}u_j\lambda^j.
\]
具有前缀 $u$ 的全部状态位于 $P(u)+\lambda^L K_\lambda$，因而位于长度为 $\lambda^L$ 的区间 $[P(u),P(u)+\lambda^L]$。令机器状态为 $u$，输出为区间中点 $P(u)+\lambda^L/2$，动作 $a$ 把 $u$ 更新为 $(a,u_0,\ldots,u_{L-2})$。这正是当前真实状态的新前缀，因此全部时刻的输出误差均至多为 $\lambda^L/2$，得到 $2^L$ 状态上界。

为证明下界，取 $2^L$ 个真实初态 $P(u)$，即所有尾部恒零的编码。两个前缀首次在位置 $k\le L-1$ 不同，较大的前缀与较小的前缀之间的差至少为
\[
 (1-\lambda)\lambda^k-(1-\lambda)\sum_{j=k+1}^{L-1}\lambda^j
 =(1-2\lambda)\lambda^k+\lambda^L
 \ge(1-\lambda)\lambda^{L-1}.
\]
若两个这样的初态使用同一个机器状态，其第零步预测相同，三角不等式要求真实输出间距至多 $2\varepsilon$，与严格上界假设矛盾。因此初始化在这 $2^L$ 个初态上单射，至少需要 $2^L$ 个状态。由于 $\lambda<1/2$，$\varepsilon_L$ 确实属于所列区间。证毕。

**推论 10.3（状态复杂度指数及黄金收缩实例）。** 对每个固定 $0<\lambda<1/2$，
\[
 \lim_{\varepsilon\downarrow0}
 \frac{\log N_\varepsilon(\lambda)}{\log(1/\varepsilon)}
 =\frac{\log2}{\log(1/\lambda)}.
\]
特别地，取 $\lambda=\varphi^{-2}$，则
\[
 N_{1/(2\varphi^{2L})}(\varphi^{-2})=2^L\quad(L\ge1),
\]
而复杂度指数为 $\log2/(2\log\varphi)$。

**证明。** 对足够小的 $\varepsilon>0$，令 $m\ge2$ 为满足 $\lambda^m/2\le\varepsilon$ 的最小整数，则
\[
 \lambda^m/2\le\varepsilon<\lambda^{m-1}/2.
\]
长度 $m$ 的前缀机器给出 $N_\varepsilon\le2^m$。长度 $m-1$ 的尾零初态族两两距离至少为 $(1-\lambda)\lambda^{m-2}$，而
\[
 2\varepsilon<\lambda^{m-1}<(1-\lambda)\lambda^{m-2},
\]
故同样的第零步单射论证给出 $N_\varepsilon\ge2^{m-1}$。于是 $\log N_\varepsilon$ 被 $(m-1)\log2$ 与 $m\log2$ 夹住，$\log(1/\varepsilon)$ 与 $m\log(1/\lambda)$ 相差有界量，取极限即得。

因为 $\varphi^2>2$，黄金特例满足 $0<\varphi^{-2}<1/2$；在定理 10.2 中代入即可。这个实例的前缀被动作确定更新，而第 9 节旋转的相位持续累积；相同黄金常数没有把两种动力学的资源界识别为同一结论。证毕。

## 11. 本批的数学来源与核验范围

**出处 11.1（逐项来源）。** 第 8.2 条是本批从确定性模拟语义推出的覆盖刻画，相关有限符号模型背景见下列文献；第 9.2 条的稠密性复用仓库无理旋转取样结论，其余证明直接给出；第 9.3 至 9.5 条的周期、丢番图下界及有理时钟构造在本批组成匹配状态界；第 9.6 条使用第 5 节的线性实现语义并直接证明所用特例；第 10.2 至 10.3 条由数字尾项、前缀更新和分离点计数直接推出。上述八条结果均按本批证明列为 `repo-derived`，其中被引用的经典构件单列为 `literature-attested`。此分类不宣告全球首创。

[^tcs-symbolic]: Giordano Pola、Antoine Girard、Paulo Tabuada，*Approximately bisimilar symbolic models for nonlinear control systems*，[arXiv:0706.0246](https://arxiv.org/abs/0706.0246)；Antoine Girard、Giordano Pola、Paulo Tabuada，*Approximately bisimilar symbolic models for incrementally stable switched systems*，[arXiv:0807.5022v1](https://arxiv.org/abs/0807.5022v1)。`literature-attested` 范围为增量稳定条件下的符号近似模型。检索读取了作者预印本条目的摘要和版本信息；这些来源不作为本批覆盖等价、黄金平方根界或精确 $2^L$ 状态数的证明，也不把本文一侧模拟称为双模拟。

[^tcs-rotation]: 固定源码：[D5/S1/Phase/IntervalSampling.lean](https://github.com/the-omega-institute/trureturing/blob/e984c77223b55a3cda565c7694098e436926183d/D5/S1/Phase/IntervalSampling.lean)，声明 `irrational_rotation_interval_sampling` 对任意无理步长、任意指定初相位给出半开区间的极限取样频率。正长度区间的正频率推出稠密性；对周期子序列使用无理步长 $p\alpha$。该源码没有被当作第 9.3 至 9.5 条状态复杂度已完成形式化的证据。

[^tcs-golden]: 固定源码：[D5/S1/Depth/GoldenContinuedFraction.lean](https://github.com/the-omega-institute/trureturing/blob/e984c77223b55a3cda565c7694098e436926183d/D5/S1/Depth/GoldenContinuedFraction.lean)，声明 `golden_ratio_continued_fraction` 给出黄金连分数的全一系数。第 9.5 条另以共轭乘积和 Fibonacci 递推完整证明其实际使用的误差不等式，无需假设某个未提供的最优逼近常数。

**约定 11.2（本批产地与证明身份）。** 本批使用 `theory-volume-template/APPEND.md`，数学推导、来源核对、文字实施和有限自检均由本会话 ChatGPT 单席串行完成；没有独立模型评审或外部作者审定。全部新条目是带完整假设的纸面证明。本批没有新增 Lean 或 Scribe，没有运行 Lean kernel、canonical `make ingest` 或生成消化状态；文件前缀的字节核对只验证尾部追加，不替代 atom 账目核验。有限数值或有理数自检的范围仅限被实际检查的实例，不承担第 9.5 条渐近量词或全时间量词。新结果未被标为 kernel-verified，文献优先权未被确立。

## 追加锚（本行以下为增补区）

## 12. 增补二·有限时间预测的熵、状态数与线性维数

**本批导航。** 本批接续 PR #8330 的 `f4202aa59e6053e4be883d7667f3d972946ff628`，读取的 dev 为 `630aac657042e88ca8bb69ee272cfcc6eb070bb8`。第 12 节把第 4、8 节的有限预测问题连接到观察熵；第 13、14 节把仿射状态保持与误差控制的前沿结论连接到仓库的核不变性和记忆核；第 15 节在严格稳定的一阶模型上求出带噪有限样本的外推风险阶。既有第 1 至 11 节不改判、不改字节。第 14.3 条限定所读外部预印本 v1 的一项投影递推，其精确状态保持定理不受此限定影响。

**定义 12.1（自主预测的观察覆盖数）。** 设非空紧致度量空间 $X$ 上有连续总更新 $F:X\to X$ 和连续观察 $o:X\to Y$，其中 $Y$ 为度量空间。令
\[
 B_H(x)=(o(x),o(Fx),\ldots,o(F^Hx)),\qquad
 d_H(x,y)=\max_{0\le t\le H}d_Y(o(F^tx),o(F^ty)).
\]
以响应集 $B_H[X]$ 自身的点作球心，记半径 $\varepsilon>0$ 的最少闭球覆盖数为 $C_H(\varepsilon)$。记 $S_H(\varepsilon)$ 为定义 8.1 中同时对全部初态、时刻 $0\le t\le H$ 正确至误差 $\varepsilon$ 的最少自主状态数。定义
\[
 h_o(F)=\lim_{\varepsilon\downarrow0}\limsup_{H\to\infty}
                   H^{-1}\log C_H(\varepsilon).
\]
本节除比特计数外使用自然对数。这是指定观察的熵；观察丢失信息时，不将它自动等同于完整系统的拓扑熵。

**定理 12.2（自主状态增长与观察熵的精确指数接口）。** 对定义 12.1 的系统，
\[
 C_H(2\varepsilon)\le S_H(\varepsilon)
                \le (H+1)C_H(\varepsilon),
\]
因而
\[
 \lim_{\varepsilon\downarrow0}\limsup_{H\to\infty}
            H^{-1}\log S_H(\varepsilon)=h_o(F).
\]
若 $o$ 是到 $o[X]$ 的拓扑嵌入，则 $h_o(F)$ 等于采用相容度量 $d_Y(o(x),o(y))$ 定义的拓扑熵。

**证明。** 紧致性和连续性使有限响应集紧致，故覆盖数有限。对任意正确预测器，在每个非空初始化纤维中选一个代表 $x_i$。同一纤维中的两条真实响应各距同一预测响应至多 $\varepsilon$，所以 $d_H(x,x_i)\le2\varepsilon$；这些代表给出左侧覆盖。

对右侧，选取覆盖中心 $B_H(x_i)$。用全部 $(i,t)$、$0\le t\le H$ 作状态，输出 $o(F^tx_i)$，更新 $(i,t)\mapsto(i,\min(t+1,H))$。把 $x$ 初始化为覆盖其响应的 $(i,0)$。该机器正确到时刻 $H$，并且时间坐标已计入状态总数。对不等式取对数、除以 $H$，使用 $\log(H+1)/H\to0$，再令 $\varepsilon\downarrow0$，两侧给出相同极限。最后，嵌入观察给出相容度量，所用覆盖正是该度量的轨道覆盖。此构造针对单一更新；多动作的整棵响应树不具有同样的线性大小上界。证毕。[^tcs2-dmd]

**定理 12.3（二进制移位的精确线性比特律）。** 取 $X=\{0,1\}^{\mathbb N}$，$F(x)_j=x_{j+1}$，$o(x)=(-1)^{x_0}\in\mathbb R$。对 $H\ge0$、$0\le\varepsilon<1$，最少自主预测状态数和当前状态比特数分别为
\[
 S_H(\varepsilon)=2^{H+1},\qquad
 \lceil\log_2 S_H(\varepsilon)\rceil=H+1.
\]

**证明。** 前 $H+1$ 位共有 $2^{H+1}$ 种取值。两种不同前缀在某个时刻 $t\le H$ 的真实输出相差 $2$；若共享一个初始内部状态，届时预测相同，与 $2\varepsilon<2$ 矛盾。反向，把长度 $H+1$ 的二进制词作为状态，输出首位的符号，每步左移并在末尾补零。初始化保存真实前缀，前 $H+1$ 次读出完全正确。这一结果的每个内部标签只表示一条前缀，没有使用未计费的外部时钟。证毕。

**定理 12.4（同一移位的线性特征维数界）。** 在定理 12.3 的 $X$ 上取独立公平比特的乘积概率测度，令 $f_t(x)=(-1)^{x_t}$。若 $V\subseteq L^2(X;\mathbb R)$ 是 $r$ 维子空间，且对每个 $0\le t\le H$ 存在 $g_t\in V$ 满足 $\|f_t-g_t\|_2\le\eta<1$，则
\[
 r\ge(H+1)(1-\eta^2).
\]
误差零时，$H+1$ 维线性移位寄存器达到最小值。这里的线性维数与定理 12.3 的离散状态数不是同一个资源。

**证明。** $f_0,\ldots,f_H$ 两两正交且范数为一。设 $P_V$ 是正交投影，则
\[
 \|P_Vf_t\|_2^2=1-\|f_t-P_Vf_t\|_2^2\ge1-\eta^2.
\]
取 $V$ 的标准正交基 $v_1,\ldots,v_r$，对每个 $v_j$ 使用 Bessel 不等式得到
\[
 \sum_{t=0}^H\|P_Vf_t\|_2^2
 =\sum_{j=1}^r\sum_{t=0}^H|\langle f_t,v_j\rangle|^2\le r.
\]
合并即得下界。上界存储向量 $(f_0(x),\ldots,f_H(x))$，用左移补零的线性映射和首坐标读出，正好实现全部指定时刻。虽然维数为 $H+1$，这个精确构造有 $2^{H+1}$ 种初始向量。论证同样约束任何固定线性读出和线性潜在更新，只要其全部预测函数属于同一个 $r$ 维特征空间；不约束任意非线性解码器。证毕。[^tcs2-dmd]

## 13. 仿射返回映射的定量保持与收缩代价

**定义 13.1（表示几何与返回缺陷）。** 给定不全相同的有限码点 $c_1,\ldots,c_m\in\mathbb R^d$，令
\[
 \bar c=m^{-1}\sum_i c_i,\quad u_i=c_i-\bar c,\quad
 U=\operatorname{span}\{u_i\},\quad
 \Sigma=m^{-1}\sum_i u_i u_i^{\mathsf T},\quad V_c=\operatorname{tr}\Sigma>0.
\]
记 $\gamma^2>0$ 为 $\Sigma$ 限制到 $U$ 的最小特征值。对仿射返回映射 $T(z)=Az+b$，定义均方根表示缺陷
\[
 \eta(T)^2=m^{-1}\sum_i\|T(c_i)-c_i\|_2^2.
\]
返回任务要求每个码点代表的符号状态保持不变；不预设 $T$ 已经精确满足该要求。

**定理 13.2（近似状态保持的定量中性界）。** 对上述数据有恒等式
\[
 \eta(T)^2=\|T(\bar c)-\bar c\|_2^2
       +\operatorname{tr}\bigl((A-I)\Sigma(A-I)^{\mathsf T}\bigr),
\]
以及
\[
 \|(A-I)|_U\|_{\mathrm{op}}\le\eta(T)/\gamma,
 \qquad
 \|Av\|_2\ge(1-\eta(T)/\gamma)\|v\|_2\quad(v\in U).
\]
特别地，$\eta(T)=0$ 强制 $A|_U=I$。

**证明。** 写 $T(c_i)-c_i=(A-I)u_i+r$，其中 $r=T(\bar c)-\bar c$。因 $\sum_i u_i=0$，平方展开的交叉项求和为零，得到恒等式。取 $\Sigma|_U$ 的标准正交特征基 $e_j$，对应特征值 $\lambda_j\ge\gamma^2$。于是
\[
 \eta(T)^2\ge\sum_j\lambda_j\|(A-I)e_j\|_2^2
 \ge\gamma^2\sum_j\|(A-I)e_j\|_2^2
 \ge\gamma^2\|(A-I)|_U\|_{\mathrm{op}}^2.
\]
最后对 $Av=v+(A-I)v$ 使用逆三角不等式。无需假设 $A$ 保持 $U$；限制算子可以取值于整个 $\mathbb R^d$。误差为零的特例对应所引文献的精确仿射中性定理。证毕。[^tcs2-error]

**定理 13.3（固定码本上的最优保持与收缩权衡）。** 对每个 $0\le q\le1$，
\[
 \inf_{T(z)=Az+b,\ \|A|_U\|_{\mathrm{op}}\le q}\eta(T)
       =(1-q)\sqrt{V_c}.
\]
最优值由 $T_q(z)=\bar c+q(z-\bar c)$ 达到。

**证明。** 对每个中心化码点，约束给出
\[
 \|(A-I)u_i\|_2\ge\|u_i\|_2-\|Au_i\|_2
                         \ge(1-q)\|u_i\|_2.
\]
把这些不等式平方求平均，代入定理 13.2 的恒等式并丢掉非负的中心偏移项，得到 $\eta(T)^2\ge(1-q)^2V_c$。映射 $T_q$ 固定中心，对全部 $u_i$ 恰产生 $(q-1)u_i$ 的误差，故取到该下界。这给出固定欧氏码本、共同仿射返回和所列算子范数约束下的精确最优值；不把它扩展到状态依赖的局部收缩。证毕。

## 14. 投影误差的交叉输入、记忆核与纠错构造

**定义 14.1（状态保持下的分块误差）。** 设仿射 $T(z)=Az+b$ 精确固定定义 13.1 的全部码点，$P$ 为到 $U$ 的正交投影，$Q=I-P$。置 $W=U^\perp$，
\[
 B=PA|_W:W\to U,\qquad D=QA|_W:W\to W.
\]
固定一个码点 $c$，考虑实际迭代 $h_{t+1}=T(h_t)+\xi_t$。写
\[
 u_t=P(h_t-c),\quad v_t=Q(h_t-c),\quad
 r_t=P\xi_t,\quad s_t=Q\xi_t.
\]
驱动 $\xi_t$ 可以依赖当前状态；下列代数恒等式不使用独立性或零均值假设。

**定理 14.2（完整投影递推与核不变性的充要条件）。** 在定义 14.1 下，
\[
 u_{t+1}=u_t+Bv_t+r_t,\qquad v_{t+1}=Dv_t+s_t,
\]
所以
\[
 u_{t+1}-u_t
 =r_t+BD^t v_0+\sum_{j=0}^{t-1}BD^{t-1-j}s_j.
\]
对所有初误差和所有驱动都有 $u_n=u_0+\sum_{t<n}r_t$，当且仅当 $B=0$，也当且仅当 $\ker P$ 被 $A$ 保持。对某一指定轨迹，逐步简化只要求该轨迹满足 $Bv_t=0$。

**证明。** 定理 13.2 的零缺陷特例给 $A|_U=I$，因此相对于 $U\oplus W$，
\[
 A=\begin{pmatrix}I&B\\0&D\end{pmatrix}.
\]
又因 $T(c)=c$，全误差满足 $h_{t+1}-c=A(h_t-c)+\xi_t$。投影后即得两条递推。归纳得到 $v_t=D^t v_0+\sum_{j<t}D^{t-1-j}s_j$，代回第一条得到记忆核公式。若 $B=0$，简化式立即成立；若简化式对所有初误差成立，令 $r_t=s_t=0$、$v_0$ 任意，在第一步得到 $Bv_0=0$，故 $B=0$。最后 $\ker P=W$，而 $Av=(Bv,Dv)$，故核不变恰好等价于 $B=0$。这是仓库零记忆判据在当前正交投影上的具体接口。证毕。[^tcs2-zero-memory]

**命题 14.3（精确仿射中性不足以推出无交叉项的投影递推）。** 存在精确固定两个不同码点的仿射返回映射，满足 $A|_U=I$、$\xi_t=0$，但 $u_1\ne u_0$。因此仅以上述条件不能推出所读预印本 v1 Corollary 1 的简单投影累加式。

**证明。** 在 $\mathbb R^2$ 取
\[
 c_-=(-1,0),\quad c_+=(1,0),\quad
 A=\begin{pmatrix}1&1\\0&1/2\end{pmatrix},\quad b=0.
\]
两个码点均固定，$U=\mathbb R(1,0)$，$A|_U=I$，但 $B=1$。令 $h_0=c_-+(0,1)$，不加任何驱动，则
\[
 v_t=2^{-t},\qquad u_t=\sum_{j=0}^{t-1}2^{-j}=2(1-2^{-t}).
\]
所以 $u_0=0$、$u_1=1$，而全部投影残差 $r_t$ 为零。预印本 v1 的 Appendix D.3 从 $PA(h_t-c)$ 转到 $P(h_t-c)$ 时，需要另外保证 $PAQ=0$，或误差一直位于 $U$，或至少沿实际轨迹满足 $Bv_t=0$。该反例不否定原文 Theorem 1 的 $A|_U=I$；它限定的是全空间扰动投影后的递推。证毕。[^tcs2-error]

**定理 14.4（稳定隐藏误差仍能产生可见的线性漂移）。** 另设 $\|D\|_{\mathrm{op}}\le\lambda<1$，并令 $r_t=0$、$s_t=w\in W$ 恒定。置 $K=B(I-D)^{-1}$。则
\[
 u_n-u_0=nKw+B\left(\sum_{t=0}^{n-1}D^t\right)
                         \bigl(v_0-(I-D)^{-1}w\bigr),
\]
从而
\[
 \left\|u_n-u_0-nKw\right\|_2
 \le\frac{\|B\|_{\mathrm{op}}}{1-\lambda}
                    \left\|v_0-(I-D)^{-1}w\right\|_2,
 \qquad
 \frac{u_n-u_0}{n}\longrightarrow Kw.
\]
同时 $v_n$ 有界。对全部常值隐藏驱动都没有此线性漂移，当且仅当 $B=0$。

**证明。** Neumann 级数给出 $(I-D)^{-1}=\sum_{j\ge0}D^j$。直接解出
\[
 v_t=(I-D)^{-1}w+D^t\bigl(v_0-(I-D)^{-1}w\bigr).
\]
将其代入 $u_n-u_0=\sum_{t<n}Bv_t$ 得到恒等式；用几何级数的范数界得到余项界，除以 $n$ 即得极限。上式也使 $v_n$ 有界。最后，全部 $w$ 的漂移为零等价于 $K=0$；由于 $I-D$ 可逆，这等价于 $B=0$。这里增长由隐藏驱动经记忆核 $BD^j$ 累积产生，当前可见的直接驱动始终为零。证毕。

**定理 14.5（保持码点读数的唯一自治斜投影）。** 在定理 14.4 的条件下，存在唯一线性映射 $\Pi_*:U\oplus W\to U$ 满足
\[
 \Pi_*|_U=I,\qquad \Pi_*A=\Pi_*.
\]
它由
\[
 \Pi_*(u,v)=u+Kv,\qquad K=B(I-D)^{-1}
\]
给出，且
\[
 \ker\Pi_*=\{(-Kv,v):v\in W\},\qquad
 \|\Pi_*\|_{\mathrm{op}}=\sqrt{1+\|K\|_{\mathrm{op}}^2}.
\]
对于任意驱动，新的误差读数 $z_t=u_t+Kv_t$ 满足精确自治递推
\[
 z_{t+1}=z_t+r_t+Ks_t.
\]

**证明。** 任意在 $U$ 上为恒等的线性读数必形如 $(u,v)\mapsto u+Lv$。条件 $\Pi A=\Pi$ 等价于 $B+LD=L$，即 $L(I-D)=B$；可逆性给唯一解 $L=K$。核的表达式随定义得到。因为 $U\ne\{0\}$，算子 $[I,K][I,K]^*=I+KK^*$ 的范数为 $1+\|K\|^2$，给出投影范数。将两条分块递推代入，并用 $B+KD=K$，得到 $z_{t+1}=z_t+r_t+Ks_t$。

所有码点差属于 $U$，所以新的读数保持这些差；其核是 $A$ 不变的稳定图子空间。该变换消除读数的隐藏依赖，但把隐藏驱动显式变成 $Ks_t$，并可能放大测量误差。它不构成自动纠错，亦不使定理 14.4 的漂移消失。证毕。

**定理 14.6（有限符号机的局部非线性纠错实现）。** 给定至少含两个元素的有限状态集 $S$、有限动作集、任意确定性转移 $\delta_a:S\to S$ 及输出 $y_i\in Y$。在 $\mathbb R^d$ 中选互异码点 $c_i$，最小距离为 $\Delta>0$。对任意 $0\le\nu<r<R<\Delta/2$，存在全空间 $C^1$ 更新 $T_a$，使从任意 $\|h_0-c_i\|_2\le r$ 出发，每步在更新之后添加任意范数至多 $\nu$ 的扰动，仍能在全部动作词后精确解码正确符号状态及其输出。

**证明。** 取 $C^1$ 函数
\[
 \theta(t)=\begin{cases}
 1,&t\le0,\\
 1-3t^2+2t^3,&0\le t\le1,\\
 0,&t\ge1,
 \end{cases}
 \qquad
 \chi_i(z)=\theta\left(\frac{\|z-c_i\|_2^2-r^2}{R^2-r^2}\right).
\]
两个接合点的导数均为零。各 $\chi_i$ 在半径 $r$ 球上为一，在半径 $R$ 球外为零；这些支撑彼此不交。固定一个码点 $c_*$，定义
\[
 T_a(z)=c_*+\sum_{i\in S}\chi_i(z)(c_{\delta_a(i)}-c_*).
\]
在 $\overline B(c_i,r)$ 上，$T_a$ 恒等于目标码点 $c_{\delta_a(i)}$。扰动之后距该码点至多 $\nu<r$，故归纳保证轨道始终处于正确的互不相交解码球中。将每个球解码成其编号，再读出 $y_i$ 即可。这里的收缩只在各个不同的局部邻域发生；同一个全局仿射算子没有被要求同时收缩所有码点差。该构造不声称某个指定 SSM、神经网络宽度或训练算法必然实现这些映射。证毕。

## 15. 半正定 Hankel 数据的外推风险与谱隙

**定义 15.1（严格稳定一阶响应的带噪外推）。** 对 $a\in(0,1)$ 定义 $m_a(k)=a^k$。它具有严格稳定的一维线性实现；任意有限 Hankel 矩阵 $(m_a(i+j))_{i,j=0}^N$ 都是半正定秩一矩阵。给定整数 $1\le T\le H$ 及 $\eta>0$，观察 $y=(y_0,\ldots,y_T)$ 满足 $|y_k-a^k|\le\eta$。定义确定性最坏情形风险
\[
 \mathcal R_{T,H}(\eta)=
 \inf_{\Psi:\mathbb R^{T+1}\to\mathbb R}
 \sup_{a\in(0,1)}\ \sup_{\max_{k\le T}|y_k-a^k|\le\eta}
                      |\Psi(y)-a^H|.
\]
这里允许任意估计器，不限制其计算量，故下界不是算法运行时间造成的。误差是逐样本有界误差，不是随机噪声方差。

**定理 15.2（一阶稳定模型的匹配有限外推风险阶）。** 对定义 15.1 的全部参数，
\[
 \min\left\{\frac{\eta H}{2T},\frac1{16}\right\}
 \le\mathcal R_{T,H}(\eta)
 \le\min\left\{\frac12,\frac{\eta H}{T}\right\}.
\]
因此在绝对常数意义下，
\[
 \mathcal R_{T,H}(\eta)=\Theta\bigl(\min\{1,\eta H/T\}\bigr).
\]

**证明。** 为证下界，置
\[
 d=\min\{2\eta/T,1/(4H)\},\qquad a=1-d,\quad b=1-2d.
\]
因 $0<d\le1/4$，两者均属于 $(0,1)$。对 $0\le k\le T$，幂差公式给 $0\le a^k-b^k\le kd\le2\eta$，故中点观测 $y_k=(a^k+b^k)/2$ 对两个系统都合法。又有
\[
 a^H-b^H=d\sum_{j=0}^{H-1}a^{H-1-j}b^j
 \ge Hd(1-2d)^{H-1}\ge Hd/2.
\]
末步使用 Bernoulli 不等式以及 $Hd\le1/4$。同一数据上的任意预测值，至少对其中一个系统有误差 $(a^H-b^H)/2\ge Hd/4$，恰好给出所列下界。

为证上界，把 $y_T$ 截断到 $[0,1]$ 得到 $z$，并输出 $z^{H/T}$。截断不会增大它与 $a^T$ 的距离；函数 $x\mapsto x^{H/T}$ 在 $[0,1]$ 的 Lipschitz 常数至多为 $H/T$，所以误差至多为 $\eta H/T$。恒输出 $1/2$ 的估计器误差至多为 $1/2$，择优给出右侧。下界又至少为 $\frac1{16}\min\{1,\eta H/T\}$，上界至多为 $\min\{1,\eta H/T\}$，得到匹配阶。这里全局秩已经固定为一；不确定性来自有限精度下的动力参数。证毕。[^tcs2-hankel]

**定理 15.3（无共同谱隙时的全未来风险恰为二分之一）。** 定义 15.1 中保持 $T<\infty$、$\eta>0$，允许估计器输出全部 $n\ge T$ 的预测序列，并以全部这些时刻的误差上确界计费，则对应最坏情形最优风险为
\[
 \mathcal R_{T,\infty}(\eta)=\frac12.
\]
该结论仍只涉及每个实例自身严格稳定、半正定 Hankel 秩一的系统。

**证明。** 恒输出 $1/2$ 给出上界。令 $d\downarrow0$，取 $a_d=1-d^2$、$b_d=1-d$。对足够小的 $d$，两者合法且全部 $k\le T$ 的响应差至多 $Td\le2\eta$，所以中点数据对二者共同合法。令 $n_d=\lfloor d^{-3/2}\rfloor$，则最终 $n_d\ge T$，并且
\[
 1-a_d^{n_d}\le n_d d^2\longrightarrow0,\qquad
 b_d^{n_d}\le e^{-n_dd}\longrightarrow0.
\]
因此二者在某个允许预测时刻的差趋于一。对任意完整序列估计器，使用这一共同数据时，至少一个系统的全时间误差不小于该差的一半；取上确界及极限得到 $1/2$ 的下界。任意正噪声预算都允许这组趋近单位特征值的系统；$\eta=0$ 不属于本命题。证毕。

**定理 15.4（共同谱隙恢复一致的全未来精度）。** 若另外已知 $0<a\le\rho<1$，定义 15.3 的全未来最优风险满足
\[
 \mathcal R^{(\rho)}_{T,\infty}(\eta)
 \le\min\left\{\frac12,\frac{\eta}{1-\rho}\right\}.
\]

**证明。** 令 $\hat a$ 为 $y_1$ 截断到 $[0,\rho]$ 的值，则 $|\hat a-a|\le\eta$。预测 $\hat a^n$，由幂差公式对全部 $n\ge1$ 有
\[
 |\hat a^n-a^n|\le n\rho^{n-1}\eta
 \le\eta\sum_{j=0}^{n-1}\rho^j\le\eta/(1-\rho).
\]
再与恒输出 $1/2$ 比较。该证明使用已知的共同标量谱隙；它不将谱半径小于一自动当作任意非正规矩阵族的一致幂界。证毕。

## 16. 本批来源、限定条件与证明身份

**出处 16.1（文献锚与推导范围）。** 第 12 节从原卷的有限行为响应出发给出观察熵接口和明确移位实例，相关前沿背景是 Hauser 与 Hölz 的 DMD 维数下界；两者分别使用最坏情形状态数与 $L^2$ 特征维数，本文不混用。第 13 节给出精确仿射中性结果的定量版本和固定码本上的最优化值。第 14 节核对 Chung、Choi、Kim 预印本 v1 的投影计算，并以分块恒等式、具体反例、记忆核和自治斜投影补足所需条件。第 15 节受到半正定 Hankel 低秩近似工作的启发，讨论其有限矩阵近似保证之外的外推义务；没有把该文未承诺的外推结论当作其主张。

**出处 16.2（文献状态）。** 本批 13 条结果均有上述完整纸面证明，列为 `repo-derived`；其中精确仿射中性、Bessel 方法、熵覆盖和两点风险下界属于已有数学方法。下列文献的特定范围列为 `literature-attested`。未建立本批定量式的全球优先权，不列 `suspected-novel`，也不声称解决一个外部开放问题。

[^tcs2-dmd]: Till Hauser、Julian Hölz，*Entropy based lower dimension bounds for finite-time prediction of Dynamic Mode Decomposition algorithms*，arXiv:2504.20269v1，提交于 2025-04-28，[原文](https://arxiv.org/abs/2504.20269v1)。核对了摘要及 PDF 的解析正文，包括第 1 节对有限分区与一般 $L^2$ 子空间的区分。截图接口未成功返回图像，因此不引用其图表。`literature-attested` 范围为熵与预测子空间维数的关系；第 12.2 条的自主状态实现及第 12.3、12.4 条的具体常数由本卷自证。

[^tcs2-error]: Jiwan Chung、Heechan Choi、Seon Joo Kim，*Rethinking State Tracking in Recurrent Models Through Error Control Dynamics*，arXiv:2605.07755v1，2026-05-08，[第 3.1、3.2 节及 Appendix D.1 至 D.3](https://arxiv.org/html/2605.07755v1)。`literature-attested` 范围是 Theorem 1 的精确仿射中性及状态依赖纠错的研究背景。本批第 14.3 条针对该固定版本的 Corollary 1 及其投影推导补条件；不据此否定其 Theorem 1、实验结果或所有仿射架构的有限时间表现。本文也不把平均误差与类别间距之比当作逐样本正确性的保证。

[^tcs2-hankel]: Michael Kapralov、Cameron Musco、Kshiteej Sheth，*Sublinear Time Low-Rank Approximation of Hankel Matrices*，arXiv:2511.21418v1，2025-11-26，条目注明 SODA 2026，[第 1.2 节 Theorem 1、2](https://arxiv.org/html/2511.21418v1)。核对的定理使用半正定 Hankel 矩阵、逐项访问、带噪 Frobenius 范数保证及结构保持的低秩输出。第 15 节使用真实的半正定秩一实例，但风险针对未观测的未来响应；有限矩阵误差界本身不包含这个量词。本文未运行或修改该文算法。

[^tcs2-zero-memory]: 当前源码 [D5/S3/Observer/LinearMemory/ZeroMemoryCriterion.lean](https://github.com/the-omega-institute/trureturing/blob/630aac657042e88ca8bb69ee272cfcc6eb070bb8/D5/S3/Observer/LinearMemory/ZeroMemoryCriterion.lean)，已读取 `eventualKernel`、`eventualKernel_is_greatest`、`zero_memory_iff_eventualKernel_eq_ker` 及核不变构件。它们给出零记忆和核不变性的既有基础；第 14 节的具体文献反例、受迫漂移及斜投影公式不因引用该源文件而自动获得 Lean 证明身份。

**约定 16.3（本批产地）。** 本批使用 `theory-volume-template/APPEND.md`；数学推导、原文核对、文字实施和有限检错由本会话 ChatGPT 单席串行完成，没有独立模型评审。正文只追加必要定义、结果、证明及来源。未新增 Lean 或 Scribe，未运行 Lean kernel、canonical `make ingest` 或生成消化账目；有限算术、矩阵和状态机检查只用于发现实现与公式错误。全称结论以本文证明为依据，未标为 kernel-verified。

## 追加锚（本行以下为增补区）

## 17. 增补三·能量下降、几何长度与受控作用量

**本批导航。** 本批接续 PR #8330 的 `223734ad64ffa1aee016c8ba7c29470e07eb1300`，读取的 dev 为 `11036b0baf142c8e6535e61f29d2cae83ecf7bba`。第 17 节区分能量梯度流、最短路和跨势垒作用量；第 18 节连接路径熵、自由能、Bellman 递推与转移谱；第 19 节给出优化问题沿观察商下降的精确条件及误差界；第 20 节计算隐藏变量消元后的能量、记忆核和快慢误差。既有条目保持原字节，不改判。数学结论均按下列量词和模型成立。

**约定 17.1（熵、几何及费用的载体）。** 第 12 节的观察熵是轨迹覆盖数的渐近增长率。本批的 Shannon 熵、相对熵分别作用于明确给定的概率分布，路径代价作用于轨迹，几何度量作用于状态空间或概率分布空间。参数 $\tau>0$ 在离散优化中是正则化强度；只有给出物理单位、热浴和动力学模型时才另解释为热能尺度。全文自然对数。梯度依赖所给度量；最短路依赖端点、可行路径及长度函数。以下均不从同名“熵”推断这些对象自动相等。

**定理 17.2（梯度流的耗散长度界及非最短路实例）。** 设 $(M,g)$ 为连通 Riemann 流形，$V\in C^1(M)$，$x:[0,T]\to M$ 为满足 $\dot x=-\operatorname{grad}_gV$ 的 $C^1$ 曲线，$T>0$。记其长度为 $L_g(x)$，则
\[
 V(x(0))-V(x(T))=\int_0^T\|\dot x\|_g^2dt
 \ge\frac{L_g(x)^2}{T}\ge\frac{d_g(x(0),x(T))^2}{T}.
\]
对任意绝对连续端点连接曲线 $z$，其动能作用量 $\frac12\int_0^T\|\dot z\|_g^2dt$ 至少为 $d_g(z(0),z(T))^2/(2T)$；有常速最短测地线时达到该界。梯度流一般不达到此界。

**证明。** 链式法则给 $dV(x(t))/dt=-\|\operatorname{grad}_gV\|_g^2=-\|\dot x\|_g^2$。积分后，以 Cauchy–Schwarz 得 $L_g(x)^2\le T\int\|\dot x\|_g^2$，再用距离是路径长度下确界得到结果。任意 $z$ 的作用量界使用同样两步；常速最短曲线令两步同时取等。

在欧氏平面取 $V(u,v)=(u^2+2v^2)/2$、初态 $(1,1)$。梯度流为 $(e^{-t},e^{-2t})$，轨迹满足 $v=u^2$。对每个 $T>0$，这段非直线曲线的长度严格大于端点间线段长度。因此即使势能处处严格凸，自然下降轨迹也未必是该几何中的端点最短路。证毕。[^tcs3-thermogeo]

**定理 17.3（自由能的概率几何耗散）。** 在平坦单位环面 $\mathbb T^d$ 上，设 $U$ 光滑、$\tau>0$，$\rho_t$ 是时间区间 $[0,T]$ 上光滑、严格正、积分为一的周期密度，并满足
\[
 \partial_t\rho=\nabla\cdot(\rho\nabla U)+\tau\Delta\rho.
\]
定义
\[
 \mathcal F_\tau(\rho)=\int U\rho+\tau\int\rho\log\rho,
 \qquad \pi_\tau=Z_\tau^{-1}e^{-U/\tau}.
\]
则
\[
 \mathcal F_\tau(\rho)=\tau\operatorname{KL}(\rho\Vert\pi_\tau)-\tau\log Z_\tau,
\]
\[
 \frac{d}{dt}\mathcal F_\tau(\rho_t)
 =-\int\rho_t\|\nabla(U+\tau\log\rho_t)\|^2,
\]
以及
\[
 \mathcal F_\tau(\rho_0)-\mathcal F_\tau(\rho_T)
 \ge T^{-1}W_2(\rho_0,\rho_T)^2.
\]
这里 $W_2$ 使用环面的测地距离，质量及迁移率采用方程中所写的归一化。

**证明。** 把 $\log\pi_\tau=-U/\tau-\log Z_\tau$ 代入相对熵，即得第一式。质量守恒和周期分部积分给
\[
 \frac{d}{dt}\mathcal F_\tau
 =\int(U+\tau\log\rho)\,\nabla\cdot\bigl(\rho\nabla(U+\tau\log\rho)\bigr)
 =-\int\rho\|\nabla(U+\tau\log\rho)\|^2.
\]
置速度 $v_t=-\nabla(U+\tau\log\rho_t)$，原方程成为连续性方程。光滑速度的流映射把 $\rho_0$ 推到 $\rho_t$。对每条流线，其端点距离平方至多为 $T\int_0^T|v_t|^2dt$；对初始质量积分便构造一个端点耦合，代价至多为 $T\int_0^T\int\rho_t|v_t|^2$。$W_2^2$ 取全部耦合的下确界，再使用耗散恒等式即得结论。本条直接证明给定光滑解的恒等式与界，没有借此证明 PDE 的存在性或每条样本轨道势能单调。证毕。[^tcs3-thermogeo]

**定理 17.4（跨势垒作用量与上坡代价）。** 对 $U\in C^1(\mathbb R^d)$ 和绝对连续路径 $z:[0,T]\to\mathbb R^d$，假设下式积分有限，定义
\[
 I_T(z)=\frac14\int_0^T\|\dot z+\nabla U(z)\|^2dt.
\]
则
\[
 I_T(z)=U(z(T))-U(z(0))+rac14\int_0^T\|\dot z-\nabla U(z)\|^2dt,
\]
且
\[
 I_T(z)\ge\max_{0\le t\le T}\bigl(U(z(t))-U(z(0))\bigr).
\]
若所有允许的端点连接路径都须经过高于初始势能至少 $b\ge0$ 的位置，则其作用量下确界至少为 $b$。

**证明。** 展开两个平方之差得 $4\dot z\cdot\nabla U(z)$，积分为 $4(U(z(T))-U(z(0)))$。对任意前缀 $[0,t]$ 使用该恒等式，丢弃余下的非负平方项及 $[t,T]$ 上的非负原积分，得到 $I_T(z)\ge U(z(t))-U(z(0))$。取最大值及路径下确界即可。对给定端点，第一式取等要求 $\dot z=+\nabla U(z)$ 几乎处处；此条件不保证任意有限时间内可以连接指定端点，特别不能假设从临界点自动出发。这里直接研究作用量，不把小噪声概率渐近或最优路径存在性加入未给出的结论。证毕。

## 18. 路径自由能、软 Bellman 与图的熵压力

**定义 18.1（有限路径的参考分布）。** 令 $\Omega$ 是有限非空可行路径集，$R(\omega)>0$ 且 $\sum_\omega R(\omega)=1$，$C:\Omega\to\mathbb R$ 为总费用。对概率分布 $P$ 定义
\[
 J_\tau(P)=\mathbb E_PC+\tau\operatorname{KL}(P\Vert R),\quad
 Z_\tau=\sum_\omega R(\omega)e^{-C(\omega)/\tau},\quad F_\tau=-\tau\log Z_\tau.
\]
只有当 $R$ 在 $\Omega$ 上均匀时，$J_\tau=\mathbb E_PC-\tau H(P)+\tau\log|\Omega|$。对一般参考分布，$-\mathbb E_P\log R$ 也是目标的一部分。

**定理 18.2（路径优化的精确 Gibbs 分解及零温极限）。** 令
\[
 P_\tau^*(\omega)=Z_\tau^{-1}R(\omega)e^{-C(\omega)/\tau}.
\]
对任意 $P$ 有
\[
 J_\tau(P)=F_\tau+\tau\operatorname{KL}(P\Vert P_\tau^*).
\]
所以 $P_\tau^*$ 是唯一极小点。若 $c_* =\min C$，$r_*=R\{C=c_*\}>0$，则
\[
 c_*\le F_\tau\le c_*-\tau\log r_*,\qquad
 \lim_{\tau\downarrow0}F_\tau=c_*.
\]

**证明。** 将 $\log P_\tau^*=\log R-C/\tau-\log Z_\tau$ 代入 KL，逐项整理得到恒等式。相对熵非负且仅在两分布相同时为零，给出唯一极小性。另有 $r_*e^{-c_*/\tau}\le Z_\tau\le e^{-c_*/\tau}$；取负对数得到夹逼与极限。最短路在此是固定可行路径集上的最小费用；若费用取几何长度才得到对应几何的最短路径。证毕。[^tcs3-gibbs][^tcs3-todorov]

**定理 18.3（路径粗粒化的条件自由能与精确损失）。** 对满射 $q:\Omega\to\mathcal Y$，记 $r=q_\#R$，定义
\[
 A_\tau(y)=-\tau\log\sum_{q(\omega)=y}R(\omega\mid y)e^{-C(\omega)/\tau},
\]
以及纤维上的分布
\[
 R_\tau(\omega\mid y)=R(\omega\mid y)
                 \exp\bigl(-(C(\omega)-A_\tau(y))/\tau\bigr).
\]
若 $p=q_\#P$，则
\[
 J_\tau(P)=\mathbb E_p A_\tau+\tau\operatorname{KL}(p\Vert r)
    +\tau\sum_{y:p(y)>0}p(y)\operatorname{KL}\bigl(P(\cdot\mid y)\Vert R_\tau(\cdot\mid y)\bigr).
\]
因此给定任意粗分布 $p$，其全部提升中最小目标恰为前两项；最优提升在每个正质量纤维使用 $R_\tau(\cdot\mid y)$。

**证明。** 分解 $P(\omega)=p(y)P(\omega\mid y)$、$R(\omega)=r(y)R(\omega\mid y)$，直接求和得到 KL 链式分解。对每个纤维使用定理 18.2，即将条件期望费用与条件 KL 合并为 $A_\tau$ 加上所列余项。按纤维求和完成证明，取指定条件分布即可达到下界。这里 $q$ 可以是整条路径的观察；推出的是路径级精确优化，不保证观察路径具有一阶 Markov 分解。证毕。[^tcs3-leonard]

**定理 18.4（有限时域的软 Bellman 线性化）。** 设有限状态集 $X$ 上有参考转移矩阵 $R$，每行和为一，支持边上的费用 $c(x,y)$ 有限，终端费用 $g:X\to\mathbb R$ 有限。控制后继分布只使用 $R$ 的支持；以下转移求和也只取支持边。给定时域 $H$，定义
\[
 V_H=g,\qquad V_t(x)=-\tau\log\sum_yR_{xy}
                   e^{-(c(x,y)+V_{t+1}(y))/\tau}.
\]
则 $V_0(x)$ 等于从固定初态 $x$ 出发的路径目标 $J_\tau$ 最小值，且最优转移为
\[
 Q_t^*(x,y)=R_{xy}
       e^{-(c(x,y)+V_{t+1}(y)-V_t(x))/\tau}.
\]
令 $z_t=e^{-V_t/\tau}$、$K_\tau(x,y)=R_{xy}e^{-c(x,y)/\tau}$，则 $z_t=K_\tau z_{t+1}$。相应软算子在一致范数下是非扩张的。若 $D_t$ 是同一支持图、同一终端费用的最小费用递推，$r_{\min}$ 为最小正参考转移概率，则
\[
 0\le V_t-D_t\le (H-t)\tau\log(1/r_{\min}).
\]

**证明。** 在每个状态上，以候选后继概率向量作变量，对费用 $c(x,y)+V_{t+1}(y)$ 使用定理 18.2，得到最小值及 $Q_t^*$。对任意允许的历史依赖转移，路径 KL 按条件分布链式求和；反向归纳给出这些逐步最小值同时达到路径最优，Markov 形式 $Q_t^*$ 已足够。指数变换直接给出线性递推。

若 $\|v-w\|_\infty\le a$，则各指数项比值位于 $[e^{-a/\tau},e^{a/\tau}]$，取负对数即得算子距离至多 $a$。一行软最小值不小于该行真实最小值，且至多比它大 $\tau\log(1/r_{\min})$；结合单调性和非扩张性逐层累积得到最后一式。本条允许直接控制后继分布并支付 KL 代价，不等同于任意指定动作约束下的 MDP。证毕。[^tcs3-todorov]

**定理 18.5（图路径熵、费用与同一转移谱）。** 设有限简单有向图强连通且含有边，支持边费用为 $c_{xy}\in\mathbb R$。置 $W_\tau(x,y)=\mathbf1_{x\to y}e^{-c_{xy}/\tau}$，其 Perron 根为 $\lambda_\tau>0$。对图上任意平稳 Markov 对 $(\pi,Q)$，定义
\[
 h(\pi,Q)=-\sum_{x,y}\pi_xQ_{xy}\log Q_{xy}.
\]
则
\[
 -\tau\log\lambda_\tau
 =\min_{\pi Q=\pi}\left(\sum_{x,y}\pi_xQ_{xy}c_{xy}-\tau h(\pi,Q)\right).
\]
另外
\[
 \lim_{n\to\infty}n^{-1}\log(W_\tau^n\mathbf1)_x=\log\lambda_\tau.
\]
若 $c_{xy}=0$，图上的路径增长熵为 $\log\rho(A)$，其中 $A$ 是邻接矩阵。若 $c_{\mathrm{cyc}}$ 为最小有向环平均费用，$d_{\max}$ 为最大出度，则
\[
 c_{\mathrm{cyc}}-\tau\log d_{\max}
 \le-\tau\log\lambda_\tau\le c_{\mathrm{cyc}},
\]
故零温极限为最小环平均费用。

**证明。** 取正右 Perron 向量 $r$，定义 $Q^*_{xy}=W_\tau(x,y)r_y/(\lambda_\tau r_x)$，各行和为一。对任意平稳 $(\pi,Q)$ 展开
\[
 \tau\sum_x\pi_x\operatorname{KL}(Q_x\Vert Q_x^*)
 =\sum\pi_xQ_{xy}c_{xy}-\tau h(\pi,Q)+\tau\log\lambda_\tau.
\]
$\log r_y-\log r_x$ 项因平稳性抵消。有限不可约 $Q^*$ 有平稳分布，代入时 KL 为零，得到变分公式。以正倍数的 $r$ 从上下夹住 $\mathbf1$，再作用 $W_\tau^n$，即可得到增长率，无需图非周期。

任意平稳边流是有限个有向环流的非负组合：沿一条正流边连续追踪至出现重复顶点，减去该环上的最小流，再迭代；每次至少消去一条正边，有限步终止。按总边质量归一化后，平均费用是各环平均费用的凸组合，故至少为 $c_{\mathrm{cyc}}$，而沿最小环确定运行达到它。最后 $0\le h(\pi,Q)\le\log d_{\max}$，代回变分式得到夹逼。这里计数权重为一，未用行归一化参考概率；归一化参考会改变熵项。长时间的环平均目标与固定端点最短路也须分别计量。证毕。[^tcs3-pressure]

## 19. 优化沿观察商下降的充要条件及尖锐误差

**定义 19.1（费用加权的观察转移）。** 沿用定理 18.4 的 $X,R,c$，另给满射 $q:X\to Y$。对观察标签 $j\in Y$ 定义
\[
 k_\tau(x,j)=\sum_{y:q(y)=j}R_{xy}e^{-c(x,y)/\tau},\qquad
 \mu_{x,j}=\sum_{y:q(y)=j,\ R_{xy}>0}R_{xy}\delta_{c(x,y)}.
\]
于是 $k_\tau(x,j)$ 是有限费用测度 $\mu_{x,j}$ 在 $1/\tau$ 处的 Laplace 变换。不存在支持边时，两者均为零。

**定理 19.2（全终端费用的软 Bellman 精确下降）。** 固定 $\tau>0$。软 Bellman 算子把每个形如 $v\circ q$ 的终端函数仍映成 $q$ 的纤维常值函数，当且仅当
\[
 q(x)=q(x')\quad\Longrightarrow\quad
 k_\tau(x,j)=k_\tau(x',j)\quad\text{对全部 }j.
\]
成立时定义 $\bar K_\tau(q(x),j)=k_\tau(x,j)$，全部有限时域、全部粗终端费用的值函数均精确下降，最优后继的粗概率也只依赖当前粗状态。

**证明。** 对粗终端 $v$，指数变换后的单步值正是
\[
 \sum_j k_\tau(x,j)e^{-v(j)/\tau}.
\]
系数在纤维上恒定给出充分性。反向，$e^{-v(j)/\tau}$ 可独立遍历全部正向量。两个系数向量与全部正向量的内积相同，固定其余坐标而改变一个坐标即可证明每个系数相同。按时间反向归纳得到全部有限时域下降。最优粗转移由 $\bar K_\tau(i,j)e^{-\bar V_{t+1}(j)/\tau}/e^{-\bar V_t(i)/\tau}$ 给出。

本条证明的是值及粗转移保真。最优微观条件转移仍可能依赖真实 $x$；仅能读取 $q(x)$ 的执行器是否可以实施它，还需要观测反馈或纤维内采样的实现条件。证毕。

**定理 19.3（全部温度保真的费用测度判据）。** 定理 19.2 的精确下降对每个 $\tau>0$ 成立，当且仅当
\[
 q(x)=q(x')\quad\Longrightarrow\quad \mu_{x,j}=\mu_{x',j}
                   \quad\text{对全部 }j.
\]
相比之下，零温最小费用算子对全部粗终端费用下降，当且仅当每个目标标签的最小支持边费用
\[
 d(x,j)=\min\{c(x,y):q(y)=j,\ R_{xy}>0\}\in\mathbb R\cup\{+\infty\}
\]
在当前观察纤维上恒定。

**证明。** 费用测度相等显然给所有温度的加权和相等。反向，固定 $x,x',j$，把两个有限测度差的全部支持点排列为 $a_1<\cdots<a_m$，系数为 $b_i$。所给条件为 $\sum_i b_i e^{-\beta a_i}=0$ 对全部 $\beta>0$ 成立。乘 $e^{\beta a_1}$ 并令 $\beta\to\infty$ 得 $b_1=0$，逐个消去即得全部系数为零。

零温算子是 $v\mapsto\min_j(d(x,j)+v(j))$。各 $d$ 相等即充分。反向令某个 $v(j)=0$，其余坐标为 $M$ 并令 $M\to\infty$；若到 $j$ 的支持非空，极限为 $d(x,j)$，否则趋于 $+\infty$。算子相同迫使这些极限逐项相同。故最小费用只读取费用测度的最小支持点，全部温度还读取各费用层的参考质量。证毕。

**定理 19.4（近似加权下降的全时域证书）。** 固定 $\tau>0$，设粗矩阵 $\bar K$ 非负且每行至少有一项为正。若存在 $\delta\ge0$ 使
\[
 e^{-\delta/\tau}\bar K(q(x),j)\le k_\tau(x,j)
                          \le e^{\delta/\tau}\bar K(q(x),j)
\]
对所有 $x,j$ 成立，则对任意粗终端费用 $g$、任意时域 $H$，真实软递推与粗递推满足
\[
 \|V_t-\bar V_t\circ q\|_\infty\le(H-t)\delta.
\]
粗递推直接使用 $\bar K$，不要求它行归一化。

**证明。** 乘上任意正终端指数向量并求和，保持上述比值界。取负 $\tau$ 对数，得到在纤维常值输入上的单步误差至多为 $\delta$。真实软算子的非扩张性由定理 18.4 给出，该论证同样适用于任意非负非零行矩阵。于是
\[
 \|V_t-\bar V_tq\|_\infty
 \le\|V_{t+1}-\bar V_{t+1}q\|_\infty+\delta.
\]
终端误差为零，反向归纳得到结果。此证书约束全部终端费用；零项也被双边界强制一致，不能用有限对数误差掩盖支持缺失。证毕。

**命题 19.5（最短费用全保真而热化值线性分离的有限系统）。** 对任意 $\Delta,\tau>0$，存在四状态系统，全部状态观察相同，任意时域的零温最小费用均为零，但同一观察下的软最优值差随时域严格线性增长；定理 19.4 的 $(H-t)\delta$ 界在该系统中精确达到。

**证明。** 取状态 $(b,i)$，其中 $b\in\{1,2\}$、$i\in\{0,1\}$，$q$ 恒定。参考转移只在同一 $b$ 内，以各 $1/2$ 概率到 $(b,0)$、$(b,1)$，费用分别为 $0,b\Delta$。每步选择零费用边可使任意时域最短费用为零，粗终端常数也被精确保留。置
\[
 z_b=\frac{1+e^{-b\Delta/\tau}}2,
\]
则零终端费用、剩余 $h$ 步时，指数值恰为 $z_b^h$，故
\[
 V_h(b,i)=-h\tau\log z_b,\qquad
 V_h(2,i)-V_h(1,i)=h\tau\log(z_1/z_2)>0.
\]
任何仅依赖当前观察的值估计至少对一个初态有误差 $h\tau\log(z_1/z_2)/2$。选择一状态粗权重 $\bar K=\sqrt{z_1z_2}$，并令 $\delta=\tau\log(z_1/z_2)/2$，定理 19.4 的两个乘法界恰在两个隐藏模式取等；粗值是两个真实值的中点，因此误差恰为 $h\delta$。状态数量有限，差异完全来自未被观察的费用分布。本条没有把费用读数偷偷并入原观察。证毕。

## 20. 势能消元、隐藏记忆与快慢闭合误差

**定义 20.1（二次能量与观测坐标）。** 对 $x\in\mathbb R^p,z\in\mathbb R^r$，$p,r\ge1$，设对称块矩阵
\[
 L=\begin{pmatrix}A&B\\B^{\mathsf T}&C\end{pmatrix}>0,\qquad
 U(x,z)=\tfrac12x^{\mathsf T}Ax+x^{\mathsf T}Bz+\tfrac12z^{\mathsf T}Cz.
\]
因此 $C>0$ 且 $S=A-BC^{-1}B^{\mathsf T}>0$。观察只保留 $x$，所有范数使用欧氏范数及其诱导算子范数。

**定理 20.2（最小势能与积分自由能的同一 Schur 形状）。** 对上述模型和 $\tau>0$，
\[
 \min_z U(x,z)=\tfrac12x^{\mathsf T}Sx,
\]
\[
 -\tau\log\int_{\mathbb R^r}e^{-U(x,z)/\tau}dz
 =\tfrac12x^{\mathsf T}Sx+\frac\tau2\log\det C
                         -\frac{r\tau}{2}\log(2\pi\tau).
\]
所以积分自由能与最小势能对 $x$ 有相同梯度 $Sx$。

**证明。** 完成平方得
\[
 U(x,z)=\tfrac12x^{\mathsf T}Sx
       +\tfrac12(z+C^{-1}B^{\mathsf T}x)^{\mathsf T}C
                       (z+C^{-1}B^{\mathsf T}x).
\]
第二项唯一极小于 $z=-C^{-1}B^{\mathsf T}x$。对 $C$ 正交对角化并逐坐标计算高斯积分，积分值为
\[
 e^{-x^{\mathsf T}Sx/(2\tau)}(2\pi\tau)^{r/2}(\det C)^{-1/2}.
\]
取对数完成证明。本条隐藏刚度 $C$ 与 $x$ 无关，因此熵修正是常数；对位置依赖的隐藏刚度，不能删掉该导数。证毕。[^tcs3-schur]

**定理 20.3（能量精确消元不保证轨迹自治）。** 对定义 20.1 的全空间欧氏梯度流
\[
 \dot x=-Ax-Bz,\qquad \dot z=-B^{\mathsf T}x-Cz,
\]
观测轨迹满足
\[
 \dot x(t)=-Ax(t)-Be^{-Ct}z_0
          +\int_0^tBe^{-C(t-s)}B^{\mathsf T}x(s)ds.
\]
对所有初态都能仅从当前 $x$ 给出同一个自治向量场，当且仅当 $B=0$。即使初始 $z_0$ 取为该 $x_0$ 的条件能量极小点，也一般不能将轨迹精确替换为 $\dot{\bar x}=-S\bar x$。

**证明。** 对隐藏方程使用常数变易公式：$z(t)=e^{-Ct}z_0-\int_0^te^{-C(t-s)}B^{\mathsf T}x(s)ds$，代入观测方程得到所列记忆核。若 $B=0$，自治显然成立；若同一 $x$ 的所有 $z$ 都给相同初始导数，则 $B(z-z')=0$ 对任意 $z,z'$ 成立，故 $B=0$。

取标量块 $A=C=2,B=1$，$x_0=1,z_0=-1/2$。全矩阵特征值为 $1,3$，且 $z_0$ 正是条件极小点。全轨迹给 $\dot x(0)=-3/2$、$\ddot x(0)=3$；有效势能的梯度流给 $\dot{\bar x}(0)=-3/2$、$\ddot{\bar x}(0)=9/4$。二阶导数已不同，所以两个轨迹无法在邻域内相同。证明不需要不稳定能量地形。证毕。

**定理 20.4（快隐藏变量使有效势能动力学具有统一误差界）。** 对 $\epsilon>0$ 改用
\[
 \dot x_\epsilon=-Ax_\epsilon-Bz_\epsilon,\qquad
 \epsilon\dot z_\epsilon=-B^{\mathsf T}x_\epsilon-Cz_\epsilon,
 \qquad\dot{\bar x}=-S\bar x,\quad\bar x(0)=x_0.
\]
令 $c=\lambda_{\min}(C)>0$、$m=\lambda_{\min}(S)>0$、$\ell=\lambda_{\min}(L)>0$，并置
\[
 R_0=\sqrt{2U(x_0,z_0)/\ell},\quad
 M_0=\|[A\ B]\|R_0,\quad
 D_0=\|C^{-1}B^{\mathsf T}\|,\quad
 w_0=z_0+C^{-1}B^{\mathsf T}x_0.
\]
则对全部 $t\ge0$，
\[
 \|x_\epsilon(t)-\bar x(t)\|
 \le\frac{\epsilon\|B\|}{c}
             \left(\|w_0\|+\frac{D_0M_0}{m}\right).
\]

**证明。** 全能量满足 $dU/dt=-\|\nabla_xU\|^2-\epsilon^{-1}\|\nabla_zU\|^2\le0$，因此 $\|(x_\epsilon,z_\epsilon)\|\le R_0$，且 $\|\dot x_\epsilon\|\le M_0$。令 $w=z_\epsilon+C^{-1}B^{\mathsf T}x_\epsilon$，直接求导得
\[
 \dot w=-\epsilon^{-1}Cw+C^{-1}B^{\mathsf T}\dot x_\epsilon,
\]
从而
\[
 \|w(t)\|\le e^{-ct/\epsilon}\|w_0\|
          +\frac{\epsilon D_0M_0}{c}(1-e^{-ct/\epsilon}).
\]
又有 $\dot x_\epsilon=-Sx_\epsilon-Bw$。两轨迹初始 $x$ 相同，故差为 $-\int_0^te^{-S(t-s)}Bw(s)ds$。对初始层一项用 $e^{-m(t-s)}\le1$ 及 $\int_0^te^{-cs/\epsilon}ds\le\epsilon/c$；对持续项用 $\int_0^te^{-m(t-s)}ds\le1/m$，相加得到一致界。快慢比例、完整能量正定性和有效谱隙共同提供闭合控制；仅有自由能公式没有给出这些动力学前提。证毕。

**定理 20.5（隐藏状态熵改变有效地形的曲率）。** 设有限指标集 $I$ 上有固定正权重 $r_i$，$\sum_i r_i=1$，光滑能量 $E_i:\mathbb R^d\to\mathbb R$。令
\[
 A_\tau(x)=-\tau\log\sum_i r_i e^{-E_i(x)/\tau},\qquad
 p_i(x)=\frac{r_i e^{-E_i(x)/\tau}}{\sum_jr_j e^{-E_j(x)/\tau}}.
\]
则
\[
 \nabla A_\tau=\mathbb E_p\nabla E_i,\qquad
 \nabla^2 A_\tau=\mathbb E_p\nabla^2E_i
                   -\tau^{-1}\operatorname{Cov}_p(\nabla E_i).
\]
即使每个 $E_i$ 都严格凸，$A_\tau$ 仍可非凸。具体地，对 $a>0$、$E_\pm(x)=(x\mp a)^2/2$、$r_\pm=1/2$，
\[
 A_\tau(x)=\frac{x^2+a^2}{2}-\tau\log\cosh(ax/\tau).
\]
若 $\tau\ge a^2$，唯一极小点为 $0$；若 $0<\tau<a^2$，$0$ 是严格局部极大点，恰有两个全局极小点 $\pm x_\tau$，其中 $0<x_\tau<a$ 且
\[
 x_\tau=a\tanh(ax_\tau/\tau).
\]

**证明。** 直接求导得 $\nabla p_i=-\tau^{-1}p_i(\nabla E_i-\mathbb E_p\nabla E_i)$，代入 $\nabla A_\tau$ 的导数即得 Hessian 公式。协方差半正定，因此隐藏分量的力差异可以降低有效曲率。

对所给双分量，合并指数得到 $\cosh$ 表达式，故 $A_\tau'(x)=x-a\tanh(ax/\tau)$，$A_\tau''(0)=1-a^2/\tau$。若 $\tau\ge a^2$，对 $x>0$ 用 $\tanh u<u$ 得 $A_\tau'(x)>0$，偶对称性给唯一极小点。若 $\tau<a^2$，导数在零点右侧为负，在 $x=a$ 为正；它的导数 $1-(a^2/\tau)\operatorname{sech}^2(ax/\tau)$ 在 $x>0$ 严格递增，所以 $A_\tau'$ 先降后升，并恰有一个正零点。对称性给两个极小点，且 $A_\tau(x)\to+\infty$ 当 $|x|\to\infty$，因此它们都是全局极小点。这是指定潜能和权重的精确分岔，不表示一般熵正则化必定使所有优化目标凸。证毕。

## 21. 本批来源、适用域与证明身份

**出处 21.1（经典桥与本卷推导）。** 第 17.2、17.3 条的梯度耗散和概率几何，第 18.2、18.4 条的 Gibbs 与 KL 控制，第 18.5 条的有限图热力学变分属于经典结构，本批按所需约定给出证明。第 18.3、19.2 至 19.5、20.2 至 20.5 条及第 17.4 条的具体陈述列为 `repo-derived`：它们由正文假设直接推导，未确立全球首创。第 19.3 条的费用测度等价与第 19.5 条的尖锐误差实例，约束从精确行为商迁移到优化商所需的新增信息。文献中的连续随机系统、量子耗散及 Sinkhorn 流不被假定已经在本卷完成相应形式化。

[^tcs3-thermogeo]: Olga Movilla Miangolarra、Ralph Sabbagh、Artemy Kolchinsky，*Wasserstein-2 gradient flows and the geometry of entropy production in classical and quantum stochastic thermodynamics*，arXiv:2606.00698v1，2026，[原文](https://arxiv.org/pdf/2606.00698)。实际读取第 II 节式 (1)–(10) 的梯度流、自由能、连续性方程及作用量距离定义，以及第 IV 节保守/耗散几何比较的范围。该文研究不同动力学及迁移率下的距离；不能据此给任意动力学指定同一个耗散几何。此引用仅承接上述数学背景，不把本文有限观察商定理归给该文。

[^tcs3-todorov]: Emanuel Todorov，*Linearly-solvable Markov decision problems*，NIPS 2006，[官方论文条目](https://papers.nips.cc/paper_files/paper/2006/hash/d806ca13ca3449af72a1ea5aedbed26a-Abstract.html)。`literature-attested` 范围：参考转移的 KL 控制费用、指数变换及线性 Bellman 结构；第 18.4 条明确控制变量为后继概率分布。

[^tcs3-leonard]: Christian Léonard，*A survey of the Schrödinger problem and some of its connections with optimal transport*，DCDS 34(4), 1533–1574，2014，[作者预印本](https://arxiv.org/abs/1308.0215)。参考范围：路径相对熵、端点约束与最优传输之间的关系。本文第 18.3 条只证明有限路径纤维上的分解，不声称已经给出连续 Schrödinger 桥的存在唯一性。

[^tcs3-pressure]: 第 18.5 条在有限不可约矩阵上直接使用 Perron 正特征向量、KL 非负性和有限环流分解完成证明。邻接图路径数提供热力学压力与熵的有限状态实例；它与第 12 节观察熵相认时，还需观察足以区分被计数的状态路径。计数参考和概率参考的常数项依本批定义分别保留。

[^tcs3-gibbs]: 固定仓库来源：[D5/S3/Divergence/StrictGibbs.lean](https://github.com/the-omega-institute/trureturing/blob/11036b0baf142c8e6535e61f29d2cae83ecf7bba/D5/S3/Divergence/StrictGibbs.lean)，用于有限 KL 严格性背景；[D5/S3/Observer/DynamicProgramming/BellmanContraction.lean](https://github.com/the-omega-institute/trureturing/blob/11036b0baf142c8e6535e61f29d2cae83ecf7bba/D5/S3/Observer/DynamicProgramming/BellmanContraction.lean) 的 `bellman_operator_contracting_unique_fixed_point` 研究折扣预测距离的最大型算子。该声明不等同于本批未折扣、费用加权的软 Bellman 算子，不直接当作本批下降判据的证明项。

[^tcs3-schur]: 仓库中已有 Schur 能量与互补块消元构件，检索到 [D5/S3/Weil/ZetaLinear/ExactStickyReduction.lean](https://github.com/the-omega-institute/trureturing/blob/11036b0baf142c8e6535e61f29d2cae83ecf7bba/D5/S3/Weil/ZetaLinear/ExactStickyReduction.lean)。其能量正定/惯性背景与本批全空间梯度流的投影问题分开计量；第 20 节给出所用二次模型的完整平方分解及动力学证明，不新增绑定包装。

**出处 21.2（前沿几何的额外限制）。** Mathis Hardion、Hugo Lavenant，*Gradient Flows of Potential Energies in the Geometry of Sinkhorn Divergences*，arXiv:2511.14278v1，2025，[原文](https://arxiv.org/pdf/2511.14278)。实际读取引言、Theorem 1.1、Sinkhorn-JKO 定义及论文对 Theorem 4.2、7.1 的适用范围说明。作者明确指出 Sinkhorn divergence 一般不是距离的平方，极限方案收敛另有条件。因此第 17 节的测地距离不被机械替换为任意 Sinkhorn divergence；“改变几何会改变下降动力学”是本批对接该文的范围。

**约定 21.3（产地及核验）。** 本批使用仓库 `theory-volume-template/APPEND.md`。数学推导、资料核对、文字实施和有限自检由本会话 ChatGPT 单席串行完成，无独立模型或作者审定。正文给出纸面证明，不新增 Lean、Scribe 或机器派生状态。未运行 canonical `make ingest`，不宣称消化账本登记完成。有限算例、矩阵代数和数值解核对只用于检错，不替代无限时域、全部温度和全部终端费用的量词。原文献的数学结果与本批结果均未被本次工作标记为 kernel-verified。

## 追加锚（本行以下为增补区）

## 22. 本批公式排版与正时间约定

**勘误 22.1（第 17.4 条平方项系数）。** 第 17.4 条第一条等式的第二个平方积分前，序列化把 TeX 的分数命令首部写成了换页控制字符。该处完整等式应读为
\[
 I_T(z)=U(z(T))-U(z(0))+\frac14\int_0^T\|\dot z-\nabla U(z)\|^2dt.
\]
其系数为四分之一，与同条证明中两个平方之差的展开一致。本条只校正排版，不改变路径假设、势垒不等式及证明。按追加纪律保留原字节，此处明确替代受损公式的读法。

**约定 22.2（第 17.3 条正时间）。** 第 17.3 条含有除以总时长的距离界，使用的时间区间满足 $T>0$。其自由能恒等式和导数公式沿给定光滑解成立；端点距离界仅在这个正时间约定下陈述。

## 追加锚（本行以下为增补区）

## 23. 增补四·有限可逆系统的热边缘与不可逆性边界

**本批导航。** 本批直接接续本卷 `adba22e5f55087c2ce96e30d99cb55a84e8f3c39`，已核对 `dev@f190d1afb930c1fe9e5f0896736737ae81eeb0a4` 及 PR #8891 的 `8d58dc56d0e6283e725054b5a25c6d5ce8104cc6`。后者已把热相关曲率与隐藏耦合、记忆核、有限数据证书及量子 Kubo 相关连接，本批复用这些对象，不再将其作为新增结果。第 23 节研究边缘演化何时能够形成半群；第 24 节从三时刻相关求条件信息，并证明绝对相关误差、Markov 近似损失与时间反转不对称可以分离；第 25、26 节分别构造经典与量子重置极限。本批扩充第 17–20 节，不改判其数学结论，不修改任何旧字节。此前伴卷保留为固定引用，此后本线推导归入本卷。

**定义 23.1（能量归一的可见与隐藏分块）。** 取有限维实反对称矩阵
\[
 \Omega=\begin{pmatrix}D&B\\-B^{\mathsf T}&E\end{pmatrix},
 \quad D\in\mathbb R^{r\times r},\quad E\in\mathbb R^{k\times k},
 \quad r,k\ge1,
\]
其中 $D,E$ 反对称，令 $M=BB^{\mathsf T}$、$g=\|B\|_2$。以 $Q=(I_r\ 0)$、$P=(0\ I_k)$ 为坐标投影，记
\[
 F_t=Qe^{t\Omega}Q^{\mathsf T},\qquad L_t=Qe^{t\Omega}P^{\mathsf T}.
\]
热坐标采用标准 Gaussian 参考 $\gamma_r\otimes\gamma_k$。对任意可见初始分布 $\nu$，以隐藏初态 $V_0\sim\gamma_k$ 独立初始化，定义概率核
\[
 \mathsf T_t(u,\cdot)=\mathcal N(F_tu,I_r-F_tF_t^{\mathsf T}),\qquad t\ge0.
\]
允许退化 Gaussian。该核对应一次联合初始化后演化到 $t$ 并取边缘；连续复合核意味着每段重新初始化隐藏变量，二者的过程语义分别指定。正定二次 Hamilton 系统经 $S^{1/2}$ 及正交分块可得到此模型，$\Omega$ 可逆时对应非退化 Poisson 结构。以下有限反对称模型也允许零频率。热量纲已吸收到坐标中，$D_{\rm KL}$ 均用自然对数。

**定理 23.2（单时刻热保持与隐藏信息账）。** 定义 23.1 中，$\|F_t\|\le1$、$L_tL_t^{\mathsf T}=I-F_tF_t^{\mathsf T}$，且 $\mathsf T_t\gamma_r=\gamma_r$。若 $D_{\rm KL}(\nu\Vert\gamma_r)<\infty$，令 $\mu_t$ 为联合初态 $\nu\otimes\gamma_k$ 的完整演化，$\mu_t^V$ 为隐藏边缘，则
\[
 D_{\rm KL}(\nu\Vert\gamma_r)-D_{\rm KL}(\mathsf T_t\nu\Vert\gamma_r)
 =I(U_t:V_t)+D_{\rm KL}(\mu_t^V\Vert\gamma_k)\ge0.
\]
此不等式分别比较每个 $t$ 与同一个初始时刻，没有蕴含两个任意正时刻之间的单调性。

**证明。** $e^{t\Omega}$ 正交，取其第一块行与转置相乘，得到 $F_tF_t^{\mathsf T}+L_tL_t^{\mathsf T}=I$。独立热隐藏变量给出定义中的条件分布，且标准 Gaussian 参考被完整正交变换保持，故边缘热参考也保持。完整流可逆且保持参考测度，所以 $D_{\rm KL}(\mu_t\Vert\gamma_r\otimes\gamma_k)=D_{\rm KL}(\nu\Vert\gamma_r)$。将左侧按两个边缘展开为 $D_{\rm KL}(\mu_t^U\Vert\gamma_r)+D_{\rm KL}(\mu_t^V\Vert\gamma_k)+I(U_t:V_t)$，得到恒等式。有限总相对熵保证上述非负项有限。这里的信息丢失使用相对参考的可区分性，不把边缘微分熵本身强制单调。证毕。

**定理 23.3（有限封闭模型的半群与全时间单调性充要条件）。** 下列四项等价：$B=0$；全部核满足 $\mathsf T_{t+s}=\mathsf T_t\mathsf T_s$；完整热初态下的可见平稳过程具有 Markov 性；对每个有限相对熵的 $\nu$，函数 $t\mapsto D_{\rm KL}(\mathsf T_t\nu\Vert\gamma_r)$ 在 $[0,\infty)$ 非增。成立时 $F_t=e^{tD}$，边缘演化为无随机噪声的正交流。若 $B\ne0$，存在平移热初态，其相对热参考的信息先损失、随后回流。

**证明。** $B=0$ 时各结论直接由分块正交流成立，相对熵保持常数。若核为半群，比较对确定初态的均值可得 $F_{t+s}=F_tF_s$。矩阵函数在零点解析，故 $F'_0=D$、$F''_0=D^2$；而直接展开完整指数给 $F''_0=D^2-BB^{\mathsf T}$，所以 $B=0$。热平稳可见过程若 Markov，其两时刻条件核恰为 $\mathsf T_t$，Chapman–Kolmogorov 等式给半群；核等式先对热边缘几乎处处成立，均值的线性及满支持使其对所有初值成立。

最后假设第四项，取 $\nu=\mathcal N(a,I_r)$，则 $\mathsf T_t\nu=\mathcal N(F_ta,I_r)$，相对熵为 $\|F_ta\|^2/2$。有限反对称矩阵存在 $t_j\to\infty$ 使 $e^{t_j\Omega}\to I$：对有限个旋转频率作同时有理逼近，若逼近整数序列无界直接取子列；若有有界重复分母，则得到精确公共周期并取其倍数。因此 $F_{t_j}a\to a$。从 $t=0$ 非增且在无穷子列回到原值，只能在每个时刻保持原值。又
\[
 F_t^{\mathsf T}F_t=I-t^2M+O(t^3),
\]
故对任意 $a$ 都有 $a^{\mathsf T}Ma=0$，从而 $M=0$。若 $M\ne0$，取 $a^{\mathsf T}Ma>0$ 即有早期严格损失和后续回升。结论只针对固定有限维、固定生成元和全部时间；它不排除有限窗口近似、无限热浴或不同尺度极限。证毕。

## 24. 三时刻条件信息、Markov 损失与时间箭头的分离

**定义 24.1（三时刻协方差）。** 在定义 23.1 的完整热初态下，观察 $U_0,U_s,U_{s+t}$，$s,t>0$。定义
\[
 A_s=I-F_s^{\mathsf T}F_s,\qquad C_t=I-F_tF_t^{\mathsf T},\qquad
 R_{s,t}=F_{s+t}-F_tF_s.
\]
在三时刻联合协方差正定时，令 $Z_{s,t}=C_t^{-1/2}R_{s,t}A_s^{-1/2}$，并记 $\mathcal I(s,t)=I(U_0:U_{s+t}\mid U_s)$。这个实验采用无额外传感噪声的真实线性读数；加入传感器噪声后须重新使用其联合协方差。

**定理 24.2（相关半群残差的条件信息公式）。** 在定义 24.1 的正定条件下，$\|Z_{s,t}\|<1$，且
\[
 \mathcal I(s,t)=-\tfrac12\log\det(I-Z_{s,t}Z_{s,t}^{\mathsf T}),
\]
\[
 \tfrac12\|Z_{s,t}\|_F^2\le\mathcal I(s,t)
 \le\frac{\|Z_{s,t}\|_F^2}{2(1-\|Z_{s,t}\|_2^2)}.
\]
另有
\[
 R_{s,t}=Qe^{t\Omega}P^{\mathsf T}Pe^{s\Omega}Q^{\mathsf T},\qquad
 \|R_{s,t}\|\le\min(1,tg)\min(1,sg).
\]
三时刻条件独立当且仅当 $R_{s,t}=0$。只有最后一项绝对残差很小，尚不足以保证条件信息很小。

**证明。** 完整指数的乘法与 $Q^{\mathsf T}Q+P^{\mathsf T}P=I$ 给出残差恒等式。由分块变参数公式，两个跨块指数分别具有 $tg,sg$ 上界，又都是正交矩阵的压缩，范数至多一。Gaussian 条件化给定 $U_s$ 后，$(U_0,U_{s+t})$ 的条件协方差为
\[
 \begin{pmatrix}A_s&R_{s,t}^{\mathsf T}\\R_{s,t}&C_t\end{pmatrix}.
\]
正定性给 Schur 补 $I-Z_{s,t}Z_{s,t}^{\mathsf T}\succ0$。用 Gaussian 条件熵的行列式公式得互信息表达式。逐奇异值使用 $x\le-\log(1-x)\le x/(1-x_*)$，$0\le x\le x_*<1$，得到两侧界。Gaussian 条件独立恰等价于条件交叉协方差为零。白化因子包含条件协方差的逆，说明绝对残差界不能单独控制条件信息。证毕。[^tcs4-gaussian]

**定理 24.3（相关误差趋零、条件记忆发散且路径反转差为零）。** 取有限个正频率、正权重且权重和为一，设标量热观察的相关函数为
\[
 f(t)=\sum_{j=1}^kw_j\cos(\omega_jt),\quad
 a=\sum_jw_j\omega_j^2>0,\quad b=\sum_jw_j\omega_j^4>a^2.
\]
该过程可由独立正定振子的 Gaussian 初态实现。对于充分小 $h>0$，三时刻协方差正定，且
\[
 \boxed{I(U_0:U_{2h}\mid U_h)
 =-\log h-\tfrac12\log\frac{b-a^2}{a}+O(h^2).}
\]
同时 $f(2h)-f(h)^2=-ah^2+O(h^4)$。对任意有限 $N$、任意 $h$，$(U_0,U_h,\ldots,U_{Nh})$ 与其坐标反转有相同分布，所以二者 KL 差为零。特别地，$f(t)=(\cos t+\cos2t)/2$ 时对数常数中 $(b-a^2)/a=9/10$。

**证明。** 每个归一振子位置读数方差为一，以系数 $\sqrt{w_j}$ 合成即可得到此平稳 Gaussian 过程。置 $v_h=1-f(h)^2$、$c_h=f(2h)-f(h)^2$。Taylor 展开给出
\[
 v_h=ah^2-(a^2/4+b/12)h^4+O(h^6),
\]
\[
 c_h=-ah^2+(7b/12-a^2/4)h^4+O(h^6),
\]
\[
 1-(c_h/v_h)^2=\frac{b-a^2}{a}h^2+O(h^4).
\]
因此 $v_h>0$，条件协方差行列式 $v_h^2-c_h^2=a(b-a^2)h^6+O(h^8)>0$；中间变量方差为一，整个三时刻协方差亦正定。代入定理 24.2 的标量公式得到渐近式。对任意 $N$，协方差的第 $(i,j)$ 项为 $f((i-j)h)$。$f$ 偶对称使其在同时将 $i,j$ 换为 $N-i,N-j$ 后不变；零均值 Gaussian 法则即使退化也由协方差决定，所以正反路径法则完全一致。最后 $a=5/2,b=17/2$ 给所列常数。该发散对应越来越密集且精确的读数，不能忽略额外噪声后将其当作可免费提取的无限信息。证毕。

**定理 24.4（最佳一阶 Markov 近似的精确路径损失）。** 设 $X_0,\ldots,X_N$ 具有严格正联合密度，以下 KL 积分均有限；有限离散全支持情形同理。令
\[
 p^{\rm M}(x_{0:N})=p_0(x_0)\prod_{j=1}^Np(x_j\mid x_{j-1}).
\]
对任意 Markov 密度 $q=q_0\prod_{j=1}^Nq_j(x_j\mid x_{j-1})$，有
\[
 D_{\rm KL}(p\Vert q)
 =\sum_{j=2}^NI(X_j:X_{0:j-2}\mid X_{j-1})
 +D_{\rm KL}(p_0\Vert q_0)
 +\sum_{j=1}^N\mathbb E_{X_{j-1}}
 D_{\rm KL}(p(\cdot\mid X_{j-1})\Vert q_j(\cdot\mid X_{j-1})).
\]
因此前一求和是全部一阶 Markov 模型的最小正向 KL 损失，由 $p^{\rm M}$ 达到。定理 24.3 的三时刻实例中，这个最小损失发散，而同一真实路径的反转 KL 恒为零。

**证明。** 将真实联合密度按完整历史条件化。每个对数比内插 $p(x_j\mid x_{j-1})$，第一部分的期望按条件互信息定义得到，第二部分对旧历史积分后只剩相邻边缘的条件 KL。初始项另列，得到恒等式及极小性。最后代入 $N=2$。此式度量错误删除历史的模型损失；第 18.2 条的自由能差使用 $D_{\rm KL}(q\Vert p^*)$，KL 方向不同，本文没有将两者自动相等。有限封闭模型的更长路径可能奇异，不能在没有密度条件时照搬本条积分写法。证毕。[^tcs4-sagawa]

**推论 24.5（三个延迟相关值的稳健记忆下界）。** 在定义 24.1 的条件下，若 $\widehat F_s,\widehat F_t,\widehat F_{s+t}$ 的算子范数误差各不超过 $\delta$，令 $\widehat R=\widehat F_{s+t}-\widehat F_t\widehat F_s$。则无需对经验条件协方差求逆，即有
\[
 \boxed{\mathcal I(s,t)\ge\tfrac12
 \bigl(\|\widehat R\|_F-\sqrt r(3\delta+\delta^2)\bigr)_+^2.}
\]

**证明。** $\|F_u\|\le1$ 给 $\|\widehat R-R_{s,t}\|\le3\delta+\delta^2$。又 $A_s,C_t\preceq I$，所以 $R_{s,t}=C_t^{1/2}Z_{s,t}A_s^{1/2}$ 给 $\|R_{s,t}\|_F\le\|Z_{s,t}\|_F$。结合 Frobenius 误差至多为 $\sqrt r$ 倍算子范数误差及定理 24.2 的下界即可。该证书可以认证非零记忆；下界等于零仅表示当前精度不足。误差预算应先包含真实白化和传感器误差，不能从未校准相关矩阵直接套用。证毕。

## 25. 隐藏重置的连续极限与耗散的尺度来源

**定义 25.1（每步新热隐藏变量）。** 固定步长 $h>0$，每步以独立 $\gamma_k$ 隐藏变量与当前可见状态共同演化时长 $h$，然后只保留可见状态。所得 Markov 链的单步核是 $\mathsf T_h$。这些重置是额外的物理或模型操作；一次初始化后继续保留同一个隐藏系统的轨迹仍由定义 23.1 的完整流给出。

**定理 25.2（固定耦合下无限频繁重置消去累积耗散）。** 在定义 25.1 中，$n$ 步后的条件均值与条件噪声协方差为
\[
 F_h^nu_0,\qquad I-F_h^n(F_h^n)^{\mathsf T}.
\]
对所有整数 $n\ge0$，有
\[
 \|F_h^n-e^{nhD}\|\le\tfrac12nh^2g^2,
 \qquad
 \|I-F_h^n(F_h^n)^{\mathsf T}\|\le nh^2g^2.
\]
因此对固定宏观时间 $T$，在 $nh\le T$、$h\downarrow0$ 时，均值趋于无耗散正交流，累积噪声趋零。

**证明。** 单步独立噪声的协方差为 $I-F_hF_h^{\mathsf T}$，递推求和望远镜消去给出 $n$ 步公式。对初始可见向量、隐藏初态为零的完整确定性流，隐藏分量在时间 $s$ 的范数至多为 $sg$ 倍初态范数；将其代回可见变参数公式，得到 $\|F_h-e^{hD}\|\le h^2g^2/2$。这也是 PR #8891 的条件均值二阶界。由于两因子均收缩，矩阵幂差的 $n$ 项望远镜展开给第一条界。再与正交矩阵 $e^{nhD}$ 比较乘积，得到协方差界。结果追踪了物理等待时间与重置次数，没有把一个有限热浴直接等同于新噪声连续注入。证毕。[^tcs4-remote]

**定理 25.3（平方根耦合缩放产生 OU 自由能耗散）。** 固定 $D,E,B$，将每步生成元改为
\[
 \Omega_h=\begin{pmatrix}D&B/\sqrt h\\-B^{\mathsf T}/\sqrt h&E\end{pmatrix},
 \qquad F^{(h)}=Qe^{h\Omega_h}Q^{\mathsf T},\qquad A_*=D-M/2.
\]
每步按定义 25.1 重新初始化隐藏变量。则
\[
 F^{(h)}=I+hA_*+O(h^2),
\]
且对每个有限 $T$ 存在不依赖 $h,n$ 的常数，使 $nh\le T$ 时
\[
 \|(F^{(h)})^n-e^{nhA_*}\|=O(Th),
\]
累积条件协方差收敛到 $I-e^{tA_*}e^{tA_*^{\mathsf T}}$，其中 $nh\to t$。极限核是
\[
 dX_t=(D-M/2)X_t\,dt+B\,dW_t,
\]
以 $\gamma_r$ 为平稳分布。对给定的光滑正密度解及可作分部积分的衰减条件，
\[
 \boxed{\frac d{dt}D_{\rm KL}(\rho_t\Vert\gamma_r)
 =-\tfrac12\int\rho_t
 \|B^{\mathsf T}\nabla\log(\rho_t/\gamma_r)\|^2dx.}
\]

**证明。** 记 $L_0=\operatorname{diag}(D,E)$、$K_0=\left(\begin{smallmatrix}0&B\\-B^{\mathsf T}&0\end{smallmatrix}\right)$，则 $h\Omega_h=hL_0+\sqrt hK_0$。指数级数的可见对角块中，含奇数个 $K_0$ 的单词为零。零阶、一次 $L_0$ 与两次 $K_0$ 给 $I+hD-hM/2$，其余非零项至少为 $h^2$。若 $\ell=\|L_0\|$、$0<h\le1$，余项可用
\[
 h^2\left[\ell^2/2+(3\ell g^2+\ell^3)/6
                +(\ell+g)^4e^{\ell+g}/24\right]
\]
控制：分别估计二、三阶剩余项和四阶起的指数尾项。$A_*+A_*^{\mathsf T}=-M\preceq0$ 使 $e^{tA_*}$ 收缩，$F^{(h)}$ 也是正交压缩。与 $e^{hA_*}$ 比较，再对 $n$ 次幂作望远镜展开，得到一致有限时域的误差界。噪声协方差仍使用定理 25.2 的精确望远镜恒等式。

线性随机方程的显式解具有协方差 $\int_0^te^{sA_*}Me^{sA_*^{\mathsf T}}ds=I-e^{tA_*}e^{tA_*^{\mathsf T}}$，所以其转移核即上述极限。Fokker–Planck 方程写成
\[
 \partial_t\rho=-\nabla\cdot(Dx\rho)
 +\tfrac12\nabla\cdot\{M[\nabla\rho+x\rho]\}.
\]
对相对熵求导并分部积分，$D$ 的零散度及 $x^{\mathsf T}Dx=0$ 使第一项贡献为零，第二项给所列平方耗散。$M$ 可退化，本文只对满足上述正则性条件的解使用导数公式。该极限同时改变耦合尺度、环境更新与时间步；没有把它当作固定有限封闭系统的长时间极限。证毕。[^tcs4-collision]

## 26. 量子有限环境中的二阶误差与热恢复缺陷

**定义 26.1（按热参考中心化的量子相互作用）。** 取有限维子系统 $A,B$，$H=H_A\otimes I+I\otimes H_B+V$，各 Hamilton 算子自伴。令 $\tau_B\succ0$ 为满足 $[H_B,\tau_B]=0$ 的密度矩阵，例如有限温度 Gibbs 态。定义
\[
 V_A=\operatorname{Tr}_B[V(I\otimes\tau_B)],\quad
 H_A^*=H_A+V_A,\quad W=V-V_A\otimes I,\quad g_q=\|W\|.
\]
$V_A$ 自伴，$\operatorname{Tr}_B[W(I\otimes\tau_B)]=0$。记 $\Phi_t(\rho)=\operatorname{Tr}_B(e^{-itH}(\rho\otimes\tau_B)e^{itH})$，并以 $\mathcal U_t^A$ 表示 $H_A^*$ 的酉信道。本节取 $\hbar=1$，迹范数不含二分之一。

**定理 26.2（热匹配初态的二阶界与一般初态的信息修正）。** 对任意可见密度矩阵 $\rho_A$ 和 $t\ge0$，
\[
 \|\Phi_t(\rho_A)-\mathcal U_t^A(\rho_A)\|_1
 \le\min\{2,2g_q^2t^2\}.
\]
对任意联合态 $\rho_{AB}$，设 $\chi=\rho_{AB}-\rho_A\otimes\tau_B$，
\[
 \mathscr E=D_{\rm KL}(\rho_{AB}\Vert\rho_A\otimes\tau_B)
 =I(A:B)_\rho+D_{\rm KL}(\rho_B\Vert\tau_B).
\]
则
\[
 \|\operatorname{Tr}_B(e^{-itH}\rho_{AB}e^{itH})
               -\mathcal U_t^A(\rho_A)\|_1
 \le\min\{2,2g_q^2t^2+2g_qt\|\chi\|_1\}
 \le\min\{2,2g_q^2t^2+2g_qt\sqrt{2\mathscr E}\}.
\]

**证明。** 相对于 $H_A^*\otimes I+I\otimes H_B$ 取相互作用绘景，令 $W_t$ 为旋转后的 $W$。其范数为 $g_q$，且因 $\tau_B$ 平稳，$\operatorname{Tr}_B[W_t(I\otimes\tau_B)]=0$。对于产品初态 $\sigma_0=\rho_A\otimes\tau_B$，一次 Duhamel 项在偏迹后为零。再次积分精确方程 $\dot\sigma_t=-i[W_t,\sigma_t]$，余项为
\[
 -\int_0^t ds\int_0^s dr\,[W_s,[W_r,\sigma_r]].
\]
用 $\|[W,X]\|_1\le2\|W\|\|X\|_1$、$\|\sigma_r\|_1=1$ 及偏迹在 Hermitian 算子上的迹范数收缩，得到 $4g_q^2$ 乘三角积分面积，即 $2g_q^2t^2$。旋回绘景不改变迹范数。

一般初态按 $\sigma_0+\chi$ 分开。自由演化后的 $\chi$ 偏迹仍为零；完整与自由酉演化在 Hermitian 输入 $\chi$ 上的一次 Duhamel 差至多为 $2g_qt\|\chi\|_1$。两部分相加得第一界。支持包含关系 $\operatorname{supp}\rho_{AB}\subseteq\operatorname{supp}\rho_A\otimes\mathcal H_B$ 及 $\tau_B\succ0$ 保证 $\mathscr E$ 有限；分解乘积参考的对数得相关性与隐藏非平衡两项。量子 Pinsker 不等式给 $\|\chi\|_1\le\sqrt{2\mathscr E}$。该精度提升依赖参考匹配的初始化；相关性或隐藏非平衡可以重新引入一阶项。证毕。[^tcs4-recovery]

**命题 26.3（同一个两比特模型中的尖锐系数、熵回流与重置极限）。** 令 $H=gZ\otimes Z$、$g>0$，隐藏参考为 $I/2$，可见初态为 $|+\rangle\langle+|$。则
\[
 \Phi_t(\rho)=\cos^2(gt)\rho+\sin^2(gt)Z\rho Z,
 \qquad\|\Phi_t(\rho)-\rho\|_1=2\sin^2(gt).
\]
所以定理 26.2 的二阶系数 $2g^2$ 在小时间达到。可见熵在 $t=0,\pi/(4g),\pi/(2g)$ 分别为 $0,\log2,0$。若每隔 $h$ 更换独立隐藏比特，则 $n$ 步相干因子为 $\cos(2gh)^n$：固定 $g$、$nh\to t$ 时趋于一；改用 $g_h=g/\sqrt h$ 时趋于 $e^{-2g^2t}$，对应生成元
\[
 \dot\rho=g^2(Z\rho Z-\rho).
\]

**证明。** 在隐藏 $Z$ 基上，联合酉是两个条件旋转 $e^{\mp igtZ}$。各半权重平均后展开给出信道公式；$\rho$ 与 $Z\rho Z$ 正交，迹范数差为 $2\sin^2(gt)$。两个非零特征值为 $\cos^2(gt),\sin^2(gt)$，得到熵值。每次独立重置使相干因子相乘。对足够小的 $h$，用 $\log\cos x=-x^2/2+O(x^4)$ 得两个极限，生成元在对角元上为零，在非对角元上为 $-2g^2$。这些极限的区别由重置操作及耦合尺度造成；闭系统的酉演化本身保持联合熵。证毕。[^tcs4-collision]

## 27. 本批结果的文献比较与证明范围

**出处 27.1（逐项贡献定位）。** 定理 23.2 的条件 KL 账、定理 24.2 的 Gaussian 信息行列式、定理 24.4 的条件 KL 分解、定理 25.3 的碰撞尺度及命题 26.3 的去相干模型均使用经典构件，不能计为同名理论的首次发现。本批相对于本卷旧版新增的是：有限可逆载体上精确半群与全时间信息单调的联合判据；三时刻残差到条件信息及稳健下界的连接；小残差、发散条件记忆和零时间反转 KL 同时成立的明确双振子族；同一参考恢复缺陷进入量子预测误差的一阶项。这些具体陈述均有正文推导，记为 `repo-derived`，表示在本卷推导得到，不表示已排除文献中的同等或更强结论。

[^tcs4-remote]: 固定远端来源：[PREDICTIVE_OBSERVABILITY_TIME_WINDOWS.md](https://github.com/the-omega-institute/trureturing/blob/8d58dc56d0e6283e725054b5a25c6d5ce8104cc6/docs/develop/theory/PREDICTIVE_OBSERVABILITY_TIME_WINDOWS.md) 第 12–19 节，已经给出相关曲率 $M$、记忆核、二阶条件均值界、Bayes 误差和有限延迟证书。本批读取后直接复用，不重复认领。其 Kubo 相关恒等式属于量子线性响应，未被本文当成无反作用的经典三时刻测量法则。该 PR 的电磁卷进一步区分磁场下的状态可观测性与方向可辨识性，本批不改写其证明。

[^tcs4-gaussian]: Charles R. Baker，*Mutual Information for Gaussian Processes*，SIAM Journal on Applied Mathematics 19(2), 451–458 (1970)，DOI [10.1137/0119044](https://doi.org/10.1137/0119044)，给出协方差算子与 Gaussian 互信息的经典关系。Sarah Marzen、James P. Crutchfield，*Information Anatomy of Stochastic Equilibria*，Entropy 16(9), 4713–4748 (2014)，[作者正文](https://www.mdpi.com/1099-4300/16/9/4713)，第 2、3 节及 Appendix E 已区分过去、现在、未来的条件信息，并讨论小采样间隔的发散。本批定理 24.3 固定有限振子模型，证明其具体系数及零反转 KL，不将一般“隐藏记忆可由条件信息度量”列为新概念。

[^tcs4-sagawa]: Takahiro Sagawa，*Stochastic Thermodynamics for Autoregressive Generative Models: A Non-Markovian Perspective*，实际读取 [arXiv:2604.07867v3](https://arxiv.org/html/2604.07867v3) 第 VII.2 节式 (89)–(93) 与 Appendix A。文中已将回顾推断分成条件互信息压缩损失与模型失配；本文的正向 Markov 拟合使用同一经典 KL 链式法则，但比较对象不是作者指定的反向生成过程。出版方记录该论文于 2026-09-10 被 PRX Intelligence 接收，DOI [10.1103/tv38-b23y](https://doi.org/10.1103/tv38-b23y)；本次可读取全文为 v3，不推断无法读取的更新版字节。第 24.3 条的反转法则是实际平衡路径的坐标反转，不能与任意模型反向协议混同。

[^tcs4-collision]: Stéphane Attal、Yan Pautrat，*From repeated to continuous quantum interactions*，[arXiv:math-ph/0311002v2](https://arxiv.org/abs/math-ph/0311002v2)，明确研究不同耦合尺度下从重复相互作用到连续量子噪声的极限。Francesco Ciccarello、Salvatore Lorenzo、Vittorio Giovannetti、G. Massimo Palma，*Quantum collision models: open system dynamics from repeated interactions*，Physics Reports 954 (2022)，[arXiv:2106.11974v2](https://arxiv.org/abs/2106.11974v2)，第 5 节及第 7 节给出主方程缩放和相关性熵账。已读取 PDF 解析正文；截图接口未成功返回，未引用其中图表。本文第 25 节给出有限实矩阵版本及误差预算，未认领碰撞极限思想的首创。

[^tcs4-recovery]: [PREDICTIVE_THERMODYNAMIC_SUFFICIENCY.md](https://github.com/the-omega-institute/trureturing/blob/e300b5df71f5ce08d857e8f2000a9e495813cdaf/docs/develop/theory/PREDICTIVE_THERMODYNAMIC_SUFFICIENCY.md) 第 3.3、3.4 条给出相互作用的一阶误差与恢复缺陷。定理 26.2 另按热参考重新中心化相互作用，用精确双重 Duhamel 余项把匹配初态改善为二阶，并把偏离该初态族的误差单独量化；这里的 $g_q$ 与伴卷全代数泄漏 $\delta(H)$ 不是同一定义。

**出处 27.2（最新记忆学习结果的范围）。** Quanjun Lang、Jianfeng Lu，*Learning Memory Kernels in Generalized Langevin Equations*，SIAM Journal on Mathematics of Data Science 8(1), 141–166 (2026)，DOI [10.1137/24M1651101](https://doi.org/10.1137/24M1651101)，已核对出版方条目与 [arXiv:2402.11705v3](https://arxiv.org/html/2402.11705v3) 第 2–4 节。其方法控制相关函数误差传向记忆核的误差；本批不重复该算法。本批三时刻证书只需三个已校准的相关值，用来检验删除历史的信息损失；有限浴回归与 Markov 极限又属于不同的模型假设。

**约定 27.3（产地与核验身份）。** 本批按 `theory-volume-template/APPEND.md` 直接追加原卷。数学、文献核对、文字实施及检错由本会话 ChatGPT 单席串行完成，没有独立模型或同行审阅。有限检查使用精确有理数/符号计算、双精度矩阵计算及 80 位标量计算，分别注明用途，不能替代一般证明。未新增 Lean、Scribe、工具、冻结记录或消化结算状态，未运行 Lean kernel、canonical `make ingest` 或仓库 CI。本文新增十条带证明结果，原条目全部保留；完整前缀字节比较用于检测误改，不代替消化账目核验。

## 追加锚（本行以下为增补区）

## 28. 增补五·固定热参考的精确熵收缩及量子维数边界

**本批导航。** 本批接续原卷 `c4b06639e9da9573f53bd841eed5e5312f9516ad`，读取的 dev 为 `806e7401e78a7b65587aac35370714b272ba2b46`，读取的 PR #8891 为 `bbea3408282f1bfb7e713f4f61f7e3b5be01f58d`。后者已将 #8899 合编进《统一预测几何》主卷，包含观测 Gramian、后验热恢复及磁场信息设计。本批不重复这些结果，在本卷第 25 节的耗散极限上继续研究：退化噪声如何经保守旋转耗散全部信息；经典与量子模型何时具有相同的精确收缩系数；有限延迟数据能够认证什么。第 1–27 节全部保留。本批不使用原卷中未完成远端交付的其他草稿编号。

**定义 28.1（固定参考的收缩系数）。** 对保持概率参考 $\gamma$ 的 Markov 核 $\mathcal K$，定义
\[
 \eta_\gamma(\mathcal K)=\sup_{0<D(\nu\Vert\gamma)<\infty}
      \frac{D(\mathcal K\nu\Vert\gamma)}{D(\nu\Vert\gamma)}.
\]
对保持满秩密度矩阵 $\tau$ 的量子信道 $\Phi$，同样定义 $\eta_\tau(\Phi)$，上确界取全部 $\rho\ne\tau$。所有对数为自然对数，迹范数不含二分之一。这里固定第二个相对熵变量，不讨论对任意两个输入同时取上确界的不同系数。经典参考 $\gamma_d$ 表示 $\mathcal N(0,I_d)$；量子参考 $I_2/2$ 表示最大混合态。后者一般不是非零 Hamilton 算子在有限正温度下的 Gibbs 态。

**定理 28.2（Gaussian 保持核的精确相对熵系数）。** 对 $F\in\mathbb R^{d\times d}$、$\|F\|_2\le1$，令
\[
 \mathcal K_F(x,\cdot)=\mathcal N(Fx,I_d-FF^{\mathsf T}),
\]
允许退化噪声。则
\[
 \boxed{\eta_{\gamma_d}(\mathcal K_F)=\|F\|_2^2.}
\]
上界适用于所有有限相对熵输入，包括非 Gaussian 输入；当 $F\ne0$ 时，沿最大右奇异向量的任意非零平移 Gaussian 输入达到该界。

**证明。** $X\sim\gamma_d$ 时输出仍为 $\gamma_d$。先考虑标量收缩核 $F=e^{-u}I_d$。对光滑、正且上下有界的参考密度 $f$，其 Ornstein–Uhlenbeck 演化 $Q_uf$ 满足
\[
 \frac{d}{du}\operatorname{Ent}_{\gamma_d}(Q_uf)
 =-\int\frac{|\nabla Q_uf|^2}{Q_uf}\,d\gamma_d,
 \qquad \nabla Q_uf=e^{-u}Q_u\nabla f.
\]
由加权 Cauchy–Schwarz 和参考不变性，右侧 Fisher 信息至多为 $e^{-2u}\int|\nabla f|^2/f\,d\gamma_d$。$Q_uf\to1$，由上下有界和控制收敛，其熵趋零；对上式从零到无穷积分得到 Gaussian 对数 Sobolev 不等式
\[
 \operatorname{Ent}_{\gamma_d}(f)\le\tfrac12\int|\nabla f|^2/f\,d\gamma_d.
\]
再将它用于每个 $Q_uf$，微分不等式给出 $\operatorname{Ent}(Q_uf)\le e^{-2u}\operatorname{Ent}(f)$。一般有限熵密度先截断、加入正底并归一化，再用 $Q_\varepsilon$ 平滑。截断密度的熵收敛、$L^1$ 连续性及输出相对熵的下半连续性，将结论延至全部有限熵输入。这是 Gaussian 对数 Sobolev 的标准半群证明，本文写出所需步骤。[^tcs5-gaussian]

令 $s=\|F\|$。$s=0$ 时输出恒为参考，$s=1$ 时上界由数据处理给出。$0<s<1$ 时，$G=F/s$ 也是收缩，先作用 $\mathcal K_{sI}$ 再作用 $\mathcal K_G$，复合均值为 $Fx$、噪声协方差为 $I-FF^{\mathsf T}$。因此
\[
 D(\mathcal K_F\nu\Vert\gamma_d)
 \le D(\mathcal K_{sI}\nu\Vert\gamma_d)
 \le s^2D(\nu\Vert\gamma_d).
\]
最后取 $\nu=\mathcal N(a,I_d)$，输出为 $\mathcal N(Fa,I_d)$；两个相对熵分别为 $|a|^2/2$、$|Fa|^2/2$。最大右奇异向量给出匹配下界，亦覆盖 $s=1$。证毕。

**定理 28.3（单量子比特的相同精确系数）。** 设 $\Phi$ 为保单位的单量子比特完全正、迹保持信道，其 Bloch 表示为
\[
 \rho_r=\tfrac12(I+r\cdot\sigma),\quad |r|\le1,
 \qquad \Phi(\rho_r)=\rho_{Tr},\quad T\in\mathbb R^{3\times3}.
\]
则
\[
 \boxed{\eta_{I_2/2}(\Phi)=\|T\|_2^2.}
\]
当 $0<\|T\|<1$ 时，沿最大右奇异向量趋近最大混合态的输入实现上确界极限；不需要给输入附加纯态假设。

**证明。** Bloch 球保持给 $\|T\|\le1$。密度矩阵的两个特征值为 $(1\pm|r|)/2$，所以
\[
 D(\rho_r\Vert I/2)=\phi(|r|),\qquad
 \phi(v)=\tfrac12[(1+v)\log(1+v)+(1-v)\log(1-v)].
\]
由 $\phi'(v)=\operatorname{artanh}v$ 积分得
\[
 \phi(v)=\sum_{k=1}^\infty\frac{v^{2k}}{2k(2k-1)},\quad0\le v\le1,
\]
端点由单调收敛解释。所有系数非负，故 $\phi(sv)\le s^2\phi(v)$，其中 $s=\|T\|$。$\phi$ 单调，得到全部输入的上界。取单位最大奇异向量 $a$，令 $r=\varepsilon a$；$\phi(v)=v^2/2+O(v^4)$，熵比趋于 $s^2$。这给出所需下界。本条是已知单比特收缩结构的固定参考版本；幂级数证明说明它依赖二能级的具体熵函数。证毕。[^tcs5-qubit]

**命题 28.4（三能级不能直接使用平方范数公式）。** 存在保单位的三能级信道，其无迹矩阵上的 Hilbert–Schmidt 收缩范数为 $1/2$，但相对于 $I_3/3$ 的相对熵系数严格大于 $1/4$。

**证明。** 取 $\Phi(\rho)=(\rho+I_3/3)/2$。它是恒等信道与完全退极化信道的等权混合，无迹部分恰乘以 $1/2$。令
\[
 \rho=\operatorname{diag}(2/3,1/6,1/6),\qquad
 \Phi(\rho)=\operatorname{diag}(1/2,1/4,1/4).
\]
直接求和给 $D(\rho\Vert I/3)=\log2/3$、$D(\Phi(\rho)\Vert I/3)=\log(9/8)/2$。熵比为
\[
 \frac{3\log(9/8)}{2\log2}>\frac14,
\]
因为 $9^6=531441>524288=2\,8^6$。这是交换对角态内的反例，已足以阻止从定理 28.3 外推到任意量子维数，也阻止把 Gaussian 结论套到任意经典离散概率空间。高维退极化的相对熵衰减另有专门理论。证毕。[^tcs5-depolarizing]

## 29. 保守旋转使退化耗散覆盖全部状态的充要条件

**定义 29.1（原卷耗散极限的固定模型）。** 沿用第 25.3 条所得线性扩散，固定 $D^{\mathsf T}=-D\in\mathbb R^{d\times d}$、$B\in\mathbb R^{d\times k}$，令
\[
 M=BB^{\mathsf T},\quad A=D-M/2,\quad F_t=e^{tA},
 \qquad dX_t=AX_t\,dt+B\,dW_t.
\]
其转移核为 $\mathcal P_t=\mathcal K_{F_t}$，参考为 $\gamma_d$。所有参数已知且不随 $t$ 改变。定义
\[
 m=\min\left\{j\ge0:\operatorname{rank}[B,DB,\ldots,D^jB]=d\right\},
\]
若不存在则记 $m=\infty$。这里只讨论有明确线性 Gaussian 半群实现的模型；第 23 节的一次初始化有限热环境不自动满足本定义。

**定理 29.2（同一 Gramian 决定可观测深度与最坏熵损失）。** 对所有 $t\ge0$，
\[
 \eta_{\gamma_d}(\mathcal P_t)=\|F_t\|^2,
 \qquad 1-\eta_{\gamma_d}(\mathcal P_t)=\lambda_{\min}G_t,
\]
\[
 G_t=I-F_t^{\mathsf T}F_t
     =\int_0^te^{sA^{\mathsf T}}BB^{\mathsf T}e^{sA}ds.
\]
以下等价：$m<\infty$；某个正时刻的熵系数严格小于一；每个正时刻的熵系数严格小于一。成立时
\[
 \boxed{1-\eta_{\gamma_d}(\mathcal P_t)=\Theta(t^{2m+1})\quad(t\downarrow0).}
\]
选任意 $t_0>0$、$c_0=\|F_{t_0}\|^2<1$，则全部有限熵初态及全部 $t\ge0$ 有
\[
 D(\mathcal P_t\nu\Vert\gamma_d)
 \le c_0^{\lfloor t/t_0\rfloor}D(\nu\Vert\gamma_d).
\]

**证明。** $A+A^{\mathsf T}=-M$，对 $F_t^{\mathsf T}F_t$ 求导并积分即得 Gramian。显式线性随机解的噪声协方差是 $I-F_tF_t^{\mathsf T}$，所以定理 28.2 给出前两式。

对 $x$，$x^{\mathsf T}G_tx=\int_0^t|B^{\mathsf T}e^{sA}x|^2ds$。在任意正窗上为零当且仅当所有导数 $B^{\mathsf T}A^jx$ 都为零；矩阵解析性和 Cayley–Hamilton 使前 $d$ 项已足够。每个有限阶的零导数空间还满足
\[
 \bigcap_{j=0}^N\ker(B^{\mathsf T}A^j)
 =\bigcap_{j=0}^N\ker(B^{\mathsf T}D^j).
\]
逐阶证明此式：若前面各 $B^{\mathsf T}D^jx=0$，则对应的 $MD^jx=0$，故到下一阶之前 $A^jx=D^jx$；反向使用同一递推。这些空间的正交补由 $[B,DB,\ldots,D^NB]$ 的列张成，因为 $D^{\mathsf T}=-D$。因此严格正定与所列秩条件等价。

有限 $m$ 下，有限导数映射 $x\mapsto(B^{\mathsf T}x,\ldots,B^{\mathsf T}A^mx)$ 有统一正下界。对 $B^{\mathsf T}e^{sA}x$ 展开到 $m$ 阶，令 $s=tu$；Hilbert Gram 矩阵 $(1/(i+j+1))_{0\le i,j\le m}$ 的正定性给多项式平方积分下界 $c t^{2m+1}|x|^2$。指数尾项的 $L^2$ 范数为 $O(t^{m+3/2})|x|$，小时间可吸收一半，得到统一下界。最小性给非零 $x$ 使第零至 $m-1$ 阶导数为零（$m=0$ 时任选单位向量），其积分为 $O(t^{2m+1})$，得到上界。最后半群性和参考保持使每个完整 $t_0$ 区间贡献因子 $c_0$，剩余时间使用数据处理。该幂次就是经典 hypocoercivity index 的时间尺度；本条把它与本卷的预测导数塔及固定参考信息逃逸放在相同矩阵上。证毕。[^tcs5-index]

## 30. 经典振子与受驱动量子比特的同一耗散曲线

**定义 30.1（共同的二维漂移）。** 固定 $\gamma>0$、$\omega\in\mathbb R$，令
\[
 A_{\gamma,\omega}=\begin{pmatrix}-\gamma&\omega\\-\omega&0\end{pmatrix}.
\]
经典模型为 $dX=A_{\gamma,\omega}Xdt+(\sqrt{2\gamma},0)^{\mathsf T}dW$，平衡参考 $\gamma_2$。量子模型为单比特 Lindblad 方程
\[
 \dot\rho=-i[(\omega/2)\sigma_y,\rho]
           +(\gamma/2)(\sigma_z\rho\sigma_z-\rho),
\]
参考为 $I_2/2$，取 $\hbar=1$。它可以看作第 26.3 条去相干极限上增加相干旋转。两种模型各自的状态空间、噪声实现及实验读取仍分别指定。

**定理 30.2（共同的最坏相对熵曲线及三阶起始律）。** 定义
\[
 s_\omega(t)=
 \begin{cases}
 \sinh(t\sqrt{\gamma^2/4-\omega^2})/\sqrt{\gamma^2/4-\omega^2},&|\omega|<\gamma/2,\\
 t,&|\omega|=\gamma/2,\\
 \sin(t\sqrt{\omega^2-\gamma^2/4})/\sqrt{\omega^2-\gamma^2/4},&|\omega|>\gamma/2.
 \end{cases}
\]
上述经典模型与量子模型的固定参考熵系数均精确等于
\[
 \boxed{c_{\gamma,\omega}(t)
 =e^{-\gamma t}\left(\sqrt{1+\gamma^2s_\omega(t)^2/4}
                     +\gamma|s_\omega(t)|/2\right)^2.}
\]
$\omega=0$ 时 $c(t)=1$；$\omega\ne0$ 时每个 $t>0$ 有 $c(t)<1$，并且
\[
 c_{\gamma,\omega}(t)=1-\frac{\gamma\omega^2}{6}t^3+O(t^4).
\]
经典上界由平移 Gaussian 态达到；量子上界由趋近最大混合态的态族逼近。

**证明。** 写 $A=-\gamma I/2+K$，则 $K^2=(\gamma^2/4-\omega^2)I$。因此 $e^{tA}=e^{-\gamma t/2}(c_*I+s_\omega(t)K)$，其中 $c_*^2-(\gamma^2/4-\omega^2)s_\omega(t)^2=1$。直接计算
\[
 \operatorname{tr}(e^{tA^{\mathsf T}}e^{tA})
 =e^{-\gamma t}(2+\gamma^2s_\omega(t)^2),\qquad
 \det(e^{tA^{\mathsf T}}e^{tA})=e^{-2\gamma t}.
\]
二阶特征方程的较大根即为盒中公式。定理 28.2 给经典系数。

量子 Bloch 坐标满足 $(\dot r_x,\dot r_z)^{\mathsf T}=A(r_x,r_z)^{\mathsf T}$、$\dot r_y=-\gamma r_y$。二维块的最大平方奇异值至少为其行列式的平方根 $e^{-\gamma t}$，故大于等于剩余方向的 $e^{-2\gamma t}$。定理 28.3 给相同系数。$\omega\ne0$ 时定义 29.1 的秩在深度一已满，故由定理 29.2 得严格收缩；$\omega=0$ 存在完整保留的方向。最后在小正时间使用 $s_\omega(t)=t+(\gamma^2/4-\omega^2)t^3/6+O(t^5)$，对公式取对数并展开，线性项相消，三阶项为 $-\gamma\omega^2t^3/6$。本条只识别一个精确的资源指标，不构造两个物理系统之间的状态同构。证毕。

**定理 30.3（固定耗散强度下的定时最优旋转与控制代价）。** 固定 $\gamma>0$ 和目标时间 $T>0$，在全部常数 $\omega$ 中优化时，两种模型均满足
\[
 \boxed{\min_{\omega\in\mathbb R}c_{\gamma,\omega}(T)=e^{-\gamma T}.}
\]
最小绝对值的达到频率为
\[
 |\omega_T|=\sqrt{\gamma^2/4+\pi^2/T^2}.
\]
若另外要求 $|\omega|\le\Omega<\infty$，则仅当 $\Omega\ge|\omega_T|$ 才能达到上述下界；对固定 $\Omega$ 的小时间极限，
\[
 \inf_{|\omega|\le\Omega}c_{\gamma,\omega}(T)
 =1-\frac{\gamma\Omega^2}{6}T^3+O(T^4).
\]

**证明。** 任意二维矩阵的最大平方奇异值至少是两平方奇异值的几何平均，所以 $c(T)\ge e^{-\gamma T}$。定理 30.2 的公式表明等号当且仅当 $s_\omega(T)=0$。前两个分支在正时间非零；第三分支的零点满足 $T\sqrt{\omega^2-\gamma^2/4}=j\pi$、$j\ge1$，得到全部达到频率及最小绝对值。紧区间 $[-\Omega,\Omega]$ 上的 Taylor 余项可一致控制，因此定理 30.2 的三阶式可对 $\omega$ 取下确界，得到最后一式。

固定参数的三阶起始律，与针对每个 $T$ 重新选择的 $e^{-\gamma T}$ 下界并不冲突。达到后一目标需要 $|\omega_T|\sim\pi/T$，量子控制 Hamilton 算子范数为 $|\omega_T|/2$；这里增加的是控制强度，不能据此宣称无成本的任意快混合。优化保守漂移以改善给定平衡的收敛已有相关文献，本条解决当前二维、常系数、定时及幅值预算问题。证毕。[^tcs5-optimal]

## 31. 从有限延迟观测认证全分布耗散及其模型边界

**定理 31.1（已知 OU 类内的单延迟熵证书）。** 在定义 29.1 的已校准完整状态模型中，取固定延迟 $h>0$。平衡配对相关为 $F_h=\mathbb E[X_hX_0^{\mathsf T}]$。若矩阵估计满足 $\|\widehat F_h-F_h\|_2\le\varepsilon$，定义
\[
 c_-=(\|\widehat F_h\|_2-\varepsilon)_+^2,
 \qquad c_+=\min\{1,(\|\widehat F_h\|_2+\varepsilon)^2\}.
\]
则 $c_-\le\eta_{\gamma_d}(\mathcal P_h)\le c_+$。若 $c_+<1$，对全部有限熵初态及全部整数 $n\ge0$ 有
\[
 \boxed{D(\mathcal P_{nh}\nu\Vert\gamma_d)
        \le c_+^nD(\nu\Vert\gamma_d).}
\]
由 $N$ 次独立热初态制备的配对样本构造 $\widehat F_h=N^{-1}\sum_{j=1}^N X_h^{(j)}(X_0^{(j)})^{\mathsf T}$，在无额外传感噪声且热白化已知时，任意失败概率 $0<\alpha<1$ 可取
\[
 \varepsilon_N=\sqrt{d(d+1)/(N\alpha)}.
\]
此预算以至少 $1-\alpha$ 概率有效。如果 $b_h=1-\|F_h\|>0$ 且 $\varepsilon_N<b_h/2$，则在同一事件上证书必为严格收缩。$m<\infty$ 时，固定维数和置信度下，$N$ 为充分大常数倍的 $h^{-4m-2}$ 是小延迟的一个保守充分预算，不宣称样本最优性。

**证明。** 范数三角不等式和定理 28.2 给系数区间；半群性使它可逐段复用。热平衡下 $X_0,X_h$ 各自协方差为 $I$，且联合 Gaussian。Wick 四阶矩给每个相关元素的样本方差为 $[1+(F_h)_{ab}^2]/N$，故
\[
 \mathbb E\|\widehat F_h-F_h\|_F^2
 =\frac{d^2+\|F_h\|_F^2}{N}\le\frac{d(d+1)}N.
\]
Markov 不等式及算子范数不超过 Frobenius 范数给所列置信预算。在该事件上 $\|\widehat F_h\|+\varepsilon_N\le\|F_h\|+2\varepsilon_N<1$。定理 29.2 给 $b_h=\Theta(h^{2m+1})$，代入预算即可。

本结论将平衡实验的矩阵误差转换为已知模型类中全部非平衡初态的熵保证；外推依赖该类的 Gaussian 转移与半群结构。只读取未闭合的投影、未知热白化、相邻时刻的非独立样本或额外仪器噪声，都需要另建误差模型。量子单比特若已获得 Bloch 矩阵的算子范数误差，也可用定理 28.3 的相同代数区间，但上述 Gaussian 样本统计不能直接充当量子测量保证。证毕。

**命题 31.2（单延迟数据不能自行证明不可逆半群）。** 对任意固定 $h>0$，存在一个有限封闭正定振子的标量热观察和一个严格耗散的标量 OU 过程，使二者任意次数独立制备得到的延迟 $h$ 平衡配对数据法则完全相同，而它们的长期信息行为不同。

**证明。** 取振子频率 $\omega=\pi/(3h)$，单位热协方差，其归一位置相关为 $f(t)=\cos(\omega t)$。另取平稳 OU 过程 $dY=-\lambda Ydt+\sqrt{2\lambda}\,dW$，其中 $\lambda=\log2/h$。两个模型的 $(X_0,X_h)$ 都是零均值、单位边缘方差、相关系数 $1/2$ 的二元 Gaussian，故全部独立配对样本法则相同。

振子从位置平移为 $a\ne0$、隐藏动量仍为独立热分布的初态出发，在 $6h$ 精确返回，位置相对热参考的 KL 为 $a^2/2$。OU 从同一位置边缘出发，在 $6h$ 的 KL 为 $2^{-12}a^2/2$。单延迟的边缘通道均具有系数 $1/4$，但振子的一次初始化过程不满足半群复合，不能把它迭代成 $(1/4)^6$。所以无论单延迟配对数据数量多大，都不能仅凭这些数据把定义 29.1 的模型假设认证出来。额外延迟、干预或先验动力学结构会改变这一辨识问题。证毕。

## 32. 本批来源、贡献边界与证明身份

**出处 32.1（直接文献与来源范围）。** 第 28.2 条是 Gaussian 对数 Sobolev 与强数据处理的具体形式；第 28.3 条属于已知单比特收缩理论；第 29.2 条的奇数短时幂次与 hypocoercivity index 是经典控制/耗散结构。本卷对这些构件给出所需完整证明，不把它们计作新的学术发现。第 28.4 条的有理三能级见证、第 30 节当前经典/量子模型的共同定时曲线与控制预算，以及第 31 节的观测证书和双模型辨识反例，按本批具体推导列为 `repo-derived`。该标记指来源与推导方式；发表级新颖性需另与最接近定理逐项比较。

[^tcs5-gaussian]: Gaussian 对数 Sobolev 的半群方法属于 Gross 理论。Anton Arnold、Jan Erb，*Sharp entropy decay for hypocoercive and non-symmetric Fokker–Planck equations with linear drift*，[arXiv:1409.5425](https://arxiv.org/abs/1409.5425)，研究线性漂移下的熵衰减及 Gaussian 不变族；Anton Arnold、Christian Schmeiser、Beatrice Signorello，*Propagator norm and sharp decay estimates for Fokker–Planck equations with linear drift*，[arXiv:2003.01405](https://arxiv.org/abs/2003.01405)，其主结果是归一 Fokker–Planck 的加权 $L^2$ 传播范数与漂移 ODE 范数一致。后者的 $L^2$ 声明不直接替代本卷的 KL 声明；第 28.2 条另给 Gaussian 核分解及固定参考证明。本批读取两篇作者条目的摘要范围，不据此引用未读取页码。

[^tcs5-qubit]: Fumio Hiai、Mary Beth Ruskai，*Contraction coefficients for noisy quantum channels*，[arXiv:1508.03551](https://arxiv.org/abs/1508.03551)，是量子收缩系数的直接来源；Mario Berta、David Sutter、Michael Walter，*Quantum Brascamp–Lieb Dualities*，Communications in Mathematical Physics 401, 1807–1830 (2023)，[原文 Example 3.11](https://doi.org/10.1007/s00220-023-04678-w)，明确给出单比特退极化的固定最大混合参考系数及趋近参考的达到方式。第 28.3 条用 Bloch 熵级数写出本批实际使用的任意保单位单比特版本。一般高维、有限温非最大混合参考和附加量子记忆均未被该证明覆盖。

[^tcs5-depolarizing]: Alexander Müller-Hermes、Daniel Stilck França、Michael M. Wolf，*Relative entropy convergence for depolarizing channels*，Journal of Mathematical Physics 57, 022202 (2016)，[arXiv:1508.07021](https://arxiv.org/abs/1508.07021)，研究满秩固定点退极化及其 log-Sobolev-1 常数。第 28.4 条只以直接可核算的三能级输入反驳无条件平方范数推广，没有重新求解一般高维收缩系数。

[^tcs5-index]: Franz Achleitner、Anton Arnold、Eric A. Carlen，*The hypocoercivity index for the short time behavior of linear time-invariant ODE systems*，Journal of Differential Equations 371, 83–115 (2023)，[作者条目](https://arxiv.org/abs/2109.10784)，给出有限耗散矩阵的短时传播范数与 $2m+1$ 指数；另见 Achleitner、Arnold、Volker Mehrmann，*Hypocoercivity and controllability in linear semi-dissipative Hamiltonian ordinary differential equations and differential-algebraic equations*，[原文 Theorem 1](https://doi.org/10.1002/zamm.202100171)，明确连接 Kalman 型秩与该指数。第 29.2 条不认领这个指数的新颖性，而将它接入第 25 节的特定极限和第 28 节的固定参考熵系数。

[^tcs5-optimal]: Anton Arnold、Beatrice Signorello，*Optimal non-symmetric Fokker–Planck equation for the convergence to a given equilibrium*，Kinetic and Related Models 15(5), 753–773 (2022)，[原文](https://doi.org/10.3934/krm.2022009)，研究固定 Gaussian 平衡、秩一扩散下的最优非对称加速和乘法常数。第 30.3 条另固定二维摩擦、常数旋转、目标时刻和控制幅值，其等号由本批显式矩阵指数给出；没有把它解释为不计控制资源的加速。

**出处 32.2（与当前前沿的实际交界）。** Jianfeng Lu，*A sharp hypocoercive entropy decay estimate for underdamped Langevin dynamics*，[arXiv:2605.01933v2](https://arxiv.org/html/2605.01933v2)，本批读取 Assumptions 2.1–2.2、Theorem 2.3 及条件熵/最优输运修正项，确认其凸势、空间 log-Sobolev 和增长前件。该文在更广的非线性族中研究显式熵速率；本批保持可精确求系数的线性与单比特载体。Lu 的 ICM 2026 文章 [*Quantitative Hypocoercivity and Lifting of Classical and Quantum Dynamics*](https://doi.org/10.1137/25M1806065) 已给出经典 Langevin 与量子 Lindblad 的统一加速框架，故“经典与量子存在共同耗散数学”本身是已有研究方向。

Pierre Monmarché、Lihan Wang，*On the entropic convergence for piecewise deterministic samplers: speedup and obstruction*，[arXiv:2606.26086v1](https://arxiv.org/html/2606.26086v1)，本批读取 Theorem 2：在其 BPS/ZZP 与速度分布前件下，即使 Gaussian 目标，也不存在文中所定义的统一衰减熵比；其 RHMC 正向结果与此分开。因此本卷从 Gaussian 线性核得到的精确系数，不能从“同一个平衡态”或“同样包含 Hamilton 运动”直接迁移到任意采样器。

**约定 32.3（产地与核验）。** 本批按 `theory-volume-template/APPEND.md` 直接追加原卷，数学推导、原文核对、实施及有限检错均由本会话 ChatGPT 单席串行完成，无独立同行或异模型评审。八条结果均给出纸面证明。仅原理论文件是本次远端变更目标；检错脚本保留本地。未新增 Lean、Scribe、冻结记录或机器消化账目，未运行 Lean kernel、canonical `make ingest` 或仓库 CI。既有时间窗与信息公式的来源分别保留，有限样本核对不代替任意输入分布、所有状态与极限量词。

## 追加锚（本行以下为增补区）
