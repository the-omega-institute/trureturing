# 递归关系的观察商、严格拼接与相容完备化

本卷是理论参考输入，不是 Lean 验证收据。输入原稿由用户在当前会话提供，作者类型为 mixed；原稿指定 GPT PRO 作为主推理来源，本批规范化、仓库摄入与审查由 Codex 完成。输入日期为 2026-09-15，所依据的项目读取基准为 the-omega-institute/trureturing 的 dev 快照；具体提交身份由本批工作树与 Git 记录保存。Lean 声明、证明项及其公理闭包仍是仓库唯一真源，本文的定义、命题和证明均不得据此标记为 kernel-verified。

## 1. 有类型关系与带见证的递归层

**定义 1.1（有类型部分操作）。** 设 \(S\) 为种类集合，\(X_s\) 为每个 \(s\in S\) 的载体。一个有限有类型操作 \(\omega\) 包含输入种类 \(s_0,\ldots,s_{k-1}\)、输出种类 \(t\)、准入域
\[
D_\omega\subseteq\prod_{j<k}X_{s_j}
\]
以及确定映射 \(F_\omega:D_\omega\to X_t\)。空输入的操作允许作为常量，但每个输入端口的种类和位置都属于操作数据。

**定义 1.2（带见证关系）。** 从 \(X\) 到 \(Y\) 的带见证关系是一个集合 \(W\) 及两个映射 \(s:W\to X\)、\(t:W\to Y\)。其支撑关系为
\[
R_W(x,y)\iff\exists w\in W,\ s(w)=x\land t(w)=y.
\]
\(W\) 中同一端点对的不同元素保留不同路径、来源或证明档案；把 \(W\) 换成 \(R_W\) 一般会丢失这些差异。

**定义 1.3（递归关系层）。** 一个递归关系系统给出集合 \(W_0,W_1,\ldots\)。每个 \(W_{\ell+1}\) 的端口映射、边界映射、准入谓词及其允许的复合，均以 \(W_\ell\) 中的对象为输入。仅给出这些集合和映射，不自动得到范畴、双范畴或无穷范畴；相应的边界恒等式、交换律、填充或一致性必须另行假设。

**命题 1.4（有限呈示的可逆编码）。** 固定有限符号集及有限端口语法后，带种类、符号、端口序号、重复出现位置和绑定作用域的有限呈示，可以编码为有类型节点和有序端口图；对良构编码，解码后与原呈示同构，差异至多为辅助节点的重命名。

**证明。** 对呈示树的叶、符号节点、端口节点和绑定边作结构归纳。每个关系实例保留其符号及从 \(0\) 到 \(k-1\) 的端口序号，重复出现的同一对象保留为两个端口而不合并成一个无序边。解码按节点类型和端口序号重建原树；归纳假设保证子树重建，根节点的符号和绑定域保证整体重建。若编码的辅助节点名字改变，端口图仍给出唯一的同构。该结论只关于有限呈示，不断言一个有限语法编码任意外延关系的全部成员。

**命题 1.5（支撑与历史的分离）。** 令 \(H\) 为历史数据类型，\(L:H\to\mathsf{Prop}\) 为合法性谓词。集合 \(\{h:H\mid L(h)\}\) 可以保留不同历史；仅以结构 \(\{p:L(h)\}\) 保存证明项，不能在一般情况下区分这些历史。

**证明。** 两个不同的 \(h,h':H\) 即使满足同一命题 \(L\)，仍是类型 \(H\) 中的不同项。相反，在命题证明无关的语义下，两个 \(p,p':L(h)\) 不提供可观察的运行时差异。因此历史必须位于数据类型中，合法性证明只承担约束作用。

## 2. 观察核与严格下降

**定义 2.1（实际像、目标逃逸与联合观察）。** 对映射 \(q:X\to Q\)，只在实际像 \(q[X]\) 上讨论下降。对总目标 \(T:X\to Y\)，定义
\[
\mathcal E(q;T)=\{(x,y)\in X^2:q(x)=q(y)\land T(x)\ne T(y)\}.
\]
若 \(d:X\to D\) 是附加观察，则
\[
\mathcal E((q,d);T)=\mathcal E(q;T)\cap\ker d.
\]

**定理 2.2（实际像上的精确因子化）。** 对任意 \(q:X\to Q\) 和 \(T:X\to Y\)，以下等价：
\[
\mathcal E(q;T)=\varnothing;
\]
\[
\exists!\,\bar T:q[X]\to Y,\qquad T=\bar T\circ q.
\]

**证明。** 若 \(\bar T\) 存在，则 \(q(x)=q(y)\) 蕴含 \(T(x)=T(y)\)，故逃逸集为空。反之，对 \(z\in q[X]\) 取任意 \(x\) 使 \(q(x)=z\)，定义 \(\bar T(z)=T(x)\)。逃逸为空保证这个值与代表元无关；于是 \(T=\bar Tq\)。若还有 \(\bar T'\) 满足同式，则对每个 \(z=q(x)\) 有 \(\bar T'(z)=T(x)=\bar T(z)\)，故唯一。

**推论 2.3（后处理不能细化旧核）。** 若 \(d=\varphi\circ q\)，则
\[
\ker(q,d)=\ker q.
\]

**证明。** \(q(x)=q(y)\) 时 \(d(x)=\varphi(q(x))=\varphi(q(y))=d(y)\)，反向由联合坐标包含 \(q\) 立即成立。

**定义 2.4（严格响应）。** 对部分操作 \(F:D\to Y\)、输入观察 \(q_{\mathrm{in}}:X\to Q\) 和输出观察 \(q_{\mathrm{out}}:Y\to B\)，定义
\[
\mathsf R(x)=
\begin{cases}
\operatorname{ok}(q_{\mathrm{out}}(F(x))),&x\in D,\\
\bot,&x\notin D,
\end{cases}
\]
其中 \(\bot\notin\operatorname{ok}(B)\)。若费用、失败位置或中间读数属于任务要求，则并入 \(\mathsf R\)。

**定理 2.5（部分操作的严格观察下降）。** 存在唯一的实际像上部分操作 \(\bar F\)，其准入性由 \(q_{\mathrm{in}}\) 决定，且成功输出观察与失败标签完全由 \(q_{\mathrm{in}}\) 决定，当且仅当
\[
\forall x,y,\quad q_{\mathrm{in}}(x)=q_{\mathrm{in}}(y)\Longrightarrow
\mathsf R(x)=\mathsf R(y).
\]

**证明。** 若下降存在，同一观察类中的两个输入具有相同准入性；准入时输出观察和其余严格响应也相同，故条件成立。反之，在每个 \(q_{\mathrm{in}}\)-纤维上，\(\mathsf R\) 为常值。把含 \(\bot\) 的纤维排除得到实际像上的准入域；对成功纤维，以其唯一的 \(\operatorname{ok}(b)\) 值定义 \(\bar F\) 的输出观察。纤维常值保证该定义良好，满射到实际像保证唯一性。

**命题 2.6（严格一孔上下文的参数条件）。** 若一个观察等价关系要被称为全载体多元操作的强同余，则允许的一孔上下文必须能把其余槽固定为任意实际参数，并且上下文语言对严格失败传播和有限前缀复合封闭。若只允许指定参数，所得等价关系至多是该受限语言的同余。

**证明。** 逐槽替换时，除被替换槽外的每个输入都保持原实际值。若该实际值不属于允许参数语言，替换步骤不能作为该语言中的上下文表达，因而无法推出全载体结论。前缀封闭性保证一次替换后的后继响应仍由允许上下文检测。仓库中 StrictOneHoleContexts 的源码给出了所有 off-slot 参数均为实际值时的单种类版本；多种类版本还需逐槽保留种类。

## 3. 真实联合像与严格拼接

**定义 3.1（真实联合像与候选拼接域）。** 设 \(C\) 为小范畴，\(M\) 为箭头集，\(s,t:M\to O\) 为边界。令
\[
M^{(2)}=\{(f,g)\in M^2:t(f)=s(g)\}
\]
为真实可复合对。给对象观察 \(q_0:O\to B\) 和箭头观察 \(q_1:M\to A\)，若 \(s,t\) 沿观察下降为 \(\bar s,\bar t\)，定义
\[
J_2=\{(q_1(f),q_1(g)):(f,g)\in M^{(2)}\},
\]
\[
P_2=\{(a,b)\in A^2:\bar t(a)=\bar s(b)\}.
\]
总有 \(J_2\subseteq P_2\)。

**命题 3.2（最小虚假拼接）。** 取四个互异对象 \(a,b,c,d\)，除恒等箭头外仅有 \(f:a\to b\) 与 \(g:c\to d\)。若观察合并 \(b,c\) 而保留 \(a,d\)，则 \(P_2\) 含有 \((q_1(f),q_1(g))\)，但该点不属于 \(J_2\)。

**证明。** 观察边界满足 \(\bar t(q_1(f))=\bar s(q_1(g))\)，所以该对属于 \(P_2\)。然而 \(t(f)=b\ne c=s(g)\)，故 \((f,g)\notin M^{(2)}\)，不在真实联合像中。

**命题 3.3（存在性拼接不等于严格下降）。** 即使 \(J_2=P_2\)，并且所有真实可复合对具有唯一且一致的观察复合输出，也不能推出原始准入域沿 \((q_1,q_1)\) 饱和。

**证明。** 取只有两个对象 \(a,b\) 的离散范畴，箭头只有 \(1_a,1_b\)。把对象和箭头都映到单点。则 \(J_2=P_2\) 是单点，所有真实可复合对的输出观察一致；但 \((1_a,1_a)\) 可复合而 \((1_a,1_b)\) 不可复合，二者观察输入相同。因此严格响应在该观察纤维上不恒定，定理 2.5 的准入下降失败。

**定理 3.4（联合关系的有限观察闭包）。** 令 \(I\) 为有限集合。对每个 \(i\in I\)，给定有限集合 \(Q_{i,n}\)、满射 \(q_{i,n}:X_i\to Q_{i,n}\) 及相容映射 \(p_{i,n}:Q_{i,n+1}\to Q_{i,n}\)，满足 \(q_{i,n}=p_{i,n}q_{i,n+1}\)。令
\[
K_i=\varprojlim_n Q_{i,n},\qquad \iota_i(x)=(q_{i,n}(x))_n,
\]
并令 \(\eta=\prod_{i\in I}\iota_i\)。对任意关系 \(R\subseteq\prod_iX_i\)，写
\[
R_n=\{(q_{i,n}(x_i))_{i\in I}:(x_i)_{i\in I}\in R\}.
\]
则
\[
\overline{\eta[R]}=
\bigcap_{n\ge0}\pi_n^{-1}(R_n),
\]
其中闭包取 \(\prod_iK_i\) 的逆极限拓扑，\(\pi_n=\prod_i\pi_{i,n}\)。

**证明。** 右侧每个 \(\pi_n^{-1}(R_n)\) 是开闭集，并且包含 \(\eta[R]\)，故包含闭包。反之，令 \(z\) 属于右侧，取任意基本邻域 \(U\) of \(z\)。该邻域只涉及有限个坐标和有限多个层；取一个不小于这些层的 \(N\)。由 \(z\in\pi_N^{-1}(R_N)\)，存在 \(x=(x_i)_i\in R\) 使 \(\pi_N(\eta(x))=\pi_N(z)\)。相容性使 \(\eta(x)\) 与 \(z\) 在 \(U\) 所有坐标上相等，故 \(U\cap\eta[R]\ne\varnothing\)。因此 \(z\in\overline{\eta[R]}\)。

**推论 3.5（闭关系的有限层判定）。** 若 \(C\subseteq\prod_iK_i\) 为闭集，则
\[
C=\bigcap_{n\ge0}\pi_n^{-1}(\pi_n(C)).
\]

**证明。** 一侧包含显然。若 \(z\notin C\)，则补集是开集，含有一个只依赖有限层 \(N\) 的基本邻域；因此不存在 \(c\in C\) 与 \(z\) 具有相同的 \(N\)-坐标，故 \(z\notin\pi_N^{-1}(\pi_N(C))\)。

**推论 3.6（恢复原关系的额外条件）。** 在定理 3.4 中，有限观察只能无条件恢复 \(\overline{\eta[R]}\)。若 \(\eta[R]\) 在完成空间中闭，则它等于有限层条件的交；若关系还要求每个完成点由原始关系中的代表实现，则必须另加实现性假设。

**证明。** 这是定理 3.4 与闭集判定的直接合取。稠密性只给闭包，不给原集合等于闭包；实现性则是把完成空间中的相容线程提升回原始见证的独立条件。

## 4. 相容塔上的连续延拓

**定义 4.1（有限观察塔）。** 对非空集合 \(X\)，称 \(q_n:X\twoheadrightarrow Q_n\) 为有限观察塔，若每个 \(Q_n\) 有限离散，且存在 \(p_n:Q_{n+1}\to Q_n\) 满足 \(q_n=p_nq_{n+1}\)。定义
\[
\widehat X=\{z\in\prod_nQ_n:\forall n,\ p_n(z_{n+1})=z_n\}
\]
及 \(\iota_X(x)=(q_n(x))_n\)。

**定理 4.2（观察完备化的基本性质）。** 有限观察塔的 \(\widehat X\) 是紧致 Hausdorff 全不连通空间，柱集构成其开闭基，\(\iota_X[X]\) 稠密，并且
\[
\iota_X(x)=\iota_X(y)\iff\forall n,\ q_n(x)=q_n(y).
\]

**证明。** \(\prod_nQ_n\) 是有限离散紧致空间的乘积，故紧致 Hausdorff。每个相容方程的解集是闭集，故 \(\widehat X\) 闭而紧致。有限坐标柱集在乘积中开闭，与 \(\widehat X\) 相交后仍开闭，并构成基。给定非空柱集，取其最高层 \(N\) 的坐标 \(z_N\)；满射 \(q_N\) 给出 \(x\in X\) 使 \(q_N(x)=z_N\)，相容性使 \(\iota_X(x)\) 落在该柱集，故原像稠密。最后一个等价逐坐标成立。

**定义 4.3（精度逃逸与模量）。** 设 \(F:X\to Y\) 为总函数，\(q_n:X\twoheadrightarrow Q_n\)、\(r_n:Y\twoheadrightarrow R_n\) 为有限观察塔。定义
\[
\mathcal E_{m,n}(F)=
\{(x,y):q_m(x)=q_m(y)\land r_n(Fx)\ne r_n(Fy)\}.
\]
若对给定 \(n\) 存在 \(m\) 使该集合为空，定义 \(\mu_F(n)\) 为最小这样的 \(m\)；不存在时令 \(\mu_F(n)=\infty\)。

**定理 4.4（有限精度逃逸与连续延拓等价）。** 以下条件等价：
\[
\forall n\ \exists m,\quad \mathcal E_{m,n}(F)=\varnothing;
\]
存在唯一连续映射 \(\widehat F:\widehat X\to\widehat Y\) 满足
\[
\widehat F\circ\iota_X=\iota_Y\circ F.
\]

**证明。** 先设第一条件成立。把每个选出的 \(m(n)\) 增大为非递减序列。由定理 2.2，对每个 \(n\) 存在唯一 \(F_n:Q_{m(n)}\to R_n\)，满足 \(F_nq_{m(n)}=r_nF\)。若 \(n<n'\)，取足够高的层 \(M\ge m(n),m(n')\)。对任意 \(u\in Q_M\)，由 \(q_M\) 满射取 \(x\) 使 \(q_M(x)=u\)。两种下投影分别等于 \(r_nF(x)\)，而 \(r_n\) 是 \(r_{n'}\) 的下投影，故输出坐标相容。于是对 \(z\in\widehat X\) 定义 \((\widehat Fz)_n=F_n(z_{m(n)})\)。这些坐标组成 \(\widehat Y\) 中的点；每个坐标只依赖一个有限坐标，故 \(\widehat F\) 连续。对 \(z=\iota_X(x)\)，定义立即给出 \(\widehat Fz=\iota_YF(x)\)。若另有连续映射满足同式，它们在稠密集 \(\iota_X[X]\) 上相等；\(\widehat Y\) Hausdorff，故二者相等。

反设连续 \(\widehat F\) 存在。固定 \(n\)，坐标函数 \(\pi_n\widehat F:\widehat X\to R_n\) 连续且目标有限离散。对每个 \(z\) 存在柱邻域 \(U_z\)，使该坐标在 \(U_z\) 上恒定。紧致性给出有限子覆盖；取这些柱邻域所涉及层数的最大值 \(m\)。两个具有相同 \(m\)-坐标的点落入同一坐标常值块，故其第 \(n\) 个输出坐标相同。限制到 \(\iota_X[X]\) 得 \(q_m(x)=q_m(y)\Rightarrow r_n(Fx)=r_n(Fy)\)，即 \(\mathcal E_{m,n}(F)=\varnothing\)。

**推论 4.5（复合模量）。** 若 \(F:X\to Y\) 与 \(G:Y\to Z\) 均满足定理 4.4 的条件，并约定 \(\mu_F(\infty)=\infty\)，则
\[
\mu_{G\circ F}(n)\le \mu_F(\mu_G(n)).
\]

**证明。** 若 \(q_m(x)=q_m(y)\)，其中 \(m=\mu_F(\mu_G(n))\)，则 \(F(x),F(y)\) 在 \(Y\) 的 \(\mu_G(n)\) 层相同，再由 \(G\) 的模量得到 \(Z\) 的第 \(n\) 层相同。

**命题 4.6（层数、上下文深度和精度的分离）。** 关系层数 \(\ell\)、允许上下文深度 \(h\) 和观察精度 \(n\) 是不同指标；在没有额外一致界时，逐指标的存在量词不能交换。

**证明。** 令 \(K=\{0,1\}^{\mathbb N}\)，\(q_m\) 记录前 \(m\) 位，令 \(T_\ell(x)=x_\ell\)。对每个 \(\ell\)，\(T_\ell\) 经 \(q_{\ell+1}\) 因子化；但不存在一个 \(m\) 使所有 \(T_\ell\) 同时经 \(q_m\) 因子化。因而 \(\forall\ell\,\exists m\) 不推出 \(\exists m\,\forall\ell\)。同理，若只允许长度至多 \(h\) 的上下文，得到的是有限深度等价，而不是全部有限词的交。关系层数描述载体递归，深度描述可用试验，精度描述观察塔坐标；只有给出交换图和统一模量时才可比较它们。

## 追加锚（本行以下为增补区）

## 5. 关系的关系：共同像、阶段提升与上下文扩展

本批把上一批的二元真实联合像提升到相容阶段系统。这里的“提升”同时有三种含义：有限读数是否来自同一个实际见证，有限阶段是否能组成一条相容线程，以及关系映射是否能从阶段代表独立地下降到极限。三者都要求额外的共同实现条件，不能由各坐标分别非空推出。

### theorem 5.1: 有限阶段关系的闭包只保存可逼近的共同像

设 \(I\) 为有限集合，\(X_i\) 为载体；对每个 \(i\) 给定有限观察塔
\(q_{i,n}:X_i\twoheadrightarrow Q_{i,n}\)，其阶段映射满足
\(q_{i,n}=p_{i,n}q_{i,n+1}\)。令
\(K_i=\varprojlim_n Q_{i,n}\)，\(\iota_i(x)=(q_{i,n}(x))_n\)。对任意关系
\(R\subseteq\prod_{i\in I}X_i\)，令

\[
R_n=\{(q_{i,n}(x_i))_{i\in I}:(x_i)_{i\in I}\in R\}.
\]

则在 \(\prod_iK_i\) 的柱拓扑中

\[
\overline{\bigl(\prod_i\iota_i\bigr)[R]}
=\bigcap_{n\ge0}\pi_n^{-1}(R_n).
\]

**证明。** 每个 \(\pi_n^{-1}(R_n)\) 是开闭集并包含
\(\bigl(\prod_i\iota_i\bigr)[R]\)，所以包含其闭包。反向地，取右侧一点
\(z\) 及其任意基本柱邻域 \(U\)。\(U\) 只涉及有限多个坐标和有限多个阶段；
取一个不低于这些阶段的 \(N\)。由 \(z\in\pi_N^{-1}(R_N)\)，存在 \(x\in R\)
使 \(\pi_N((\prod_i\iota_i)(x))=\pi_N(z)\)。相容性使这两个点在 \(U\) 的所有
坐标上相同，故 \(U\) 与原关系像相交。于是 \(z\) 属于闭包。

该结论的方向是单向的：有限阶段信息无条件恢复的是关系像的闭包。
只有在原关系像本身闭合时，右侧交集才等于原关系；若还要求完成点来自原始载体，
则须另加见证提升或实现性假设。

### theorem 5.2: 有限非空相容阶段必有共同见证

设 \(J\) 为小的共滤范畴，\(F:J\to\mathsf{Type}\) 为对象值有限且非空的图。
则其相容截面集合非空；等价地，存在一族 \(x_j\in F(j)\)，对每条箭头
\(u:j\to j'\) 都有 \(F(u)(x_j)=x_{j'}\)。

**证明。** 对每个对象 \(j\)，有限性和非空性给出有限离散空间 \(F(j)\)。
所有对象值的乘积取积拓扑；每条箭头的相容等式给出一个闭条件。共滤性保证
任意有限组相容条件可在某个共同阶段同时满足。闭条件族因此具有有限交性质。
有限离散空间乘积的紧致性给出全体闭条件的共同点，即所需相容截面。

“每一层有见证”只给出对象值非空；若没有有限性或共滤性，不能从中推出共同截面。
特别地，集合 \(F_n=\{m\in\mathbb N:m\ge n\}\) 虽逐层非空，却没有满足恒等遗忘约束的
全局截面。

### proposition 5.3: 局部读数的联合像由重叠同余决定

对 \(m,n\in\mathbb N\)，令

\[
\rho_{m,n}:\mathbb Z\to\mathbb Z/m\mathbb Z\times\mathbb Z/n\mathbb Z,\qquad
\rho_{m,n}(x)=(x\bmod m,x\bmod n).
\]

则

\[
\operatorname{im}\rho_{m,n}
=\{(a,b):a\bmod\gcd(m,n)=b\bmod\gcd(m,n)\}.
\]

因此 \(\rho_{m,n}\) 满射当且仅当 \(\gcd(m,n)=1\)。两个局部读数各自满射并不推出联合读数满射；
例如 \(m=n=2\) 时，\((0,1)\) 分别是两个合法局部值，却没有共同整数见证。

**证明。** 任意整数的两个余数在最大公因数上相等，给出包含关系。反向地，若 \(a,b\) 在最大公因数上相等，
广义中国剩余定理给出同时满足两个同余式的整数。联合像等式随即成立。联合像等于整个乘积恰当于最大公因数只有一个剩余类，
即最大公因数为 \(1\)。

这说明“每个边缘关系都可达”与“边缘关系有共同实现”是两个独立命题。
该例的 Lean 形式化锚是 D5/S3/Factorization/PrimePowers/CompatibleResidueJointImage；
其结论覆盖任意自然模数，包括零模和一模的退化情形。

### theorem 5.4: 逆极限映射的阶段自然性及其独立反推

令 \(I\) 为预序，\(\mathsf X,\mathsf Y\) 为阶段系统，
\(\delta_i:\mathsf X_i\to\mathsf Y_i\) 为逐阶段映射。以下两条分别成立：

1. 若对所有 \(i\le j\) 和 \(x\in\mathsf X_j\) 有
   \[
   \mathsf Y_{j\to i}(\delta_jx)=\delta_i(\mathsf X_{j\to i}x),
   \]
   则存在唯一极限映射 \(\Delta:\varprojlim\mathsf X\to\varprojlim\mathsf Y\)，
   且其第 \(i\) 个坐标为 \(\delta_i\) 作用于第 \(i\) 个坐标。
2. 反之，若每个投影 \(\varprojlim\mathsf X\to\mathsf X_i\) 都满射，并且存在一个具有上述坐标公式的极限映射 \(\Delta\)，
   则阶段自然性等式必然成立。

**证明。** 第一条按坐标定义 \((\Delta z)_i=\delta_i(z_i)\)；自然性保证这些坐标相容，故得到极限点。
任何满足同一坐标公式的映射逐坐标相等，唯一性成立。第二条固定 \(i\le j\) 及 \(x\in\mathsf X_j\)。
由投影满射取 \(z\) 使 \(z_j=x\)。极限点 \(\Delta z\) 的相容性给出
\[
\mathsf Y_{j\to i}(\Delta z)_j=(\Delta z)_i.
\]
代入坐标公式和 \(z_i=\mathsf X_{j\to i}x\) 即得所需自然性。这里的坐标满射是必要的反推条件；
没有它，极限映射只约束实际可提升的阶段元素，不能反射全部阶段等式。

### theorem 5.5: 呈示的 pro-Hom 是阶段映射的极限—余极限

设 \(\mathcal C\) 为小范畴，\(X:I^{\mathrm{op}}\to\mathcal C\) 与
\(Y:J^{\mathrm{op}}\to\mathcal C\) 是滤序呈示。按呈示方向记阶段映射，则相应 pro-对象之间的态射类型满足

\[
\operatorname{Hom}_{\mathrm{Pro}(\mathcal C)}(X,Y)
\cong
\varprojlim_{j\in J^{\mathrm{op}}}\ \varinjlim_{i\in I}
\operatorname{Hom}_{\mathcal C}(X_i,Y_j).
\]

一个 pro-态射在每个目标阶段 \(j\) 都有某个足够细的源阶段 \(i\) 代表；
这些代表在目标阶段的细化箭头下相容。两个一对象呈示退化为普通范畴中的 Hom 集合。

**证明。** 先对固定目标对象取源阶段 Hom 的滤余极限，再对目标阶段取相容极限。
Yoneda 嵌入把呈示对象的态射识别为该极限—余极限；类型值余极限的联合满射给出每个目标坐标的阶段代表，
极限投影方程给出代表类的相容性。一对象时两层极限—余极限均退化，得到通常的态射集合。

这给出一种严格的“关系的关系”对象：高阶关系不是自由地把各阶段标签相乘，而是一个相容阶段族。
若只保存每个目标阶段的一个未相容代表，就没有 pro-态射。

### proposition 5.6: 扩展操作签名只会细化上下文观察商

设 \(S\) 是有类型部分操作签名，\(T\) 通过嵌入旧符号、保留每个旧元的元数和 Option 值函数而扩展 \(S\)。
对任意基础读数 \(q:X\to Q\)，记 \(\simeq_S,\simeq_T\) 为所有严格一孔上下文的观察等价。则

\[
\simeq_T\subseteq\simeq_S.
\]

此外，\(\simeq_S\) 是 \(q\) 的核以下所有强同余的最大者：它保留每个操作的准入域、成功输出观察和严格失败传播。

**证明。** \(T\) 的上下文族包含由旧符号组成的全部 \(S\)-上下文；因此在 \(T\) 中相等的所有观察，
限制到旧上下文后仍在 \(S\) 中相等，得到包含关系。对最大性，逐槽替换使用任意实际 off-slot 参数，并以严格失败标签传播；
这保证 \(\simeq_S\) 本身是强同余。若 \(\theta\) 是另一个强同余且 \(\theta\subseteq\ker q\)，对一个操作的各输入逐槽替换，
强同余把每次替换的准入和输出保持在同一 \(\theta\)-类；有限次替换后，所有允许上下文的观察相等，故
\(\theta\subseteq\simeq_S\)。

因此递归增加关系符号时，观察核只能保持或缩小；若新增符号只对旧标签作后处理，核不变；
若新增符号允许新的实际上下文，则它可能严格缩小核，但必须由一个旧纤维内的响应差异见证。
对应的形式化锚为 D5/S3/ConceptDynamics/Observation/StrictOneHoleContexts。

本批的共同边界是：有限阶段闭包提供“可逼近”；相容截面提供“可共同实现”；阶段自然性提供“可下降”；
pro-Hom 提供“高阶关系的相容封装”；上下文最大性提供“新增操作的观测单调性”。任何一步缺失，
都只能报告边缘像、部分代表或闭包，不能报告原始高阶关系已经恢复。

## 追加锚（本行以下为增补区）

## 6. 增补·既有陈述的条件与适用范围

本批在第 5 节之后追加：本节限定第 2.5、2.6、3.2、3.6 及第 5 节相关条目的条件和量词；第 7 节给出关系复合与完备化的交换判据；第 8 节列来源与范围。以下说明按既有编号定位，不另立重复定理候选。第 5.1 条的闭包等式重述定理 3.4，不计为新增数学结果。既有正文中的批次指称仍属于其原批次。

### 6.1 第 3.6 与 5.1 条：闭像、关系代表与环境满射

沿用定理 3.4 的全部假设和记号，令

$$
K=\prod_{i\in I}K_i,\qquad
\widehat R=\bigcap_{n\ge 0}\pi_n^{-1}(R_n).
$$

有限阶段像恢复的集合恰为

$$
\widehat R=\overline{\eta[R]}\subseteq K.
$$

若 $\eta[R]$ 在 $K$ 中闭，则 $\widehat R=\eta[R]$，因而已经有

$$
\forall z\in\widehat R\ \exists x\in R,\qquad \eta(x)=z.
$$

这里每个完成关系点有一个原始关系代表，直接来自像集的定义，不须再加独立的实现性假设。反之，若上述存在量词成立，则 $\widehat R\subseteq\eta[R]$；结合定理 3.4 即得 $\eta[R]=\widehat R$，所以像闭。在闭像条件下，每个完成关系点的代表唯一，当且仅当 $\eta|_R$ 单射，即

$$
\forall x,y\in R,\qquad \eta(x)=\eta(y)\Longrightarrow x=y.
$$

因此，有限层条件确定的是 $K$ 中的关系像；与原始关系 $R$ 一一识别还需上述单射条件。对指定原输入 $x$，$\eta(x)\in\widehat R$ 在闭像时保证存在 $x^{\prime}\in R$ 与它观察相同，却不保证 $x\in R$；后者可由 $R$ 对 $\eta$ 的纤维饱和保证。不能把位于不同载体中的 $\eta[R]$ 与 $R$ 直接写成相等。

“整个环境空间的每一点都有原始载体代表”是另一个量词：

$$
\forall z\in K\ \exists x\in\prod_{i\in I}X_i,\qquad \eta(x)=z.
$$

这要求 $\eta$ 对整个 $K$ 满射。若进一步要求这些代表都取自 $R$，则要求 $\eta[R]=K$。这两种对整个环境空间的实现要求均不由 $\eta[R]$ 闭推出。第 3.6 与 5.1 条中“必须另加实现性”的措辞仅可用于这种扩大了对象范围的要求；对 $\widehat R$ 内的代表存在性，闭像已经充分。

### 6.2 第 5.3 条：零模约定与满射蕴含方向

第 5.3 条中的商统一解释为整数环的商，特别是

$$
\mathbb Z/0\mathbb Z=\mathbb Z,\qquad
\mathbb Z/1\mathbb Z=\{0\}.
$$

模零的商映射是恒等映射；对整数 $x,y$，条件 $x\equiv y\pmod 0$ 就是 $x=y$，不是自动成立的条件。

令 $d=\gcd(m,n)$。因 $d\mid m$ 且 $d\mid n$，有良定义的商映射

$$
r_{m,d}:\mathbb Z/m\mathbb Z\longrightarrow\mathbb Z/d\mathbb Z,
\qquad
r_{n,d}:\mathbb Z/n\mathbb Z\longrightarrow\mathbb Z/d\mathbb Z.
$$

第 5.3 条的联合像条件精确写为

$$
\operatorname{im}\rho_{m,n}
=\{(a,b):r_{m,d}(a)=r_{n,d}(b)\}.
$$

若 $m=0<n$，该条件是 $b=a\bmod n$，其中 $a$ 是整数；共同整数代表就是 $a$。若 $n=0<m$，对称地由整数坐标 $b$ 给出代表。若 $m=n=0$，则 $d=0$，条件是整数相等，联合像为 $\mathbb Z\times\mathbb Z$ 的对角线。非零模情形沿用第 5.3 条的广义中国剩余定理。因此，原有结论

$$
\rho_{m,n}\text{ 满射}\quad\Longleftrightarrow\quad\gcd(m,n)=1
$$

仍覆盖所有自然模数，包括 $(0,1)$ 与 $(1,0)$。

每个整数商映射均满射，且每个商都有零元素。在这里，联合满射蕴含两个边缘映射分别满射：固定一个边缘值，将另一边缘值取为零，再用联合满射取得共同代表。反向不成立；$m=n=2$ 时两个边缘均满射，但 $(0,1)$ 不在联合像中。故原文“两个独立命题”应收紧为“联合满射是更强条件，边缘分别满射不足以推出联合满射”，不能解读成两个方向都不存在蕴含。

### 6.3 第 5.4 条：坐标满射的充分性与逐系统边界

第 5.4 条的两个条件命题及其证明保留；唯一性只在满足所列坐标公式的映射中成立。所有源极限投影满射是一般反推证明的充分假设，不是对每个具体系统都必要的假设，故替代原末句的“必要”表述。

具体地，令 $p_j:\varprojlim\mathsf X\to\mathsf X_j$ 为源投影。只要存在满足坐标公式的 $\Delta$，对任意 $i\le j$，总能推出

$$
\forall x\in\operatorname{im}p_j,\qquad
\mathsf Y_{j\to i}(\delta_jx)
=\delta_i(\mathsf X_{j\to i}x).
$$

这是把一个提升 $z$ 代入 $\Delta z$ 的相容方程所得。若 $p_j$ 满射，便覆盖该等式的全部输入；对固定的非恒等阶段箭头，这一步只用其源阶段 $j$ 的投影。对于不能提升的输入，坐标公式本身不提供直接测试，但仍可由具体系统的其他结构推出相应等式，不能据此断言自然性必定无法反推。

取仅有 $0<1$ 的两层预序，以及源系统

$$
\mathsf X_1=\{*\},\qquad
\mathsf X_0=\{0,1\},\qquad
\mathsf X_{1\to0}(*)=0.
$$

其极限仅含 $z=(0,*)$。投影 $p_0$ 的像是 $\{0\}$，故不满射；$p_1$ 则满射。对任意同指标目标系统 $\mathsf Y$、任意逐阶段映射 $\delta_0,\delta_1$，如果存在满足第 5.4 条坐标公式的 $\Delta$，则 $\Delta z$ 的相容性给出

$$
\mathsf Y_{1\to0}(\delta_1(*))
=\delta_0(0)
=\delta_0(\mathsf X_{1\to0}(*)).
$$

这就是唯一非恒等阶段箭头的自然性等式，且 $*$ 已穷尽其输入；两个恒等箭头的自然性由系统恒等律成立。因此，即使源极限到某阶段的投影不满射，该系统的全部阶段自然性仍可由坐标公式反推。此例直接否定原文的逐系统必要性表述。

### 6.4 第 5.5 条：小性、代表类相容与共同细化

第 5.5 条的指标须明确为小滤范畴 $I,J$，不是仅给出两个未规定箭头与滤性的指标集合。固定声明宇宙，使 $I,J$ 的对象集和态射集以及 $\mathcal C$ 的各 Hom 集均位于同一个宇宙中；原文的小范畴 $\mathcal C$ 也可取在该宇宙内。于是所有阶段 Hom、其滤余极限及外层小极限均型良好。更一般地，可令 $\mathcal C$ 的对象宇宙为 $u$、Hom 宇宙为 $v$，而 $I,J$ 的对象与 Hom 同在 $v$，并保持两者的小性与滤性。

对 $X:I^{\mathrm{op}}\to\mathcal C$ 和 $Y:J^{\mathrm{op}}\to\mathcal C$，沿用第 5.5 条的公式

$$
\operatorname{Hom}_{\mathrm{Pro}(\mathcal C)}(X,Y)
\cong
\varprojlim_{j\in J^{\mathrm{op}}}
\varinjlim_{i\in I}\operatorname{Hom}_{\mathcal C}(X_i,Y_j).
$$

固定目标阶段 $j$ 后，源箭头 $u:i\to k$ 通过预复合 $X(u^{\mathrm{op}}):X_k\to X_i$ 给出 Hom 的余极限结构映射。一个 pro-态射在每个目标阶段确定一个余极限类 $c_j$；该类可由某个 $f_j:X_{i_j}\to Y_j$ 表示。外层极限的相容性首先是这些类的相容性。

精确地，给定任意目标箭头 $\beta:j\to j'$，以及 $c_j,c_{j'}$ 的任意两个阶段代表 $f_j,f_{j'}$，类相容意味着存在共同源细化阶段 $k\in I$ 及箭头

$$
u:i_j\to k,\qquad v:i_{j'}\to k,
$$

使

$$
f_j\circ X(u^{\mathrm{op}})
=Y(\beta^{\mathrm{op}})\circ f_{j'}\circ X(v^{\mathrm{op}})
\quad\text{作为 }X_k\to Y_j\text{ 的态射}.
$$

这是滤余极限中两个代表类相等的共同细化判据。它保证存在一次使该比较相等的细化，不声称未经细化的任意代表直接交换，也不声称随意选取一个共同阶段就已相等。相应存在量词的 $k,u,v$ 可以依赖于 $\beta$ 及所选代表；滤性不提供覆盖无限多个目标阶段的统一源阶段，不能把逐目标、逐比较的存在量词改为全体目标共用一个源阶段。

退化为普通 Hom 的指标应明确取离散单点范畴 $I=J=\mathbf 1$，即仅一个对象且仅有其恒等箭头。此时两个呈示分别只指定 $A,B\in\mathcal C$，两层极限与余极限退化为 $\operatorname{Hom}_{\mathcal C}(A,B)$。仅说“一对象范畴”不够，因为该对象还可能有非恒等自同态；仓内 `singleStageDiagram` 实际采用的是 `Discrete PUnit`。

### 6.5 第 5.6 条：多种类条件与不变核的准确含义

第 5.6 条所引 `StrictOneHoleContexts` 的现有 Lean 声明使用一个载体 $X$、一个读数 $q:X\to Q$，所有操作的输入与成功输出都在同一 $X$ 中。以下多种类读法须补齐类型条件，其依据是本节给出的逐槽替换论证，不属于该单载体声明已经形式化的范围。

令 $\mathcal S$ 为种类集合，对每个 $s\in\mathcal S$ 给定载体 $X_s$ 和读数 $q_s:X_s\to Q_s$。签名 $S$ 中每个操作 $\omega$ 有有限个有序输入种类 $s_0,\ldots,s_{k-1}$、输出种类 $t$、准入域及确定的成功输出

$$
D_\omega\subseteq\prod_{r<k}X_{s_r},\qquad
F_\omega:D_\omega\to X_t.
$$

扩展 $S\hookrightarrow T$ 必须保留每个旧符号的元数、各输入槽种类、输出种类，以及整个部分操作，包括准入性和实际成功输出。种类、载体和读数在比较中固定。

对输入孔种类 $s$ 与输出种类 $t$，令 $\mathcal C_S(s,t)$ 为所有类型相合的有限严格一孔上下文。每个 $\mathcal C_S(s,s)$ 包含该种类的空上下文；基本一步允许将其余每个槽固定为该槽载体中的任意实际参数；语言允许在任何后续上下文前加上类型相合的基本一步，即对有限前缀复合封闭。失败以标签 $\bot$ 严格传播，且 $\bot$ 与每个成功观察标签均不同。若上下文 $C$ 成功输出 $z\in X_t$，记其观察为 $\operatorname{ok}(q_t(z))$，失败时记为 $\bot$。于是逐种类定义

$$
x\simeq_{S,s}y
\quad\Longleftrightarrow\quad
\forall t\in\mathcal S\ \forall C\in\mathcal C_S(s,t),\qquad
\operatorname{Obs}_{q_t}(C(x))=\operatorname{Obs}_{q_t}(C(y)).
$$

在这些条件下，第 5.6 条的强同余按种类解释：每个 $\theta_s$ 是 $X_s$ 上的等价关系；对于任一操作和任意逐槽 $\theta_{s_r}$ 等价的两组输入，二者准入性相同，成功时输出位于同一个 $\theta_t$ 类。上下文等价族是满足 $\theta_s\subseteq\ker q_s$ 的最大强同余族，且签名扩展给出每个种类上的包含

$$
\simeq_{T,s}\ \subseteq\ \simeq_{S,s}.
$$

逐槽替换的理由如下。对逐槽等价的输入 $a,b$，在第 $r$ 步把前 $r$ 个槽取自 $b$、其余槽取自 $a$，再只替换第 $r$ 个槽。其余槽的值均是各自种类中的实际参数，故这一步属于允许的一孔上下文。把任意输出种类相合的后续上下文接在该步之后，前缀封闭性使整个试验仍属于语言。被替换输入的上下文等价因而保证所有后续观察相同；取空后续上下文可分辨成功与失败，取全部后续上下文则保证成功输出仍上下文等价。有限次替换给出整个操作的强同余性。空上下文又给出 $\simeq_{S,s}\subseteq\ker q_s$。反过来，任意满足这些核包含的强同余族，在每个基本一步保持准入及输出等价类，对有限上下文归纳即保持最终观察，因此包含于上下文等价族。旧上下文保留在扩展语言中，遂得上述细化关系。

第 5.6 条关于“核不变”的准确条件是：每个新增操作都保持旧上下文等价族的准入与成功输出等价类。写成量词，就是对每个新增 $\omega$ 及任意 $a,b\in\prod_{r<k}X_{s_r}$，若

$$
\forall r<k,\qquad a_r\simeq_{S,s_r}b_r,
$$

则须有

$$
a\in D_\omega\quad\Longleftrightarrow\quad b\in D_\omega,
$$

并且在准入时满足

$$
F_\omega(a)\simeq_{S,t}F_\omega(b).
$$

旧操作已保持该等价族；新增操作也满足上述条件时，旧等价族就是扩展签名的强同余，由最大性得 $\simeq_{S,s}\subseteq\simeq_{T,s}$，故核不变。反之，若扩展前后上下文等价族相同，扩展语言的强同余性立即给出上述条件。因此“对旧标签作后处理”只有在标签记录旧上下文等价类，并同时记录准入与成功输出类时，才能据此保证不变；仅要求即时输出读数 $q_t\circ F_\omega$ 在旧类上不变是不够的。

一个单载体反例已能区分这两种条件。取 $X=\{a,b,c,d\}$，读数 $q:X\to\{0,1\}$，以及总的一元操作 $f,g:X\to X$，用向量规定

$$
q=(0,0,0,1),\qquad
f=(a,a,d,d),\qquad
g=(a,c,a,a).
$$

三个向量均依次列出输入 $a,b,c,d$ 的输出，复合 $qfg$ 表示 $q\circ f\circ g$。旧语言只含 $f$，故其上下文为有限次迭代 $f^n$，包括 $n=0$ 的空上下文。因 $q(a)=q(b)=0$ 且 $f(a)=f(b)=a$，有 $a\simeq_S b$。然而

$$
q\circ g=(0,0,0,0),\qquad
q\circ f\circ g=(0,1,0,0).
$$

所以 $q\circ g$ 甚至是常值的旧读数后处理，但新增上下文 $f\circ g$ 已区分 $a,b$。具体地，$g(a)=a$ 与 $g(b)=c$ 即时读数相同，却被旧上下文 $f$ 区分，故不属于同一个旧上下文等价类。这说明不变核条件必须保持旧上下文的全部后续响应，不能只保持新增操作的即时 $q$ 输出。

上述多种类论证与反例均是对第 5.6 条适用条件的正文限定；现有单载体 Lean 声明不据此扩张为多种类证明，本节不主张新增 Lean 形式化或消化状态。

### 6.6 第 2.5、2.6 与 3.2 条：下降类型、充分条件与代表纤维

第 2.5 条中唯一下降的成功输出空间应为观察值空间 $B$。不含其他响应数据时，精确类型和公式为

$$
\bar D=q_{\mathrm{in}}[D]\subseteq q_{\mathrm{in}}[X],\qquad
\bar F:\bar D\to B,\qquad
\bar F(q_{\mathrm{in}}(x))=q_{\mathrm{out}}(F(x))\quad(x\in D).
$$

严格响应在输入观察纤维上恒定，使 $D$ 饱和，定义良好且在实际像上唯一。若并入费用、失败位置等数据，则下降取值于所要求的完整响应空间。这里不是 $Y$ 值下降的唯一性：取两个不同的 $y_0,y_1\in Y$ 且 $q_{\mathrm{out}}(y_0)=q_{\mathrm{out}}(y_1)$，同一个成功观察不能唯一选定其中一个。

第 2.6 条的全实际参数、严格失败传播和有限前缀封闭，是一般上下文同余证明的充分条件，不能称为每个具体系统中同余成立的逻辑必要条件。取任意集合 $X$、任意读数 $q:X\to Q$，总操作 $F(x,y)=x$，而受限语言仅含恒等上下文。此时上下文等价就是 $\ker q$；若 $q(x)=q(x')$ 且 $q(y)=q(y')$，则

$$
q(F(x,y))=q(x)=q(x')=q(F(x',y')).
$$

准入恒真，故任意这样的核仍为 $F$ 的强同余，尽管语言不含一般逐槽基本上下文。原条目的逐槽证明说明一般证明需要哪些可用试验，不排除具体操作由自身结构保持受限语言的等价关系。

第 3.2 条须明确

$$
q_0(a),\qquad q_0(b)=q_0(c),\qquad q_0(d)
$$

是三个两两不同的值，并保留第 3.1 条的边界下降假设。若 $q_1(h)=q_1(f)$，则边界下降给出

$$
(q_0(s(h)),q_0(t(h)))=(q_0(a),q_0(b)).
$$

恒等箭头的两个观察边界相等，不满足此式；另一条非恒等箭头 $g$ 的观察边界为 $(q_0(b),q_0(d))$，也不满足。所给范畴除恒等箭头外仅有 $f,g$，所以

$$
q_1^{-1}(\{q_1(f)\})=\{f\},\qquad
q_1^{-1}(\{q_1(g)\})=\{g\}.
$$

第二式由同一论证得到。因 $q_0(b)=q_0(c)$，观察箭头对属于候选拼接域；但两个观察纤维的唯一代表对是 $(f,g)$，且 $t(f)=b\ne c=s(g)$。这才排除任何实际可复合代表，证明该观察对不在真实联合像中。只检验原 $f,g$ 不可复合而不排除同纤维其他代表，本身不足以作此结论。

### 6.7 第 5.2 条：函子性与共滤性的完整条件

第 5.2 条的 $F:J\to\mathsf{Type}$ 必须是函子，满足恒等与复合律；$J$ 为小共滤范畴，含非空性、任意两个对象有共同前驱、任意平行箭头可经前复合等化三个条件。共同前驱和等化条件使任意有限组相容方程可在一个共同阶段同时实现；取该阶段的一个元素并映到相关对象，函子律保证这些方程成立。有限非空对象值的离散乘积紧致，故所有相容闭条件有共同点。不要求过渡映射满射。所得共同点是一族相容截面；若要求来自某个另给原始载体中的单个代表，还须该载体到截面集合的相应实现条件。

## 7. 观察完备化与共同中间见证的关系复合

本节固定非空载体 $X,Y,Z$。对每个 $U\in\{X,Y,Z\}$ 给定有限实际像观察塔

$$
q_n^U:U\twoheadrightarrow Q_n^U,\qquad n\in\mathbb N,\qquad
q_n^U=p_{m,n}^Uq_m^U\quad(m\ge n).
$$

各 $Q_n^U$ 有限离散，过渡映射满足恒等律与复合律。令

$$
K_U=\varprojlim_n Q_n^U,\qquad
\iota_U:U\to K_U,\quad \iota_U(u)=(q_n^U(u))_n,\qquad
\pi_n^U:K_U\to Q_n^U.
$$

$\iota_U$ 是实际载体到完成空间的自然映射，不预设单射。第 4.2 条给出 $K_U$ 紧致 Hausdorff、实际像稠密及柱集开闭基；又因 $\pi_n^U\iota_U=q_n^U$，每个 $\pi_n^U$ 满射。乘积投影和过渡映射使用上标 $XZ$ 或 $XYZ$，例如 $\pi_n^{XZ}=\pi_n^X\times\pi_n^Z$、$p_{m,n}^{XYZ}=p_{m,n}^X\times p_{m,n}^Y\times p_{m,n}^Z$。

给定支撑关系 $R\subseteq X\times Y$、$S\subseteq Y\times Z$，令

$$
C=S\circ R=\{(x,z):\exists y\in Y,\ R(x,y)\land S(y,z)\}.
$$

两次实际关系成员资格要求同一个 $y$。区分实际像与其在相应完成乘积中的闭包：

$$
R^0=(\iota_X\times\iota_Y)[R],\qquad
S^0=(\iota_Y\times\iota_Z)[S],\qquad
C^0=(\iota_X\times\iota_Z)[C],
$$

$$
\widehat R=\overline{R^0},\qquad
\widehat S=\overline{S^0},\qquad
\widehat C=\overline{C^0}.
$$

定义实际阶段像及有限层候选复合

$$
R_n=(q_n^X\times q_n^Y)[R],\qquad
S_n=(q_n^Y\times q_n^Z)[S],\qquad
C_n=(q_n^X\times q_n^Z)[C],\qquad D_n=S_n\circ R_n.
$$

总有 $C_n\subseteq D_n$；$D_n$ 只要求两个实际中间代表的第 $n$ 层读数相同。保留中间元素时，令

$$
W=\{(x,y,z)\in X\times Y\times Z:R(x,y)\land S(y,z)\},\qquad
W^0=(\iota_X\times\iota_Y\times\iota_Z)[W],\qquad
\widehat W=\overline{W^0},
$$

$$
T=\{(\xi,\eta,\zeta)\in K_X\times K_Y\times K_Z:
(\xi,\eta)\in\widehat R\land(\eta,\zeta)\in\widehat S\},\qquad
P=\widehat S\circ\widehat R=\operatorname{pr}_{XZ}(T).
$$

这里保留的是支撑关系中的端点与中间元素；$W$ 不记录同一三元组的多条历史或证明档案，不能与第 1.2 条任意带见证关系的数据载体混同。

**定理 7.1（逐有限层可复合与完成空间的共同中间见证）。** 在上述数据下，$P$ 闭，并且

$$
P=\bigcap_{n\ge0}(\pi_n^{XZ})^{-1}(D_n),\qquad
\widehat C\subseteq P.
$$

等价地，对任意 $\xi\in K_X$、$\zeta\in K_Z$，

$$
(\xi,\zeta)\in P
\ \Longleftrightarrow\
\forall n\in\mathbb N\ \exists b_n\in Q_n^Y,\quad
(\pi_n^X\xi,b_n)\in R_n\ \land\ (b_n,\pi_n^Z\zeta)\in S_n.
$$

保留中间见证时有

$$
\widehat W\subseteq T,\qquad
\operatorname{pr}_{XZ}(\widehat W)=\widehat C,\qquad
\operatorname{pr}_{XZ}(T)=P.
$$

**证明。** 若 $(\xi,\zeta)\in P$，取共同中间点 $\eta\in K_Y$。由第 3.4 条的有限观察闭包判定，$b_n=\pi_n^Y\eta$ 满足每层所列关系条件。

反之，设每层都有这样的 $b_n$，在 $K_Y$ 中定义

$$
F_n=\{\eta\in K_Y:
(\pi_n^X\xi,\pi_n^Y\eta)\in R_n,\
(\pi_n^Y\eta,\pi_n^Z\zeta)\in S_n\}.
$$

有限离散层的纤维开闭，故 $F_n$ 闭；$\pi_n^Y$ 满射使 $b_n$ 可提升，故 $F_n$ 非空。实际阶段关系像经下投影仍属低层关系，因而 $F_{n+1}\subseteq F_n$。紧致性给出 $\eta\in\bigcap_n F_n$，再次由闭包判定得到 $(\xi,\eta)\in\widehat R$ 和 $(\eta,\zeta)\in\widehat S$。这证明交集表达式；逐层所选的 $b_n$ 不必事先相容，紧致性取得同一个 $\eta$。交集中的每个集合都开闭，所以 $P$ 闭。

实际三元组的中间点 $y$ 映为 $\iota_Y(y)$ 后仍共同见证两条完成关系，故 $C^0\subseteq P$；取闭包得 $\widehat C\subseteq P$。$T$ 是两个闭关系的连续逆像之交，因此闭，且包含 $W^0$，所以 $\widehat W\subseteq T$。连续性给出

$$
\operatorname{pr}_{XZ}(\widehat W)
\subseteq\overline{\operatorname{pr}_{XZ}(W^0)}
=\overline{C^0}=\widehat C.
$$

另一方面，$\widehat W$ 紧致，其在 Hausdorff 空间 $K_X\times K_Z$ 中的连续像闭，并包含 $\operatorname{pr}_{XZ}(W^0)=C^0$，故也包含 $\widehat C$。两侧相等。$\operatorname{pr}_{XZ}(T)=P$ 是复合的定义。证毕。

所得共同见证属于 $K_Y$，不自动属于 $\iota_Y[Y]$；即使属于，也不自动使两个闭包成员资格由同一个实际 $y$ 实现。$P$ 已闭，再对它取闭包不能消除与 $\widehat C$ 的差距。

**命题 7.2（关系复合与完备化交换的确切阶段判据）。** 对每个 $n\in\mathbb N$，

$$
\pi_n^{XZ}[P]=\bigcap_{m\ge n}p_{m,n}^{XZ}[D_m].
$$

右侧在有限集合中递减，故存在 $m_0\ge n$，使所有 $m\ge m_0$ 都满足 $p_{m,n}^{XZ}[D_m]=\pi_n^{XZ}[P]$。因此

$$
\widehat C=P
\ \Longleftrightarrow\
\forall n\in\mathbb N\ \exists m\ge n,\quad
p_{m,n}^{XZ}[D_m]=C_n.
$$

令

$$
E_n=\{(a,b,c)\in Q_n^X\times Q_n^Y\times Q_n^Z:
(a,b)\in R_n\land(b,c)\in S_n\},\qquad
W_n=(q_n^X\times q_n^Y\times q_n^Z)[W].
$$

保留中间见证的交换判据为

$$
\widehat W=T
\ \Longleftrightarrow\
\forall n\in\mathbb N\ \exists m\ge n,\quad
p_{m,n}^{XYZ}[E_m]=W_n.
$$

端点判据的实际元素量词版为：对每个 $n$，存在 $m\ge n$，对所有 $x\in X$、$y_0,y_1\in Y$、$z\in Z$，若

$$
R(x,y_0)\land S(y_1,z)\land q_m^Y(y_0)=q_m^Y(y_1),
$$

则存在 $(x',y,z')\in W$，使

$$
q_n^X(x')=q_n^X(x),\qquad q_n^Z(z')=q_n^Z(z).
$$

**证明。** 固定 $n$。由定理 7.1，$u\in P$ 蕴含 $\pi_m^{XZ}(u)\in D_m$，下投影即得 $\pi_n^{XZ}[P]\subseteq\bigcap_{m\ge n}p_{m,n}^{XZ}[D_m]$。反之，取右侧的 $\alpha$，对 $m\ge n$ 定义

$$
H_m=\{u\in K_X\times K_Z:
\pi_n^{XZ}(u)=\alpha,\ \pi_m^{XZ}(u)\in D_m\}.
$$

因 $\alpha\in p_{m,n}^{XZ}[D_m]$，可取相应的 $m$ 层候选，再由 $\pi_m^{XZ}$ 满射提升，故 $H_m$ 非空。各 $H_m$ 闭且递减；紧致性取得 $u\in\bigcap_{m\ge n}H_m$。该点满足所有 $m\ge n$ 层条件，下投影又满足较低层条件，故由定理 7.1 得 $u\in P$，而 $\pi_n^{XZ}(u)=\alpha$。这证明第一式。

集合 $p_{m,n}^{XZ}[D_m]$ 在有限集合 $Q_n^X\times Q_n^Z$ 中递减，只有有限次严格缩小，故最终稳定于其交集。实际共同像满足

$$
p_{m,n}^{XZ}[C_m]=C_n,\qquad
C_m\subseteq D_m,\qquad
C_n\subseteq p_{m,n}^{XZ}[D_m]\quad(m\ge n).
$$

第一等式的满射方向由同一个实际 $(x,z)\in C$ 的第 $m$ 层读数给出。有限层纤维开闭，取闭包不增加或丢失该层像，所以

$$
\pi_n^{XZ}[\widehat C]=C_n.
$$

若 $\widehat C=P$，第一式及有限稳定性就给出所需 $m$。反之，若每个 $n$ 有一个 $m$ 使所列阶段像等于 $C_n$，第一式和始终成立的包含给出 $\pi_n^{XZ}[P]=C_n$。$P$ 中每点因此满足 $C$ 的全部有限观察条件，由第 3.4 条属于 $\widehat C$。结合定理 7.1 的包含得等式。

对于三元版本，闭包判定给出

$$
T=\bigcap_{m\ge0}(\pi_m^{XYZ})^{-1}(E_m).
$$

固定第 $n$ 层三元坐标 $\alpha\in\bigcap_{m\ge n}p_{m,n}^{XYZ}[E_m]$，用

$$
H_m^{XYZ}=\{u\in K_X\times K_Y\times K_Z:
\pi_n^{XYZ}(u)=\alpha,\ \pi_m^{XYZ}(u)\in E_m\}
$$

重复上述论证：$\pi_m^{XYZ}$ 满射保证非空，阶段关系的相容性保证递减，各集闭；紧致性交出一个满足全部层条件的三元点。因此

$$
\pi_n^{XYZ}[T]=\bigcap_{m\ge n}p_{m,n}^{XYZ}[E_m].
$$

有限递减交最终稳定；同一实际三元组的读数又给出

$$
p_{m,n}^{XYZ}[W_m]=W_n,\qquad
W_m\subseteq E_m,\qquad
\pi_n^{XYZ}[\widehat W]=W_n.
$$

若 $\widehat W=T$，取稳定阶段即可得到所列三元等式。反之，每个 $n$ 的阶段等式和始终成立的 $W_n\subseteq p_{m,n}^{XYZ}[E_m]$，使 $T$ 每点满足 $W$ 的全部有限观察条件，故 $T\subseteq\widehat W$；反向包含由定理 7.1 成立。

最后，任一 $D_m$ 候选可分别用 $R(x,y_0)$ 与 $S(y_1,z)$ 的实际代表表示，中间坐标相等恰为 $q_m^Y(y_0)=q_m^Y(y_1)$。其端点下投影属于 $C_n$，恰指存在所列实际共同三元组，故实际元素量词版等价于 $p_{m,n}^{XZ}[D_m]\subseteq C_n$。反向包含始终成立，遂得等价。证毕。

此判据允许先提高精度再排除虚假候选，不要求同一层的 $D_n=C_n$。有限稳定只给每个固定 $n$ 的阶段存在性，不给统一阶段界或可计算的停止界。

**定理 7.3（闭关系像与中间代表提升保证严格交换）。** 假定 $R^0$ 在 $K_X\times K_Y$ 中闭、$S^0$ 在 $K_Y\times K_Z$ 中闭，并且以下条件至少一个成立：

1. $\iota_Y$ 单射。
2. $R$ 在完整中间观察纤维上饱和，即
   $$
   \forall x\in X\ \forall y_0,y_1\in Y,\quad
   R(x,y_0)\land\iota_Y(y_0)=\iota_Y(y_1)\ \Longrightarrow\ R(x,y_1).
   $$
3. $S$ 在完整中间观察纤维上饱和，即
   $$
   \forall y_0,y_1\in Y\ \forall z\in Z,\quad
   S(y_1,z)\land\iota_Y(y_0)=\iota_Y(y_1)\ \Longrightarrow\ S(y_0,z).
   $$

则

$$
W^0=\widehat W=T,\qquad C^0=\widehat C=P.
$$

若进一步 $\iota_X,\iota_Z$ 单射，则对每个指定实际端点 $x\in X$、$z\in Z$，

$$
\exists y\in Y,\ R(x,y)\land S(y,z)
\ \Longleftrightarrow\
\forall n\in\mathbb N\ \exists b\in Q_n^Y,\quad
(q_n^X(x),b)\in R_n\land(b,q_n^Z(z))\in S_n.
$$

一组充分拓扑假设是：$X,Y,Z$ 为紧致 Hausdorff 空间，各 $q_n^U$ 连续，$R,S$ 在原乘积空间中闭，且中间观察族分离 $Y$ 的点。若三个载体的观察族均分离点，则还得到指定实际端点的版本。

**证明。** 闭性给出 $\widehat R=R^0$、$\widehat S=S^0$。取 $(\xi,\eta,\zeta)\in T$，由这两个实际像表示，分别取 $x\in X$、$y_0,y_1\in Y$、$z\in Z$，满足

$$
R(x,y_0),\qquad S(y_1,z),\qquad
\iota_X(x)=\xi,\quad
\iota_Y(y_0)=\eta=\iota_Y(y_1),\quad
\iota_Z(z)=\zeta.
$$

若 $\iota_Y$ 单射，则 $y_0=y_1$；若 $R$ 纤维饱和，则 $R(x,y_1)$，可取 $y_1$；若 $S$ 纤维饱和，则 $S(y_0,z)$，可取 $y_0$。三种情况都得到一个实际共同中间见证，其三元像是给定的 $(\xi,\eta,\zeta)$。故 $T\subseteq W^0$，而 $W^0\subseteq T$ 总成立。$T$ 闭，遂有 $W^0=\widehat W=T$。投影后 $C^0=P$，又由定理 7.1 的闭性得到 $C^0=\widehat C=P$。

对指定端点，右侧有限层条件由定理 7.1 等价于 $(\iota_X(x),\iota_Z(z))\in P$。刚证的实际实现给出某个 $(x',y,z')\in W$，其端点完整观察分别等于 $\iota_X(x),\iota_Z(z)$；两端的单射性迫使 $x'=x$、$z'=z$，因此原关系成员资格由所指定的实际端点实现。另一方向直接取实际 $y$ 的每层读数即可。

在所列拓扑假设下，$\iota_U$ 的每个坐标 $q_n^U$ 连续，故 $\iota_U$ 连续。闭关系 $R,S$ 是紧致乘积的闭子集，因而紧致；连续像 $R^0,S^0$ 紧致，目标 Hausdorff 保证它们闭。中间观察分离点恰使 $\iota_Y$ 单射，故上述结论适用。三族观察都分离点时，两端单射性也成立。证毕。

关系像在完成空间中闭，比关系在原载体中相对闭强。闭像保证完成关系成员资格有实际代表；中间单射性或饱和性把两个相同完整观察的代表换成一个；两端单射性才进一步固定所指定的实际端点。

**命题 7.4（闭包复合、端点交换与见证交换的严格反例）。** 一般情况下，$\widehat C\subseteq P$ 与 $\widehat W\subseteq T$ 均可严格；端点交换不推出见证交换，全部两条边关系的有限阶段像不决定实际共同像。闭关系像不能单独代替中间代表条件；原关系相对闭且观察分离，也不能单独代替完成空间中的闭像条件。

**证明。** 以下三组构造中均取 $X=Z=\{*\}$，两端观察恒为单点。

第一组取完整 Cantor 空间 $Y=\{0,1\}^{\mathbb N}$，$q_n^Y$ 记录位置 $0,\ldots,n-1$。其相容有限前缀恰是一条无限二进制序列，且柱拓扑就是积拓扑，故 $K_Y=Y$、$\iota_Y=\mathrm{id}$。令

$$
A_\varepsilon=\{y\in Y:\exists N\in\mathbb N\ \forall k\ge N,\ y_k=\varepsilon\}
\quad(\varepsilon\in\{0,1\}),\qquad
R=\{*\}\times A_0,\quad S=A_1\times\{*\}.
$$

任意有限前缀都可续接为最终恒零或恒一序列，故 $A_0,A_1$ 都稠密。同一序列不可能最终同时恒零、恒一，故它们互斥。于是

$$
C=\varnothing,\qquad
\widehat R=\{*\}\times Y,\qquad
\widehat S=Y\times\{*\},\qquad
\widehat C=\varnothing\subsetneq\{(*,*)\}=P.
$$

每个 $D_n$ 为端点单点，$C_n$ 为空。这里全部完成中间点都是原 $Y$ 点，失败来自原关系成员资格无法共同实现。

再令 $p=(0,0,\ldots)$，把 $S$ 改为 $S'=(A_1\cup\{p\})\times\{*\}$。因 $A_1$ 已有全部有限前缀，所有 $S_n'=S_n$，而 $R_n$ 不变，两个完成关系也不变。但

$$
A_0\cap(A_1\cup\{p\})=\{p\},\qquad
C'=S'\circ R=\{(*,*)\},\qquad
(C')^0=\widehat C'=P'=\{(*,*)\},
$$

$$
(W')^0=\widehat W'=\{(*,p,*)\}
\subsetneq \{*\}\times Y\times\{*\}=T'.
$$

其中三元单点在 Hausdorff 空间中闭，故其闭包不增点。这证明端点交换严格弱于见证交换；相同的全部 $R_n,S_n$ 可对应不同的 $C_n,W_n$，所以第 7.2 条必须另含实际共同像数据。

第二组取

$$
Y=\{0,1\},\qquad R=\{(*,0)\},\qquad S=\{(1,*)\}.
$$

若所有中间观察都是到单点的常值映射，则每层及 $K_Y$ 均为单点。$R^0,S^0$ 为闭单点，实际 $C$ 空，而 $P=\{(*,*)\}$。此时 $\iota_Y$ 不单射，两个关系也均不满足第 7.3 条的相应饱和性，故仅有闭关系像不足。

保持实际关系不变，改用第 $0$ 层常值、所有 $n\ge1$ 层精确的观察塔。相容线程由其精确层唯一决定，故 $K_Y=Y$；两完成关系仍分别通过 $0$ 和 $1$，没有共同中间点。因此

$$
\widehat C=P=\varnothing,\qquad
D_0=\{(*,*)\}\ne C_0=\varnothing,\qquad
D_n=C_n=\varnothing\quad(n\ge1).
$$

交换成立却没有每层的同阶段相等；提高到精确层才排除第 $0$ 层的假候选。

第三组令 $e_k\in\{0,1\}^{\mathbb N}$ 为只在位置 $k$ 等于 $1$ 的序列，取

$$
Y=\{e_k:k\in\mathbb N\},\qquad
q_n^Y(y)=(y_0,\ldots,y_{n-1}),\qquad Q_n^Y=q_n^Y[Y].
$$

$Q_n^Y$ 恰含全零前缀及每个只有一个 $1$ 的长度 $n$ 前缀；过渡为截断，观察按定义满射。相容线程给出一条无限序列：若有两个 $1$，足够长的前缀就不在相应 $Q_n^Y$ 中，矛盾；若有一个 $1$，线程是相应的 $e_k$；若没有，则为全零点 $p$。这些线程反过来都满足阶段条件，且识别保持柱集，故完成空间及自然映射为

$$
K_Y=Y\cup\{p\},\qquad p=(0,0,\ldots),\qquad
\iota_Y:Y\hookrightarrow Y\cup\{p\}.
$$

指定位置 $k$ 为 $1$ 的柱集在 $Y$ 中仅含 $e_k$，故每个单点开，$Y$ 的观察拓扑离散。令

$$
B_{\mathrm{ev}}=\{e_{2k}:k\in\mathbb N\},\qquad
B_{\mathrm{odd}}=\{e_{2k+1}:k\in\mathbb N\},\qquad
R=\{*\}\times B_{\mathrm{ev}},\quad S=B_{\mathrm{odd}}\times\{*\}.
$$

两子集在离散的原 $Y$ 中均闭，故 $R,S$ 在原乘积中相对闭，且 $C=\varnothing$。$p$ 的任意基本邻域只规定有限个位置为零，总可在更高偶位置或奇位置放置唯一的 $1$，故 $p$ 属于两子集在 $K_Y$ 中的闭包。另一方面，每个 $e_j$ 的上述单点柱邻域排除不含它的那个子集；$K_Y$ 又只有这些点和 $p$，所以精确地

$$
\overline{B_{\mathrm{ev}}}^{\,K_Y}=B_{\mathrm{ev}}\cup\{p\},\qquad
\overline{B_{\mathrm{odd}}}^{\,K_Y}=B_{\mathrm{odd}}\cup\{p\}.
$$

两闭包的交恰为 $\{p\}$，由此

$$
\widehat C=\varnothing,\qquad P=\{(*,*)\},\qquad
T=\{(*,p,*)\},\qquad p\notin\iota_Y[Y].
$$

完成复合的唯一共同中间见证不是原 $Y$ 点。这证明原载体相对闭性与观察分离仍不足以保证实际实现，区别于第一组的原关系成员资格缺失。证毕。

## 8. 本批的来源、范围与产地

文献表态：紧致性、紧致因子的闭投影、有限非空共滤极限与滤余极限的共同细化判据均属已有数学。第 7 节是基于这些构件和本卷观察塔定义的纸面推导（repo-derived）；未查证全球首创。以下固定源码仅锚定所列构件，不表示第 7 节整体交换判据已有 Lean 形式化。

项目源码固定于 `43aad93d4245edaa7cf8421a0de8a84392125107`，mathlib 固定于 `db584cd6d46c92f209a44c0f1c829460d327499d`：

| 固定源码 | 声明名 | 引用范围 |
| --- | --- | --- |
| [CompactLocalRealization](https://github.com/the-omega-institute/trureturing/blob/43aad93d4245edaa7cf8421a0de8a84392125107/D5/S3/Observer/Completion/CompactLocalRealization.lean) | `compact_local_realization` | 紧致空间中的有限局部实现 |
| [FiniteCofilteredLimit](https://github.com/the-omega-institute/trureturing/blob/43aad93d4245edaa7cf8421a0de8a84392125107/D5/S3/ObserverMemory/InverseLimits/FiniteCofilteredLimit.lean) | `finite_cofiltered_limit_nonempty` | 有限非空共滤系统的相容截面 |
| [IndependentDescentCriterion](https://github.com/the-omega-institute/trureturing/blob/43aad93d4245edaa7cf8421a0de8a84392125107/D5/S3/ObserverMemory/InverseLimitMorphisms/IndependentDescentCriterion.lean) | `inverse_limit_descent_and_independent_converse` | 坐标下降及满投影下的反推 |
| [GeneralHomFormula](https://github.com/the-omega-institute/trureturing/blob/43aad93d4245edaa7cf8421a0de8a84392125107/D5/S3/ObserverMemory/ProObjects/GeneralHomFormula.lean) | `pro_category_hom_formula`、`pro_hom_has_stage_representatives`、`pro_hom_stage_classes_compatible`、`singleStageDiagram` | pro-Hom、阶段代表类与单点呈示 |
| [StrictOneHoleContexts](https://github.com/the-omega-institute/trureturing/blob/43aad93d4245edaa7cf8421a0de8a84392125107/D5/S3/ConceptDynamics/Observation/StrictOneHoleContexts.lean) | `contextual_equivalence_is_greatest`、`signature_extension_refines` | 单载体上下文最大强同余与签名扩展 |
| [CompatibleResidueJointImage](https://github.com/the-omega-institute/trureturing/blob/43aad93d4245edaa7cf8421a0de8a84392125107/D5/S3/Factorization/PrimePowers/CompatibleResidueJointImage.lean) | `joint_residue_image_eq_compatible_pairs`、`residue_realization_independent_iff_coprime` | 含零模的联合余数像与互素判据 |
| [Mathlib/Topology/Maps/Proper/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Topology/Maps/Proper/Basic.lean) | `isClosedMap_fst_of_compactSpace` | 紧致因子的投影为闭映射 |
| [Mathlib/Topology/Compactness/Compact.lean](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Topology/Compactness/Compact.lean) | `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed` | 非空递减闭集的紧致性交 |
| [Mathlib/CategoryTheory/Limits/Types/ColimitTypeFiltered.lean](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/CategoryTheory/Limits/Types/ColimitTypeFiltered.lean) | `Functor.ιColimitType_eq_iff_of_isFiltered` | 滤余极限类相等的共同细化判据 |

产地：追加结构采用 theory-volume-template。主数学推理由 ChatGPT Pro 完成，条件核对与 TeX 规范化由 Codex 完成。

范围：本批为纸面陈述与证明，未新增或运行 Lean 验证。单载体源码锚不覆盖第 6 节的多种类推广；第 7 节只处理支撑关系及共同中间元素，不恢复同一三元组的多条历史或证明档案。本文不声明消化或冻结机器状态。

## 追加锚（本行以下为增补区）

## 9. 增补·普遍拼接保真的有限性边界

**本批导航。** 本批在完整卷基准 `1f193e8045b4091637dd5483f218cfc4fbfb352a` 之上增补：第 9 节给出普遍拼接保真的有限性边界、任意端点交换的闭包分离判据及全部有限分划的超滤子完成；第 10 节列本批来源、边界与核验。本批扩充第 7 节的关系复合与完备化交换问题，不改判既有条目；对旧推论 3.6 的引用按第 6.1 节校正后的量词解释。基线叙述中的“本次”“本轮”仍指写下它的那一次工作，本批不改写它们。

本节在 ZFC 中工作，层指标从 $0$ 开始。沿用有限实际像观察塔及关系完成的定义：

$$
K_U=\varprojlim_n Q_{U,n},
\qquad
\iota_U(u)=(q_{U,n}(u))_{n\in\mathbb N},
$$

以及

$$
\widehat T =
\overline{(\iota_U\times\iota_V)[T]}
\subseteq K_U\times K_V
\qquad
(T\subseteq U\times V).
$$

闭包始终取在所写的完成空间中，不将其与实际像混同。沿用定理 3.4、定义 4.1、定理 4.2 与第 7 节的记号和基本性质；关系代表的解释以第 6.1 节为准。[^rro9_repo]

**定理 9.1（可数有限观察塔的普遍单点拼接保真，等价于有限层已分清全部身份）。** 设 $Y\ne\varnothing$，给定满射

$$
q_n:Y\twoheadrightarrow Q_n
\qquad(n\in\mathbb N),
$$

其中每个 $Q_n$ 有限离散，并有

$$
p_n:Q_{n+1}\to Q_n,
\qquad
q_n=p_n\circ q_{n+1}.
$$

令

$$
K_Y=\varprojlim_n Q_n,
\qquad
\iota_Y(y)=(q_n(y))_{n\in\mathbb N}.
$$

取端点 $X=Z=\{\ast\}$，均配常值精确塔。对任意 $A,B\subseteq Y$，定义

$$
R_A=\{\ast\}\times A,
\qquad
S_B=B\times\{\ast\}.
$$

则以下三个条件等价：

$$
\begin{aligned}
\mathrm{(a)}\quad&
\forall A,B\subseteq Y,\qquad
\widehat{S_B\circ R_A} =
\widehat S_B\circ\widehat R_A;
\\
\mathrm{(b)}\quad&
Y\text{ 有限，且 }\iota_Y\text{ 单射};
\\
\mathrm{(c)}\quad&
\exists N\in\mathbb N,\qquad q_N\text{ 单射}.
\end{aligned}
$$

这些条件成立时，还有

$$
\iota_Y[Y]=K_Y,
$$

因而完成空间是与 $Y$ 双射的有限离散空间。

**证明。**

首先，把单点端点测试精确化。由乘积拓扑中的闭包定义，

$$
\widehat R_A =
\{\ast\}\times\overline{\iota_Y[A]},
\qquad
\widehat S_B =
\overline{\iota_Y[B]}\times\{\ast\}.
$$

两种端点复合均为 $\{(\ast,\ast)\}$ 的子集，并且

$$
\widehat{S_B\circ R_A}\ne\varnothing
\quad\Longleftrightarrow\quad
A\cap B\ne\varnothing,
$$

$$
\widehat S_B\circ\widehat R_A\ne\varnothing
\quad\Longleftrightarrow\quad
\overline{\iota_Y[A]}
\cap
\overline{\iota_Y[B]}
\ne\varnothing.
$$

若 $A\cap B\ne\varnothing$，任取其中一个元素，其观察像就在上述两个闭包中。因此，条件 (a) 等价于

$$
\mathrm{(P)}\qquad
\forall A,B\subseteq Y,\quad
A\cap B=\varnothing
\Longrightarrow
\overline{\iota_Y[A]}
\cap
\overline{\iota_Y[B]}
=\varnothing.
$$

第一步：非单射产生两个实际元素即可见的障碍。

若 $\iota_Y$ 不单射，存在

$$
y_0\ne y_1,
\qquad
\iota_Y(y_0)=\iota_Y(y_1).
$$

取

$$
A=\{y_0\},
\qquad
B=\{y_1\}.
$$

则 $A\cap B=\varnothing$，但两个观察像的闭包包含同一个点。于是

$$
\widehat{S_B\circ R_A}=\varnothing,
\qquad
\widehat S_B\circ\widehat R_A=\{(\ast,\ast)\}.
$$

所以 (a) 蕴含 $\iota_Y$ 单射。这个障碍不依赖可数性、紧致性或可度量性。

第二步：单射而无限时，仍会产生共同闭包点。

反设 $\iota_Y$ 单射且 $Y$ 无限。在 ZFC 中可取两两不同的元素序列

$$
y_0,y_1,y_2,\ldots\in Y.
$$

对每个 $r\in\mathbb N$，令

$$
F_r =
\overline{\{\iota_Y(y_j):j\ge r\}}
\subseteq K_Y.
$$

这些集合非空、闭且递减。由 $K_Y$ 紧致，

$$
\bigcap_{r\in\mathbb N}F_r\ne\varnothing.
$$

取

$$
\eta\in\bigcap_{r\in\mathbb N}F_r.
$$

记逆极限坐标投影为 $\pi_n:K_Y\to Q_n$，并令

$$
V_n(\eta) =
\{v\in K_Y:\pi_n(v)=\pi_n(\eta)\}.
$$

由塔的相容性，$V_n(\eta)$ 是递减的开闭邻域基：任意涉及有限多个层的邻域，都包含某个 $V_n(\eta)$。

递归选择严格递增的自然数序列 $(j_n)$，使

$$
\iota_Y(y_{j_n})\in V_n(\eta).
$$

其存在性如下：已选定 $j_{n-1}$ 时，由

$$
\eta\in F_{j_{n-1}+1}
$$

及 $V_n(\eta)$ 为开邻域，存在 $j>j_{n-1}$ 使

$$
\iota_Y(y_j)\in V_n(\eta).
$$

可以取满足条件的最小自然数 $j$。初始步骤同理由 $\eta\in F_0$ 得到。

对任意固定的 $m$，当 $n\ge m$ 时，

$$
\iota_Y(y_{j_n})\in V_n(\eta)\subseteq V_m(\eta).
$$

故

$$
\iota_Y(y_{j_n})\longrightarrow\eta.
$$

现在定义

$$
A=\{y_{j_{2r}}:r\in\mathbb N\},
\qquad
B=\{y_{j_{2r+1}}:r\in\mathbb N\}.
$$

由于原序列的元素互异，$A\cap B=\varnothing$；由于两个子序列均收敛到 $\eta$，

$$
\eta\in
\overline{\iota_Y[A]}
\cap
\overline{\iota_Y[B]}.
$$

这违反 (P)。

事实上，这个障碍在每个有限层都有明确表现：

$$
\forall n\in\mathbb N,\qquad
\pi_n(\eta)\in q_n[A]\cap q_n[B],
$$

尽管

$$
A\cap B=\varnothing.
$$

因此，每层都存在候选中间读数，并不提供同一个实际中间元素。

结合第一步与第二步，得到 (a) 蕴含 (b)。

第三步：有限且观察单射，必在某个有限层已经单射。

假设 (b)。对每对不同的 $y,y'\in Y$，定义其首次分离层

$$
n(y,y') =
\min\{n\in\mathbb N:q_n(y)\ne q_n(y')\}.
$$

该集合非空，因为 $\iota_Y$ 单射。令

$$
N =
\max\Bigl(
\{0\}
\cup
\{n(y,y'):y,y'\in Y,\ y\ne y'\}
\Bigr).
$$

由于 $Y$ 有限，这个最大值存在。

若 $q_N(y)=q_N(y')$，则沿塔下投影，在所有不高于 $N$ 的层都有相同读数。若 $y\ne y'$，这与第 $n(y,y')$ 层已经分离矛盾。因此 $q_N$ 单射，得到 (c)。

反之，若 (c) 成立，则 $Y$ 单射到有限集合 $Q_N$，所以 $Y$ 有限；并且

$$
\iota_Y(y)=\iota_Y(y')
\Longrightarrow
q_N(y)=q_N(y')
\Longrightarrow
y=y'.
$$

故 (c) 蕴含 (b)。

第四步：有限且观察单射，足以通过所有单点测试。

假设 (b)。任意 $A,B\subseteq Y$ 的观察像都是 Hausdorff 空间 $K_Y$ 中的有限集，因而闭。于是

$$
\overline{\iota_Y[A]}
\cap
\overline{\iota_Y[B]} =
\iota_Y[A]\cap\iota_Y[B] =
\iota_Y[A\cap B].
$$

故 (P) 成立，从而 (a) 成立。

最后，$\iota_Y[Y]$ 是有限闭集，又由实际像塔的基本性质稠密于 $K_Y$，因此

$$
K_Y=\iota_Y[Y].
$$

有限 Hausdorff 空间离散。证毕。

假设与选择原则的使用边界。

有限像保证完成空间的紧致性，也使“某层单射”推出载体有限。可数塔提供了上述可数柱邻域基；第二步正是在这里把紧致聚集现象转换成一条可拆成两部分的收敛序列。证明没有另行调用可度量性定理，所用的是更具体的可数柱邻域基；当然，该完成空间本身可度量。

通常选择原理的一项明确使用，是从任意无限 $Y$ 取出互异元素序列。给定该序列与题设紧致性之后，子列指标可以用自然数最小元递归选定。有限层分离、有限集合闭性及非单射障碍均不需要无限选择。本节记录的是上述证明的依赖，不声称这是最弱的选择公理配置。

**定理 9.2（紧致中间空间中，单点测试已经刻画任意端点的普遍交换）。** 设 $Y$ 为集合，$K$ 为紧致 Hausdorff 空间，$j:Y\to K$ 为映射。本定理不要求中间观察系统可数。

以下两个条件等价：

闭包分离条件：

$$
\forall A,B\subseteq Y,\quad
A\cap B=\varnothing
\Longrightarrow
\overline{j[A]}\cap\overline{j[B]}=\varnothing.
$$

普遍端点交换条件：对任意集合 $X,Z$、任意拓扑空间 $L_X,L_Z$、任意映射

$$
j_X:X\to L_X,
\qquad
j_Z:Z\to L_Z,
$$

以及任意关系

$$
R\subseteq X\times Y,
\qquad
S\subseteq Y\times Z,
$$

定义

$$
\widehat R =
\overline{(j_X\times j)[R]},
\qquad
\widehat S =
\overline{(j\times j_Z)[S]},
$$

$$
\widehat{S\circ R} =
\overline{(j_X\times j_Z)[S\circ R]}.
$$

则恒有

$$
\widehat{S\circ R} =
\widehat S\circ\widehat R.
$$

特别地，在定理 9.1 的可数有限实际像塔假设下，(a)、(b)、(c) 还等价于：对任意端点观察塔及任意关系 $R,S$，上述端点交换成立。**不需要端点实际像闭，也不需要端点观察映射单射或满射到完成空间。**

**证明。**

普遍端点交换蕴含闭包分离，只需取两个单点端点，并使用定理 9.1 证明开头的单点计算。该计算本身没有使用中间塔的可数性。

下面证明反方向。

先证明由中间紧致性保证的包含方向。

令

$$
\mathcal F =
\{(\xi,\eta,\zeta)\in L_X\times K\times L_Z:
(\xi,\eta)\in\widehat R,\quad
(\eta,\zeta)\in\widehat S\}.
$$

由于 $\widehat R,\widehat S$ 闭，$\mathcal F$ 闭。其端点投影恰为

$$
C =
\widehat S\circ\widehat R.
$$

中间因子 $K$ 紧致，保证 $C$ 闭。具体地，若 $(\xi,\zeta)\notin C$，则对每个 $\eta\in K$，存在开邻域

$$
U_\eta\ni\xi,\qquad
H_\eta\ni\eta,\qquad
V_\eta\ni\zeta
$$

使

$$
(U_\eta\times H_\eta\times V_\eta)\cap\mathcal F =
\varnothing.
$$

从 $(H_\eta)_{\eta\in K}$ 中取有限子覆盖，再分别交对应的 $U_\eta$ 与 $V_\eta$，便得到 $(\xi,\zeta)$ 的一个与 $C$ 不交的乘积开邻域。因此 $C$ 闭。

每个实际复合见证 $y\in Y$ 都给出完成空间中的见证 $j(y)$，所以

$$
(j_X\times j_Z)[S\circ R]\subseteq C.
$$

取闭包得到

$$
\widehat{S\circ R}
\subseteq
\widehat S\circ\widehat R.
$$

再证明闭包分离排除额外端点。

设

$$
(\xi,\zeta)\in\widehat S\circ\widehat R.
$$

取 $\eta\in K$ 使

$$
(\xi,\eta)\in\widehat R,
\qquad
(\eta,\zeta)\in\widehat S.
$$

任取开邻域

$$
U\ni\xi,
\qquad
V\ni\zeta.
$$

定义对应的实际中间见证集合

$$
A_U =
\{y\in Y:
\exists x\in X,\quad
j_X(x)\in U\ \land\ (x,y)\in R\},
$$

$$
B_V =
\{y\in Y:
\exists z\in Z,\quad
j_Z(z)\in V\ \land\ (y,z)\in S\}.
$$

对 $\eta$ 的任意开邻域 $H$，由 $(\xi,\eta)\in\widehat R$ 可知

$$
(U\times H)\cap(j_X\times j)[R]\ne\varnothing.
$$

故 $H\cap j[A_U]\ne\varnothing$。因此

$$
\eta\in\overline{j[A_U]}.
$$

同理，

$$
\eta\in\overline{j[B_V]}.
$$

闭包分离条件的逆否命题给出

$$
A_U\cap B_V\ne\varnothing.
$$

取 $y\in A_U\cap B_V$。根据定义，存在 $x\in X$ 与 $z\in Z$，使

$$
j_X(x)\in U,\qquad
j_Z(z)\in V,
$$

$$
(x,y)\in R,\qquad
(y,z)\in S.
$$

于是

$$
(x,z)\in S\circ R,
$$

从而

$$
(U\times V)\cap(j_X\times j_Z)[S\circ R]\ne\varnothing.
$$

由于 $U,V$ 任意，

$$
(\xi,\zeta)\in\widehat{S\circ R}.
$$

这证明了反向包含，故等式成立。证毕。

适用边界。

证明只在保证闭关系复合闭合的方向使用中间空间紧致性；排除虚假端点的方向使用闭包分离条件。两个端点空间甚至不必紧致或 Hausdorff。因而，端点完成所增加的点，以及端点实际像可能不闭，都不构成这里的额外障碍。

上述结论比较的是两个完成关系，本身不保证关系像闭，闭包符号不能据此删去。按第 6.1 节对推论 3.6 的校正，对关系 $T\subseteq U\times V$ 及观察映射 $e:U\times V\to L_U\times L_V$，若 $e[T]$ 闭，则 $\overline{e[T]}=e[T]$，每个完成关系点已经有某个 $t\in T$ 作为实际关系代表，无须再为该存在性附加实现假设。在此闭像条件下，代表唯一当且仅当 $e|_T$ 单射。对一个指定实际端点对 $t_0$，$e(t_0)\in\overline{e[T]}$ 只保证存在 $t\in T$ 与 $t_0$ 观察相同；要推出 $t_0\in T$，还可要求 $T$ 对 $e$ 的纤维饱和，或要求 $e$ 在整个原始端点乘积上单射。整个环境 $L_U\times L_V$ 的每一点都有实际端点代表，则要求 $e$ 对该环境满射；若要求代表均取自 $T$，则要求 $e[T]=L_U\times L_V$。这些量词均不能与完成关系内部的代表存在性混同。[^rro9_repo]

**命题 9.3（全部有限分划给出无限反例，但单点测试与一般端点交换仍然等价）。** 设 $Y$ 为任意无限集合。以 $Y$ 的全部有限分划为观察指标：每个分划只含非空块，细分划向粗分划映射到包含它的块。记这一共滤指标系统为 $\mathfrak P_f(Y)$，并定义

$$
q_{\mathcal P}:Y\twoheadrightarrow\mathcal P,
\qquad
q_{\mathcal P}(y)=\text{分划 }\mathcal P\text{ 中包含 }y\text{ 的块},
$$

$$
K_Y^{\mathrm{all}} =
\varprojlim_{\mathcal P\in\mathfrak P_f(Y)}\mathcal P.
$$

则 $K_Y^{\mathrm{all}}$ 可识别为 $Y$ 上全部超滤子组成的 Stone 空间，即离散空间 $Y$ 的 Stone–Čech 完成；实际元素 $y$ 对应主超滤子

$$
\delta_y=\{A\subseteq Y:y\in A\}.
$$

有限分划与超滤子的标准对应见文献中的有限分划刻画。[^rro9_ultrafilter]

对每个 $A\subseteq Y$，记

$$
A^\ast =
\{\mathfrak u\in K_Y^{\mathrm{all}}:A\in\mathfrak u\}.
$$

则

$$
\overline{\delta[A]}=A^\ast,
$$

并且对所有 $A,B\subseteq Y$，

$$
\overline{\delta[A]}
\cap
\overline{\delta[B]} =
(A\cap B)^\ast.
$$

因此，所有单点端点测试均通过，但 $Y$ 无限，且没有任何有限分划层能够单射。这是**去掉可数塔限制后**对有限性结论的反例，不是对定理 9.1 的反例。

此外，对这个固定的中间完成，任意端点观察塔及任意关系仍满足

$$
\widehat{S\circ R} =
\widehat S\circ\widehat R.
$$

端点无须也采用全部有限分划。

**证明。**

首先，有限分划的总集合是一个集合，任意有限组分划都有由非空块交组成的共同细化。因此，上述系统确为共滤的有限实际像观察系统。

每个分划空间有限离散，逆极限是其乘积中由相容等式确定的闭子空间。在 ZFC 中，由乘积紧致性可知 $K_Y^{\mathrm{all}}$ 紧致 Hausdorff。每个实际元素给出一条相容线程，故它非空。

线程与超滤子的对应。

给定一条线程

$$
\xi=(C_{\mathcal P})_{\mathcal P\in\mathfrak P_f(Y)},
\qquad
C_{\mathcal P}\in\mathcal P,
$$

定义

$$
\mathfrak u_\xi =
\{A\subseteq Y:
\exists\mathcal P\in\mathfrak P_f(Y),\quad
C_{\mathcal P}\subseteq A\}.
$$

它包含 $Y$ 而不包含空集，并显然向上封闭。

若 $A,B\in\mathfrak u_\xi$，分别取所需分划 $\mathcal P,\mathcal Q$，再取共同细化 $\mathcal R$。线程相容性给出

$$
C_{\mathcal R}
\subseteq
C_{\mathcal P}\cap C_{\mathcal Q}
\subseteq A\cap B.
$$

故 $A\cap B\in\mathfrak u_\xi$。

对任意 $A\subseteq Y$，考察删去空块后的二分划

$$
\{A,Y\setminus A\}\setminus\{\varnothing\}.
$$

线程选中的块包含于 $A$ 或 $Y\setminus A$，所以两者之一属于 $\mathfrak u_\xi$；两者不能同时属于这个真滤子。因此 $\mathfrak u_\xi$ 是超滤子。

反之，一个超滤子在每个有限分划中恰含一个块：不能含两个不交块；若一个块也不含，则所有块的补集都属于它，其有限交为空，矛盾。令 $C_{\mathcal P}$ 为该唯一块。向上封闭性保证这些选择在细化下相容。两个构造互为逆。

指定线程的某个分划坐标为一个块 $C$，恰对应超滤子满足 $C\in\mathfrak u$。因此，该对应也保持柱拓扑。

子集闭包的精确计算。

由二分划可知，对任意 $A\subseteq Y$，$A^\ast$ 开闭，且

$$
K_Y^{\mathrm{all}}\setminus A^\ast =
(Y\setminus A)^\ast.
$$

这些集合构成拓扑基，并满足

$$
A^\ast\cap B^\ast=(A\cap B)^\ast.
$$

由于 $\delta[A]\subseteq A^\ast$ 且 $A^\ast$ 闭，

$$
\overline{\delta[A]}\subseteq A^\ast.
$$

反过来，设 $\mathfrak u\in A^\ast$，并取它的任意基本邻域 $C^\ast$。则

$$
A\in\mathfrak u,
\qquad
C\in\mathfrak u,
$$

所以

$$
A\cap C\in\mathfrak u,
\qquad
A\cap C\ne\varnothing.
$$

取 $y\in A\cap C$，便有

$$
\delta_y\in\delta[A]\cap C^\ast.
$$

故 $\mathfrak u\in\overline{\delta[A]}$，证明

$$
\overline{\delta[A]}=A^\ast.
$$

取 $A=Y$ 也得到实际像稠密。

于是

$$
\overline{\delta[A]}
\cap
\overline{\delta[B]} =
(A\cap B)^\ast,
$$

而

$$
(A\cap B)^\ast\ne\varnothing
\quad\Longleftrightarrow\quad
A\cap B\ne\varnothing.
$$

反向蕴含由交集中的任意实际元素所确定的主超滤子给出。因此所有单点端点测试均成立。

与此同时，$\delta$ 单射，因为不同实际元素可由二分划分开；但 $Y$ 无限，所以它不可能单射到任何一个有限分划的块集合。故去掉可数性后，条件 (a) 可以成立，而条件 (b)、(c) 均不成立。

一般端点的复合也成立。

这里已有紧致中间空间和闭包分离条件，故定理 9.2 直接适用。为明确实际见证如何产生，设

$$
(\xi,\mathfrak u)\in\widehat R,
\qquad
(\mathfrak u,\zeta)\in\widehat S.
$$

对任意端点邻域 $U\ni\xi$、$V\ni\zeta$，采用定理 9.2 中的实际见证集合 $A_U,B_V$。由闭包定义及刚证明的闭包公式，

$$
\mathfrak u\in\overline{\delta[A_U]}=A_U^\ast,
\qquad
\mathfrak u\in\overline{\delta[B_V]}=B_V^\ast.
$$

所以

$$
A_U,B_V\in\mathfrak u,
\qquad
A_U\cap B_V\ne\varnothing.
$$

交集中的一个实际 $y$，连同其定义提供的 $x,z$，就在 $U\times V$ 中给出实际复合端点。反向包含因此成立；另一方向由中间紧致性成立。这是闭包和滤子有限交性质的直接证明，不以函子保复合或保弱拉回的名称代替论证。证毕。

可数性、选择原则与实现性的边界。

该反例保留了每层有限、实际像满射、共滤相容和完成空间紧致等条件；改变的是观察指标不再要求可数。定理 9.1 中提取收敛实际子列的一步不能推广到这里：若主点序列 $(\delta_{y_n})$ 的实际元素互异，取

$$
A=\{y_{2n}:n\in\mathbb N\},
$$

则序列的偶数项位于开闭集 $A^\ast$，奇数项位于其补集，因此这条序列不可能收敛。同样的分割论证适用于任何互异主点子列。

无限 $Y$ 的余有限子集构成真滤子；由超滤子引理扩张得到的超滤子不含任何有限集，因而非主。[^rro9_ultrafilter] 所以

$$
\delta[Y]\subsetneq K_Y^{\mathrm{all}},
$$

尽管所有上述端点交换都成立。这里的任意指标紧致性与超滤子存在性均在 ZFC 中使用，不据此主张无选择或有效构造版本。

这里使用全部有限分划组成的指标系统，不能将它视为定理 9.1 的可数塔。端点交换不把非主完成见证变成实际元素，也不包含关于其他关系提升定义或任意函子弱拉回保持性的断言。

## 10. 本批的来源、边界与核验

**文献表态。** 第 9 节沿用完整卷基准 `1f193e8045b4091637dd5483f218cfc4fbfb352a` 中定理 3.4、定义 4.1、定理 4.2、第 6.1 节及第 7 节的关系完成框架。[^rro9_repo] 有限分划的超滤子刻画、主超滤子、余有限滤子的非主超滤子扩张，以及离散空间的 Stone–Čech 完成，均是标准构件；Leinster 第 1 节给出相应定义、例子与命题，并将有限分划刻画归于 Galvin 与 Horn。[^rro9_ultrafilter] 定理 9.1、定理 9.2 与命题 9.3 的闭包公式及端点交换在正文给出纸面论证，不主张全球原创性，也不将这些完整陈述归为所引文献或 Mathlib 已直接证明的同名结果。

源码核对固定在 Mathlib 提交 `db584cd6d46c92f209a44c0f1c829460d327499d`。在 [Mathlib/Topology/Compactification/StoneCech.lean](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Topology/Compactification/StoneCech.lean) 中，`ultrafilterBasis_is_basis`、`ultrafilter_isOpen_basic`、`ultrafilter_isClosed_basic` 对应 $A^\ast$ 的开闭基，`ultrafilter_compact` 与 `Ultrafilter.t2Space` 对应超滤子空间的紧致 Hausdorff 性，`denseRange_pure` 与 `isDenseEmbedding_pure` 对应离散载体的主超滤子稠密嵌入，`ultrafilter_extend_extends` 与 `continuous_ultrafilter_extend` 给出到紧致 Hausdorff 空间的连续延拓构件。在 [Mathlib/Topology/Ultrafilter.lean](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Topology/Ultrafilter.lean) 中，`mem_closure_iff_ultrafilter` 刻画闭包成员资格，`Ultrafilter.clusterPt_iff` 刻画超滤子的聚点与收敛关系。这些核对限于相关声明及其源码，不构成本批三条结果的 Lean 证明。

**产地。** 追加结构采用 theory-volume-template 及其 APPEND 模板，协作载体为 sshx；ChatGPT Pro 提供主数学推理与正式结果草稿，Codex 依据该草稿、固定仓库来源及文献作源码核对与格式实施。

**本批不主张的。** 本批是 ZFC 下的纸面结果，未新增或运行 Lean，未 kernel-verified。可数塔、紧致中间空间及所用选择原则的边界分别见三条结果正文；不把非主超滤子当作实际元素，不断言无选择或有效构造版本。

[^rro9_repo]: 完整卷固定提交 `1f193e8045b4091637dd5483f218cfc4fbfb352a`，[RECURSIVE_RELATIONAL_OBSERVATION.md](https://github.com/the-omega-institute/trureturing/blob/1f193e8045b4091637dd5483f218cfc4fbfb352a/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md)：定理 3.4“联合关系的有限观察闭包”、定义 4.1“有限观察塔”、定理 4.2“观察完备化的基本性质”、第 6.1 节“第 3.6 与 5.1 条：闭像、关系代表与环境满射”，以及第 7 节“观察完备化与共同中间见证的关系复合”。旧推论 3.6 的实现性措辞按第 6.1 节解释。

[^rro9_ultrafilter]: Tom Leinster, *Codensity and the ultrafilter monad*, *Theory and Applications of Categories* **28** (2013), 332–370，[arXiv:1209.3606v3](https://arxiv.org/html/1209.3606v3)。标准构件对应第 1 节定义 1.1–1.2、例 1.3–1.4、命题 1.5（Galvin 与 Horn），以及该节末尾关于离散空间 Stone–Čech 完成与超滤子的说明。本批核对其 HTML 正文；本节所需的闭包公式及端点复合等式在正文直接证明。

## 追加锚（本行以下为增补区）

## 11. 增补·重复历史的观察商与运算扩展

**定义 11.0（约定）。** 本节采用通常外部集合论中的自然数 $\mathbb N=\{0,1,2,\ldots\}$，并以外部自然数归纳解释有限迭代。对映射 $f$，记 $\ker f=\{(x,y):f(x)=f(y)\}$；这里的“核”始终指等值关系，不指零元的原像。历史载体为集合 $H$，初始历史为 $e\in H$，后继为 $S:H\to H$；端状态映射为 $E:H\to X$，观察映射为 $q:H\to B$，其中 $X,B$ 分别为端状态和观察记录的载体。历史载体、端状态、观察记录及观察记录上的运算分别指定，不预先认定它们保存相同的区别。实际像、严格响应及上下文的约定见定义 2.1、2.4 与命题 2.6。[^rro11_volume]

**定理 11.1（无混淆、无遗漏生成的自然数刻画）。** 设 $H$ 为集合，$e\in H$，$S:H\to H$。以下三种表述等价。

生成表述：每个历史都由有限次后继生成，而且后继无混淆、初始历史没有前驱，即

$$
H=\{S^n(e):n\in\mathbb N\},\qquad
S\text{ 单射},\qquad
e\notin S[H].
$$

同构表述：存在唯一双射 $\nu:\mathbb N\to H$，满足

$$
\nu(0)=e,\qquad
\nu(n+1)=S(\nu(n)).
$$

该双射必为 $\nu(n)=S^n(e)$。

归纳表述：$S$ 单射、$e\notin S[H]$，并且对每个外部子集 $A\subseteq H$ 都有

$$
e\in A\ \land\ S[A]\subseteq A
\quad\Longrightarrow\quad
A=H.
$$

在这些等价条件下，对任意集合 $Y$、$y_0\in Y$ 和映射 $T:Y\to Y$，存在唯一映射 $f:H\to Y$，使得

$$
f(e)=y_0,\qquad f\circ S=T\circ f.
$$

其值由

$$
f(\nu(n))=T^n(y_0)
$$

唯一确定。

这里对 $A\subseteq H$ 的量化是外部全子集量化，不是仅针对某个固定语言中可定义谓词的形式归纳模式。自然数及其归纳已用于表述和证明该刻画。

**证明。** 先假设生成表述成立。定义 $\nu(n)=S^n(e)$，无遗漏条件立即给出满射性。若 $\nu(m)=\nu(n)$ 且 $m<n$，则 $S^m$ 单射，故

$$
e=S^{n-m}(e)=S\bigl(S^{n-m-1}(e)\bigr),
$$

与 $e\notin S[H]$ 矛盾。因此 $\nu$ 单射。它满足所述初始值和后继方程；任何满足这两个方程的映射，均由外部自然数归纳与 $\nu$ 逐项相等，故唯一。

反之，设同构表述成立。满射性给出无遗漏生成。若 $S(x)=S(y)$，写 $x=\nu(m)$、$y=\nu(n)$，则

$$
\nu(m+1)=\nu(n+1).
$$

由 $\nu$ 单射得到 $m+1=n+1$，从而 $x=y$。若存在 $x=\nu(n)$ 使 $S(x)=e$，则 $\nu(n+1)=\nu(0)$，同样矛盾。因此生成表述成立。

无遗漏生成与所列全子集归纳原则等价。一个包含 $e$ 且对 $S$ 封闭的子集，依据外部自然数归纳包含每个 $S^n(e)$，故在无遗漏生成下等于 $H$。反之，轨道子集

$$
A_0=\{S^n(e):n\in\mathbb N\}
$$

包含 $e$ 且对 $S$ 封闭；将归纳原则用于 $A_0$，即得 $A_0=H$。

最后，利用 $\nu$ 的双射性定义 $f(\nu(n))=T^n(y_0)$。这一定义满足两个递归方程。若 $g$ 也满足它们，外部自然数归纳给出 $g(\nu(n))=T^n(y_0)$；再由 $\nu$ 满射得到 $g=f$。

原始历史的自由性不自动传给端状态 $E:H\to X$ 或观察 $q:H\to B$。例如取 $H=\mathbb N$、$e=0$、$S(n)=n+1$，令 $E(n)=*$、$q(n)=n\bmod 2$，则原始历史满足全部条件，而端状态丢失全部次数，观察只保留奇偶。对于多标记或多事件自由历史，固定一个追加操作通常不能生成整个载体；应用本条时，应限制到重复该固定标记或事件的子载体，而不能把多标记历史整体误认成单一后继轨道。[^rro11_history] 证毕。

**定理 11.2（单一重复的自治观察核及运算下降）。** 设 $q:\mathbb N\twoheadrightarrow B$，不预设 $B$ 有限。以下条件等价：观察满足后继稳定性

$$
q(n)=q(m)\quad\Longrightarrow\quad q(n+1)=q(m+1);
$$

存在映射 $s:B\to B$，使 $s(q(n))=q(n+1)$；存在二元运算 $\oplus:B\times B\to B$，使

$$
q(n+m)=q(n)\oplus q(m).
$$

存在时，$s$ 和 $\oplus$ 均唯一，且 $\oplus$ 使 $B$ 成为以 $q(0)$ 为单位元、由 $q(1)$ 生成的交换幺半群。

这些条件成立时，$\ker q$ 恰有以下两种可能：它是等号关系；或者存在唯一的阈值 $t\ge0$ 和周期 $p\ge1$，使

$$
n\mathrel{R_{t,p}}m
\quad\Longleftrightarrow\quad
n=m\ \lor\
\bigl(n\ge t\ \land\ m\ge t\ \land\ n\equiv m\pmod p\bigr),
$$

且 $\ker q=R_{t,p}$。反之，每个 $R_{t,p}$ 都是某个满射自治观察的核。非等号情形下，$B$ 自动有限，且

$$
|B|=t+p.
$$

此外，每个这样的核都自动允许自然数乘法在两个槽位上同时下降：存在唯一运算 $\otimes:B\times B\to B$，使

$$
q(nm)=q(n)\otimes q(m).
$$

因此 $q$ 是从自然数半环到其观察商半环的满同态，允许平凡半环情形。乘法的自动下降特指自然数加法同余；它也没有推出任意新增二元运算都会下降。阈值—周期核形是自然数加法幺半群同余的标准分类。[^rro11_monogenic][^rro11_periodicity]

**证明。** 写 $n\sim m$ 表示 $q(n)=q(m)$。后继稳定性通过外部自然数归纳推出

$$
n\sim m\quad\Longrightarrow\quad n+k\sim m+k
\qquad(k\in\mathbb N).
$$

若 $a\sim a'$、$b\sim b'$，则

$$
a+b\sim a'+b\sim a'+b'.
$$

故定义 $q(a)\oplus q(b)=q(a+b)$ 与代表元无关。满射性给出唯一性，结合律、交换律和单位元律从自然数加法下降。反过来，若加法下降，则

$$
q(n+1)=q(n)\oplus q(1),
$$

立即得到后继稳定性。

同样，后继稳定性恰保证 $s(q(n))=q(n+1)$ 与代表元无关；满射性给出唯一性。若这样的 $s$ 已存在，则后继稳定性显然成立。

下面证明完整核形。若没有不同自然数具有相同读数，则核为等号。否则定义

$$
t=\min\{i\in\mathbb N:\exists j>i,\ i\sim j\},
\qquad
p=\min\{d\ge1:t\sim t+d\}.
$$

两个集合均非空，故最小值存在。由平移稳定性，

$$
n\sim n+p\qquad(n\ge t).
$$

先证明 $0,1,\ldots,t+p-1$ 的读数两两不同。若 $i<j$ 且 $i<t$，则 $i\sim j$ 直接违背 $t$ 的最小性。余下情形可写成

$$
i=t+r,\qquad j=t+s,\qquad 0\le r<s<p.
$$

假设 $i\sim j$。将两边同时平移 $p-s$，得到

$$
t+(p-s+r)\sim t+p\sim t.
$$

但 $1\le p-s+r<p$，这违背 $p$ 的最小性。因此所列代表的读数确实两两不同。此处只使用向前平移，没有对观察后的后继作未经许可的反向消去。

定义规范代表

$$
\rho_{t,p}(n)=
\begin{cases}
n,&n<t,\\
t+((n-t)\bmod p),&n\ge t.
\end{cases}
$$

若 $n\ge t$，写 $n-t=kp+r$，其中 $0\le r<p$。反复使用尾部的 $p$ 步相等，得到

$$
n=t+kp+r\sim t+r=\rho_{t,p}(n).
$$

对 $n<t$ 也有 $n\sim\rho_{t,p}(n)$。因规范代表的读数两两不同，

$$
n\sim m
\quad\Longleftrightarrow\quad
\rho_{t,p}(n)=\rho_{t,p}(m).
$$

展开右侧，正是所述 $R_{t,p}$。规范代表共有 $t+p$ 个，且 $q$ 满射，故 $|B|=t+p$。

阈值 $t$ 是首次参与向后碰撞的较小下标，周期 $p$ 是该下标的最小正返回步长，二者由核唯一确定。反之，任意给定 $t\ge0$、$p\ge1$，关系 $R_{t,p}$ 是 $\rho_{t,p}$ 的等值核，因而是等价关系。若两个相关数不相等，它们均在尾部且同余；同时加一后仍均在尾部且同余。因此 $R_{t,p}$ 满足后继稳定性，取相应商映射便得到所需自治观察。

最后证明乘法下降，不再依赖核的显式分类。由加法同余性，对 $k$ 归纳可得

$$
a\sim a'\quad\Longrightarrow\quad ka\sim ka'.
$$

归纳起点是 $0\sim0$；归纳步使用 $ka+a\sim ka'+a'$。因此，当 $a\sim a'$、$b\sim b'$ 时，

$$
ab\sim a'b\sim a'b'.
$$

这保证 $\otimes$ 定义良好；满射性给出唯一性，其结合律、单位元律、零元律及对 $\oplus$ 的分配律均由自然数运算下降。证毕。

**定理 11.3（奇偶观察在幂与减法扩签名下的精确细化）。** 固定基本观察

$$
q:\mathbb N\to\{0,1\},\qquad q(n)=n\bmod2.
$$

每个上下文是一个有限、恰含一个孔的运算表达式，其他输入位置允许填入任意固定自然数参数；参数在比较两个输入时保持不变。允许恒等上下文 $C(x)=x$。

对总运算签名 $\Sigma$，定义

$$
n\equiv_\Sigma m
\quad\Longleftrightarrow\quad
\forall C,\ q(C(n))=q(C(m)),
$$

其中 $C$ 遍历该签名的全部有限一孔上下文。“最粗保 $q$ 的同余”指包含于 $\ker q$、且对所有基本运算相容的最大等价关系。[^rro11_contexts]

令

$$
\Sigma_0=\{+,\times\},\qquad
\Sigma_1=\{+,\times,\operatorname{pow}\},
\qquad
\operatorname{pow}(a,b)=a^b,
$$

其中幂是两个槽位都可参与上下文的总运算，并约定 $0^0=1$。则

$$
\equiv_{\Sigma_0}=R_{0,2}=\ker q,
$$

而

$$
n\equiv_{\Sigma_1}m
\quad\Longleftrightarrow\quad
q(n)=q(m)\ \land\ (n=0\Longleftrightarrow m=0).
$$

因此 $\equiv_{\Sigma_1}=R_{1,2}$，恰有三类：

$$
\{0\},\qquad
\{2,4,6,\ldots\},\qquad
\{1,3,5,\ldots\}.
$$

再分别向 $\Sigma_1$ 加入截断减法或严格部分减法：

$$
d_{\mathrm t}(a,b)=
\begin{cases}
a-b,&b\le a,\\
0,&b>a,
\end{cases}
\qquad
d_{\mathrm p}(a,b)=
\begin{cases}
\operatorname{ok}(a-b),&b\le a,\\
\bot,&b>a.
\end{cases}
$$

这里部分减法的“严格”指失败必须被记录并向外传播，准入域仍是 $b\le a$。对含部分运算的上下文，使用观察

$$
q_\bot(\operatorname{ok}(n))=\operatorname{ok}(q(n)),
\qquad
q_\bot(\bot)=\bot,
$$

其中失败标签与两个成功标签均不同。部分运算的强同余须同时保持准入性和成功结果的等价类。

对 $\Sigma_{\mathrm t}=\Sigma_1\cup\{d_{\mathrm t}\}$ 与 $\Sigma_{\mathrm p}=\Sigma_1\cup\{d_{\mathrm p}\}$，均有

$$
\equiv_{\Sigma_{\mathrm t}}
=\equiv_{\Sigma_{\mathrm p}}
=\Delta_{\mathbb N}.
$$

于是这些观察商的类数依次为 $2$、$3$ 和 $\aleph_0$。这是相对于明确操作语言的身份细化，不是几何维数的增长。

**证明。** 首先，任何包含于 $\ker q$ 的运算同余都使全部有限一孔上下文保持观察相等：对上下文的构造作归纳，孔的位置使用所给等价，其他位置使用固定参数的自反等价，再使用基本运算的相容性。部分情形同时归纳失败传播和成功结果的等价。因此，只要一个候选关系本身是相应同余，并且关系外的每一对都能被某个上下文区分，就证明了它恰为所求最粗同余。

在 $\Sigma_0$ 中，加法和乘法都只依赖输入的奇偶来决定输出奇偶。故 $\ker q$ 对两种运算相容，上下文归纳给出

$$
\ker q\subseteq\equiv_{\Sigma_0}.
$$

恒等上下文给出反向包含，故二者相等。

令 $R$ 表示“奇偶相同且同时为零或同时非零”。先证明 $R$ 对 $\Sigma_1$ 的全部基本运算相容。对自然数，

$$
a+b=0\Longleftrightarrow a=b=0,
\qquad
ab=0\Longleftrightarrow a=0\ \lor\ b=0.
$$

结合和、积的奇偶规则可知，和与积的零性及奇偶性均由两个输入的 $R$-类决定。

由自然幂的递归定义，对指数归纳得到

$$
a^b=0\Longleftrightarrow a=0\ \land\ b>0,
$$

以及

$$
q(a^b)=
\begin{cases}
1,&b=0,\\
q(a),&b>0.
\end{cases}
$$

这些公式包括 $a=b=0$ 的情形。因此幂结果的零性与奇偶性也完全由两个输入的 $R$-类决定，$R$ 确为 $\Sigma_1$ 同余。上下文归纳于是给出

$$
R\subseteq\equiv_{\Sigma_1}.
$$

反向包含不能只靠一个反例，而须排除所有关系外的对。若 $n,m$ 奇偶不同，恒等上下文已经区分它们。若奇偶相同但零性不同，则其中一个为 $0$，另一个为某个正偶数 $2k$。上下文

$$
C(x)=0^x
$$

满足

$$
q(C(0))=1,\qquad q(C(2k))=0.
$$

故这类对也全部可区分。除此以外的对正是 $R$，所以 $\equiv_{\Sigma_1}=R=R_{1,2}$。

对截断减法，任取 $n<m$。由于 $m\ge1$，允许的固定参数 $m-1$ 给出上下文

$$
C(x)=d_{\mathrm t}(x,m-1).
$$

此时

$$
C(n)=0,\qquad C(m)=1,
$$

故任意两个不同自然数都能被区分。相等输入当然在全部上下文中有相同响应，因此 $\equiv_{\Sigma_{\mathrm t}}=\Delta_{\mathbb N}$。

对严格部分减法，任取 $n<m$，使用

$$
C(x)=d_{\mathrm p}(x,m).
$$

则

$$
C(n)=\bot,\qquad C(m)=\operatorname{ok}(0).
$$

两者在严格观察下不同，故同样得到等号关系。这一分离实际上只使用失败与成功的区别，不需要利用两个不同成功数值的奇偶差异。以上两种减法的分离均不依赖先加入幂。

允许全部自然数参数是本条所述语言的明确契约，但不是这些结论的最小假设。幂的必要性分离只需一个可用的偶数底数，例如 $0$ 或 $2$。对于两种减法，只要常量 $1$ 可用并允许任意有限嵌套，就已足够：令

$$
u_{\mathrm t}(x)=d_{\mathrm t}(x,1),\qquad
u_{\mathrm p}(x)=d_{\mathrm p}(x,1).
$$

归纳可知，$u_{\mathrm t}^{\,m-1}$ 将任意 $n<m$ 与 $m$ 分别送到 $0$ 与 $1$；严格迭代 $u_{\mathrm p}^{\,m}$ 在 $n<m$ 时失败，在 $m$ 时成功返回 $0$。所以不必把每个自然数分别设为原始常量；允许常量 $0,1$ 和加法形成闭项，也能提供全部自然数参数。这里每个上下文有限，但没有以一张预先给定的有限测试表代替全部上下文量化。

新增读数 $d(n)=q(0^n)$ 不是旧读数 $q(n)$ 的后处理，因为 $q(0)=q(2)$ 而 $d(0)\ne d(2)$。证毕。

**定理 11.4（交换幺半群补逆元的稳定核与观察保真）。** 设 $(M,+,0)$ 为交换幺半群，$\eta_M:M\to G(M)$ 为其 Grothendieck 群的规范同态。[^rro11_grothendieck] 则

$$
\eta_M(a)=\eta_M(b)
\quad\Longleftrightarrow\quad
\exists c\in M,\ a+c=b+c.
$$

因此

$$
\eta_M\text{ 单射}
\quad\Longleftrightarrow\quad
M\text{ 满足消去律}.
$$

进一步，设 $q:M\twoheadrightarrow B$ 为交换幺半群满同态，$B$ 只取实际像，记

$$
R=\ker q,\qquad
K_M=\{(a,b):\exists c\in M,\ a+c=b+c\}.
$$

保留旧观察区别须区分下面两个不同要求。

若只把原始载体送入 $G(M)$，要求旧读数能从补群后的原始点恢复，则存在唯一幺半群同态

$$
\bar q:\eta_M[M]\to B,\qquad
\bar q(\eta_M(a))=q(a)
$$

的充要条件是

$$
K_M\subseteq R,
$$

也就是

$$
a+c=b+c\quad\Longrightarrow\quad q(a)=q(b).
$$

这里恢复映射的定义域是实际像 $\eta_M[M]$，不是整个群 $G(M)$。

若同时对观察幺半群补逆元，则存在规范群同态 $G(q):G(M)\to G(B)$，满足

$$
G(q)\circ\eta_M=\eta_B\circ q.
$$

记 $q^{\mathrm g}=\eta_B\circ q$，则

$$
\ker q^{\mathrm g} =
\{(a,b):\exists c\in M,\ q(a+c)=q(b+c)\}.
$$

尤其

$$
R\subseteq\ker q^{\mathrm g},
\qquad
\ker q^{\mathrm g}=R
\quad\Longleftrightarrow\quad
B\text{ 满足消去律}.
$$

所以“补群后不额外丢失既有读数”不要求 $q$ 原本单射；它要求明确比较补群前后的观察核。源载体补群的核 $K_M$、旧观察核 $R$ 和补群观察核 $\ker q^{\mathrm g}$ 不得混为一个关系。

**证明。** 对一般交换幺半群，采用带稳定项的净差对构造：

$$
(a,b)\approx(a',b')
\quad\Longleftrightarrow\quad
\exists c\in M,\ a+b'+c=a'+b+c.
$$

该关系自反且对称。若前一关系由 $c$ 见证，后一关系

$$
(a',b')\approx(a'',b'')
$$

由 $d$ 见证，则

$$
\begin{aligned}
a+b''+(b'+c+d)
&=(a+b'+c)+b''+d\\
&=(a'+b+c)+b''+d\\
&=b+c+(a'+b''+d)\\
&=b+c+(a''+b'+d)\\
&=a''+b+(b'+c+d).
\end{aligned}
$$

因此 $b'+c+d$ 见证传递性；这里没有使用 $M$ 的消去律。

令 $G(M)=(M\times M)/{\approx}$。若两组代表等价分别有见证 $c,d$，则它们逐坐标相加后的等价由 $c+d$ 见证，故

$$
[(a,b)]+[(u,v)]=[(a+u,b+v)]
$$

定义良好。交换坐标也保持等价，故可定义

$$
-[(a,b)]=[(b,a)].
$$

单位元为 $[(0,0)]$；由于 $[(a+b,a+b)]=[(0,0)]$，所列负元确为逆元。其余交换群公理由 $M$ 的结合律、交换律和单位元律下降。

定义 $\eta_M(a)=[(a,0)]$。任意交换群 $A$ 及幺半群同态 $f:M\to A$ 都唯一扩张为

$$
\widetilde f:G(M)\to A,\qquad
\widetilde f([(a,b)])=f(a)-f(b).
$$

若两对由稳定项 $c$ 见证等价，将对应等式映入 $A$ 并在群中消去 $f(c)$，便得到右侧相等，故定义良好。它是群同态；每个类均为 $\eta_M(a)-\eta_M(b)$，因而扩张唯一。这确认所构造的群具有 Grothendieck 群的泛性质。

直接把 $(a,0)$、$(b,0)$ 代入等价关系，得到

$$
\eta_M(a)=\eta_M(b)
\quad\Longleftrightarrow\quad
\exists c,\ a+c=b+c.
$$

若 $M$ 消去，则该核为等号，$\eta_M$ 单射。反之，若 $\eta_M$ 单射且 $a+c=b+c$，映入群并消去 $\eta_M(c)$ 后得到 $\eta_M(a)=\eta_M(b)$，从而 $a=b$。

现在讨论旧读数恢复。若 $\bar q$ 存在，$\eta_M(a)=\eta_M(b)$ 必然推出 $q(a)=q(b)$，故 $K_M\subseteq R$。若此包含成立，则在实际像上定义

$$
\bar q(\eta_M(a))=q(a)
$$

与代表元无关。它保持加法和单位元，因为 $q$ 与 $\eta_M$ 都是幺半群同态；实际像的定义保证唯一性。这只得到实际像上的恢复，不擅自声称它能以相同目标 $B$ 延伸到全部新增逆元。

将泛性质用于幺半群同态 $\eta_B\circ q$，得到唯一 $G(q)$ 及所列交换等式。由已证核公式在 $B$ 上的应用，

$$
\eta_B(q(a))=\eta_B(q(b))
\quad\Longleftrightarrow\quad
\exists d\in B,\ q(a)+d=q(b)+d.
$$

由于 $q$ 满射，每个 $d$ 可写成 $q(c)$；再使用同态性，即得

$$
\ker q^{\mathrm g} =
\{(a,b):\exists c\in M,\ q(a+c)=q(b+c)\}.
$$

取 $c=0$ 给出 $R\subseteq\ker q^{\mathrm g}$。

若 $B$ 消去，所列等式立即推出 $q(a)=q(b)$，故两个观察核相等。反之，设两个观察核相等。任取 $u,v,d\in B$，满足 $u+d=v+d$。由满射性取 $a,b\in M$，使 $q(a)=u$、$q(b)=v$。在 $G(B)$ 中消去 $\eta_B(d)$，得到 $q^{\mathrm g}(a)=q^{\mathrm g}(b)$；核相等于是给出 $u=q(a)=q(b)=v$。因此 $B$ 消去。

上述两种保真要求确实不同。取定理 11.3 的三类观察 $\tau:\mathbb N\twoheadrightarrow B$，并使用其下降加法。因为 $\mathbb N$ 消去，$\eta_{\mathbb N}$ 单射，三个旧读数均能在 $\eta_{\mathbb N}[\mathbb N]$ 上恢复；然而

$$
\tau(0)\ne\tau(2),\qquad
\tau(0)+\tau(1)=\tau(2)+\tau(1).
$$

所以 $\eta_B$ 必须合并零类和正偶类。奇偶观察又经 $B$ 下降到加法群 $\mathbb Z/2\mathbb Z$，其群扩张阻止奇类与偶类合并。因此补群后的旧读数恰回到两类。源载体补群没有造成这一损失；损失来自另一步对非消去观察幺半群的补群。证毕。

[^rro11_volume]: [RECURSIVE_RELATIONAL_OBSERVATION.md](https://raw.githubusercontent.com/the-omega-institute/trureturing/1f193e8045b4091637dd5483f218cfc4fbfb352a/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md)。引用范围为定义 2.1 的实际像、定义 2.4 的严格响应及命题 2.6 的上下文参数条件。

[^rro11_history]: 固定提交 `2a79bd8d9dc9c393b30fc0a6455513008ecbcb4c`：[HistoryCarrier.lean](https://raw.githubusercontent.com/the-omega-institute/trureturing/2a79bd8d9dc9c393b30fc0a6455513008ecbcb4c/D5/S0/History/HistoryCarrier.lean) 定义自由标记历史、自由事件历史与追加；[EventHistoryInduction.lean](https://raw.githubusercontent.com/the-omega-institute/trureturing/2a79bd8d9dc9c393b30fc0a6455513008ecbcb4c/D5/S0/History/Generation/EventHistoryInduction.lean) 的 `event_history_induction` 针对任意追加事件给出归纳原则。它不直接断言整个多事件历史载体由单个固定后继生成。

[^rro11_monogenic]: James East and Nik Ruškuc, *Classification of congruences of twisted partition monoids*, [arXiv:2010.04392v3，第 2.1 节](https://arxiv.org/html/2010.04392v3#S2.SS1)。该节正文明确采用 $\mathbb N=\{0,1,2,\ldots\}$，并给出每个非平凡加法幺半群同余的完整关系公式及唯一参数 $m\ge0$、$d\ge1$；它们分别对应定理 11.2 的阈值 $t$ 与周期 $p$。此处直接引用该节的分类陈述。

[^rro11_periodicity]: 固定提交 `2a79bd8d9dc9c393b30fc0a6455513008ecbcb4c`：[FiniteInputGeneratorPeriodicity.lean](https://raw.githubusercontent.com/the-omega-institute/trureturing/2a79bd8d9dc9c393b30fc0a6455513008ecbcb4c/D5/S3/ObserverMemory/Prediction/FiniteInputGeneratorPeriodicity.lean)。`finite_input_generator_eventually_periodic` 的适用范围是有限状态与有限确定输入生成器构成的自治乘积轨道；它给出最终周期，不单独给出定理 11.2 的最小参数与全部核形。

[^rro11_contexts]: 固定提交 `2a79bd8d9dc9c393b30fc0a6455513008ecbcb4c`：[StrictOneHoleContexts.lean](https://raw.githubusercontent.com/the-omega-institute/trureturing/2a79bd8d9dc9c393b30fc0a6455513008ecbcb4c/D5/S3/ConceptDynamics/Observation/StrictOneHoleContexts.lean)。相关声明为 `contextual_equivalence_is_greatest` 与 `signature_extension_refines`；其上下文保留任意实际非孔参数，严格记录失败。“扩签名只能细化上下文同余”的一般框架是标准复用。

[^rro11_grothendieck]: mathlib 固定提交 `db584cd6d46c92f209a44c0f1c829460d327499d`：[GrothendieckGroup.lean](https://raw.githubusercontent.com/leanprover-community/mathlib4/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/GroupTheory/MonoidLocalization/GrothendieckGroup.lean) 中，`Algebra.GrothendieckGroup` 是在全体元素处作局部化；`Algebra.GrothendieckGroup.of_injective` 在交换幺半群前提外显式要求 `IsCancelMul`，`Algebra.GrothendieckGroup.lift` 给出到任意交换群的同态扩张等价。[MonoidLocalization/Basic.lean](https://raw.githubusercontent.com/leanprover-community/mathlib4/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/GroupTheory/MonoidLocalization/Basic.lean) 的 `Localization.r_iff_exists` 与 `Localization.mk_eq_mk_iff` 在一般交换幺半群上保留属于所局部化子幺半群的稳定乘子；取全体元素组成的子幺半群并按加法记号翻译，即为定理 11.4 的稳定项等价。省去稳定项的 `Localization.mk_eq_mk_iff'` 另要求消去性，不能用于一般非消去情形。

## 追加锚（本行以下为增补区）

## 12. 增补·闭像与原关系闭性的饱和条件

**定义 12.0（饱和化）。** 设 $X,K$ 为拓扑空间，$j:X\to K$ 连续，$A\subseteq X$。定义 $A$ 关于 $j$ 的饱和化为

$$
\operatorname{Sat}_j(A)=j^{-1}(j[A])
=\{x\in X:\exists a\in A,\ j(x)=j(a)\}.
$$

若 $A=\operatorname{Sat}_j(A)$，称 $A$ 关于 $j$ 饱和，即 $A$ 是完整 $j$ 纤维的并。子集均取子空间拓扑；“紧致”指每个开覆盖存在有限子覆盖，不附加 Hausdorff 条件。

对第 7 节的关系记号，给 $X,Y,Z$ 指定拓扑，并假设每个 $q_n^U$ 连续；$Q_n^U$ 仍取有限离散拓扑，$K_U$ 取逆极限的子空间拓扑。于是 $\iota_U$ 连续。所有关系载体均取积拓扑，记

$$
j_{XY}=\iota_X\times\iota_Y:X\times Y\to K_X\times K_Y,
\qquad
j_{YZ}=\iota_Y\times\iota_Z:Y\times Z\to K_Y\times K_Z.
$$

对 $R\subseteq X\times Y$、$S\subseteq Y\times Z$，沿用 $R^0=j_{XY}[R]$、$S^0=j_{YZ}[S]$。“原关系相对闭”分别指在给定的 $X\times Y$、$Y\times Z$ 中闭。

**定理 12.1（第7.3条闭性比较的更正）。** 第 7.3 条证明后的首句“关系像在完成空间中闭，比关系在原载体中相对闭强。”的无条件比较不成立，以如下条件命题替代。一般构件为标准点集拓扑复用；紧致性结论的数学引文附于本条。[^rro12_compact]

1. 对任意连续映射 $j:X\to K$ 及任意 $A\subseteq X$，若 $j[A]$ 在 $K$ 中闭，则 $\operatorname{Sat}_j(A)$ 在 $X$ 中闭。若另有 $A=\operatorname{Sat}_j(A)$，则可据此推出 $A$ 在 $X$ 中闭；$j$ 单射是保证此饱和条件的一个充分条件。因此，$R^0$ 闭保证 $\operatorname{Sat}_{j_{XY}}(R)$ 闭，在 $R=\operatorname{Sat}_{j_{XY}}(R)$ 时推出 $R$ 闭；$S$ 的对应结论使用 $j_{YZ}$。这里要求的是关于整个关系积映射的饱和性，仅有中间映射 $\iota_Y$ 单射并不保证 $R$ 或 $S$ 满足该条件。
2. 对任意连续映射 $j:X\to K$ 及任意紧致子集 $A\subseteq X$，$j[A]$ 紧致；若 $K$ 为 Hausdorff，则 $j[A]$ 闭。源空间 $X$ 紧致且 $A$ 在 $X$ 中闭，足以保证 $A$ 紧致。因此，在连续观察下，紧致关系 $R,S$ 的完成像 $R^0,S^0$ 闭；特别地，$X,Y,Z$ 紧致且 $R,S$ 在原乘积中闭足以保证该闭像条件。
3. 即使原载体紧致 Hausdorff、所有观察连续且中间观察单射，闭关系像仍不必推出原关系相对闭。具体取通常拓扑的 $X=[0,1]$、单点空间 $Y=Z=\{*\}$，对每个 $U\in\{X,Y,Z\}$ 和每个 $n\in\mathbb N$ 令 $Q_n^U=\{*\}$，观察及过渡映射均为唯一的常值映射。取
   $$
   R=(0,1]\times\{*\},\qquad S=\{(*,*)\}.
   $$
   则 $R^0,S^0$ 是闭单点，$\iota_Y$ 单射，而 $R$ 在 $X\times Y$ 中不闭。
4. 反向蕴含也不成立：原关系相对闭、所有观察连续并分离点，仍不保证完成像闭；第 7.4 条证明第三组已经给出此例。因此，在一般连续观察下，两种闭性不能无条件排序。

第 7.3 条的闭像与中间代表条件、其紧致 Hausdorff 充分拓扑假设及证明均保留；上述替代只更正证明之后的无条件闭性比较。

**证明。** 对第一项，连续性使闭集 $j[A]$ 的原像 $j^{-1}(j[A])$ 闭，这正是 $\operatorname{Sat}_j(A)$。若 $A$ 饱和，该原像就是 $A$。总有 $A\subseteq\operatorname{Sat}_j(A)$；若 $j$ 单射，任取 $x\in\operatorname{Sat}_j(A)$，存在 $a\in A$ 使 $j(x)=j(a)$，单射性给出 $x=a\in A$，故反向包含成立。这不需要假设 $j$ 为拓扑嵌入。对关系应用同一论证时，连续映射是 $j_{XY}$ 或 $j_{YZ}$，其纤维同时涉及两个坐标；中间坐标单射本身不排除另一坐标的观察纤维含有不同点。

对第二项，$j|_A:A\to j[A]$ 连续且满射。任取 $j[A]$ 的开覆盖，其原像覆盖 $A$；$A$ 的紧致性给出有限子覆盖，满射性使相应有限个原开集覆盖 $j[A]$，所以 $j[A]$ 紧致。若 $K$ 为 Hausdorff，任取 $z\in K\setminus j[A]$。对每个 $b\in j[A]$，取分别包含 $b,z$ 的不交开邻域 $U_b,V_b$。有限个 $U_{b_1},\ldots,U_{b_m}$ 覆盖 $j[A]$，则 $V_{b_1}\cap\cdots\cap V_{b_m}$ 是 $z$ 的开邻域且与 $j[A]$ 不交。因此 $K\setminus j[A]$ 开，$j[A]$ 闭；$j[A]=\varnothing$ 时结论直接成立。

若 $X$ 紧致且 $A$ 闭，将 $A$ 的任意子空间开覆盖写成 $A\cap U_i$，其中 $U_i$ 在 $X$ 中开；把 $X\setminus A$ 加入这些 $U_i$ 即得 $X$ 的开覆盖。有限子覆盖限制到 $A$，证明 $A$ 紧致。对关系而言，$j_{XY},j_{YZ}$ 连续，且第 7 节的 $K_X\times K_Y$、$K_Y\times K_Z$ 为 Hausdorff，故紧致 $R,S$ 有闭像。有限个紧致空间的乘积紧致，因而 $X,Y,Z$ 紧致且 $R,S$ 在原乘积中闭时，这两个关系均紧致，满足上述条件。[^rro12_product]

对第三项，所有观察层均为单点，故每个 $K_U$ 也是单点；所有观察连续，过渡律成立。$R,S$ 均非空，所以 $R^0,S^0$ 各为整个单点乘积，因而闭。$Y$ 本身为单点，故 $\iota_Y$ 单射。但对每个整数 $k\ge1$，$(1/k,*)\in R$，且在给定积拓扑中

$$
(1/k,*)\longrightarrow(0,*),\qquad (0,*)\notin R.
$$

闭集必包含其内部序列在环境空间中的极限，因此 $R$ 不闭。该例中 $j_{XY}$ 恒值且 $R$ 非空，故

$$
\operatorname{Sat}_{j_{XY}}(R)=X\times Y\ne R.
$$

于是第一项保证的是整个原乘积闭，不能据此推出 $R$ 闭。

对第四项，直接采用第 7.4 条证明第三组的 $Y=\{e_k:k\in\mathbb N\}$ 及其观察拓扑。该拓扑离散，前缀观察连续且分离点，原关系 $R=\{*\}\times B_{\mathrm{ev}}$、$S=B_{\mathrm{odd}}\times\{*\}$ 相对闭；但该组已证全零点 $p$ 属于 $B_{\mathrm{ev}}$、$B_{\mathrm{odd}}$ 在 $K_Y$ 中的闭包，并且 $p\notin Y$。故 $(\ast,p)$、$(p,\ast)$ 分别属于 $R^0,S^0$ 的闭包而不属于这些像，两个完成像均不闭。结合第三项即排除无条件的双向强弱比较。

最后，第 7.3 条的证明从 $R^0,S^0$ 闭得到 $\widehat R=R^0$、$\widehat S=S^0$，再用中间单射性或该条所列的单侧纤维饱和性合并两个中间代表；这一步没有从闭像反推原关系闭。该条的充分拓扑假设则通过本条第二项从原闭关系的紧致性推出闭像，再使用观察分离点。因此上述反例与更正不改变第 7.3 条的充分条件及其证明。证毕。

[^rro12_compact]: The Stacks Project, *Topology*：[引理 5.12.3，Tag 005C](https://stacks.math.columbia.edu/tag/005C)（紧致空间的闭子集紧致）；[引理 5.12.7(1)，Tag 04Z9](https://stacks.math.columbia.edu/tag/04Z9)（紧致空间的连续像紧致）；[引理 5.12.4(1)，Tag 08YB](https://stacks.math.columbia.edu/tag/08YB)（Hausdorff 空间的紧致子集闭）。这些条目中的 quasi-compact 对应定义 12.0 的紧致性。

[^rro12_product]: The Stacks Project, *Topology*，[Tychonov 定理，Tag 08ZU](https://stacks.math.columbia.edu/tag/08ZU)：紧致空间的乘积紧致；此处仅使用有限乘积情形，紧致性按定义 12.0 的开覆盖意义理解。

## 追加锚（本行以下为增补区）
## 13. 增补·幂运算的有限观察相容性

**定义 13.0（观察核、细化与数论记号）。** 本节取 $\mathbb N=\{0,1,2,\ldots\}$，使用自然数上的总幂运算
$$
a^0=1,\qquad a^{b+1}=a^b a,
$$
特别约定 $0^0=1$。对 $t\ge0$、$p\ge1$，沿用阈值—周期核
$$
n\mathrel{R_{t,p}}m
\quad\Longleftrightarrow\quad
n=m\ \lor\
\bigl(n\ge t\ \land\ m\ge t\ \land\ n\equiv m\pmod p\bigr).
$$
称等价关系 $R$ 双槽保幂，若
$$
\forall a,a',b,b'\in\mathbb N,\qquad
a\mathrel R a'\ \land\ b\mathrel R b'
\quad\Longrightarrow\quad
a^b\mathrel R (a')^{b'}.
$$
关系包含 $R'\subseteq R$ 表示 $R'$ 细化 $R$；某类细化中的最粗者，指该类中按关系包含排序的最大元素。

对正整数 $n$，记
$$
\operatorname{Pr}(n)=\{\ell:\ell\text{ 为素数且 }\ell\mid n\}.
$$
对素数 $\ell$，$v_\ell(n)$ 表示 $\ell$ 在 $n$ 的素因子分解中的指数，并定义
$$
h(n)=
\max\bigl(\{0\}\cup
\{v_\ell(n):\ell\in\operatorname{Pr}(n)\}\bigr).
$$
因此 $\operatorname{Pr}(1)=\varnothing$、$h(1)=0$。记 $\ell^e\parallel n$ 表示 $e=v_\ell(n)\ge1$。

有限群 $G$ 的指数定义为
$$
\operatorname{exp}(G)
=\operatorname{lcm}\{\operatorname{ord}(g):g\in G\},
$$
其中 $\operatorname{ord}(g)$ 是 $g$ 的阶。对 $n\ge2$，令
$$
U(n)=(\mathbb Z/n\mathbb Z)^\times,\qquad
\lambda(n)=\operatorname{exp}(U(n)),
$$
并约定 $\lambda(1)=1$。这是 Carmichael 函数的标准群指数定义，参见 Kevin Ford、Florian Luca 与 Carl Pomerance，*The image of Carmichael's $\lambda$-function*，第 1 节，[arXiv:1408.6506v2](https://arxiv.org/html/1408.6506v2)。

**定理 13.1（阈值—周期核双槽保幂的完整分类）。** 对任意 $t\ge0$、$p\ge1$，关系 $R_{t,p}$ 双槽保幂，当且仅当
$$
(t,p)=(0,1)
\quad\text{或}\quad
\bigl(t\ge\max\{1,h(p)\}\ \land\ \lambda(p)\mid p\bigr).
$$
等价地，除单点商 $R_{0,1}$ 外，充要条件为
$$
t\ge1,\qquad
\forall\,\ell^e\parallel p,\quad
e\le t\ \land\ \ell-1\mid p.
$$
特别地，$p=1$ 时所有 $t\ge0$ 都允许；$p>1$ 时，阈值条件和周期条件缺一不可。

这里 $\lambda(p)\mid p$ 等价于“每个素因子 $\ell\mid p$ 都满足 $\ell-1\mid p$”，是 Novák–Carmichael 数的标准判据，参见 Alexander Kalmynin，*Novák-Carmichael numbers and shifted primes without large prime factors*，第 2 节引理 1，[arXiv:1706.07343v1](https://arxiv.org/html/1706.07343v1)。下面证明本条所需的等价及其与观察核条件的联系。

**证明。** 先说明有限群指数的基本性质。若 $g$ 的阶为 $r$，则对正整数 $d$ 作带余除法，得到
$$
g^d=1_G\quad\Longleftrightarrow\quad r\mid d.
$$
对群中所有元素取最小公倍数，因而
$$
\forall g\in G,\ g^d=1_G
\quad\Longleftrightarrow\quad
\operatorname{exp}(G)\mid d.
$$
因此，对 $p\ge2$，
$$
\lambda(p)\mid p
\quad\Longleftrightarrow\quad
\forall a\in\mathbb N,\ 
\gcd(a,p)=1\Longrightarrow a^p\equiv1\pmod p.
$$

由定理 11.2，$R_{t,p}$ 已对乘法的两个槽位相容。固定指数 $b$，对 $b$ 归纳便得
$$
a\mathrel{R_{t,p}}a'
\quad\Longrightarrow\quad
a^b\mathrel{R_{t,p}}(a')^b.
$$
归纳起点是两边都等于 $1$，所以也涵盖零底数与零指数。故新增要求恰在指数槽。

更精确地，双槽保幂等价于
$$
\forall a\in\mathbb N,\qquad
a^t\mathrel{R_{t,p}}a^{t+p}.
$$
必要性来自 $t\mathrel{R_{t,p}}t+p$。反之，假设上述关系成立。对任意 $n\ge t$，利用乘法相容性得到
$$
a^{n+p}
=a^{n-t}a^{t+p}
\mathrel{R_{t,p}}
a^{n-t}a^t
=a^n.
$$
若 $b\mathrel{R_{t,p}}b'$ 且 $b\ne b'$，交换二者后可写成
$$
b\ge t,\qquad b'=b+kp,\qquad k\ge1.
$$
反复应用上述关系即得 $a^b\mathrel{R_{t,p}}a^{b'}$。结合底数槽的相容性，
$$
a^b\mathrel{R_{t,p}}(a')^b
\mathrel{R_{t,p}}(a')^{b'},
$$
便得到双槽保幂。

先处理 $t=0$。因 $0\mathrel{R_{0,p}}p$，取底数 $a=0$，保幂必要求
$$
1=0^0\mathrel{R_{0,p}}0^p=0.
$$
而 $R_{0,p}$ 就是模 $p$ 同余，所以 $p\mid1$，即 $p=1$。反之，$R_{0,1}$ 是全关系，当然保幂。

以下设 $t\ge1$。底数 $a=0$ 时，
$$
0^t=0^{t+p}=0;
$$
底数 $a=1$ 时，两边都等于 $1$。当 $a\ge2$ 时，自然数归纳给出
$$
a^t\ge2^t\ge t,\qquad a^{t+p}\ge a^t.
$$
两项均在周期尾部。因此，前述指数槽条件恰等价于
$$
\forall a\in\mathbb N,\qquad
a^{t+p}\equiv a^t\pmod p.
$$

假设这个同余恒等式成立。对每个 $\ell^e\parallel p$，取底数 $a=\ell$，得到
$$
\ell^e\mid \ell^{t+p}-\ell^t
=\ell^t(\ell^p-1).
$$
由于 $\ell\nmid\ell^p-1$，右侧的 $\ell$-进赋值恰为 $t$，故 $e\le t$。于是
$$
h(p)\le t.
$$
另一方面，若 $\gcd(a,p)=1$，则可在模 $p$ 的单位群中消去 $a^t$，得到
$$
a^p\equiv1\pmod p.
$$
群指数的基本性质于是给出 $\lambda(p)\mid p$。当 $p=1$ 时，这个整除关系按约定也成立。必要性得证。

现在证明所需的周期判据
$$
\lambda(p)\mid p
\quad\Longleftrightarrow\quad
\forall\ell\in\operatorname{Pr}(p),\ \ell-1\mid p.
$$
$p=1$ 时两边都成立，以下设 $p>1$。

先设 $\lambda(p)\mid p$，固定 $\ell^e\parallel p$，写
$$
p=\ell^e m,\qquad \gcd(\ell,m)=1.
$$
每个模 $\ell$ 的非零剩余类 $x$ 都可提升为模 $p$ 的单位：取不被 $\ell$ 整除的整数代表 $u$，再由中国剩余定理选择
$$
a\equiv u\pmod{\ell^e},\qquad
a\equiv1\pmod m.
$$
于是 $\gcd(a,p)=1$，从而 $x^p=1$ 于域 $\mathbb F_\ell$ 中。

令 $d=\operatorname{exp}(\mathbb F_\ell^\times)$。有限群的陪集分割表明每个元素的阶整除群阶，故 $d\mid\ell-1$。另一方面，$\mathbb F_\ell$ 上的非零多项式 $X^d-1$ 在全部 $\ell-1$ 个非零元素处消失；域上次数为 $d$ 的非零多项式至多有 $d$ 个根，故 $d\ge\ell-1$。因此
$$
d=\ell-1.
$$
既然每个非零元素的 $p$ 次幂都是 $1$，群指数的基本性质给出 $d\mid p$，即 $\ell-1\mid p$。这个论证也包括 $\ell=2$。

反之，设每个素因子 $\ell\mid p$ 都满足 $\ell-1\mid p$。对 $\ell^e\parallel p$，有
$$
\ell^{e-1}\mid p,\qquad
\ell-1\mid p,\qquad
\gcd(\ell^{e-1},\ell-1)=1,
$$
所以
$$
\ell^{e-1}(\ell-1)\mid p.
$$
模 $\ell^e$ 的单位群恰有
$$
\ell^e-\ell^{e-1}=\ell^{e-1}(\ell-1)
$$
个元素。因此，对任何满足 $\ell\nmid a$ 的底数，有限群的阶整除性质给出
$$
a^p\equiv1\pmod{\ell^e}.
$$
特别地，若 $\gcd(a,p)=1$，上式对 $p$ 的每个素数幂因子都成立；这些因子两两互素，故
$$
a^p\equiv1\pmod p.
$$
于是 $\lambda(p)\mid p$，周期判据得证。此证明不要求模合数的单位群为循环群，也未把非单位底数当作单位处理。

最后证明充分性。设
$$
t\ge\max\{1,h(p)\},\qquad \lambda(p)\mid p.
$$
由已证周期判据，对每个 $\ell^e\parallel p$ 都有 $\ell-1\mid p$。固定任意底数 $a\in\mathbb N$。

若 $\ell\mid a$，则 $t\ge e$，所以
$$
a^t\equiv a^{t+p}\equiv0\pmod{\ell^e}.
$$
若 $\ell\nmid a$，则上一段已经证明 $a^p\equiv1\pmod{\ell^e}$，故
$$
a^{t+p}=a^t a^p\equiv a^t\pmod{\ell^e}.
$$
这两个分支逐个处理了每个素数幂因子，因而也涵盖“对某些因子是单位、对另一些因子不是单位”的底数。由素数幂因子的两两互素性，
$$
a^{t+p}\equiv a^t\pmod p.
$$
$p=1$ 时该同余无条件成立。结合已经证明的阈值判断与指数槽化约，得到双槽保幂。两种参数表述的等价性也随之成立。证毕。

**定理 13.2（阈值—周期核的有限保幂修复与唯一最粗细化）。** 固定任意 $t\ge0$、$p\ge1$。定义有限素数集序列
$$
S_0=\operatorname{Pr}(p),
$$
$$
S_{j+1}
=S_j\cup
\bigcup_{\ell\in S_j}\operatorname{Pr}(\ell-1),
\qquad 0\le j<p,
$$
并定义
$$
P(p)=
\operatorname{lcm}
\bigl(\{p\}\cup\{\ell-1:\ell\in S_p\}\bigr).
$$
令
$$
T(t,p)=
\begin{cases}
0,&(t,p)=(0,1),\\
\max\{t,1,h(P(p))\},&(t,p)\ne(0,1).
\end{cases}
$$
则
$$
R_*:=R_{T(t,p),P(p)}
$$
双槽保幂，且
$$
R_*\subseteq R_{t,p}.
$$
该观察商有限，恰有 $T(t,p)+P(p)$ 个类。构造只需上述明确给出的 $p$ 步有限集合运算，并有显式整除界
$$
P(p)\mid \operatorname{lcm}(1,2,\ldots,p).
$$

全部有限保幂细化 $R_{u,v}$ 恰由以下参数给出：$u\ge t$、$p\mid v$，且 $(u,v)$ 满足定理 13.1 的充要条件。它们具有唯一最粗者 $R_*$；亦即，对所有 $u\ge0$、$v\ge1$，
$$
R_{u,v}\subseteq R_{t,p}
\ \land\
R_{u,v}\text{ 双槽保幂}
\quad\Longrightarrow\quad
R_{u,v}\subseteq R_*.
$$
更一般地，$R_*$ 也是包含于 $R_{t,p}$、同时对 $\{+,\times,\operatorname{pow}\}$ 相容的所有等价关系中的最大者，不必预先要求这些等价关系具有有限商。

**证明。** 先记录阈值—周期核的包含次序：
$$
R_{u,v}\subseteq R_{t,p}
\quad\Longleftrightarrow\quad
u\ge t\ \land\ p\mid v.
$$
这也是 James East 与 Nik Ruškuc，*Classification of congruences of twisted partition monoids*，第 2.1 节式 (2.2) 的标准包含判据，参见 [arXiv:2010.04392v3](https://arxiv.org/html/2010.04392v3#S2.SS1)。

为明确此处的方向，若左侧成立，则
$$
u\mathrel{R_{u,v}}u+v
$$
是一对不同元素，因而 $u\mathrel{R_{t,p}}u+v$ 强制 $u\ge t$ 及 $p\mid v$。反之，若这两个参数条件成立，则任何不同的 $R_{u,v}$-相关元素均不小于 $u\ge t$，且其差为 $v$ 的倍数，从而也是 $p$ 的倍数，所以属于 $R_{t,p}$。

下面证明素数集构造在给定步数内已封闭。归纳可知，每个 $S_j$ 都只含不超过 $p$ 的素数：初始素数整除 $p$；若新素数 $r$ 整除某个 $\ell-1$，则
$$
r\le\ell-1<\ell\le p.
$$
同时 $S_j\subseteq S_{j+1}$。不超过 $p$ 的素数至多有 $p-1$ 个，因此前 $p$ 步不可能每一步都严格增加。一旦某一步满足 $S_{j+1}=S_j$，该集合已经对所定义的增补操作封闭，之后各步都保持不变。故 $S_p$ 满足
$$
\ell\in S_p
\quad\Longrightarrow\quad
\operatorname{Pr}(\ell-1)\subseteq S_p.
$$
$p=1$ 时，各集合均为空，结论同样成立。

简记 $P=P(p)$。显然 $p\mid P$。若素数 $r\mid P$，则由最小公倍数的素因子分解，$r$ 必整除 $p$，或整除某个 $\ell-1$，其中 $\ell\in S_p$。前一情形给出 $r\in S_0\subseteq S_p$；后一情形由封闭性给出 $r\in S_p$。因此
$$
\operatorname{Pr}(P)\subseteq S_p.
$$
对每个 $r\in\operatorname{Pr}(P)$，数 $r-1$ 正是定义 $P$ 时列入最小公倍数的一项，所以
$$
r-1\mid P.
$$
由定理 13.1 中已经证明的周期判据，
$$
\lambda(P)\mid P.
$$

令
$$
L_p=\operatorname{lcm}(1,2,\ldots,p).
$$
定义 $P$ 时使用的数 $p$ 整除 $L_p$；每个 $\ell\in S_p$ 都满足 $2\le\ell\le p$，故正整数 $\ell-1$ 也整除 $L_p$。于是
$$
P\mid L_p,
$$
得到所述显式整除界。

若 $(t,p)=(0,1)$，则 $P=1$、$T(t,p)=0$，故 $R_*=R_{0,1}$，所需性质直接成立。否则，按定义
$$
T(t,p)\ge t,\qquad
T(t,p)\ge\max\{1,h(P)\}.
$$
结合 $\lambda(P)\mid P$，定理 13.1 给出 $R_*$ 双槽保幂；再由 $p\mid P$ 及包含判据，得到
$$
R_*\subseteq R_{t,p}.
$$
阈值以下共有 $T(t,p)$ 个单元素类，尾部共有 $P$ 个剩余类，所以商的类数恰为 $T(t,p)+P$。至此已对所有 $t,p$ 给出有限修复，而非仅给出条件性的最粗性结论。

进一步证明 $P$ 的精确最小性。设正整数 $v$ 满足
$$
p\mid v,\qquad \lambda(v)\mid v.
$$
由周期判据，每个素因子 $\ell\mid v$ 都满足 $\ell-1\mid v$。归纳证明
$$
S_j\subseteq\operatorname{Pr}(v)
\qquad(0\le j\le p).
$$
起点来自 $p\mid v$。若结论对 $S_j$ 成立，则对每个 $\ell\in S_j$ 都有 $\ell\mid v$，进而 $\ell-1\mid v$；所以 $\ell-1$ 的所有素因子仍整除 $v$，得到下一步的包含。

因此，每个 $\ell\in S_p$ 都整除 $v$，从而 $\ell-1\mid v$。连同 $p\mid v$，得到
$$
P(p)\mid v.
$$
故 $P(p)$ 是满足 $p\mid v$ 且 $\lambda(v)\mid v$ 的正整数中，按整除排序的最小元素。这一最小性比较的是全部正整数 $v$，不限于某个预先截断的搜索范围。

现在设 $R_{u,v}\subseteq R_{t,p}$ 且 $R_{u,v}$ 双槽保幂。包含判据给出
$$
u\ge t,\qquad p\mid v.
$$
若旧核是 $R_{0,1}$，则任何关系都包含于 $R_*=R_{0,1}$，最粗性显然成立。

以下设 $(t,p)\ne(0,1)$。此时 $R_{u,v}$ 不可能是全关系，因为全关系不能包含于这个非全关系旧核。故定理 13.1 给出
$$
u\ge\max\{1,h(v)\},\qquad \lambda(v)\mid v.
$$
由 $P$ 的最小性，$P\mid v$，从而逐素数比较赋值可得
$$
h(P)\le h(v).
$$
因此
$$
u\ge\max\{t,1,h(P)\}=T(t,p).
$$
再用一次包含判据，
$$
R_{u,v}\subseteq R_{T(t,p),P}=R_*.
$$
由于 $R_*$ 本身已是合格细化，它就是最大元素，而不仅是极大元素；最大元素的唯一性立即成立。包含判据与定理 13.1 的合取，也给出了定理所述全部有限细化的参数刻画。

最后，设 $E\subseteq R_{t,p}$ 是任意对 $\{+,\times,\operatorname{pow}\}$ 相容的等价关系。若 $E$ 为等号关系，则显然 $E\subseteq R_*$。若不是等号关系，由定理 11.2 的自然数加法同余分类，存在有限参数 $u\ge0$、$v\ge1$，使
$$
E=R_{u,v}.
$$
于是刚才证明的最粗性适用，仍得 $E\subseteq R_*$。另一方面，$R_*$ 对加法、乘法的相容性来自定理 11.2，对幂的相容性已经证明。因此它确为该签名下所有保留旧区别的同余中的最大者。证毕。

## 追加锚（本行以下为增补区）
## 14. 增补·保幂共尾观察与逆向运算的连续性边界

**定义 14.0（观察指标、相容完成与保幂子族）。** 取 $\mathbb{N}=\{0,1,2,\ldots\}$，自然数幂满足 $a^0=1$，特别地 $0^0=1$。令
$$
I=\mathbb{N}\times\mathbb{N}_{>0},
\qquad
(t,p)\preceq(u,v)\quad\Longleftrightarrow\quad t\le u\quad \land\quad p\mid v.
$$
指标越大表示观察越细。对 $\alpha=(t,p)$，定义
$$
n\mathrel{R_\alpha}m
\quad\Longleftrightarrow\quad
n=m\quad \lor\quad \bigl(n,m\ge t\quad \land\quad n\equiv m\pmod p\bigr),
\qquad
Q_\alpha=\mathbb{N}/R_\alpha,
$$
并记商映射为 $q_\alpha$。每个 $Q_\alpha$ 取有限离散拓扑。若 $\alpha\preceq\beta$，记规范映射为
$$
b_{\beta\alpha}:Q_\beta\longrightarrow Q_\alpha,
\qquad
b_{\beta\alpha}(q_\beta(n))=q_\alpha(n).
$$
自然数加法幺半群的非等号同余具有上述阈值—周期形式；其包含次序见 [East–Ruškuc，*Classification of congruences of twisted partition monoids*，arXiv:2010.04392v3，第 2.1 节及式 (2.2)](https://arxiv.org/html/2010.04392v3)。这里引用的范围是加法同余的分类与包含次序。

令 $J\subseteq I$ 为双槽保幂指标集，即
$$
\alpha\in J
\quad\Longleftrightarrow\quad
\forall a,a',b,b'\in\mathbb{N},\quad
\bigl(a\mathrel{R_\alpha}a'\quad \land\quad b\mathrel{R_\alpha}b'\bigr)
\Longrightarrow a^b\mathrel{R_\alpha}(a')^{b'}.
$$
对所考虑的指标子集 $D$，定义
$$
K_D=
\left\{(x_\alpha)_{\alpha\in D}\in\prod_{\alpha\in D}Q_\alpha:
\forall\alpha,\beta\in D,\quad
\alpha\preceq\beta\Longrightarrow b_{\beta\alpha}(x_\beta)=x_\alpha
\right\},
\qquad
\iota_D(n)=(q_\alpha(n))_{\alpha\in D},
$$
赋予 $K_D$ 乘积拓扑的子空间拓扑，坐标投影记为 $\pi_\alpha$。保序映射 $f:D\to E$ 称为共尾映射，若对每个 $e\in E$，存在 $d\in D$ 使 $e\preceq f(d)$。

**假设 14.0a（第 13 节的算术前置）。** 采用第 13.1 条的如下双槽保幂判据：
$$
J=\{(0,1)\}\quad \cup\quad
\left\{(t,p):t\ge1,\quad
\forall\,\ell^e\parallel p,\quad
e\le t\quad \land\quad \ell-1\mid p
\right\}.
$$
其中 $\ell$ 遍历素数。沿用 $\operatorname{Pr}(p)$ 表示 $p$ 的素因子集，并令
$$
h(p)=\max\bigl(\{0\}\cup\{v_\ell(p):\ell\in\operatorname{Pr}(p)\}\bigr).
$$
对每个 $p\ge1$，使用第 13.2 条的有限构造
$$
S_0=\operatorname{Pr}(p),
\qquad
S_{j+1}=S_j\cup\bigcup_{\ell\in S_j}\operatorname{Pr}(\ell-1)
\quad(0\le j<p),
$$
$$
P(p)=\operatorname{lcm}\bigl(\{p\}\cup\{\ell-1:\ell\in S_p\}\bigr),
\qquad
T(t,p)=
\begin{cases}
0,&(t,p)=(0,1),\\
\max\{t,1,h(P(p))\},&(t,p)\ne(0,1),
\end{cases}
$$
并定义 $\kappa(t,p)=(T(t,p),P(p))$。上述分类是本节明确采用的数学前置；下条证明给出所需的保幂充分性及该有限构造的最小性论证。参见[《递归关系观察》第 13.1—13.2 条](https://raw.githubusercontent.com/the-omega-institute/trureturing/d75daccad7efe749379873a4b5f8dbba95a862f9/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md)。素因子条件 $\ell-1\mid p$ 与所有模 $p$ 单位的 $p$ 次幂均为 $1$ 的等价，是 [Kalmynin，*Novák-Carmichael numbers and shifted primes without large prime factors*，arXiv:1706.07343v1，第 2 节引理 1](https://arxiv.org/html/1706.07343v1) 的判据；该引文只支持周期条件，不包含阈值条件或以下连续性结论。

**定理 14.1（保幂共尾性、完成比较与加乘幂的联合连续延拓）。** 在上述定义与算术前置下，有
$$
\alpha\preceq\beta\quad\Longleftrightarrow\quad R_\beta\subseteq R_\alpha.
$$
若 $\alpha=(t,p)$、$\beta=(u,v)$，则
$$
\alpha\vee\beta=(\max\{t,u\},\operatorname{lcm}(p,v)),
\qquad
R_{\alpha\vee\beta}=R_\alpha\cap R_\beta.
$$
映射 $\kappa:I\to J$ 满足
$$
\alpha\preceq\kappa(\alpha),
\qquad
\kappa(\alpha)\preceq\gamma
\quad\Longleftrightarrow\quad
\alpha\preceq\gamma
\quad(\gamma\in J).
$$
因此 $\kappa$ 保序、在 $J$ 上为恒等映射且幂等；$J\hookrightarrow I$ 与 $\kappa:I\to J$ 都是共尾映射。任意两个指标的最小保幂共同细化是 $\kappa(\alpha\vee\beta)$。若两个指标本来都属于 $J$，则 $\alpha\vee\beta\in J$。

一个同时共尾于 $I$ 与 $J$ 的显式可数塔为
$$
L_k=\operatorname{lcm}(1,2,\ldots,k),
\qquad
c_k=(k,L_k),
\qquad k\ge1.
$$
具体地，$c_k\in J$、$c_k\preceq c_{k+1}$，且
$$
k\ge\max\{1,t,p\}\quad\Longrightarrow\quad (t,p)\preceq c_k.
$$

两个完成 $K_I$、$K_J$ 都是紧致 Hausdorff 空间，具有开闭柱集基，且相应的 $\iota_D$ 为稠密单射。由原 $\mathbb{N}$ 上恒等映射诱导的坐标限制
$$
\Phi:K_I\longrightarrow K_J,
\qquad
\Phi((x_\alpha)_{\alpha\in I})=(x_\gamma)_{\gamma\in J}
$$
是同胚，满足 $\Phi\circ\iota_I=\iota_J$；其逆映射显式为
$$
\bigl(\Psi(y)\bigr)_\alpha
=b_{\kappa(\alpha),\alpha}\bigl(y_{\kappa(\alpha)}\bigr).
$$
二者也都通过坐标限制同胚于 $\varprojlim_k Q_{c_k}$。

在这个共同完成上，自然数加法、乘法与双槽自然数幂分别具有唯一的联合连续延拓。对于指定输出指标 $\alpha$，加法与乘法可以在两个输入槽都使用精度 $\alpha$；幂可以在两个输入槽都使用精度 $\kappa(\alpha)$。这是允许输入比输出更细的因子化结论，并不要求每个 $Q_\alpha$ 本身都具有同层幂运算。

**证明。** 若 $R_{u,v}\subseteq R_{t,p}$，则不同元素 $u,u+v$ 在 $R_{t,p}$ 下相关，强制 $u\ge t$ 且 $p\mid v$。反之，这两个参数条件使每对不同的 $R_{u,v}$ 相关元素也在 $R_{t,p}$ 下相关。包含判据得证。两个关系的交同时要求达到两个阈值且差被两个周期整除，故得到所述上确界公式。

每个 $R_{t,p}$ 都在同时平移两个元素后保持成立，所以它是加法同余。由重复加法，固定自然数倍乘保持该同余；依次改变两个因子，得到乘法的双槽相容性。因此固定指数时，幂的底数槽也由归纳保持该同余。这正是[《递归关系观察》第 11.2 条](https://raw.githubusercontent.com/the-omega-institute/trureturing/d75daccad7efe749379873a4b5f8dbba95a862f9/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md) 的运算下降论证。

先证明共尾构造实际使用的保幂充分性。设 $t\ge1$，且每个 $\ell^e\parallel p$ 都满足 $e\le t$ 与 $\ell-1\mid p$。若 $\ell\mid a$，则 $a^t$ 与 $a^{t+p}$ 都被 $\ell^e$ 整除。若 $\ell\nmid a$，则
$$
\ell^{e-1}(\ell-1)\mid p,
$$
因为两个因子互素且分别整除 $p$；模 $\ell^e$ 的单位群有 $\ell^{e-1}(\ell-1)$ 个元素，故 $a^p\equiv1\pmod{\ell^e}$。逐个素数幂合并得到
$$
a^{t+p}\equiv a^t\pmod p.
$$
$p=1$ 时该同余无条件成立。底数 $a=0,1$ 时两幂相等；$a\ge2$ 时，两幂均不小于 $2^t\ge t$。因此总有 $a^{t+p}\mathrel{R_{t,p}}a^t$。乘以 $a^{b-t}$ 并反复使用乘法同余，可得所有 $b\ge t$ 的 $p$ 步指数平移保持观察。结合底数槽的相容性，得到双槽保幂。全关系 $R_{0,1}$ 则直接满足保幂。

现证明 $\kappa$ 的最小性。构造 $S_j$ 时，每个新加入的素数都严格小于产生它的素数，且所有素数均不超过 $p$。集合序列单调增加，而这样的素数至多有 $p-1$ 个；故前 $p$ 步内必有一次不再增加，此后保持不变。因此 $S_p$ 对所定义的增补操作封闭。由此
$$
p\mid P(p),
\qquad
\operatorname{Pr}(P(p))\subseteq S_p,
\qquad
r\in\operatorname{Pr}(P(p))\Longrightarrow r-1\mid P(p).
$$
于是，除 $(0,1)$ 的单独分支外，刚才证明的充分性适用于 $(T(t,p),P(p))$，故 $\kappa(\alpha)\in J$ 且 $\alpha\preceq\kappa(\alpha)$。

设 $\gamma=(u,v)\in J$ 且 $\alpha=(t,p)\preceq\gamma$。若 $\alpha=(0,1)$，则 $\kappa(\alpha)=\alpha\preceq\gamma$。否则 $\gamma\ne(0,1)$，算术前置给出
$$
u\ge\max\{1,h(v)\},
\qquad
\ell\mid v\Longrightarrow\ell-1\mid v
\quad(\ell\text{ 为素数}).
$$
由 $p\mid v$ 起步，对 $j$ 归纳得到 $S_j\subseteq\operatorname{Pr}(v)$：若 $\ell\in S_j$，则 $\ell-1\mid v$，所以它的每个素因子仍整除 $v$。故 $P(p)\mid v$，继而 $h(P(p))\le h(v)$，于是
$$
T(t,p)\le u,
\qquad
P(p)\mid v.
$$
即 $\kappa(\alpha)\preceq\gamma$。反方向由 $\alpha\preceq\kappa(\alpha)$ 立即得到，因而所述最小性等价式成立。

若 $\alpha\preceq\beta$，则 $\kappa(\beta)$ 是 $\alpha$ 的一个保幂细化，最小性给出 $\kappa(\alpha)\preceq\kappa(\beta)$。若 $\gamma\in J$，最小性与膨胀性给出 $\kappa(\gamma)=\gamma$，从而幂等性以及两个映射的共尾性成立。保幂同余的交仍保幂，因此 $J$ 对上述有限上确界封闭；其余共同细化结论也由最小性得到。

对显式塔，若 $\ell^e\parallel L_k$，则 $\ell^e\le k$，故 $e\le k$；并且 $\ell\le k$，所以 $\ell-1\mid L_k$。保幂充分性给出 $c_k\in J$。显然 $L_k\mid L_{k+1}$。又当 $k\ge p$ 时 $p\mid L_k$，故 $k\ge\max\{1,t,p\}$ 足以保证 $(t,p)\preceq c_k$。这一共尾塔的成立只需刚才证明的保幂充分性。

有限离散空间的乘积紧致 Hausdorff，相容方程定义闭子集，因此 $K_I$、$K_J$ 紧致 Hausdorff；有限坐标柱集给出开闭基。这也是 profinite 空间的标准逆极限构造，见 [Stacks Project，定义 5.22.1 与引理 5.22.2](https://stacks.math.columbia.edu/tag/08ZW)；在有限幺半群范畴中的相应构造见 [Kyriakoglou–Perrin，*Profinite semigroups*，arXiv:1703.10088v1，第 5.1—5.2 节](https://arxiv.org/html/1703.10088v1)。这里所用范围是有限离散逆极限及其拓扑性质。

给定一个非空基本柱邻域，选择其中全部指标的共同细化 $\delta$；对于 $K_J$，可取保幂共同细化。邻域中某点的 $\delta$ 坐标有自然数代表 $n$，而相容性保证 $\iota_D(n)$ 位于该邻域，故自然数像稠密。任意两个不同自然数，可用阈值大于二者的指标区分；再取其保幂细化，同样在 $J$ 中区分。因此两个自然数映射都单射。

$\Phi$ 显然连续。由于 $\kappa$ 保序，所给 $\Psi(y)$ 满足全部相容方程，且每个输出坐标只依赖 $y$ 的一个有限坐标，故 $\Psi$ 连续。对 $\gamma\in J$，$\kappa(\gamma)=\gamma$，所以 $\Phi\Psi(y)=y$；对 $x\in K_I$，相容性给出
$$
b_{\kappa(\alpha),\alpha}(x_{\kappa(\alpha)})=x_\alpha,
$$
故 $\Psi\Phi(x)=x$。它们在自然数上的作用确为恒等比较。对于可数塔，令 $k(\alpha)=\max\{1,t,p\}$；由塔线程 $z=(z_k)$ 恢复任意坐标的公式为
$$
x_\alpha=b_{c_{k(\alpha)},\alpha}(z_{k(\alpha)}).
$$
选取更高塔层不改变该值；共同更高层保证所有坐标相容。该公式与坐标限制互逆且连续，证明两种完成都同胚于所述塔极限。

最后构造运算。每个 $Q_\alpha$ 上已有加法 $+_\alpha$ 与乘法 $\cdot_\alpha$，其过渡映射保持这两种运算。故定义
$$
\pi_\alpha(x+y)=\pi_\alpha(x)+_\alpha\pi_\alpha(y),
\qquad
\pi_\alpha(xy)=\pi_\alpha(x)\cdot_\alpha\pi_\alpha(y).
$$
若 $\gamma\in J$，记其良定义的有限幂运算为 $E_\gamma$。对任意 $\alpha\in I$，定义
$$
\pi_\alpha(E(x,y))=
b_{\kappa(\alpha),\alpha}
\left(E_{\kappa(\alpha)}
\bigl(\pi_{\kappa(\alpha)}(x),\pi_{\kappa(\alpha)}(y)\bigr)\right).
$$
保幂指标之间的过渡映射保持有限幂运算：在两个输入类中分别取自然数代表即可验证。结合 $\kappa$ 的保序性，上式的输出坐标相容，因此定义了 $K_I$ 中的点。三种运算的每个输出坐标都由两个有限输入坐标决定，故对积拓扑联合连续；它们在自然数像上分别等于原来的加法、乘法与幂。$\iota_I(\mathbb{N})^2$ 稠密而目标 Hausdorff，故每种联合连续延拓唯一。通过 $\Phi$ 搬运即得 $K_J$ 上的相同延拓；唯一性保证比较同胚保持三种运算。

这里幂的因子化只使用
$$
a\mathrel{R_{\kappa(\alpha)}}a'
\quad \land\quad b\mathrel{R_{\kappa(\alpha)}}b'
\quad\Longrightarrow\quad
q_\alpha(a^b)=q_\alpha((a')^{b'}).
$$
它不蕴含 $R_\alpha$ 本身保幂。例如 $\alpha=(0,2)$ 时，两个输入对 $(0,0)$、$(0,2)$ 在同层的两个槽位分别不可区分，却有 $0^0=1$、$0^2=0$，输出奇偶不同；而 $\kappa(0,2)=(1,2)$ 提供了足够的较细输入。这也与[《递归关系观察》第 11.3 条](https://raw.githubusercontent.com/the-omega-institute/trureturing/d75daccad7efe749379873a4b5f8dbba95a862f9/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md) 的零指数分离一致。证毕。

**定义 14.0b（逆向运算、严格总响应与目标拓扑）。** 以下取 $K=K_I$，并通过定理 14.1 的同胚识别另一完成，记 $\iota=\iota_I$。定义截断减法
$$
F(n,m)=\max\{n-m,0\}.
$$
令
$$
K^\perp=\{\perp\}\sqcup\operatorname{ok}(K)
$$
取拓扑不交并，其中 $\operatorname{ok}:K\to\operatorname{ok}(K)$ 为同胚；两个分量都开闭，且 $\perp$ 为孤立点。严格部分减法的总响应定义为
$$
D(n,m)=
\begin{cases}
\operatorname{ok}(\iota(n-m)),&n\ge m,\\
\perp,&n<m.
\end{cases}
$$
其延拓要求在整个 $K^2$ 上定义，并与所有实际自然数输入的成功或失败响应相符。特别地，$\operatorname{ok}(\iota(0))\ne\perp$。

有限严格输出空间与投影定义为
$$
Q_\alpha^\perp=\{\perp\}\sqcup\operatorname{ok}(Q_\alpha),
\qquad
\pi_\alpha^\perp(\perp)=\perp,
\qquad
\pi_\alpha^\perp(\operatorname{ok}(x))
=\operatorname{ok}(\pi_\alpha(x)).
$$
所谓分别连续延拓，是指每个固定 $x\in K$ 的第二槽切片以及每个固定 $y\in K$ 的第一槽切片都连续；这里固定参数遍历整个完成，不限于实际自然数像。

**定理 14.2（减法的有限逃逸、实际参数切片与分别连续性的障碍）。** 对每个非平凡输出指标 $\alpha\in I\setminus\{(0,1)\}$，都有
$$
\forall\beta,\gamma\in I\quad \exists n,n',m,m'\in\mathbb{N},\quad
n\mathrel{R_\beta}n'
\quad \land\quad m\mathrel{R_\gamma}m'
\quad \land\quad q_\alpha(F(n,m))\ne q_\alpha(F(n',m')).
$$
对于 $\alpha=(0,1)$，截断减法的输出读数恒定，这是唯一例外。严格总响应则对每个输出指标，包括 $(0,1)$，都有
$$
\forall\alpha\in I\quad \forall\beta,\gamma\in I\quad \exists n,n',m,m'\in\mathbb{N},\quad
n\mathrel{R_\beta}n'
\quad \land\quad m\mathrel{R_\gamma}m'
\quad \land\pi_\alpha^\perp(D(n,m))\ne\pi_\alpha^\perp(D(n',m')).
$$
因而不存在分别延拓 $\iota\circ F$ 与 $D$ 的联合连续映射
$$
K^2\longrightarrow K,
\qquad
K^2\longrightarrow K^\perp.
$$
这些失败结论在仅采用保幂输入精度的系统中仍成立。

然而，对每个固定实际参数 $c\in\mathbb{N}$，以下四个一元映射都具有唯一连续延拓：
$$
n\longmapsto\iota(F(n,c)),
\qquad
m\longmapsto\iota(F(c,m)),
$$
$$
n\longmapsto D(n,c),
\qquad
m\longmapsto D(c,m).
$$
对于指定输出指标 $\alpha=(t,p)$，第一槽变化的两个映射可使用输入精度 $(t+c,p)$；第二槽变化的两个映射可使用输入精度 $(c+1,1)$。在 $J$ 中，把这两个指标分别替换为其 $\kappa$ 细化仍足够。

尽管上述所有实际参数切片都能延拓，两个二元响应均不存在定义于整个 $K^2$ 的分别连续延拓。具体地，令 $s_k=k!$，则存在
$$
\omega=\lim_{k\to\infty}\iota(s_k)\ne\iota(0).
$$
记
$$
f_{k,l}=\iota(F(s_k,s_l)),
\qquad
d_{k,l}=D(s_k,s_l).
$$
下面每个内层与外层极限都存在，但
$$
\lim_{l\to\infty}\lim_{k\to\infty}f_{k,l}=\omega,
\qquad
\lim_{k\to\infty}\lim_{l\to\infty}f_{k,l}=\iota(0),
$$
$$
\lim_{l\to\infty}\lim_{k\to\infty}d_{k,l}=\operatorname{ok}(\omega),
\qquad
\lim_{k\to\infty}\lim_{l\to\infty}d_{k,l}=\perp.
$$

**证明。** 首先明确有限因子化所使用的目标。给各 $Q_\alpha^\perp$ 的过渡映射保留失败标签，并在成功分量使用 $b_{\beta\alpha}$。一个相容线程的所有坐标具有同一成功或失败标签：任意两个坐标可提升到共同更细坐标，而过渡映射不改变标签。因此全失败线程唯一；全成功线程恰对应一个 $K$ 中的点。逐坐标映射给出
$$
K^\perp\cong\varprojlim_{\alpha\in I}Q_\alpha^\perp,
$$
且两边的成功、失败分量都是开闭集，故这正是所指定的不交并拓扑。

对 $H=\iota\circ F$ 或 $H=D$，分别令 $r_\alpha=\pi_\alpha$ 或 $r_\alpha=\pi_\alpha^\perp$。把[《递归关系观察》第 4.4 条](https://raw.githubusercontent.com/the-omega-institute/trureturing/d75daccad7efe749379873a4b5f8dbba95a862f9/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md) 应用于共同共尾塔的乘积观察，联合连续延拓存在的充要条件是
$$
\forall\alpha\in I\quad \exists\beta,\gamma\in I\quad
\forall n,n',m,m'\in\mathbb{N},\quad
\bigl(n\mathrel{R_\beta}n'\quad \land\quad m\mathrel{R_\gamma}m'\bigr)
\Longrightarrow
r_\alpha(H(n,m))=r_\alpha(H(n',m')).
$$
允许两个输入精度不同不改变该判据，因为可将二者同时提升到一个共同共尾塔层。必要性也直接来自紧致性：连续的有限输出读数有有限个常值柱邻域覆盖，两个槽位分别取这些柱邻域涉及指标的共同细化，即得到统一输入精度。这里有限开闭覆盖可在单个更细逆极限层实现，亦见 [Stacks Project 引理 5.22.4](https://stacks.math.columbia.edu/tag/08ZW)。

固定输入指标 $\beta=(u,v)$、$\gamma=(w,z)$，取 $A\ge\max\{u,w\}$。先设截断减法的输出指标 $\alpha=(t,p)$ 满足 $t\ge1$。令 $M=\operatorname{lcm}(v,z)$，比较
$$
(n,m)=(A,A),
\qquad
(n',m')=(A+M,A).
$$
两个输入槽分别具有相同的指定读数，而截断减法的结果分别为 $0$ 与 $M$。由于 $M>0$ 且 $0<t$，$0$ 是 $R_{t,p}$ 的单元素类，故两个输出读数不同。

若 $t=0$、$p>1$，令
$$
M=2\operatorname{lcm}(v,z,p),
$$
并比较
$$
(n,m)=(A,A+1),
\qquad
(n',m')=(A+M,A+1).
$$
两个槽位的输入读数仍分别相同；输出为 $0$ 与 $M-1$，而
$$
M-1\equiv-1\not\equiv0\pmod p.
$$
这证明每个非平凡截断减法输出层的全输入精度逃逸。对于 $(0,1)$，$Q_{0,1}$ 只有一点，输出当然恒定。

对严格总响应，令 $M=\operatorname{lcm}(v,z)$，比较
$$
(n,m)=(A,A),
\qquad
(n',m')=(A,A+M).
$$
第一槽完全相同，第二槽在 $R_\gamma$ 下相关；两个响应却为
$$
D(A,A)=\operatorname{ok}(\iota(0)),
\qquad
D(A,A+M)=\perp.
$$
所有 $Q_\alpha^\perp$ 都保留这个区别，即使 $Q_\alpha$ 本身只有一点。因此严格响应在每个输出层都有所断言的逃逸。由有限因子化判据，两个联合连续延拓都不存在。反例对全部 $\beta,\gamma\in I$ 成立，自然也对 $J$ 中的输入精度成立。

现在固定实际参数 $c$。若
$$
n\mathrel{R_{t+c,p}}n',
$$
则或者 $n=n'$，或者两者都不小于 $t+c\ge c$，且模 $p$ 同余。后一种情形中，两次减法均成功，差值均不小于 $t$ 且模 $p$ 同余。因此 $(t+c,p)$ 同时决定指定层的截断结果和严格响应；可能失败的输入 $n<c$ 在此精度下不会与不同输入混同。

若变化的是第二槽，则 $R_{c+1,1}$ 将 $0,1,\ldots,c$ 分别保留为单元素类，并把所有 $m>c$ 放入同一尾类。在单元素类上结果完全确定；在尾类上，截断结果恒为 $0$，严格响应恒为 $\perp$。特别地，$m=c$ 的成功零值不会与 $m>c$ 的失败混同。于是对每个有限输出层都有一个足够的一元输入精度，第 4.4 条给出四种连续延拓；自然数像稠密且相应目标 Hausdorff，故延拓唯一。进一步细化输入不会破坏因子化，所以 $\kappa$ 替换同样有效。

最后证明分别连续延拓的障碍。在 profinite 半群中，阶乘幂序列收敛的标准事实见 [Kyriakoglou–Perrin，*Profinite semigroups*，arXiv:1703.10088v1，第 5.5 节](https://arxiv.org/html/1703.10088v1)；以下直接给出本处所需、同时包含固定自然数偏移的坐标证明。

对 $\alpha=(t,p)$，记 $\tau_\alpha(\bar r)$ 为其尾部中模 $p$ 剩余类 $\bar r$ 所对应的商类。固定 $c\in\mathbb{N}$。当 $k$ 足够大时，$p\mid k!$ 且 $k!-c\ge t$，所以
$$
q_\alpha(F(k!,c))=\tau_\alpha(\overline{-c}).
$$
因此每个有限坐标最终恒定；这些最终坐标相容，因为过渡等式在原序列的每一项上成立。于是存在
$$
\omega_c=\lim_{k\to\infty}\iota(F(k!,c))\in K,
\qquad
\pi_\alpha(\omega_c)=\tau_\alpha(\overline{-c}).
$$
取 $c=0$ 得 $\omega=\omega_0=\lim_k\iota(k!)$。在指标 $(1,1)$ 上，$\omega$ 的坐标是正数尾类，而 $\iota(0)$ 的坐标是零的单元素类，故 $\omega\ne\iota(0)$。

再令 $c=s_l=l!$。对每个固定输出周期 $p$，当 $l$ 足够大时 $p\mid s_l$，所以
$$
\pi_\alpha(\omega_{s_l})
=\tau_\alpha(\overline{-s_l})
=\tau_\alpha(\bar0)
=\pi_\alpha(\omega).
$$
因而 $\omega_{s_l}\to\omega$。固定 $l$ 后，让 $k\to\infty$，得到
$$
\lim_{k\to\infty}f_{k,l}=\omega_{s_l},
\qquad
\lim_{k\to\infty}d_{k,l}=\operatorname{ok}(\omega_{s_l}),
$$
因为此时最终都有 $s_k\ge s_l$。再令 $l\to\infty$，得到第一种顺序的两个极限。

另一方面，固定 $k$ 后，当 $l$ 足够大时 $s_l>s_k$，所以
$$
f_{k,l}=\iota(0),
\qquad
d_{k,l}=\perp.
$$
先令 $l\to\infty$ 再令 $k\to\infty$，得到第二种顺序的两个极限。以上全部收敛都发生在明确指定的 $K$ 或 $K^\perp$ 拓扑中。

若存在任一响应的分别连续延拓 $\widetilde H$，由于两个输入序列都收敛到 $\omega$，先对一个固定输入使用切片连续性，再对另一个输入使用切片连续性，必有
$$
\lim_{l\to\infty}\lim_{k\to\infty}
\widetilde H(\iota(s_k),\iota(s_l))
=\widetilde H(\omega,\omega)
=\lim_{k\to\infty}\lim_{l\to\infty}
\widetilde H(\iota(s_k),\iota(s_l)).
$$
对截断减法，这将强制 $\omega=\iota(0)$；对严格响应，这将强制 $\operatorname{ok}(\omega)=\perp$。二者均矛盾，故分别连续延拓也不存在。证毕。

## 追加锚（本行以下为增补区）
## 15. 连续辅助观察：有限覆盖标签与对跖商的欧氏障碍

**定义 15.0（覆盖、纤维分离与三种辅助量）。** 记 $\mathbb N_0=\{0,1,2,\ldots\}$，$[N]=\{1,\ldots,N\}$，其中 $[0]=\varnothing$，并给每个 $[N]$ 离散拓扑。设 $X,B$ 为 Hausdorff 空间，$B\ne\varnothing$，$d\ge1$ 为固定整数。称连续满射 $q:X\to B$ 为固定 $d$ 页覆盖，若每个 $b\in B$ 都有开邻域 $U$，使
$$
q^{-1}(U)=\bigsqcup_{i=1}^{d}V_i,
\qquad
q|_{V_i}:V_i\longrightarrow U
$$
是同胚，且各 $V_i$ 在 $X$ 中开。特别地，每条纤维恰有 $d$ 个点。本节不预设 $X$ 或 $B$ 连通。

对映射 $r:X\to Y$，称 $r$ 分离 $q$ 的纤维，若
$$
q(x)=q(y)\ \land\ r(x)=r(y)\quad\Longrightarrow\quad x=y.
$$
这等价于联合映射
$$
J_r=(q,r):X\longrightarrow B\times Y
$$
单射。这里对联合观察 $J_r$ 应用定理 2.2，目标取 $\operatorname{id}_X$；要求恢复的是点本身，而不是只恢复某个较粗目标。覆盖在 $B$ 上的平凡化，是满足 $\operatorname{pr}_B\circ H=q$ 的同胚 $H:X\to B\times[d]$。连续截面是满足 $q\circ s=\operatorname{id}_B$ 的连续映射 $s:B\to X$。

定义
$$
\lambda_{\mathrm{set}}(q)
=
\min\{N\in\mathbb N_0:\exists r:X\to[N],\ J_r\text{ 单射}\},
$$
$$
\lambda_{\mathrm{disc}}(q)
=
\min\{N\in\mathbb N_0:\exists\text{ 连续 }r:X\to[N],\ J_r\text{ 单射}\},
$$
$$
\mu_{\mathbb R}(q)
=
\min\{m\in\mathbb N_0:\exists\text{ 连续 }r:X\to\mathbb R^m,\ J_r\text{ 单射}\}.
$$
候选集合为空时，相应值约定为 $\infty$；$\mathbb R^0$ 是单点空间。第一项不要求标签连续，第二项要求离散标签连续，第三项最小化固定商映射下连续欧氏辅助读数的坐标数。

覆盖的局部页定义参考：Allen Hatcher，*Algebraic Topology*，§1.3，第 56 页，[原书](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf)。

**定理 15.1（恰好一页一个标签的精确等价）。** 对定义 15.0 的固定 $d$ 页覆盖，以下三种数据相互确定：

（甲）连续映射 $r:X\to[d]$，在每条 $q$-纤维上单射。

（乙）在 $B$ 上的平凡化 $H:X\to B\times[d]$。

（丙）有序的 $d$ 条连续截面 $s_1,\ldots,s_d$，满足对每个 $b\in B$，
$$
s_i(b)\ne s_j(b)\quad(i\ne j),
\qquad
q^{-1}(b)=\{s_1(b),\ldots,s_d(b)\}.
$$
对应关系为
$$
H(x)=(q(x),r(x)),
\qquad
s_i(b)=H^{-1}(b,i),
\qquad
r(s_i(b))=i.
$$
因此，对给定的 $r$，逐纤维单射恰好保证 $(q,r)$ 本身是平凡化，而不只是集合双射。此结论包括 $d=1$，不要求连通性。

**证明。** 先证覆盖映射 $q$ 是开映射。若 $O\subseteq X$ 开，在任意均匀覆盖邻域 $U$ 上，
$$
q(O)\cap U=\bigcup_{i=1}^{d}q(O\cap V_i),
$$
右侧在 $U$ 中开，故 $q(O)$ 在 $B$ 中开。

给定甲，令 $X_i=r^{-1}(\{i\})$。这些集合开闭。每条纤维有 $d$ 个点，标签也恰有 $d$ 个，故逐纤维单射实际是逐纤维双射。因此
$$
q_i=q|_{X_i}:X_i\longrightarrow B
$$
是连续双射。由于 $X_i$ 开且 $q$ 开，$q_i$ 也是开映射，因而是同胚。令 $s_i=q_i^{-1}$，便得到丙；同时 $H=(q,r)$ 的逆映射在每个开片 $B\times\{i\}$ 上为 $(b,i)\mapsto s_i(b)$，故连续，得到乙。

给定乙，公式 $s_i(b)=H^{-1}(b,i)$ 直接给出丙。为从丙恢复甲，须验证截面像确实开，而不能只用集合分解。取 $x=s_i(b)$，选取含 $b$ 的均匀覆盖邻域 $U$ 及含 $x$ 的局部页 $V$。集合
$$
W=U\cap s_i^{-1}(V)
$$
是含 $b$ 的开邻域。由截面方程和 $q|_V$ 的单射性，
$$
s_i(W)=V\cap q^{-1}(W),
$$
故 $s_i(W)$ 在 $X$ 中开。于是每个 $s_i(B)$ 都开；其补集是其余截面像的并，故也开。由穷尽性与互异性定义 $r(s_i(b))=i$，每个单点的原像均开，所以 $r$ 连续，并且逐纤维单射。

上述公式还说明三次构造彼此互逆。若 $d=1$，同一证明表明 $q$ 是同胚，唯一标签与唯一截面分别为常值标签与 $q^{-1}$。证毕。

**定理 15.2（增加有限离散标签不能绕过平凡化障碍）。** 对定义 15.0 的覆盖及任意 $N\in\mathbb N_0$，
$$
\exists\text{ 连续 }r:X\to[N]\text{ 分离 }q\text{ 的纤维}
\quad\Longleftrightarrow\quad
N\ge d\ \land\ q\text{ 在 }B\text{ 上平凡}.
$$
特别地，
$$
\lambda_{\mathrm{disc}}(q)=
\begin{cases}
d,&q\text{ 平凡},\\
\infty,&q\text{ 不平凡}.
\end{cases}
$$
此处不需要 $B$ 连通。

更精确地，对任何这样的 $r$，令
$$
S(b)=\{r(x):q(x)=b\}\subseteq[N].
$$
则 $S(b)$ 恒有 $d$ 个元素，且 $b\mapsto S(b)$ 局部常值。联合映射 $(q,r)$ 是到开闭子空间
$$
E_r=\{(b,a)\in B\times[N]:a\in S(b)\}
$$
的同胚。若 $N>d$，则 $E_r\ne B\times[N]$；迫使平凡化的是可以把标签连续压缩到 $d$ 个，而不是原联合映射满射到较大乘积。

**证明。** 纤维非空且恰有 $d$ 个点，逐纤维单射首先给出 $N\ge d$。固定 $b_0\in B$，取均匀覆盖邻域 $U$，记各局部逆分支为 $t_i:U\to V_i$。每个 $r\circ t_i$ 连续且值域离散，因此
$$
W=\bigcap_{i=1}^{d}
(r\circ t_i)^{-1}\bigl(\{r(t_i(b_0))\}\bigr)
$$
是 $U$ 中含 $b_0$ 的开邻域。在 $W$ 上，每条局部页的标签都恒定，故 $S$ 恒定。这里仅取有限次交，没有使用局部连通性或连通性。

按 $[N]$ 的通常次序定义
$$
\rho(x)
=
1+\#\{a\in S(q(x)):a<r(x)\}.
$$
对每条纤维，$\rho$ 就是其 $d$ 个不同标签的次序排名，故取遍 $[d]$ 且单射。在刚构造的 $W$ 上，$\rho$ 在每条局部页上恒定；这些局部页是开集并覆盖 $X$，所以 $\rho:X\to[d]$ 连续。由定理 15.1，$(q,\rho)$ 是平凡化。反之，平凡化提供连续的 $d$ 值标签，再与任意单射 $[d]\to[N]$ 复合即可。

在同一个 $W$ 上，
$$
E_r\cap(W\times[N])=W\times S(b_0).
$$
因此 $E_r$ 及其补集都局部为开集，故 $E_r$ 开闭。映射 $(q,r)$ 在 $q^{-1}(W)$ 上把不同局部页同胚地送到不同的片 $W\times\{a\}$，所以其逆映射局部连续，进而在 $E_r$ 上连续。若 $N>d$，每个 $b$ 上都有未使用标签，故 $E_r$ 是真子集。

若 $B$ 连通，局部常值映射 $S$ 进一步必为常值，此时可以固定一个 $d$ 元子集统一重编号；平凡化结论并不需要这一步。无连通性时，排名一般依赖 $(q(x),r(x))$，不能断言只对 $r(x)$ 作一个固定后处理便可压缩。对此有明确反例：令
$$
B=\bigl\{\{1,2\},\{1,3\},\{2,3\}\bigr\},
\qquad
X=\{(A,a):A\in B,\ a\in A\},
$$
两者都取离散拓扑，令 $q(A,a)=A$、$r(A,a)=a$。这是两页覆盖及连续三值分离标签。任意函数 $\varphi:[3]\to[2]$ 都把某两个不同元素送到同一值，而这两个元素恰构成某条纤维的标签集，故 $\varphi\circ r$ 不分离该纤维。上述依赖 $q$ 的排名仍给出连续二值分离标签。证毕。

**命题 15.3（一个一般覆盖截面只保证劈出一页）。** 对定义 15.0 的覆盖，若存在连续截面 $s$，则 $s(B)$ 在 $X$ 中开闭，且
$$
q|_{s(B)}:s(B)\longrightarrow B
$$
是同胚。若 $d\ge2$，则限制映射
$$
q|_{X\setminus s(B)}:X\setminus s(B)\longrightarrow B
$$
是固定 $d-1$ 页覆盖。因此两页覆盖有一个连续截面当且仅当平凡，但一般有限覆盖不能把一个截面等同于完全平凡化；即使基空间连通也不能。

**证明。** 截面像开及限制映射为同胚，已由定理 15.1 证明中的局部论证给出，该论证不需要其他截面。固定 $b\in B$，选取均匀覆盖邻域 $U$，把含 $s(b)$ 的局部页记为 $V_1$，并缩小到
$$
W=U\cap s^{-1}(V_1).
$$
在 $W$ 上，$s$ 恰为第一局部逆分支，所以
$$
q^{-1}(W)\setminus s(B)
=
\bigsqcup_{i=2}^{d}\bigl(V_i\cap q^{-1}(W)\bigr).
$$
这既证明补集开，也证明它是固定 $d-1$ 页覆盖。若 $d=2$，补集上的一页覆盖是同胚，其逆给出第二条截面，再用定理 15.1 即得平凡化。

为证明最后的否定结论，取两个圆周的拓扑不交并
$$
X=S^1\sqcup S^1,\qquad B=S^1,
$$
并令第一份上的映射为 $z\mapsto z$，第二份上的映射为 $z\mapsto z^2$。小圆弧有两条连续平方根分支，故这是三页覆盖。第一份圆周的包含给出连续截面。然而若它平凡，定理 15.1 将给出连续三值分离标签。第二份圆周连通，所以该标签在第二份上必为常值；但其中 $z$ 与 $-z$ 是同一纤维中的不同点，矛盾。证毕。

圆周幂映射的覆盖结构参考：Hatcher，*Algebraic Topology*，§1.3，第 56 页，[原书](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf)。

**命题 15.4（紧致自由对合的差映射桥）。** 设 $K\ne\varnothing$ 为紧致 Hausdorff 空间，$\tau:K\to K$ 连续，满足
$$
\tau^2=\operatorname{id}_K,
\qquad
\tau(x)\ne x\quad(x\in K).
$$
令 $Q=K/\langle\tau\rangle$ 取商拓扑，$q:K\to Q$ 为轨道商。则 $Q$ 紧致 Hausdorff，$q$ 是两页覆盖。

对每个整数 $m\ge1$，以下存在性条件等价：存在连续纤维分离读数 $r:K\to\mathbb R^m$；存在连续映射 $f:K\to\mathbb R^m\setminus\{0\}$ 满足 $f(\tau x)=-f(x)$；存在连续映射 $u:K\to S^{m-1}$ 满足 $u(\tau x)=-u(x)$。其中球面取标准欧氏单位球面。

对给定的连续 $r$，有精确判据
$$
(q,r)\text{ 单射}
\quad\Longleftrightarrow\quad
\Delta_r(x):=r(x)-r(\tau x)\ne0\quad(\forall x\in K).
$$
满足判据时，
$$
u_r(x)=\frac{\Delta_r(x)}{\|\Delta_r(x)\|}
$$
是上述奇映射，而且
$$
\min_{x\in K}\|\Delta_r(x)\|>0.
$$
此时 $(q,r)$ 是到 $Q\times\mathbb R^m$ 中闭子空间的拓扑嵌入。零维欧氏目标不可能分离纤维；一维欧氏分离读数存在，当且仅当 $q$ 平凡，也当且仅当 $q$ 有一个连续截面。

**证明。** 由 $\tau^2=\operatorname{id}_K$，$\tau$ 是同胚。对开集 $V\subseteq K$，
$$
q^{-1}(q(V))=V\cup\tau(V)
$$
开，故商映射 $q$ 是开映射。对任意 $x$，用 Hausdorff 性选取分别包含 $x,\tau x$ 的不交开集 $A,C$。令 $V=A\cap\tau^{-1}(C)$，则 $x\in V$ 且 $V\cap\tau(V)=\varnothing$。于是
$$
q^{-1}(q(V))=V\sqcup\tau(V),
$$
而两片各自通过 $q$ 连续、开且双射地映到 $q(V)$，所以都是同胚。这证明两页覆盖性质。

不同轨道 $O,P$ 是互不相交的有限集。对每个 $a\in O$、$b\in P$，取包含相应点的不交开集 $A_{ab},C_{ab}$。令
$$
A_0=\bigcup_{a\in O}\bigcap_{b\in P}A_{ab},
\qquad
C_0=\bigcup_{b\in P}\bigcap_{a\in O}C_{ab}.
$$
它们分别包含 $O,P$，都是开集且互不相交。将它们替换为
$$
A_0\cap\tau(A_0),
\qquad
C_0\cap\tau(C_0),
$$
得到仍包含相应轨道的不交饱和开集；它们在商中的像是不交开邻域，故 $Q$ Hausdorff。它又是紧致空间 $K$ 的连续像，所以紧致。

商纤维恰为 $\{x,\tau x\}$，且两点不同。因此联合单射恰好要求 $r(x)\ne r(\tau x)$，即差映射处处非零。直接计算得到
$$
\Delta_r(\tau x)
=
r(\tau x)-r(\tau^2x)
=
-\Delta_r(x).
$$
非零差映射连续，除以其连续正范数就得到连续奇映射 $u_r$。反过来，若 $f$ 是处处非零的连续奇映射，则把 $f$ 本身作为读数，有
$$
f(x)-f(\tau x)=2f(x)\ne0.
$$
而球面值奇映射本来就处处非零。这证明三种存在性条件等价；并未假设原读数 $r$ 是奇映射。

连续正函数 $x\mapsto\|\Delta_r(x)\|$ 在非空紧致空间上取得最小值，该值不能为零。又因 $Q\times\mathbb R^m$ Hausdorff，任意闭集 $F\subseteq K$ 都紧致，其像 $(q,r)(F)$ 紧致而闭。所以联合映射在其实际像上的连续逆存在，且整个实际像紧致而闭，得到所述嵌入。

当 $m=0$ 时，读数只有一个值，不能区分任意一对 $x,\tau x$。当 $m=1$ 时，归一化的奇映射取值于离散两点集 $S^0=\{-1,1\}$，因而由定理 15.1 给出平凡化。反向地，任何平凡化的二值标签在每条二点纤维上取两个不同值，将它们分别记为 $-1,1$，即得连续奇实值读数。若只给一个连续截面 $s$，则 $s$ 与 $\tau\circ s$ 连续、逐点互异并穷尽纤维，仍由定理 15.1 得平凡化；平凡化当然给出截面。证毕。

局部轨道商覆盖参考：Hatcher，*Algebraic Topology*，命题 1.40(a)，第 72 页，[原书](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf)。差映射与归一化参考：Jiří Matoušek，*Using the Borsuk–Ulam Theorem*，§2.1，第 24 页，[第 2 章样章](https://beckassets.blob.core.windows.net/product/readingsample/250866/9783540003625_excerpt_001.pdf)。二值余坐标与截面的对应亦是《QUANTITATIVE_DIAGONALIZATION_OBSERVER_COMPLETION》[定理 5.1](https://raw.githubusercontent.com/the-omega-institute/trureturing/c4ef9baf3444a8e1992f6859eecc64e5faa6e0cb/docs/develop/theory/QUANTITATIVE_DIAGONALIZATION_OBSERVER_COMPLETION.md)的两元素群特例；上面的证明只使用本条明列的假设。

**定理 15.5（对跖商的集合二值补充与连续离散障碍）。** 对任意 $n\in\mathbb N_0$，令
$$
S^n=\left\{(x_0,\ldots,x_n)\in\mathbb R^{n+1}:
\sum_{i=0}^{n}x_i^2=1\right\},
\qquad
q_n:S^n\longrightarrow\mathbb{RP}^n=S^n/(x\sim-x).
$$
则 $q_n$ 是紧致 Hausdorff 空间之间的两页覆盖，并且
$$
\lambda_{\mathrm{set}}(q_n)=2.
$$
当 $n\ge1$ 时，不存在到任何离散空间的连续纤维分离读数，因而
$$
\lambda_{\mathrm{disc}}(q_n)=\infty,
$$
且 $q_n$ 无连续截面、不平凡。当 $n=0$ 时，
$$
S^0=\{-1,1\},
\qquad
\mathbb{RP}^0=\{*\},
\qquad
\lambda_{\mathrm{disc}}(q_0)=2,
$$
并且 $q_0$ 平凡。

**证明。** 对合 $\tau(x)=-x$ 连续且自由，因为单位向量不可能等于其负向量。球面非空、紧致 Hausdorff，故命题 15.4 给出商空间性质和两页覆盖。

对于任意 $x\in S^n$，定义
$$
k(x)=\min\{i\in\{0,\ldots,n\}:x_i\ne0\},
\qquad
\varepsilon(x)=
\begin{cases}
1,&x_{k(x)}>0,\\
-1,&x_{k(x)}<0.
\end{cases}
$$
至少一个坐标非零，所以定义总是有意义。显然 $k(-x)=k(x)$ 且 $\varepsilon(-x)=-\varepsilon(x)$。将 $1,-1$ 重编号为 $1,2$，得到分离每条纤维的二值集合标签。另一方面，任何一条纤维都有两个不同点，故少于两个标签不可能分离它。这证明集合标签数恰为二，并且不需要从每条纤维任意选择代表。事实上还得到显式集合截面
$$
s([x])=\varepsilon(x)x,
$$
因为右侧在把 $x$ 替换成 $-x$ 时不变。

当 $n\ge1$ 时，$S^n$ 道路连通：若 $x,y$ 不互为对跖点，规范化线段
$$
t\longmapsto
\frac{(1-t)x+ty}{\|(1-t)x+ty\|},
\qquad 0\le t\le1,
$$
给出连接二者的道路；若 $y=-x$，在 $\mathbb R^{n+1}$ 中选一个不与 $x$ 共线的单位向量，经过它连接两段上述道路。连续映射把连通空间送到连通子空间，而离散空间的非空连通子空间只能是单点。因此任何连续离散读数都恒定，不能区分 $x$ 与 $-x$。由定理 15.1 和命题 15.3，两页覆盖的平凡化及连续截面也均不存在。特别地，刚构造的集合二值标签与集合截面在这些维数下不能是连续的。

当 $n=0$ 时，定义域就是离散两点集，商是单点。标签 $\varepsilon(x)=x$ 连续并分离该纤维，且 $q_0$ 显然是单点基空间上的平凡两页覆盖。证毕。

**定理 15.6（对跖商的最小连续欧氏辅助坐标数）。** 对任意 $n,m\in\mathbb N_0$，
$$
\exists\text{ 连续 }r:S^n\to\mathbb R^m
\text{ 使 }(q_n,r)\text{ 单射}
\quad\Longleftrightarrow\quad
m\ge n+1.
$$
因此
$$
\mu_{\mathbb R}(q_n)=n+1,
$$
且满足单射条件的每个联合映射，都是到 $\mathbb{RP}^n\times\mathbb R^m$ 中闭子空间的拓扑嵌入。结合定理 15.5，
$$
\bigl(\lambda_{\mathrm{set}}(q_n),
\lambda_{\mathrm{disc}}(q_n),
\mu_{\mathbb R}(q_n)\bigr)
=
\begin{cases}
(2,2,1),&n=0,\\
(2,\infty,n+1),&n\ge1.
\end{cases}
$$
等价地，对 $m\ge1$，存在连续奇映射 $S^n\to S^{m-1}$ 当且仅当 $m\ge n+1$。

**证明。** 下界使用 Borsuk–Ulam 定理的如下形式：对每个整数 $k\ge0$ 和每个连续映射 $F:S^k\to\mathbb R^k$，存在 $x\in S^k$ 使 $F(x)=F(-x)$。这里不要求 $F$ 为奇映射。参考：Matoušek，*Using the Borsuk–Ulam Theorem*，定理 2.1.1 的 BU1a，第 23 页，及第 24 页与 BU1b 的等价证明，[第 2 章样章](https://beckassets.blob.core.windows.net/product/readingsample/250866/9783540003625_excerpt_001.pdf)；亦见 Hatcher，*Algebraic Topology*，推论 2B.7，第 176 页，[原书](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf)。

首先，$m=0$ 时读数恒定，任意对跖点仍有相同联合读数，所以对所有 $n\ge0$ 都不可能单射。其次，设 $n\ge1$ 且 $1\le m\le n$。对任意连续 $r:S^n\to\mathbb R^m$，补零得到连续映射
$$
\widetilde r:S^n\longrightarrow\mathbb R^n,
\qquad
\widetilde r(x)=\bigl(r(x),0_{\mathbb R^{n-m}}\bigr).
$$
当 $m=n$ 时这里就是原映射。Borsuk–Ulam 给出 $x$ 使
$$
\widetilde r(x)=\widetilde r(-x),
$$
于是 $r(x)=r(-x)$；同时 $q_n(x)=q_n(-x)$ 且 $x\ne-x$，所以联合映射不单射。这同时覆盖 $m=n$ 和 $m<n$，证明任何可行的 $m$ 都至少为 $n+1$。

反向地，对 $m\ge n+1$，取
$$
r_m(x_0,\ldots,x_n)
=
\bigl(x_0,\ldots,x_n,0_{\mathbb R^{m-n-1}}\bigr).
$$
这是连续映射，并且
$$
r_m(-x)=-r_m(x),
\qquad
\|r_m(x)-r_m(-x)\|=2.
$$
因此它分离每条对跖纤维；在最小维数 $m=n+1$ 时就是标准包含 $r(x)=x$。联合映射的闭嵌入结论由命题 15.4 的紧致到 Hausdorff 论证得到。

若 $n=0$，前面已单独排除 $m=0$，而 $r(x)=x\in\mathbb R$ 区分 $S^0$ 的两点，所以最小值确为一，不需要对负维球面作任何约定。最后，奇球面映射的存在性等价由命题 15.4 直接得到。证毕。

**命题 15.7（圆周平方覆盖的精确对应）。** 将 $S^1$ 视为复平面的单位圆，令
$$
p:S^1\longrightarrow S^1,
\qquad p(z)=z^2.
$$
映射
$$
h:\mathbb{RP}^1\longrightarrow S^1,
\qquad h([z])=z^2
$$
是同胚，且 $p=h\circ q_1$。因此 $p$ 的集合标签数为二，不存在连续离散纤维分离标签，不存在连续全局截面，而连续欧氏辅助坐标数恰为二。一个达到上界的读数为
$$
r(z)=(\operatorname{Re}z,\operatorname{Im}z).
$$

**证明。** 平方在 $z$ 与 $-z$ 上取值相同，所以由商拓扑得到连续映射 $h$。若 $z^2=w^2$，则 $(z-w)(z+w)=0$，故 $w=z$ 或 $w=-z$，所以 $h$ 单射。每个单位复数写成 $e^{it}$ 后都有单位平方根 $e^{it/2}$，故 $h$ 满射。定义域紧致、值域 Hausdorff，因而这个连续双射是同胚。

对任意辅助目标 $Y$ 及读数 $r:S^1\to Y$，
$$
(p,r)=(h\times\operatorname{id}_Y)\circ(q_1,r).
$$
故两种商下的纤维分离条件完全相同。截面也通过 $h$ 互相转换：若 $p\circ s=\operatorname{id}_{S^1}$，则 $s\circ h$ 是 $q_1$ 的截面；若 $q_1\circ t=\operatorname{id}_{\mathbb{RP}^1}$，则 $t\circ h^{-1}$ 是 $p$ 的截面。现在应用定理 15.5、15.6 即得全部结论，所列实部与虚部读数就是标准平面包含。证毕。

## 追加锚（本行以下为增补区）
